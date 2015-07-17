/* -*- Mode: C; tab-width: 4; c-basic-offset: 4; indent-tabs-mode: nil -*- */
/*
 * Thread management for memcached.
 */
#include "memcached.h"
#include <assert.h>
#include <stdio.h>
#include <errno.h>
#include <stdlib.h>
#include <errno.h>
#include <string.h>
#include <pthread.h>

#ifdef __sun
#include <atomic.h>
#endif

#include <sys/mman.h>
#include "parsec.h"

#define ITEMS_PER_ALLOC 64

/* An item in the connection queue. */
typedef struct conn_queue_item CQ_ITEM;
struct conn_queue_item {
    int               sfd;
    enum conn_states  init_state;
    int               event_flags;
    int               read_buffer_size;
    enum network_transport     transport;
    CQ_ITEM          *next;
};

/* A connection queue. */
typedef struct conn_queue CQ;
struct conn_queue {
    CQ_ITEM *head;
    CQ_ITEM *tail;
    pthread_mutex_t lock;
};

/* Lock for cache operations (item_*, assoc_*) */
pthread_mutex_t cache_lock;

/* Connection lock around accepting new connections */
pthread_mutex_t conn_lock = PTHREAD_MUTEX_INITIALIZER;

#if !defined(HAVE_GCC_ATOMICS) && !defined(__sun)
pthread_mutex_t atomics_mutex = PTHREAD_MUTEX_INITIALIZER;
#endif

/* Lock for global stats */
static pthread_mutex_t stats_lock = PTHREAD_MUTEX_INITIALIZER;

/* Lock to cause worker threads to hang up after being woken */
static pthread_mutex_t worker_hang_lock;

/* Free list of CQ_ITEM structs */
static CQ_ITEM *cqi_freelist;
static pthread_mutex_t cqi_freelist_lock;

static pthread_mutex_t *item_locks;

static ck_spinlock_mcs_t *item_locks_mcs;

/* size of the item lock hash table */
static uint32_t item_lock_count;
unsigned int item_lock_hashpower;
#define hashsize(n) ((unsigned long int)1<<(n))
#define hashmask(n) (hashsize(n)-1)

static LIBEVENT_DISPATCHER_THREAD dispatcher_thread;

/*
 * Each libevent instance has a wakeup pipe, which other threads
 * can use to signal that they've put a new connection on its queue.
 */
static LIBEVENT_THREAD *threads;

/*
 * Number of worker threads that have finished setting themselves up.
 */
static int init_count = 0;
static pthread_mutex_t init_lock;
static pthread_cond_t init_cond;


static void thread_libevent_process(int fd, short which, void *arg);

unsigned short refcount_incr(unsigned short *refcount) {
    PARSEC_NOT_USED;
#ifdef HAVE_GCC_ATOMICS
    return __sync_add_and_fetch(refcount, 1);
#elif defined(__sun)
    return atomic_inc_ushort_nv(refcount);
#else
    unsigned short res;
    mutex_lock(&atomics_mutex);
    (*refcount)++;
    res = *refcount;
    mutex_unlock(&atomics_mutex);
    return res;
#endif
}

unsigned short refcount_decr(unsigned short *refcount) {
    PARSEC_NOT_USED;
#ifdef HAVE_GCC_ATOMICS
    return __sync_sub_and_fetch(refcount, 1);
#elif defined(__sun)
    return atomic_dec_ushort_nv(refcount);
#else
    unsigned short res;
    mutex_lock(&atomics_mutex);
    (*refcount)--;
    res = *refcount;
    mutex_unlock(&atomics_mutex);
    return res;
#endif
}

struct item_mcslock {
    ck_spinlock_mcs_context_t l;
    char padding[CACHE_LINE*2 - sizeof(ck_spinlock_mcs_context_t)];
} __attribute__((aligned(CACHE_LINE)));

/* 1 per thread for fast path lock ops. Allocate additional ones on
 * stack if holding multiple locks -- e.g. in item_alloc. */
struct item_mcslock item_mcslock[NUM_CPU] __attribute__((aligned(4096)));

void item_mcs_lock(uint32_t hv) {
    ck_spinlock_mcs_lock(&item_locks_mcs[hv & hashmask(item_lock_hashpower)], &(item_mcslock[thd_local_id].l));
}

void item_mcs_unlock(uint32_t hv) {
    ck_spinlock_mcs_unlock(&item_locks_mcs[hv & hashmask(item_lock_hashpower)], &(item_mcslock[thd_local_id].l));
}

/* try lock/unlock are not on fast path -- they need to pass in the
 * mcs lock context (from their stack). */
void *item_try_mcslock(uint32_t hv, void *lock_context) {
    ck_spinlock_mcs_t *l = &item_locks_mcs[hv & hashmask(item_lock_hashpower)];

    if (ck_spinlock_mcs_trylock(l, lock_context)) {
        return l;
    } 
    return NULL;
}

void item_try_mcsunlock(void *lock, void *lock_context) {
    ck_spinlock_mcs_unlock(lock, lock_context);
}

/* Special case. When ITEM_LOCK_GLOBAL mode is enabled, this should become a
 * no-op, as it's only called from within the item lock if necessary.
 * However, we can't mix a no-op and threads which are still synchronizing to
 * GLOBAL. So instead we just always try to lock. When in GLOBAL mode this
 * turns into an effective no-op. Threads re-synchronize after the power level
 * switch so it should stay safe.
 */
void *item_trylock(uint32_t hv) {
    pthread_mutex_t *lock = &item_locks[hv & hashmask(item_lock_hashpower)];
    if (pthread_mutex_trylock(lock) == 0) {
        return lock;
    }
    return NULL;
}

void item_trylock_unlock(void *lock) {
    mutex_unlock((pthread_mutex_t *) lock);

}

void item_lock(uint32_t hv) {
    mutex_lock(&item_locks[hv & hashmask(item_lock_hashpower)]);
}

void item_unlock(uint32_t hv) {
    mutex_unlock(&item_locks[hv & hashmask(item_lock_hashpower)]);
}

static void wait_for_thread_registration(int nthreads) {
    while (init_count < nthreads) {
        pthread_cond_wait(&init_cond, &init_lock);
    }
}

static void register_thread_initialized(void) {
    pthread_mutex_lock(&init_lock);
    init_count++;
    pthread_cond_signal(&init_cond);
    pthread_mutex_unlock(&init_lock);
    /* Force worker threads to pile up if someone wants us to */
    pthread_mutex_lock(&worker_hang_lock);
    pthread_mutex_unlock(&worker_hang_lock);
}

/* Must not be called with any deeper locks held:
 * item locks, cache_lock, stats_lock, etc
 */
void pause_threads(enum pause_thread_types type) {
    char buf[1];
    int i;

    buf[0] = 0;
    switch (type) {
        case PAUSE_ALL_THREADS:
            slabs_rebalancer_pause();
            lru_crawler_pause();
        case PAUSE_WORKER_THREADS:
            buf[0] = 'p';
            pthread_mutex_lock(&worker_hang_lock);
            break;
        case RESUME_ALL_THREADS:
            slabs_rebalancer_resume();
            lru_crawler_resume();
        case RESUME_WORKER_THREADS:
            pthread_mutex_unlock(&worker_hang_lock);
            break;
        default:
            fprintf(stderr, "Unknown lock type: %d\n", type);
            assert(1 == 0);
            break;
    }

    /* Only send a message if we have one. */
    if (buf[0] == 0) {
        return;
    }

    pthread_mutex_lock(&init_lock);
    init_count = 0;
    for (i = 0; i < settings.num_threads; i++) {
        if (write(threads[i].notify_send_fd, buf, 1) != 1) {
            perror("Failed writing to notify pipe");
            /* TODO: This is a fatal problem. Can it ever happen temporarily? */
        }
    }
    wait_for_thread_registration(settings.num_threads);
    pthread_mutex_unlock(&init_lock);
}

/*
 * Initializes a connection queue.
 */
static void cq_init(CQ *cq) {
    pthread_mutex_init(&cq->lock, NULL);
    cq->head = NULL;
    cq->tail = NULL;
}

/*
 * Looks for an item on a connection queue, but doesn't block if there isn't
 * one.
 * Returns the item, or NULL if no item is available
 */
static CQ_ITEM *cq_pop(CQ *cq) {
    CQ_ITEM *item;

    pthread_mutex_lock(&cq->lock);
    item = cq->head;
    if (NULL != item) {
        cq->head = item->next;
        if (NULL == cq->head)
            cq->tail = NULL;
    }
    pthread_mutex_unlock(&cq->lock);

    return item;
}

/*
 * Adds an item to a connection queue.
 */
static void cq_push(CQ *cq, CQ_ITEM *item) {
    item->next = NULL;

    pthread_mutex_lock(&cq->lock);
    if (NULL == cq->tail)
        cq->head = item;
    else
        cq->tail->next = item;
    cq->tail = item;
    pthread_mutex_unlock(&cq->lock);
}

/*
 * Returns a fresh connection queue item.
 */
static CQ_ITEM *cqi_new(void) {
    CQ_ITEM *item = NULL;
    pthread_mutex_lock(&cqi_freelist_lock);
    if (cqi_freelist) {
        item = cqi_freelist;
        cqi_freelist = item->next;
    }
    pthread_mutex_unlock(&cqi_freelist_lock);

    if (NULL == item) {
        int i;

        /* Allocate a bunch of items at once to reduce fragmentation */
        item = malloc(sizeof(CQ_ITEM) * ITEMS_PER_ALLOC);
        if (NULL == item) {
            STATS_LOCK();
            stats.malloc_fails++;
            STATS_UNLOCK();
            return NULL;
        }

        /*
         * Link together all the new items except the first one
         * (which we'll return to the caller) for placement on
         * the freelist.
         */
        for (i = 2; i < ITEMS_PER_ALLOC; i++)
            item[i - 1].next = &item[i];

        pthread_mutex_lock(&cqi_freelist_lock);
        item[ITEMS_PER_ALLOC - 1].next = cqi_freelist;
        cqi_freelist = &item[1];
        pthread_mutex_unlock(&cqi_freelist_lock);
    }

    return item;
}


/*
 * Frees a connection queue item (adds it to the freelist.)
 */
static void cqi_free(CQ_ITEM *item) {
    pthread_mutex_lock(&cqi_freelist_lock);
    item->next = cqi_freelist;
    cqi_freelist = item;
    pthread_mutex_unlock(&cqi_freelist_lock);
}


/*
 * Creates a worker thread.
 */
static void create_worker(void *(*func)(void *), void *arg) {
    pthread_t       thread;
    pthread_attr_t  attr;
    int             ret;

    pthread_attr_init(&attr);

    if ((ret = pthread_create(&thread, &attr, func, arg)) != 0) {
        fprintf(stderr, "Can't create thread: %s\n",
                strerror(ret));
        exit(1);
    }
}

/*
 * Sets whether or not we accept new connections.
 */
void accept_new_conns(const bool do_accept) {
    pthread_mutex_lock(&conn_lock);
    do_accept_new_conns(do_accept);
    pthread_mutex_unlock(&conn_lock);
}
/****************************** LIBEVENT THREADS *****************************/

/*
 * Set up a thread's information.
 */
static void setup_thread(LIBEVENT_THREAD *me) {
    me->base = event_init();
    if (! me->base) {
        fprintf(stderr, "Can't allocate event base\n");
        exit(1);
    }

    /* Listen for notifications from other threads */
    event_set(&me->notify_event, me->notify_receive_fd,
              EV_READ | EV_PERSIST, thread_libevent_process, me);
    event_base_set(me->base, &me->notify_event);

    if (event_add(&me->notify_event, 0) == -1) {
        fprintf(stderr, "Can't monitor libevent notify pipe\n");
        exit(1);
    }

    me->new_conn_queue = malloc(sizeof(struct conn_queue));
    if (me->new_conn_queue == NULL) {
        perror("Failed to allocate memory for connection queue");
        exit(EXIT_FAILURE);
    }
    cq_init(me->new_conn_queue);

    if (pthread_mutex_init(&me->stats.mutex, NULL) != 0) {
        perror("Failed to initialize mutex");
        exit(EXIT_FAILURE);
    }

    me->suffix_cache = cache_create("suffix", SUFFIX_SIZE, sizeof(char*),
                                    NULL, NULL);
    if (me->suffix_cache == NULL) {
        fprintf(stderr, "Failed to create suffix cache\n");
        exit(EXIT_FAILURE);
    }
}

/* alloc + link / replace. Flattened from the state machine. */
static int
set_key(char* key, int nkey, char *data, int nbytes)
{
    item *old_it, *it;
    uint32_t hv;
    int retry = 1;
start:
    lib_enter();
    /* alloc */
    it = item_alloc(key, nkey, 0, 0, nbytes+2);
    if (!it) {
        printf("ERROR: item_alloc failed once? \n");
        lib_exit();
        if (retry) {
            retry = 0;
             goto start;
        }
        printf("alloc failed\n");

        return -1;
    }
    memcpy(ITEM_data(it), data, nbytes);

    /* link / replace next */
    hv = hash(ITEM_key(it), it->nkey);

    /* bucket lock */
    item_mcs_lock(hv);

    old_it = do_item_get(key, it->nkey, hv);

    if (old_it != NULL) {
        item_replace(old_it, it, hv);
    } else {
        do_item_link(it, hv);
    }
    /* unlock */
    item_mcs_unlock(hv);

    lib_exit();

    return 0;
}

static int
test_get_key(char* key, int nkey)
{
    item *it;

    lib_enter();

    it = item_get(key, nkey);
    if (it)
        item_update(it);

    /* only safe to access before the _exit. We can invoke callback
     * function here. */
    lib_exit();

    if (!it) return 0;

    return 1;
}

/*
 * Worker thread: main event loop
 */
/* static void *worker_libevent(void *arg) { */
/*     LIBEVENT_THREAD *me = arg; */

/*     /\* Any per-thread setup can happen here; memcached_thread_init() will block until */
/*      * all threads have finished initializing. */
/*      *\/ */

/*     register_thread_initialized(); */

/*     event_base_loop(me->base, 0); */
/*     return NULL; */
/* } */

/*
 * Processes an incoming "handle a new connection" item. This is called when
 * input arrives on the libevent wakeup pipe.
 */
static void thread_libevent_process(int fd, short which, void *arg) {
    LIBEVENT_THREAD *me = arg;
    CQ_ITEM *item;
    char buf[1];

    if (read(fd, buf, 1) != 1)
        if (settings.verbose > 0)
            fprintf(stderr, "Can't read from libevent pipe\n");

    switch (buf[0]) {
    case 'c':
    item = cq_pop(me->new_conn_queue);

    if (NULL != item) {
        conn *c = conn_new(item->sfd, item->init_state, item->event_flags,
                           item->read_buffer_size, item->transport, me->base);
        if (c == NULL) {
            if (IS_UDP(item->transport)) {
                fprintf(stderr, "Can't listen for events on UDP socket\n");
                exit(1);
            } else {
                if (settings.verbose > 0) {
                    fprintf(stderr, "Can't listen for events on fd %d\n",
                        item->sfd);
                }
                close(item->sfd);
            }
        } else {
            c->thread = me;
        }
        cqi_free(item);
    }
        break;
    /* we were told to pause and report in */
    case 'p':
    register_thread_initialized();
        break;
    }
}

/* Which thread we assigned a connection to most recently. */
static int last_thread = -1;

/*
 * Dispatches a new connection to another thread. This is only ever called
 * from the main thread, either during initialization (for UDP) or because
 * of an incoming connection.
 */
void dispatch_conn_new(int sfd, enum conn_states init_state, int event_flags,
                       int read_buffer_size, enum network_transport transport) {
    CQ_ITEM *item = cqi_new();
    char buf[1];
    if (item == NULL) {
        close(sfd);
        /* given that malloc failed this may also fail, but let's try */
        fprintf(stderr, "Failed to allocate memory for connection object\n");
        return ;
    }

    int tid = (last_thread + 1) % settings.num_threads;

    LIBEVENT_THREAD *thread = threads + tid;

    last_thread = tid;

    item->sfd = sfd;
    item->init_state = init_state;
    item->event_flags = event_flags;
    item->read_buffer_size = read_buffer_size;
    item->transport = transport;

    cq_push(thread->new_conn_queue, item);

    MEMCACHED_CONN_DISPATCH(sfd, thread->thread_id);
    buf[0] = 'c';
    if (write(thread->notify_send_fd, buf, 1) != 1) {
        perror("Writing to thread notify pipe");
    }
}

/*
 * Returns true if this is the thread that listens for new TCP connections.
 */
int is_listen_thread() {
    return pthread_self() == dispatcher_thread.thread_id;
}

/********************************* ITEM ACCESS *******************************/

/*
 * Allocates a new item.
 */
item *item_alloc(char *key, size_t nkey, int flags, rel_time_t exptime, int nbytes) {
    item *it;
    /* do_item_alloc handles its own locks */
    it = do_item_alloc(key, nkey, flags, exptime, nbytes, 0);
    return it;
}

/*
 * Returns an item if it hasn't been marked as expired,
 * lazy-expiring as needed.
 */
item *item_get(const char *key, const size_t nkey) {
    item *it;
    uint32_t hv;
    
    hv = hash(key, nkey);
//    item_lock(hv);
    it = do_item_get(key, nkey, hv);
//    item_unlock(hv);
    
    return it;
}

item *item_touch(const char *key, size_t nkey, uint32_t exptime) {
    item *it;
    uint32_t hv;
    hv = hash(key, nkey);
    item_lock(hv);
    it = do_item_touch(key, nkey, exptime, hv);
    item_unlock(hv);
    return it;
}

/*
 * Links an item into the LRU and hashtable.
 */
int item_link(item *item) {
    int ret;
    uint32_t hv;

    hv = hash(ITEM_key(item), item->nkey);
    item_lock(hv);
    ret = do_item_link(item, hv);
    item_unlock(hv);
    return ret;
}

/*
 * Decrements the reference count on an item and adds it to the freelist if
 * needed.
 */
void item_remove(item *item) {
    uint32_t hv;
    hv = hash(ITEM_key(item), item->nkey);

    item_lock(hv);
    do_item_remove(item);
    item_unlock(hv);
}

/*
 * Replaces one item with another in the hashtable.
 * Unprotected by a mutex lock since the core server does not require
 * it to be thread-safe.
 */
int item_replace(item *old_it, item *new_it, const uint32_t hv) {
    return do_item_replace(old_it, new_it, hv);
}

/*
 * Unlinks an item from the LRU and hashtable.
 */
void item_unlink(item *item) {
    uint32_t hv;
    hv = hash(ITEM_key(item), item->nkey);
    item_lock(hv);
    do_item_unlink(item, hv);
    item_unlock(hv);
}

/*
 * Moves an item to the back of the LRU queue.
 */
void item_update(item *item) {
    /* uint32_t hv; */
    /* hv = hash(ITEM_key(item), item->nkey); */

//    item_lock(hv);
    do_item_update(item);
//    item_unlock(hv);
}

/*
 * Does arithmetic on a numeric item value.
 */
enum delta_result_type add_delta(conn *c, const char *key,
                                 const size_t nkey, int incr,
                                 const int64_t delta, char *buf,
                                 uint64_t *cas) {
    enum delta_result_type ret;
    uint32_t hv;

    hv = hash(key, nkey);
    item_lock(hv);
    ret = do_add_delta(c, key, nkey, incr, delta, buf, cas, hv);
    item_unlock(hv);
    return ret;
}

/*
 * Stores an item in the cache (high level, obeys set/add/replace semantics)
 */
enum store_item_type store_item(item *item, int comm, conn* c) {
    enum store_item_type ret;
    uint32_t hv;

    hv = hash(ITEM_key(item), item->nkey);
    item_lock(hv);
    ret = do_store_item(item, comm, c, hv);
    item_unlock(hv);
    return ret;
}

/*
 * Flushes expired items after a flush_all call
 */
void item_flush_expired() {
    mutex_lock(&cache_lock);
    do_item_flush_expired();
    mutex_unlock(&cache_lock);
}

/*
 * Dumps part of the cache
 */
char *item_cachedump(unsigned int slabs_clsid, unsigned int limit, unsigned int *bytes) {
    char *ret;

    mutex_lock(&cache_lock);
    ret = do_item_cachedump(slabs_clsid, limit, bytes);
    mutex_unlock(&cache_lock);
    return ret;
}

/*
 * Dumps statistics about slab classes
 */
void  item_stats(ADD_STAT add_stats, void *c) {
    mutex_lock(&cache_lock);
    do_item_stats(add_stats, c);
    mutex_unlock(&cache_lock);
}

void  item_stats_totals(ADD_STAT add_stats, void *c) {
    mutex_lock(&cache_lock);
    do_item_stats_totals(add_stats, c);
    mutex_unlock(&cache_lock);
}

/*
 * Dumps a list of objects of each size in 32-byte increments
 */
void  item_stats_sizes(ADD_STAT add_stats, void *c) {
    mutex_lock(&cache_lock);
    do_item_stats_sizes(add_stats, c);
    mutex_unlock(&cache_lock);
}

/******************************* GLOBAL STATS ******************************/

void STATS_LOCK() {
    PARSEC_NOT_USED;
    return;
    pthread_mutex_lock(&stats_lock);
}

void STATS_UNLOCK() {
    PARSEC_NOT_USED;
    return;
    pthread_mutex_unlock(&stats_lock);
}

void threadlocal_stats_reset(void) {
    int ii, sid;
    for (ii = 0; ii < settings.num_threads; ++ii) {
        pthread_mutex_lock(&threads[ii].stats.mutex);

        threads[ii].stats.get_cmds = 0;
        threads[ii].stats.get_misses = 0;
        threads[ii].stats.touch_cmds = 0;
        threads[ii].stats.touch_misses = 0;
        threads[ii].stats.delete_misses = 0;
        threads[ii].stats.incr_misses = 0;
        threads[ii].stats.decr_misses = 0;
        threads[ii].stats.cas_misses = 0;
        threads[ii].stats.bytes_read = 0;
        threads[ii].stats.bytes_written = 0;
        threads[ii].stats.flush_cmds = 0;
        threads[ii].stats.conn_yields = 0;
        threads[ii].stats.auth_cmds = 0;
        threads[ii].stats.auth_errors = 0;

        for(sid = 0; sid < MAX_NUMBER_OF_SLAB_CLASSES; sid++) {
            threads[ii].stats.slab_stats[sid].set_cmds = 0;
            threads[ii].stats.slab_stats[sid].get_hits = 0;
            threads[ii].stats.slab_stats[sid].touch_hits = 0;
            threads[ii].stats.slab_stats[sid].delete_hits = 0;
            threads[ii].stats.slab_stats[sid].incr_hits = 0;
            threads[ii].stats.slab_stats[sid].decr_hits = 0;
            threads[ii].stats.slab_stats[sid].cas_hits = 0;
            threads[ii].stats.slab_stats[sid].cas_badval = 0;
        }

        pthread_mutex_unlock(&threads[ii].stats.mutex);
    }
}

void threadlocal_stats_aggregate(struct thread_stats *stats) {
    int ii, sid;

    /* The struct has a mutex, but we can safely set the whole thing
     * to zero since it is unused when aggregating. */
    memset(stats, 0, sizeof(*stats));

    for (ii = 0; ii < settings.num_threads; ++ii) {
        pthread_mutex_lock(&threads[ii].stats.mutex);

        stats->get_cmds += threads[ii].stats.get_cmds;
        stats->get_misses += threads[ii].stats.get_misses;
        stats->touch_cmds += threads[ii].stats.touch_cmds;
        stats->touch_misses += threads[ii].stats.touch_misses;
        stats->delete_misses += threads[ii].stats.delete_misses;
        stats->decr_misses += threads[ii].stats.decr_misses;
        stats->incr_misses += threads[ii].stats.incr_misses;
        stats->cas_misses += threads[ii].stats.cas_misses;
        stats->bytes_read += threads[ii].stats.bytes_read;
        stats->bytes_written += threads[ii].stats.bytes_written;
        stats->flush_cmds += threads[ii].stats.flush_cmds;
        stats->conn_yields += threads[ii].stats.conn_yields;
        stats->auth_cmds += threads[ii].stats.auth_cmds;
        stats->auth_errors += threads[ii].stats.auth_errors;

        for (sid = 0; sid < MAX_NUMBER_OF_SLAB_CLASSES; sid++) {
            stats->slab_stats[sid].set_cmds +=
                threads[ii].stats.slab_stats[sid].set_cmds;
            stats->slab_stats[sid].get_hits +=
                threads[ii].stats.slab_stats[sid].get_hits;
            stats->slab_stats[sid].touch_hits +=
                threads[ii].stats.slab_stats[sid].touch_hits;
            stats->slab_stats[sid].delete_hits +=
                threads[ii].stats.slab_stats[sid].delete_hits;
            stats->slab_stats[sid].decr_hits +=
                threads[ii].stats.slab_stats[sid].decr_hits;
            stats->slab_stats[sid].incr_hits +=
                threads[ii].stats.slab_stats[sid].incr_hits;
            stats->slab_stats[sid].cas_hits +=
                threads[ii].stats.slab_stats[sid].cas_hits;
            stats->slab_stats[sid].cas_badval +=
                threads[ii].stats.slab_stats[sid].cas_badval;
        }

        pthread_mutex_unlock(&threads[ii].stats.mutex);
    }
}

void slab_stats_aggregate(struct thread_stats *stats, struct slab_stats *out) {
    int sid;

    out->set_cmds = 0;
    out->get_hits = 0;
    out->touch_hits = 0;
    out->delete_hits = 0;
    out->incr_hits = 0;
    out->decr_hits = 0;
    out->cas_hits = 0;
    out->cas_badval = 0;

    for (sid = 0; sid < MAX_NUMBER_OF_SLAB_CLASSES; sid++) {
        out->set_cmds += stats->slab_stats[sid].set_cmds;
        out->get_hits += stats->slab_stats[sid].get_hits;
        out->touch_hits += stats->slab_stats[sid].touch_hits;
        out->delete_hits += stats->slab_stats[sid].delete_hits;
        out->decr_hits += stats->slab_stats[sid].decr_hits;
        out->incr_hits += stats->slab_stats[sid].incr_hits;
        out->cas_hits += stats->slab_stats[sid].cas_hits;
        out->cas_badval += stats->slab_stats[sid].cas_badval;
    }
}

static void *worker_parsec(void *arg);

#include <sys/types.h>
#include <sys/stat.h>
#include <fcntl.h>

#define N_OPS 10000000
#define N_KEYS 1000000

#define KEY_LENGTH 16
#define V_LENGTH   (KEY_LENGTH * 2)

char ops[N_OPS][KEY_LENGTH + 1];

#define P99_CALC

#ifdef P99_CALC
// 99 percentile
#define N_LOG (N_OPS / 25) //4M * 4 = 16 MB
#define N_1P  (N_OPS / 100 / NUM_CPU)
unsigned long p99[N_LOG];
#endif

int load_trace(void);
void preload_keys(void);

void preload_keys(void)
{
    /* insert all the keys into the cache before accessing the
     * traces. If the cache is large enough, there will be no miss.*/
    int fd, i, ret;
    char buf[KEY_LENGTH + 1], v[V_LENGTH];
    int bytes;
    char *load_file = "../mc_trace/trace_load_key";

    ret = mlock(ops, N_OPS*(KEY_LENGTH + 1));
	if (ret) {
		printf("Cannot lock cache memory (%d). Check privilege. Exit.\n", ret);
		exit(-1);
	}

#ifdef P99_CALC
    ret = mlock(p99, N_LOG*(sizeof(unsigned long)));
	if (ret) {
		printf("Cannot lock cache memory (%d). Check privilege. Exit.\n", ret);
		exit(-1);
	}
#endif

    fd = open(load_file, O_RDONLY);
    if (fd < 0) {
        printf("cannot open file %s. Exit.\n", load_file);
        exit(-1);
    }

    for (i = 0; i < N_KEYS; i++) {
        bytes = read(fd, buf, KEY_LENGTH + 1);
        assert(bytes == KEY_LENGTH + 1);

        memcpy(v, buf, KEY_LENGTH);
        memcpy(&v[KEY_LENGTH], buf, KEY_LENGTH);

        ret = set_key(buf, KEY_LENGTH, v, V_LENGTH);
        assert(ret == 0);
    }
    close(fd);
}

int load_trace(void)
{
    int fd;
    int bytes;
    unsigned long i;
    char buf[KEY_LENGTH + 2];

    printf("loading trace file @%s...\n", TRACE_FILE);
    /* read the entire trace into memory. */
    fd = open(TRACE_FILE, O_RDONLY);
    if (fd < 0) {
        printf("cannot open file %s. Exit.\n", TRACE_FILE);
        exit(-1);
    }
    
    for (i = 0; i < N_OPS; i++) {
        bytes = read(fd, buf, KEY_LENGTH+2);
        assert(bytes == KEY_LENGTH + 2);
        assert(buf[KEY_LENGTH + 1] == '\n');
        memcpy(ops[i], buf, KEY_LENGTH + 1);
    }
    close(fd);

    return 0;
}

/*
 * Initializes the thread subsystem, creating various worker threads.
 *
 * nthreads  Number of worker event handler threads to spawn
 * main_base Event base for main thread
 */
void memcached_thread_init(int nthreads, struct event_base *main_base) {
    int         i;
    int         power;

    pthread_mutex_init(&cache_lock, NULL);
    pthread_mutex_init(&worker_hang_lock, NULL);

    pthread_mutex_init(&init_lock, NULL);
    pthread_cond_init(&init_cond, NULL);

    pthread_mutex_init(&cqi_freelist_lock, NULL);
    cqi_freelist = NULL;

    /* Want a wide lock table, but don't waste memory */
    if (nthreads < 3) {
        power = 10;
    } else if (nthreads < 4) {
        power = 11;
    } else if (nthreads < 5) {
        power = 12;
    } else {
        /* 8192 buckets, and central locks don't scale much past 5 threads */
        /* power = 13; */
        
        power = 13;
    }

    if (power >= hashpower) {
        fprintf(stderr, "Hash table power size (%d) cannot be equal to or less than item lock table (%d)\n", hashpower, power);
        fprintf(stderr, "Item lock table grows with `-t N` (worker threadcount)\n");
        fprintf(stderr, "Hash table grows with `-o hashpower=N` \n");
        exit(1);
    }

    item_lock_count = hashsize(power);
    item_lock_hashpower = power;

    item_locks     = calloc(item_lock_count, sizeof(pthread_mutex_t));
    item_locks_mcs = calloc(item_lock_count, sizeof(ck_spinlock_mcs_t));

    if (!item_locks_mcs) {
        perror("Can't allocate item locks");
        exit(1);
    }
    for (i = 0; i < item_lock_count; i++) {
        pthread_mutex_init(&item_locks[i], NULL);
        item_locks_mcs[i] = CK_SPINLOCK_MCS_INITIALIZER;
    }

    threads = calloc(nthreads, sizeof(LIBEVENT_THREAD));
    if (! threads) {
        perror("Can't allocate thread descriptors");
        exit(1);
    }

    dispatcher_thread.base = main_base;
    dispatcher_thread.thread_id = pthread_self();

    for (i = 0; i < nthreads; i++) {
        int fds[2];
        if (pipe(fds)) {
            perror("Can't create notify pipe");
            exit(1);
        }

        threads[i].notify_receive_fd = fds[0];
        threads[i].notify_send_fd = fds[1];
        threads[i].id = i;

        setup_thread(&threads[i]);
        /* Reserve three fds for the libevent base, and two for the pipe */
        stats.reserved_fds += 5;
    }

    parsec_init();

    printf("MC: loading trace file...\n");
    preload_keys();
    load_trace();

    printf("MC: creating %d worker threads\n", nthreads);
    for (i = 0; i < nthreads; i++) {
        create_worker(worker_parsec, &threads[i]);
    }

    /* Wait for all the threads to set themselves up before returning. */
    pthread_mutex_lock(&init_lock);
    wait_for_thread_registration(nthreads);
    pthread_mutex_unlock(&init_lock);
}

__attribute__ ((unused)) static void 
test_test(void)
{
    int i, j, k, ret;
    char aaa = 'a';
    char aa[4];
    char value[CACHE_LINE];

    printf("thd %d: starting set + get...\n", thd_local_id);
    memset(value, 0, CACHE_LINE);

    aa[0] = aaa;
    for (i = 0; i < 5; i++) {
        aa[1] = i;
        for (j = 0; j < 128; j++) {
            aa[2] = j;
            for (k = 0; k < 128; k++) {
                aa[3] = k;

//                printf("thd %d, %d %d %d\n", thd_local_id, i,j,k);
                ret = set_key(aa, 4, value, CACHE_LINE);
                if (ret) printf("--------------set failed?!\n");
            }
        }
        printf("thd %d, %d\n", thd_local_id, i);
    }

    printf("and counting ...\n");
    /* browse cache content */
    int tot = 0;
    for (i = 0; i < 128; i++) {
        aa[1] = i;
        for (j = 0; j < 128; j++) {
            aa[2] = j;
            for (k = 0; k < 128; k++) {
                /* printf("k %d\n", k); */
                aa[3] = k;
                ret = test_get_key(aa, 4);
                if (ret) {
                    /* count keys */
                    tot++;
                }
            }
        }
    }

    printf("Thd %d: verified tot %d keys in cache\n", thd_local_id, tot);

    return;
}

#define rdtscll(val) __asm__ __volatile__("rdtsc" : "=A" (val))

#ifdef P99_CALC
//#define AVG   (800)
//#define THRES (2*AVG)
static int cmpfunc(const void * a, const void * b)
{
    return ( *(int*)a - *(int*)b );
}
#endif

static void 
bench(void)
{
    int i, ret;
    unsigned long n_read = 0, n_update = 0;
#ifdef P99_CALC
    unsigned long n_large = 0;
#endif
    char *op, value[V_LENGTH], key[KEY_LENGTH];
    int id = thd_local_id, jump = settings.num_threads;
    unsigned long long s, e, s1, e1, tot_cost = 0, max = 0, cost;

    /* prepare the value -- no real database op needed. */
    memset(value, 1, V_LENGTH);

    rdtscll(s);
    for (i = id; i < N_OPS; i += jump) {
        op = ops[i];
        memcpy(key, &op[1], KEY_LENGTH);
//        key = &op[1];

        rdtscll(s1);        
        if (*op == 'R') {
            n_read++;

            ret = test_get_key(key, KEY_LENGTH);

            assert(ret);
            if (!ret) {
                /* If get returns null, do a set. */
                n_update++;
                ret = set_key(key, KEY_LENGTH, value, V_LENGTH);
                assert(ret == 0);
            }
            /* char *v = ITEM_data(it); */
            /* if (it) { */
            /*     for (j = 0; j < V_LENGTH; j++) { */
            /*         if (v[j] != op[1 + j % KEY_LENGTH]) { */
            /*             printf(" %d: %d, %d \n", j, v[j], op[1 + (j % KEY_LENGTH)]); */
            /*         } */
            /*         assert(v[j] == op[1 + j % KEY_LENGTH]); */
            /*     } */
            /* } */
        } else {
            assert(*op == 'U');
            n_update++;

            ret = set_key(key, KEY_LENGTH, value, V_LENGTH);
            assert(ret == 0);
        }
        rdtscll(e1);
        cost = e1-s1;
        tot_cost += cost;
        if (cost > max) max = cost;
#ifdef P99_CALC
        if (id == 0 && cost > THRES) {
            p99[n_large] = cost;
            if (n_large < N_LOG - 1) {
                n_large++;
            }
        }
#endif
    }
    rdtscll(e);

    if (id == 0) {
#ifdef P99_CALC
        if (n_large < N_LOG-1 && n_large >= N_1P) {
            qsort(p99, n_large, sizeof(unsigned long), cmpfunc);
            printf("[%d, (%lu), %d], largest %lu, 99p %lu\n", N_1P, n_large, N_LOG, p99[n_large - 1], p99[n_large - N_1P]);
        } else {
            printf("not enough samples for 99percentile... [%d, %d] -> got %lu\n", N_1P, N_LOG, n_large);
        }
#endif
        printf("Thd %d: tot %lu ops (r %lu, u %lu) done, %llu (%llu) cycles per op, max %llu\n", 
               (int)thd_local_id, n_read+n_update, n_read, n_update, (unsigned long long)(e-s)/(n_read + n_update), 
               tot_cost/(n_read+n_update),  max);
    } else {
        printf("Thd %d: tot %lu ops (r %lu, u %lu) done, %llu (%llu) cycles per op, max %llu\n", 
               (int)thd_local_id, n_read+n_update, n_read, n_update, (unsigned long long)(e-s)/(n_read + n_update), 
               tot_cost/(n_read+n_update),  max);
    }
}

volatile int done = 0;
static void *worker_parsec(void *arg) {
    LIBEVENT_THREAD *me = arg;

    thd_local_id = me->id;

    sleep(1);
    thd_set_affinity(pthread_self(), thd_local_id);
    set_prio();
    meas_sync_start();
//QW
    if (thd_local_id == 0) {
        bench();
    } else {
        bench();
    }
    meas_sync_end();

    register_thread_initialized();
    
    return 0;
}
