/* PARSEC library implementation */
#ifndef PARSEC_HEADER_H
#define PARSEC_HEADER_H

#include <ck_queue.h>
#include <ck_spinlock.h>

#include <stdbool.h>
#include <stdio.h>
#include <stdlib.h>
#ifndef __USE_GNU
#define __USE_GNU
#endif
#include <sched.h>
#include <pthread.h>
#include <assert.h>
#include <sys/time.h>
#include <unistd.h>
#include <errno.h>
#include <sys/syscall.h>
#include "memcached.h"

#define rdtscll(val) __asm__ __volatile__("rdtsc" : "=A" (val))

#ifndef CACHE_LINE
#define CACHE_LINE 64
#endif

#define MEAS_ITER (1<<20)

/* void * worker(void *arg); */

void thd_set_affinity(pthread_t tid, int cpuid);
void set_prio(void);

void meas_sync_start(void);
void meas_sync_end(void);

/* 
 * Return values:
 * 0 on failure due to contention (*target != old)
 * 1 otherwise (*target == old -> *target = updated)
 */
static inline int 
cos_cas(unsigned long *target, unsigned long old, unsigned long updated)
{
	char z;
	__asm__ __volatile__("lock cmpxchgl %2, %0; setz %1"
			     : "+m" (*target),
			       "=a" (z)
			     : "q"  (updated),
			       "a"  (old)
			     : "memory", "cc");
	return (int)z;
}

void * timer_update(void *arg);

static inline pthread_t 
create_timer_thd(int cpuid)
{
	pthread_t t;
	int ret;

	ret = pthread_create(&t, 0, timer_update, (void *)cpuid);
	if (ret < 0) exit(-1);
	assert(t);

	thd_set_affinity(t, cpuid);

	return t;
}

/********************************************************/

#ifndef likely
#define unlikely(x)   __builtin_expect(!!(x), 0)
#define likely(x)     __builtin_expect(!!(x), 1)
#endif

//#define CACHE_LINE (64)
#define CACHE_ALIGNED __attribute__((aligned(CACHE_LINE)))
#define PAGE_SIZE (4096)
#define PAGE_ALIGNED  __attribute__((aligned(PAGE_SIZE)))
#define PACKED __attribute__((packed))
#define EQUIESCENCE (200)

static inline void cos_mem_fence(void)
{
        __asm__ __volatile__("mfence" ::: "memory");
}

/* 2 cache lines for this struct to avoid false sharing caused by
 * prefetching. */
struct quiescence_timing {
	volatile quie_time_t time_in, time_out;
	volatile quie_time_t last_known_quiescence;
	char __padding[CACHE_LINE*2 - 3*sizeof(quie_time_t)];
} CACHE_ALIGNED PACKED;

struct other_cpu {
	quie_time_t time_in, time_out;
	quie_time_t time_updated;
};

struct percpu_info {
	/* Quiescence_timing info of this CPU */
	struct quiescence_timing timing;
	/* Quiescence_timing info of other CPUs known by this CPU */
	struct other_cpu timing_others[NUM_CPU];
	/* padding an additional cacheline for prefetching */
	char __padding[CACHE_LINE*2 - ((sizeof(struct other_cpu)*NUM_CPU) % CACHE_LINE)];
} CACHE_ALIGNED PACKED;

struct percpu_info timing_info[NUM_CPU];

struct global_timestamp {
	quie_time_t ts;
	char __padding[CACHE_LINE*2 - sizeof(quie_time_t)];
} PACKED CACHE_ALIGNED;

volatile struct global_timestamp glb_ts CACHE_ALIGNED;

/* Instead of relying on synced rdtsc, this approach emulates a global
 * timestamp at coarse granularity. Only a single thread should be
 * calling the increment function. */

static inline void 
global_timestamp_inc(void) 
{
	ck_pr_faa_uint((unsigned int *)&(glb_ts.ts), 2);
	cos_mem_fence();
}

static inline quie_time_t 
get_global_timestamp(void)
{
	return glb_ts.ts;
}

extern __thread int thd_local_id;

/* For now, we assume per-thread instead of per-cpu. */
static inline int 
get_cpu(void) 
{
	return thd_local_id;
}

#define SYNC_USE_RDTSC

static inline quie_time_t 
get_time(void) 
{
	quie_time_t curr_t;
	
#ifdef SYNC_USE_RDTSC
	rdtscll(curr_t);
#else
	curr_t = get_global_timestamp();
#endif
	return curr_t;
}

#define TS_GRANULARITY (2000)

static inline void
timing_update_remote(struct percpu_info *curr, int remote_cpu)
{
	struct quiescence_timing *cpu_i;
	cpu_i = &timing_info[remote_cpu].timing;

	curr->timing_others[remote_cpu].time_in  = cpu_i->time_in;
	curr->timing_others[remote_cpu].time_out = cpu_i->time_out;

	/* We are reading remote cachelines possibly, so this time
	 * stamp reading cost is fine. */
	curr->timing_others[remote_cpu].time_updated = get_time();

	/* If remote core has information that can help, use it. */
	if (curr->timing.last_known_quiescence < cpu_i->last_known_quiescence)
		curr->timing.last_known_quiescence = cpu_i->last_known_quiescence;

	cos_mem_fence();

	return;
}

/********************************************************/

struct quie_mem_meta {
	quie_time_t time_deact; /* used for tracking quiescence */
	size_t size;
	struct quie_mem_meta *next; /* linked-list (freelist or quiescence_waiting queue) */
	void *mem;  /* pointer to the memory region (i.e. next cacheline) */
	char __padding[CACHE_LINE - sizeof(quie_time_t) - sizeof(void *) 
		       - sizeof(struct quie_mem_meta *)- sizeof(size_t)];
} CACHE_ALIGNED;

#define MEM_SIZE (512*1024*1024)
char *allmem, *quie_mem;

static inline unsigned int 
round2next_pow2(unsigned int v) 
{
	/* compute the next highest power of 2 of 32-bit v */
	v--;
	v |= v >> 1;
	v |= v >> 2;
	v |= v >> 4;
	v |= v >> 8;
	v |= v >> 16;
	v++;

	return v;
}

struct quie_queue {
	struct quie_mem_meta *tail; /* adding to here when freeing */
	struct quie_mem_meta *head; /* removing from here when allocating */
	size_t n_items;
} PACKED;

/* Per cpu / thread */
#define QUIE_QUEUE_N_SLAB (32)
struct quie_queue_slab {
	struct quie_queue slab_queue[QUIE_QUEUE_N_SLAB];
	/* Padding to avoid false sharing. 2 cachelines for prefetching. */
	char __padding[CACHE_LINE*2 - ((sizeof(struct quie_queue)*QUIE_QUEUE_N_SLAB) % CACHE_LINE)];
};

/* The global freelist used for balancing. */
struct freelist {
	struct quie_mem_meta *head;
	ck_spinlock_t l;
	size_t n_items;
	/* Padding to avoid false sharing. 2 cachelines for prefetching. */
	char __padding[CACHE_LINE*2 - sizeof(struct quie_mem_meta *)
		       - sizeof(ck_spinlock_t) - sizeof(size_t)];
} PACKED;

struct glb_freelist_slab {
	struct freelist slab_freelists[QUIE_QUEUE_N_SLAB];
};

/* global freelist is not on the fast path -- we still want per slab
 * lock anyway */
struct glb_freelist_slab glb_freelist CACHE_ALIGNED;

/* used to add free item to the head */
static inline void
quie_queue_add_head(struct quie_queue *queue, struct quie_mem_meta *meta)
{
	if (queue->head) {
		assert(queue->tail && queue->tail->next == NULL);
		meta->next = queue->head;
	} else {
		assert(queue->n_items == 0);
		/* empty queue */
		queue->tail = meta;
		meta->next  = NULL;
	}

	queue->head = meta;
	queue->n_items++;
	/* printf("queue add head: %d items\n", queue->n_items); */

	return;
}

static inline void
quie_queue_add(struct quie_queue *queue, struct quie_mem_meta *meta)
{
	/* per thread for now. */
	meta->next = NULL;

	if (queue->tail) {
		assert(queue->tail->next == NULL);
		queue->tail->next = meta;
	} else {
		assert(queue->n_items == 0);
		/* empty queue */
		queue->head = meta;
	}

	queue->tail = meta;
	queue->n_items++;

	return;
}

static inline struct quie_mem_meta *
quie_queue_remove(struct quie_queue *queue)
{
	struct quie_mem_meta *ret;

	/* per thread for now. */
	ret = queue->head;
	if (!ret) return NULL;

	queue->head = ret->next;
	ret->next = NULL;
	queue->n_items--;
	
	if (queue->n_items == 0) queue->tail = NULL;

	/* printf("queue remove: %d items\n", queue->n_items); */

	return ret;
}

/* FIXME: we assume per thread for now. */
/* qwq: quiescence-waiting queues */
struct quie_queue_slab qwq[NUM_CPU] CACHE_ALIGNED;

static inline int
size2slab(size_t orig_size)
{
	unsigned int i;
	unsigned int size = orig_size;
	
	if (!size) return 0;

	/* less than a cacheline uses same slab. */
	size = round2next_pow2(orig_size) / CACHE_LINE;
	if (orig_size < CACHE_LINE) size = 1;

	for (i = 0; i < QUIE_QUEUE_N_SLAB; i++) {
		size >>= 1;
		if (!size) break;
	}

	if (unlikely(size)) {
		printf("no slab for size %u\n", orig_size);
		return -1;
	}

	return i;
}

//#define QUIE_QUEUE_LIMIT (256)
/* return free mem to global when balance limit */
#define QUIE_QUEUE_BALANCE_UPPER_LIMIT (QUIE_QUEUE_LIMIT * 4)
#define QUIE_QUEUE_BALANCE_LOWER_LIMIT (QUIE_QUEUE_LIMIT * 2)

static inline int 
glb_freelist_get(struct quie_queue *queue, size_t size)
{
	struct quie_mem_meta *next, *head, *last;
	struct freelist *freelist;
	int i;

	freelist = &glb_freelist.slab_freelists[size2slab(size)];

	ck_spinlock_lock(&freelist->l);
	head = last = next = freelist->head;

	for (i = 0; i < QUIE_QUEUE_LIMIT && next; i++) {
		last = next;
		next = last->next;
	}

	assert(freelist->n_items >= (unsigned int)i);
	freelist->n_items -= i;
	freelist->head = next;

	ck_spinlock_unlock(&freelist->l);

	if (i > 0) {
		/* we get from head to last, adding to the local queue */
		/* they are free items -- so add them to the head. */
		last->next = queue->head;
		queue->head = head;
		queue->n_items += i;

		if (queue->tail == NULL) queue->tail = last;
	}

	return i;
}


#endif
