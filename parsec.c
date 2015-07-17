#include "parsec.h"
#include <sys/mman.h>
#include <ck_pr.h>
#include <sched.h>
#include <sys/time.h>
#include <sys/resource.h>

/* # of cachelines allocated. */
volatile unsigned long n_cacheline = 0;

void 
spin_delay(unsigned long long cycles)
{
	unsigned long long s, e, curr;

	rdtscll(s); 
	e = s + cycles;

	curr = s;
	while (curr < e) rdtscll(curr);

	return;
}

__thread int thd_local_id;

static inline void *
get_mem(size_t size)
{
	int n;
	unsigned long old, new;
	struct quie_mem_meta *meta;
	
	/* # of cachelines. */
	if (!size) return NULL;

	n = round2next_pow2(size) / CACHE_LINE;
	if (!n) n = 1;
	assert((unsigned long)(n * CACHE_LINE) >= size);

	/* 2 additional cachelines: 
	 * 1 (at the beginning) for meta-data (time-stamp, etc.), 
	 * 1 (at the end) to avoid prefetching caused false sharing. */
	n += 2;

	/* cas loop. Should only happen during warm up. */
	while (1) {
		old = n_cacheline;
		new = old + n;
		if (new >= (MEM_SIZE / CACHE_LINE)) {
			/* all memory used. */
			return NULL;
		}
	
		if (cos_cas((unsigned long *)&n_cacheline, old, new)) break;
	}

	meta = (struct quie_mem_meta *)((unsigned long)quie_mem + old * CACHE_LINE);

	meta->next       = NULL;
	meta->time_deact = 0;
	meta->size       = round2next_pow2(size);
	/* data memory after meta */
	meta->mem        = (void *)((unsigned long)meta + CACHE_LINE);

	assert(((unsigned long)meta + meta->size) <= ((unsigned long)quie_mem + MEM_SIZE));

	return meta;
}

static inline void 
quie_queue_fill(struct quie_queue *queue, size_t size) 
{
	int i, diff;
	struct quie_mem_meta *meta;

	/* try freelist first -- the items are added to the
	 * quie waiting queue. */

	glb_freelist_get(queue, size);

	diff = QUIE_QUEUE_LIMIT - queue->n_items;
	/* printf("fill %d to %d\n", queue->n_items, QUIE_QUEUE_LIMIT); */
	for (i = 0; i < diff; i++) {
		meta = get_mem(size);
		if (!meta) return;

		meta->time_deact = 0;
		quie_queue_add_head(queue, meta);
	}

	return;
}

/* char debug_mem[PAGE_SIZE] PAGE_ALIGNED; */
/* #define N_DEBUG (10) */
/* int *state = (int *)&debug_mem[1024]; */

static inline int 
parsec_try_quiescence(quie_time_t orig_timestamp, const int waiting)
{
	int i, curr_cpu, first_try, done_i = 0;
	quie_time_t min_known_quie;
	quie_time_t in, out, update;
	struct percpu_info *cpuinfo;
	struct quiescence_timing *timing_local;
	quie_time_t time_check;

/* #define TIMESTAMP_ADJUSTMENT (0) */
/* 	time_check = orig_timestamp + TIMESTAMP_ADJUSTMENT; */
	time_check = orig_timestamp;

	curr_cpu  = get_cpu();

	cpuinfo = &timing_info[curr_cpu];
	timing_local = &cpuinfo->timing;

	if (unlikely(time_check > timing_local->time_in)) {
//		printf(">>>>>>>>>> QUIESCENCE wait error %llu %llu!\n", time_check, timing_local->time_in);
		return -EQUIESCENCE;
	}

	min_known_quie = (unsigned long long)(-1);

	for (i = 0; i < NUM_CPU; i++) {
		if (i == curr_cpu) continue;

		first_try = 1;
		done_i = 0;
	re_check:
		if (time_check < timing_local->last_known_quiescence) 
			break;

		in     = cpuinfo->timing_others[i].time_in;
		out    = cpuinfo->timing_others[i].time_out;
		update = cpuinfo->timing_others[i].time_updated;

		if ((time_check < in) || 
		    ((time_check < update) && (in < out))) {
			done_i = 1;
		}
		
		if (done_i) {
			/* assertion: update >= in */
			if (in < out) {
				if (min_known_quie > update) min_known_quie = update;
			} else {
				if (min_known_quie > in) min_known_quie = in;
			}
			continue;
		}

		/* If no waiting allowed, then read at most one remote
		 * cacheline per core. */
		if (first_try) {
			first_try = 0;
		} else {
			if (!waiting) return -1;
		}

		timing_update_remote(cpuinfo, i);

		goto re_check;
	}

	if (i == NUM_CPU) {
		/* This implies we went through all cores. Thus the
		 * min_known_quie can be used to determine global quiescence. */
		if (timing_local->last_known_quiescence < min_known_quie)
			timing_local->last_known_quiescence = min_known_quie;
	}

	cos_mem_fence();

	return 0;
}

/* force waiting for quiescence */
int 
parsec_quiescence_wait(quie_time_t orig_timestamp)
{
	/* waiting for quiescence if needed. */
	return parsec_try_quiescence(orig_timestamp, 1);
}

int 
parsec_quiescence_check(quie_time_t orig_timestamp)
{
	/* non-waiting */
	return parsec_try_quiescence(orig_timestamp, 0);
}

static inline struct quie_mem_meta *
quie_queue_alloc(struct quie_queue *queue, const int waiting)
{
	struct quie_mem_meta *ret, *head;

	head = queue->head;
	if (!head) return NULL;

	if (parsec_try_quiescence(head->time_deact, waiting)) {
//		printf("Quiescence waiting error\n");
		return NULL;
	}
	ret = quie_queue_remove(queue);

	assert(ret == head);

	return ret;
}

void *
q_alloc(size_t size, const int waiting)
{
	/* try free-list first */
	struct quie_queue *queue;
	struct quie_mem_meta *meta = NULL;
	int cpu, slab_id;

	cpu = get_cpu();
	slab_id = size2slab(size);
	assert(slab_id < QUIE_QUEUE_N_SLAB);

	queue = &(qwq[cpu].slab_queue[slab_id]);
//	printf("cpu %d, queue %p\n", cpu, queue);

	if (queue->n_items < QUIE_QUEUE_LIMIT) {
		/* This will add items (new or from global freelist)
		 * onto quie_queue if possible. */
		quie_queue_fill(queue, size);
	}

	if (queue->n_items >= QUIE_QUEUE_LIMIT) {
		/* Ensure the minimal amount of items on the
		 * quiescence queue. */
		meta = quie_queue_alloc(queue, waiting);
	}

	if (!meta) {
		/* printf("No memory allocated\n"); */
		return NULL;
	}
	assert(meta->size >= size);

	return meta->mem;
}

void 
lib_enter(void) 
{
	int curr_cpu;
	quie_time_t curr_time;
	struct quiescence_timing *timing;
	
	curr_cpu  = get_cpu();
	curr_time = get_time();

	timing = &timing_info[curr_cpu].timing;
	timing->time_in = curr_time;
	
	/* Following is needed when we have coarse granularity
	 * time-stamps (i.e. non-cycle granularity, which means we
	 * could have same time-stamp for different events). */
	timing->time_out = curr_time - 1;

	cos_mem_fence();
	
	return;
}

void 
lib_exit(void) 
{
	int curr_cpu;
	struct quiescence_timing *timing;
	
	curr_cpu = get_cpu();
	timing = &timing_info[curr_cpu].timing;

	cos_mem_fence();
	/* memory barrier, then write time stamp. */
	timing->time_out = timing->time_in + 1;
	
	return;
}

/* try returning from local qwq to glb freelist. */
static inline int 
quie_queue_balance(struct quie_queue *queue)
{
	struct quie_mem_meta *head, *last = NULL;
	struct freelist *freelist;
	size_t size;
	int return_n = 0;

	head = queue->head;
	size = head->size;
	assert(size == round2next_pow2(head->size));

	while (queue->head && (queue->n_items > QUIE_QUEUE_BALANCE_LOWER_LIMIT)) {
		/* only return quiesced items. */
		if (parsec_quiescence_check(queue->head->time_deact) == 0) {
			return_n++;
			last = queue->head;
			assert(last->size == size);
			quie_queue_remove(queue);
			/* construct a local list */
			last->next = queue->head;
		} else {
			break;
		}
	}

	if (return_n) {
		assert(head && last);
		/* last is the last item on the local list. */
		freelist = &(glb_freelist.slab_freelists[size2slab(size)]);

		/* add the freed item list to the global freelist. */
		ck_spinlock_lock(&(freelist->l));
		last->next = freelist->head;
		freelist->head = head;
		freelist->n_items += return_n;
		ck_spinlock_unlock(&(freelist->l));
	}

	return 0;
}

int
q_free(void *node)
{
	struct quie_mem_meta *meta;
	struct quie_queue *queue;
	int cpu;

	if ((unsigned long)node % CACHE_LINE) return -EINVAL;

	cpu = get_cpu();
	meta = (struct quie_mem_meta *)((unsigned long)node - CACHE_LINE);
	meta->time_deact = get_time();

	queue = &(qwq[cpu].slab_queue[size2slab(meta->size)]);
	quie_queue_add(queue, meta);
	
	if (queue->n_items >= QUIE_QUEUE_BALANCE_UPPER_LIMIT) {
		quie_queue_balance(queue);
	}
	
	return 0;
}

void *
lib_exec(void *(*func)(void *), void *arg) 
{
	void *ret;

	lib_enter();
	ret = func(arg);
	lib_exit();

	return ret;
}

/* not used for now */
static void parsec_quiesce(void)
{
	quie_time_t t = get_time();
	
	lib_enter();
	parsec_quiescence_wait(t);
	lib_exit();
}

static int 
qmem_free(void *mem)
{
	int ret;

	lib_enter();
	ret = q_free(mem);
	lib_exit();

	return ret;
}

/* Not used for now. */
/* This checks quiescence based on pure local knowledge (and without
 * waiting for it). No remote readings. return 0 if quiesced. */
static int
parsec_quiescence_quick_check(quie_time_t time_check)
{
	struct quiescence_timing *timing_local;

	timing_local = &timing_info[get_cpu()].timing;
	if (time_check > timing_local->last_known_quiescence) return -1;

	/* quiesced */
	return 0;
}

void *
timer_update(void *arg)
{
	(void)arg;

	glb_ts.ts = 10;

	/* printf("timer thread running on cpu %d\n", (int)arg); */
	while (1) {
		spin_delay(TS_GRANULARITY);
		global_timestamp_inc();
	}
}

static void call_getrlimit(int id, char *name)
{
	struct rlimit rl;

	if (getrlimit(id, &rl)) {
		perror("getrlimit: ");
		exit(-1);
	}		
}

static void call_setrlimit(int id, rlim_t c, rlim_t m)
{
	struct rlimit rl;

	rl.rlim_cur = c;
	rl.rlim_max = m;
	if (setrlimit(id, &rl)) {
		exit(-1);
	}		
}

void set_prio(void)
{
	struct sched_param sp;

	call_getrlimit(RLIMIT_CPU, "CPU");
#ifdef RLIMIT_RTTIME
	call_getrlimit(RLIMIT_RTTIME, "RTTIME");
#endif
	call_getrlimit(RLIMIT_RTPRIO, "RTPRIO");
	call_setrlimit(RLIMIT_RTPRIO, RLIM_INFINITY, RLIM_INFINITY);
	call_getrlimit(RLIMIT_RTPRIO, "RTPRIO");	
	call_getrlimit(RLIMIT_NICE, "NICE");

	if (sched_getparam(0, &sp) < 0) {
		perror("getparam: ");
		exit(-1);
	}
	sp.sched_priority = sched_get_priority_max(SCHED_RR);
	if (sched_setscheduler(0, SCHED_RR, &sp) < 0) {
		perror("setscheduler: ");
		exit(-1);
	}
	if (sched_getparam(0, &sp) < 0) {
		perror("getparam: ");
		exit(-1);
	}
	assert(sp.sched_priority == sched_get_priority_max(SCHED_RR));

	return;
}

struct thd_active {
	int accessed;
	int done;
	int avg;
	int max;
	int read_avg;
	int read_max;
} CACHE_ALIGNED;

struct thd_active thd_active[NUM_CPU] CACHE_ALIGNED;
volatile int use_ncores;

int cpu_assign[41] = {0, 4, 8, 12, 16, 20, 24, 28, 32, 36,
		      1, 5, 9, 13, 17, 21, 25, 29, 33, 37,
		      2, 6, 10, 14, 18, 22, 26, 30, 34, 38,
		      3, 7, 11, 15, 19, 23, 27, 31, 35, 39, -1};

void thd_set_affinity(pthread_t tid, int id)
{
	cpu_set_t s;
	int ret, cpuid;

	cpuid = cpu_assign[id];
	/* printf("tid %d (%d) to cpu %d\n", tid, id, cpuid); */
	CPU_ZERO(&s);
	CPU_SET(cpuid, &s);
	ret = pthread_setaffinity_np(tid, sizeof(cpu_set_t), &s);
	
	if (ret) {
		printf("setting affinity error for tid %d on cpu %d\n", (int)tid, cpuid);
		assert(0);
	}
}

void meas_sync_start(void) {
	int cpu = get_cpu();
	ck_pr_store_int(&thd_active[cpu].done, 0);
	ck_pr_store_int(&thd_active[cpu].avg, 0);
	ck_pr_store_int(&thd_active[cpu].max, 0);
	ck_pr_store_int(&thd_active[cpu].read_avg, 0);
	ck_pr_store_int(&thd_active[cpu].read_max, 0);

	if (cpu == 0) {
		int k = 1;
		while (k < use_ncores) {
			while (1) {
				if (ck_pr_load_int(&thd_active[k].accessed)) break;
			}
			k++;
		}
		ck_pr_store_int(&thd_active[0].accessed, 1);
	} else {
		ck_pr_store_int(&thd_active[cpu].accessed, 1);
		while (ck_pr_load_int(&thd_active[0].accessed) == 0) ;
	} // sync!
}

void meas_sync_end() {
	int i;
	int cpu = get_cpu();
	ck_pr_store_int(&thd_active[cpu].accessed, 0);

	if (cpu == 0) { // output!!!
//		printf("test done %d, syncing\n", NUM_CPU_COS);
		// sync first!
		for (i = 1; i < use_ncores;i++) {
			while (1) {
				if (ck_pr_load_int(&thd_active[i].done)) break;
			}
		}

		ck_pr_store_int(&thd_active[0].done, 1);
	} else {
		ck_pr_store_int(&thd_active[cpu].done, 1);
		while (ck_pr_load_int(&thd_active[0].done) == 0) ;
	}
}

#define ITEM_SIZE (2*CACHE_LINE)
static void mem_warmup(void)
{
	/* memcached: mem pre-allocation warm up. */
	int i;
	unsigned long k = 0, tot_items = (unsigned long)MEM_SIZE / (2*CACHE_LINE + ITEM_SIZE);
	unsigned long **ptrs = malloc(sizeof(void*) * tot_items);

	while (1) {
		assert(k < tot_items);
		ptrs[k] = q_alloc(ITEM_SIZE, 1);
		if (!ptrs[k]) break;
		k++;
	}

	for (i = 0; i < k; i++) {
		qmem_free(ptrs[i]);
	}
	
	free((void *)ptrs);

	/* sanity checks below! */

	struct quie_queue *queue = &(qwq[get_cpu()].slab_queue[size2slab(ITEM_SIZE)]);
	struct freelist *fl = &(glb_freelist.slab_freelists[size2slab(ITEM_SIZE)]);

	/* printf("queue size %d, fl %d\n", queue->n_items, fl->n_items); */

	struct quie_mem_meta *mem = queue->head;
	for (i = 0; i < queue->n_items; i++) {
		mem = mem->next;
	}
	assert(mem == NULL);

	mem = fl->head;
	for (i = 0; i < fl->n_items; i++) {
		mem = mem->next;
	}
	assert(mem == NULL);
	
	return;
}

void parsec_init(void)
{
	int i, ret;

	use_ncores = NUM_CPU;

	allmem = malloc(MEM_SIZE + PAGE_SIZE);
	/* adjust to page aligned. */
	quie_mem = allmem + (PAGE_SIZE - (unsigned long)allmem % PAGE_SIZE); 
	assert((unsigned long)quie_mem % PAGE_SIZE == 0);

	ret = mlock(allmem, MEM_SIZE + PAGE_SIZE);
	if (ret) {
		printf("Cannot lock cache memory (%d). Check privilege. Exit.\n", ret);
		exit(-1);
	}
	memset(allmem, 0, MEM_SIZE + PAGE_SIZE);

	for (i = 0; i < QUIE_QUEUE_N_SLAB; i++) {
		ck_spinlock_init(&glb_freelist.slab_freelists[i].l);
	}

	for (i = 0; i < NUM_CPU; i++) {
		timing_info[i].timing.time_in  = 0;
		timing_info[i].timing.time_out = 1;
	}

	mem_warmup();

	printf("\n << PARSEC: init done, cache memory %d MBs. Quiescence queue size %d >>> \n", 
	       MEM_SIZE >> 20, QUIE_QUEUE_LIMIT);

	return;
}
