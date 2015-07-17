/*
 * Copyright 2011-2012 Samy Al Bahra.
 * All rights reserved.
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions
 * are met:
 * 1. Redistributions of source code must retain the above copyright
 *    notice, this list of conditions and the following disclaimer.
 * 2. Redistributions in binary form must reproduce the above copyright
 *    notice, this list of conditions and the following disclaimer in the
 *    documentation and/or other materials provided with the distribution.
 *
 * THIS SOFTWARE IS PROVIDED BY THE AUTHOR AND CONTRIBUTORS ``AS IS'' AND
 * ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE
 * IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE
 * ARE DISCLAIMED.  IN NO EVENT SHALL THE AUTHOR OR CONTRIBUTORS BE LIABLE
 * FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL
 * DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS
 * OR SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION)
 * HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT
 * LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY
 * OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF
 * SUCH DAMAGE.
 */

#include <assert.h>
#include <stdlib.h>
#include <stdio.h>
#include <string.h>
#include <pthread.h>

#include <ck_barrier.h>
#include <ck_ring.h>
#include <ck_spinlock.h>
#include "../../common.h"

#ifndef ITERATIONS
#define ITERATIONS 128
#endif

struct context {
	unsigned int tid;
	unsigned int previous;
	unsigned int next;
};

struct entry {
	unsigned long value_long;
	unsigned int magic;
	unsigned int ref;
	int tid;
	int value;
};

static int nthr;
static ck_ring_t *ring;
static ck_ring_t ring_spmc CK_CC_CACHELINE;
static struct affinity a;
static int size;
static int eb;
static ck_barrier_centralized_t barrier = CK_BARRIER_CENTRALIZED_INITIALIZER;

static void *
test_spmc(void *c)
{
	unsigned int observed = 0;
	unsigned long previous = 0;
	int i, j, tid;

	(void)c;
        if (aff_iterate(&a)) {
                perror("ERROR: Could not affine thread");
                exit(EXIT_FAILURE);
        }

	tid = ck_pr_faa_int(&eb, 1);
	ck_pr_fence_memory();
	while (ck_pr_load_int(&eb) != nthr - 1);

	for (i = 0; i < ITERATIONS; i++) {
		for (j = 0; j < size; j++) {
			struct entry *o;

			/* Keep trying until we encounter at least one node. */
			if (j & 1) {
				while (ck_ring_dequeue_spmc(&ring_spmc, &o) == false);
			} else {
				while (ck_ring_trydequeue_spmc(&ring_spmc, &o) == false);
			}

			observed++;
			if (o->value < 0
			    || o->value != o->tid
			    || o->magic != 0xdead
			    || (previous != 0 && previous >= o->value_long)) {
				ck_error("[0x%p] (%x) (%d, %d) >< (0, %d)\n",
					(void *)o, o->magic, o->tid, o->value, size);
			}

			o->magic = 0xbeef;
			o->value = -31337;
			o->tid = -31338;
			previous = o->value_long;

			if (ck_pr_faa_uint(&o->ref, 1) != 0) {
				ck_error("[%p] We dequeued twice.\n", (void *)o);
			}

			free(o);
		}
	}

	fprintf(stderr, "[%d] Observed %u\n", tid, observed);
	return NULL;
}

static void *
test(void *c)
{
	struct context *context = c;
	struct entry *entry;
	int i, j;
	bool r;
	ck_barrier_centralized_state_t sense =
	    CK_BARRIER_CENTRALIZED_STATE_INITIALIZER;

        if (aff_iterate(&a)) {
                perror("ERROR: Could not affine thread");
                exit(EXIT_FAILURE);
        }

	if (context->tid == 0) {
		struct entry *entries;

		entries = malloc(sizeof(struct entry) * size);
		assert(entries != NULL);

		if (ck_ring_size(ring) != 0) {
			ck_error("More entries than expected: %u > 0\n",
				ck_ring_size(ring));
		}

		for (i = 0; i < size; i++) {
			entries[i].value = i;
			entries[i].tid = 0;

			r = ck_ring_enqueue_spmc(ring, entries + i);
			assert(r != false);
		}

		if (ck_ring_size(ring) != (unsigned int)size) {
			ck_error("Less entries than expected: %u < %d\n",
				ck_ring_size(ring), size);
		}

		if (ck_ring_capacity(ring) != ck_ring_size(ring) + 1) {
			ck_error("Capacity less than expected: %u < %u\n",
				ck_ring_size(ring), ck_ring_capacity(ring));
		}
	}

	/*
	 * Wait for all threads. The idea here is to maximize the contention.
	 */
	ck_barrier_centralized(&barrier, &sense, nthr);

	for (i = 0; i < ITERATIONS; i++) {
		for (j = 0; j < size; j++) {
			while (ck_ring_dequeue_spmc(ring + context->previous, &entry) == false);

			if (context->previous != (unsigned int)entry->tid) {
				ck_error("[%u:%p] %u != %u\n",
					context->tid, (void *)entry, entry->tid, context->previous);
			}

			if (entry->value < 0 || entry->value >= size) {
				ck_error("[%u:%p] %u </> %u\n",
					context->tid, (void *)entry, entry->tid, context->previous);
			}

			entry->tid = context->tid;
			r = ck_ring_enqueue_spmc(ring + context->tid, entry);
			assert(r == true);
		}
	}

	return NULL;
}

int
main(int argc, char *argv[])
{
	int i, r;
	void *buffer;
	unsigned long l;
	struct context *context;
	pthread_t *thread;

	if (argc != 4) {
		ck_error("Usage: validate <threads> <affinity delta> <size>\n");
	}

	a.request = 0;
	a.delta = atoi(argv[2]);

	nthr = atoi(argv[1]);
	assert(nthr >= 1);

	size = atoi(argv[3]);
	assert(size > 4 && (size & size - 1) == 0);
	size -= 1;

	ring = malloc(sizeof(ck_ring_t) * nthr);
	assert(ring);

	context = malloc(sizeof(*context) * nthr);
	assert(context);

	thread = malloc(sizeof(pthread_t) * nthr);
	assert(thread);

	fprintf(stderr, "SPSC test:");
	for (i = 0; i < nthr; i++) {
		context[i].tid = i;
		if (i == 0) {
			context[i].previous = nthr - 1;
			context[i].next = i + 1;
		} else if (i == nthr - 1) {
			context[i].next = 0;
			context[i].previous = i - 1;
		} else {
			context[i].next = i + 1;
			context[i].previous = i - 1;
		}

		buffer = malloc(sizeof(void *) * (size + 1));
		assert(buffer);
		memset(buffer, 0, sizeof(void *) * (size + 1));
		ck_ring_init(ring + i, buffer, size + 1);
		r = pthread_create(thread + i, NULL, test, context + i);
		assert(r == 0);
	}

	for (i = 0; i < nthr; i++)
		pthread_join(thread[i], NULL);

	fprintf(stderr, " done\n");

	fprintf(stderr, "SPMC test:\n");
	buffer = malloc(sizeof(void *) * (size + 1));
	assert(buffer);
	memset(buffer, 0, sizeof(void *) * (size + 1));
	ck_ring_init(&ring_spmc, buffer, size + 1);
	for (i = 0; i < nthr - 1; i++) {
		r = pthread_create(thread + i, NULL, test_spmc, context + i);
		assert(r == 0);
	}

	for (l = 0; l < (unsigned long)size * ITERATIONS * (nthr - 1) ; l++) {
		struct entry *entry = malloc(sizeof *entry);

		assert(entry != NULL);
		entry->value_long = l;
		entry->value = (int)l;
		entry->tid = (int)l;
		entry->magic = 0xdead;
		entry->ref = 0;

		/* Wait until queue is not full. */
		while (ck_ring_enqueue_spmc(&ring_spmc, entry) == false)
			ck_pr_stall();
	}

	for (i = 0; i < nthr - 1; i++)
		pthread_join(thread[i], NULL);

	return (0);
}

