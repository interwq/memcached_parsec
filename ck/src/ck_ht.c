/*
 * Copyright 2012 Samy Al Bahra.
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

#include <ck_ht.h>

#ifdef CK_F_HT
/*
 * This implementation borrows several techniques from Josh Dybnis's
 * nbds library which can be found at http://code.google.com/p/nbds
 *
 * This release currently only includes support for 64-bit platforms.
 * We can address 32-bit platforms in a future release.
 */
#include <ck_cc.h>
#include <ck_md.h>
#include <ck_pr.h>
#include <ck_stdint.h>
#include <stdbool.h>
#include <string.h>

#include "ck_ht_hash.h"
#include "ck_internal.h"

#ifndef CK_HT_BUCKET_LENGTH

#ifdef CK_HT_PP
#define CK_HT_BUCKET_SHIFT 2ULL
#else
#define CK_HT_BUCKET_SHIFT 1ULL
#endif

#define CK_HT_BUCKET_LENGTH (1U << CK_HT_BUCKET_SHIFT)
#define CK_HT_BUCKET_MASK (CK_HT_BUCKET_LENGTH - 1)
#endif

#ifndef CK_HT_PROBE_DEFAULT
#define CK_HT_PROBE_DEFAULT 64ULL
#endif

struct ck_ht_map {
	enum ck_ht_mode mode;
	uint64_t deletions;
	uint64_t probe_maximum;
	uint64_t probe_length;
	uint64_t probe_limit;
	uint64_t size;
	uint64_t n_entries;
	uint64_t mask;
	uint64_t capacity;
	uint64_t step;
	struct ck_ht_entry *entries;
};

void
ck_ht_stat(struct ck_ht *table,
	   struct ck_ht_stat *st)
{
	struct ck_ht_map *map = table->map;

	st->n_entries = map->n_entries;
	st->probe_maximum = map->probe_maximum;
	return;
}

void
ck_ht_hash(struct ck_ht_hash *h,
	   struct ck_ht *table,
	   const void *key,
	   uint16_t key_length)
{

	h->value = MurmurHash64A(key, key_length, table->seed);
	return;
}

void
ck_ht_hash_direct(struct ck_ht_hash *h,
		  struct ck_ht *table,
		  uintptr_t key)
{

	ck_ht_hash(h, table, &key, sizeof(key));
	return;
}

static void
ck_ht_hash_wrapper(struct ck_ht_hash *h,
		   const void *key,
		   size_t length,
		   uint64_t seed)
{

	h->value = MurmurHash64A(key, length, seed);
	return;
}

static struct ck_ht_map *
ck_ht_map_create(struct ck_ht *table, uint64_t entries)
{
	struct ck_ht_map *map;
	uint64_t size, n_entries;

	n_entries = ck_internal_power_2(entries);
	size = sizeof(struct ck_ht_map) +
		   (sizeof(struct ck_ht_entry) * n_entries + CK_MD_CACHELINE - 1);

	map = table->m->malloc(size);
	if (map == NULL)
		return NULL;

	map->mode = table->mode;
	map->size = size;
	map->probe_limit = ck_internal_max_64(n_entries >>
	    (CK_HT_BUCKET_SHIFT + 2), CK_HT_PROBE_DEFAULT);

	map->deletions = 0;
	map->probe_maximum = 0;
	map->capacity = n_entries;
	map->step = ck_internal_bsf_64(map->capacity);
	map->mask = map->capacity - 1;
	map->n_entries = 0;
	map->entries = (struct ck_ht_entry *)(((uintptr_t)(map + 1) +
	    CK_MD_CACHELINE - 1) & ~(CK_MD_CACHELINE - 1));

	if (map->entries == NULL) {
		table->m->free(map, size, false);
		return NULL;
	}

	memset(map->entries, 0, sizeof(struct ck_ht_entry) * n_entries);
	return map;
}

static void
ck_ht_map_destroy(struct ck_malloc *m, struct ck_ht_map *map, bool defer)
{

	m->free(map, map->size, defer);
	return;
}

static inline size_t
ck_ht_map_probe_next(struct ck_ht_map *map, size_t offset, ck_ht_hash_t h, size_t probes)
{
	ck_ht_hash_t r;
	size_t stride;

	(void)probes;
	r.value = h.value >> map->step;
	stride = (r.value & ~CK_HT_BUCKET_MASK) << 1
		     | (r.value & CK_HT_BUCKET_MASK);

	return (offset + (stride | CK_HT_BUCKET_LENGTH)) & map->mask;
}

bool
ck_ht_init(ck_ht_t *table,
	   enum ck_ht_mode mode,
	   ck_ht_hash_cb_t *h,
	   struct ck_malloc *m,
	   uint64_t entries,
	   uint64_t seed)
{

	if (m == NULL || m->malloc == NULL || m->free == NULL)
		return false;

	table->m = m;
	table->mode = mode;
	table->seed = seed;

	if (h == NULL) {
		table->h = ck_ht_hash_wrapper;
	} else {
		table->h = h;
	}

	table->map = ck_ht_map_create(table, entries);
	return table->map != NULL;
}

static struct ck_ht_entry *
ck_ht_map_probe_wr(struct ck_ht_map *map,
		   ck_ht_hash_t h,
		   ck_ht_entry_t *snapshot,
		   ck_ht_entry_t **available,
		   const void *key,
		   uint16_t key_length,
		   uint64_t *probe_limit)
{
	struct ck_ht_entry *bucket, *cursor;
	struct ck_ht_entry *first = NULL;
	size_t offset, i, j;
	uint64_t probes = 0;

#ifndef CK_HT_PP
	uint64_t d = 0;
	uint64_t d_prime = 0;
retry:
#endif

	offset = h.value & map->mask;

	for (i = 0; i < map->probe_limit; i++) {
		/*
		 * Probe on a complete cache line first. Scan forward and wrap around to
		 * the beginning of the cache line. Only when the complete cache line has
		 * been scanned do we move on to the next row.
		 */
		bucket = (void *)((uintptr_t)(map->entries + offset) &
			     ~(CK_MD_CACHELINE - 1));

		for (j = 0; j < CK_HT_BUCKET_LENGTH; j++) {
			uint16_t k;

			probes++;
			cursor = bucket + ((j + offset) & (CK_HT_BUCKET_LENGTH - 1));

			/*
			 * It is probably worth it to encapsulate probe state
			 * in order to prevent a complete reprobe sequence in
			 * the case of intermittent writers.
			 */
			if (cursor->key == CK_HT_KEY_TOMBSTONE) {
				if (first == NULL)
					first = cursor;

				continue;
			}

			if (cursor->key == CK_HT_KEY_EMPTY)
				goto leave;

			if (cursor->key == (uintptr_t)key)
				goto leave;

			if (map->mode == CK_HT_MODE_BYTESTRING) {
				void *pointer;

				/*
				 * Check memoized portion of hash value before
				 * expensive full-length comparison.
				 */
				k = ck_ht_entry_key_length(cursor);
				if (k != key_length)
					continue;

#ifdef CK_HT_PP
				if ((cursor->value >> CK_MD_VMA_BITS) != ((h.value >> 32) & CK_HT_KEY_MASK))
					continue;
#else
				if (cursor->hash != h.value)
					continue;

				if (probe_limit == NULL) {
					d_prime = ck_pr_load_64(&map->deletions);

					/*
					 * It is possible that the slot was
					 * replaced, initiate a re-probe.
					 */
					if (d != d_prime)
						goto retry;
				}
#endif

				pointer = ck_ht_entry_key(cursor);
				if (memcmp(pointer, key, key_length) == 0)
					goto leave;
			}
		}

		offset = ck_ht_map_probe_next(map, offset, h, probes);
	}

	return NULL;

leave:
	*probe_limit = probes;
	*available = first;
	*snapshot = *cursor;

	return cursor;
}

static struct ck_ht_entry *
ck_ht_map_probe_rd(struct ck_ht_map *map,
		   ck_ht_hash_t h,
		   ck_ht_entry_t *snapshot,
		   const void *key,
		   uint16_t key_length)
{
	struct ck_ht_entry *bucket, *cursor;
	size_t offset, i, j;
	uint64_t probes = 0;
	uint64_t probe_maximum;

#ifndef CK_HT_PP
	uint64_t d = 0;
	uint64_t d_prime = 0;
retry:
#endif

	probe_maximum = ck_pr_load_64(&map->probe_maximum);
	offset = h.value & map->mask;

	for (i = 0; i < map->probe_limit; i++) {
		/*
		 * Probe on a complete cache line first. Scan forward and wrap around to
		 * the beginning of the cache line. Only when the complete cache line has
		 * been scanned do we move on to the next row.
		 */
		bucket = (void *)((uintptr_t)(map->entries + offset) &
			     ~(CK_MD_CACHELINE - 1));

		for (j = 0; j < CK_HT_BUCKET_LENGTH; j++) {
			uint16_t k;

			probes++;
			cursor = bucket + ((j + offset) & (CK_HT_BUCKET_LENGTH - 1));

#ifdef CK_HT_PP
			snapshot->key = (uintptr_t)ck_pr_load_ptr(&cursor->key);
			ck_pr_fence_load();
			snapshot->value = (uintptr_t)ck_pr_load_ptr(&cursor->value);
#else
			d = ck_pr_load_64(&map->deletions);
			snapshot->key = (uintptr_t)ck_pr_load_ptr(&cursor->key);
			ck_pr_fence_load();
			snapshot->key_length = ck_pr_load_64(&cursor->key_length);
			snapshot->hash = ck_pr_load_64(&cursor->hash);
			snapshot->value = (uintptr_t)ck_pr_load_ptr(&cursor->value);
#endif

			/*
			 * It is probably worth it to encapsulate probe state
			 * in order to prevent a complete reprobe sequence in
			 * the case of intermittent writers.
			 */
			if (snapshot->key == CK_HT_KEY_TOMBSTONE)
				continue;

			if (snapshot->key == CK_HT_KEY_EMPTY)
				goto leave;

			if (snapshot->key == (uintptr_t)key)
				goto leave;

			if (map->mode == CK_HT_MODE_BYTESTRING) {
				void *pointer;

				/*
				 * Check memoized portion of hash value before
				 * expensive full-length comparison.
				 */
				k = ck_ht_entry_key_length(snapshot);
				if (k != key_length)
					continue;
#ifdef CK_HT_PP
				if ((snapshot->value >> CK_MD_VMA_BITS) != ((h.value >> 32) & CK_HT_KEY_MASK))
					continue;
#else
				if (snapshot->hash != h.value)
					continue;

				d_prime = ck_pr_load_64(&map->deletions);

				/*
				 * It is possible that the slot was
				 * replaced, initiate a re-probe.
				 */
				if (d != d_prime)
					goto retry;
#endif

				pointer = ck_ht_entry_key(snapshot);
				if (memcmp(pointer, key, key_length) == 0)
					goto leave;
			}
		}

		if (probes > probe_maximum)
			return NULL;

		offset = ck_ht_map_probe_next(map, offset, h, probes);
	}

	return NULL;

leave:
	return cursor;
}

uint64_t
ck_ht_count(ck_ht_t *table)
{
	struct ck_ht_map *map = ck_pr_load_ptr(&table->map);

	return ck_pr_load_64(&map->n_entries);
}

bool
ck_ht_next(struct ck_ht *table,
	   struct ck_ht_iterator *i,
	   struct ck_ht_entry **entry)
{
	struct ck_ht_map *map = table->map;
	uintptr_t key;

	if (i->offset >= map->capacity)
		return false;

	do {
		key = map->entries[i->offset].key;
		if (key != CK_HT_KEY_EMPTY && key != CK_HT_KEY_TOMBSTONE)
			break;
	} while (++i->offset < map->capacity);

	if (i->offset >= map->capacity)
		return false;

	*entry = map->entries + i->offset++;
	return true;
}

bool
ck_ht_reset_spmc(struct ck_ht *table)
{
	struct ck_ht_map *map, *update;

	map = table->map;
	update = ck_ht_map_create(table, map->capacity);
	if (update == NULL)
		return false;

	ck_pr_store_ptr(&table->map, update);
	ck_ht_map_destroy(table->m, map, true);
	return true;
}

bool
ck_ht_grow_spmc(ck_ht_t *table, uint64_t capacity)
{
	struct ck_ht_map *map, *update;
	struct ck_ht_entry *bucket, *previous;
	struct ck_ht_hash h;
	size_t k, i, j, offset;
	uint64_t probes;

restart:
	map = table->map;

	if (map->capacity >= capacity)
		return false;

	update = ck_ht_map_create(table, capacity);
	if (update == NULL)
		return false;

	for (k = 0; k < map->capacity; k++) {
		previous = &map->entries[k];

		if (previous->key == CK_HT_KEY_EMPTY || previous->key == CK_HT_KEY_TOMBSTONE)
			continue;

		if (table->mode == CK_HT_MODE_BYTESTRING) {
#ifdef CK_HT_PP
			void *key;
			uint16_t key_length;

			key = ck_ht_entry_key(previous);
			key_length = ck_ht_entry_key_length(previous);
#endif

#ifndef CK_HT_PP
			h.value = previous->hash;
#else
			table->h(&h, key, key_length, table->seed);
#endif
		} else {
#ifndef CK_HT_PP
			h.value = previous->hash;
#else
			table->h(&h, &previous->key, sizeof(previous->key), table->seed);
#endif
		}

		offset = h.value & update->mask;
		probes = 0;

		for (i = 0; i < update->probe_limit; i++) {
			bucket = (void *)((uintptr_t)(update->entries + offset) & ~(CK_MD_CACHELINE - 1));

			for (j = 0; j < CK_HT_BUCKET_LENGTH; j++) {
				struct ck_ht_entry *cursor = bucket + ((j + offset) & (CK_HT_BUCKET_LENGTH - 1));

				probes++;
				if (cursor->key == CK_HT_KEY_EMPTY) {
					*cursor = *previous;
					update->n_entries++;

					if (probes > update->probe_maximum)
						update->probe_maximum = probes;

					break;
				}
			}

			if (j < CK_HT_BUCKET_LENGTH)
				break;

			offset = ck_ht_map_probe_next(update, offset, h, probes);
		}

		if (i == update->probe_limit) {
			/*
			 * We have hit the probe limit, the map needs to be even
			 * larger.
			 */
			ck_ht_map_destroy(table->m, update, false);
			capacity <<= 1;
			goto restart;
		}
	}

	ck_pr_fence_store();
	ck_pr_store_ptr(&table->map, update);
	ck_ht_map_destroy(table->m, map, true);
	return true;
}

bool
ck_ht_remove_spmc(ck_ht_t *table,
		  ck_ht_hash_t h,
		  ck_ht_entry_t *entry)
{
	struct ck_ht_map *map;
	struct ck_ht_entry *candidate, *priority, snapshot;
	uint64_t probes;

	map = table->map;

	if (table->mode == CK_HT_MODE_BYTESTRING) {
		candidate = ck_ht_map_probe_wr(map, h, &snapshot, &priority,
				ck_ht_entry_key(entry),
				ck_ht_entry_key_length(entry),
				&probes);
	} else {
		candidate = ck_ht_map_probe_wr(map, h, &snapshot, &priority,
				(void *)entry->key,
				sizeof(entry->key),
				&probes);
	}

	/* No matching entry was found. */
	if (candidate == NULL || snapshot.key == CK_HT_KEY_EMPTY)
		return false;

	*entry = snapshot;
	ck_pr_store_ptr(&candidate->key, (void *)CK_HT_KEY_TOMBSTONE);

	/*
	 * It is possible that the key is read before transition into
	 * the tombstone state. Assuming the keys do match, a reader
	 * may have already acquired a snapshot of the value at the time.
	 * However, assume the reader is preempted as a deletion occurs
	 * followed by a replacement. In this case, it is possible that
	 * the reader acquires some value V' instead of V. Let us assume
	 * however that any transition from V into V' (essentially, update
	 * of a value without the reader knowing of a K -> K' transition),
	 * is preceded by an update to the deletions counter. This guarantees
	 * any replacement of a T key also implies a D -> D' transition.
	 * If D has not transitioned, the value has yet to be replaced so it
	 * is a valid association with K and is safe to return. If D has
	 * transitioned after a reader has acquired a snapshot then it is
	 * possible that we are in the invalid state of (K, V'). The reader
	 * is then able to attempt a reprobe at which point the only visible
	 * states should be (T, V') or (K', V'). The latter is guaranteed
	 * through memory fencing.
	 */
	ck_pr_store_64(&map->deletions, map->deletions + 1);
	ck_pr_fence_store();
	ck_pr_store_64(&map->n_entries, map->n_entries - 1);
	return true;
}

bool
ck_ht_get_spmc(ck_ht_t *table,
	       ck_ht_hash_t h,
	       ck_ht_entry_t *entry)
{
	struct ck_ht_entry *candidate, snapshot;
	struct ck_ht_map *map;
	uint64_t d, d_prime;

restart:
	map = ck_pr_load_ptr(&table->map);

	/*
	 * Platforms that cannot read key and key_length atomically must reprobe
	 * on the scan of any single entry.
	 */
	d = ck_pr_load_64(&map->deletions);

	if (table->mode == CK_HT_MODE_BYTESTRING) {
		candidate = ck_ht_map_probe_rd(map, h, &snapshot,
		    ck_ht_entry_key(entry), ck_ht_entry_key_length(entry));
	} else {
		candidate = ck_ht_map_probe_rd(map, h, &snapshot,
		    (void *)entry->key, sizeof(entry->key));
	}

	d_prime = ck_pr_load_64(&map->deletions);
	if (d != d_prime) {
		/*
		 * It is possible we have read (K, V'). Only valid states are
		 * (K, V), (K', V') and (T, V). Restart load operation in face
		 * of concurrent deletions or replacements.
		 */
		goto restart;
	}

	if (candidate == NULL || snapshot.key == CK_HT_KEY_EMPTY)
		return false;

	*entry = snapshot;
	return true;
}

bool
ck_ht_set_spmc(ck_ht_t *table,
	       ck_ht_hash_t h,
	       ck_ht_entry_t *entry)
{
	struct ck_ht_entry snapshot, *candidate, *priority;
	struct ck_ht_map *map;
	uint64_t probes;

	for (;;) {
		map = table->map;

		if (table->mode == CK_HT_MODE_BYTESTRING) {
			candidate = ck_ht_map_probe_wr(map, h, &snapshot, &priority,
					ck_ht_entry_key(entry),
					ck_ht_entry_key_length(entry),
					&probes);
		} else {
			candidate = ck_ht_map_probe_wr(map, h, &snapshot, &priority,
					(void *)entry->key,
					sizeof(entry->key),
					&probes);
		}

		if (candidate != NULL)
			break;

		if (ck_ht_grow_spmc(table, map->capacity << 1) == false)
			return false;
	}

	if (probes > map->probe_maximum)
		ck_pr_store_64(&map->probe_maximum, probes);

	if (candidate->key != CK_HT_KEY_EMPTY && priority != NULL) {
		/*
		 * If we are replacing an existing entry and an earlier
		 * tombstone was found in the probe sequence then replace
		 * the existing entry in a manner that doesn't affect linearizability
		 * of concurrent get operations. We avoid a state of (K, B)
		 * (where [K, B] -> [K', B]) by guaranteeing a forced reprobe
		 * before transitioning from K to T. (K, B) implies (K, B, D')
		 * so we will reprobe successfully from this transient state.
		 */
#ifndef CK_HT_PP
		ck_pr_store_64(&priority->key_length, entry->key_length);
		ck_pr_store_64(&priority->hash, entry->hash);
#endif
		ck_pr_store_ptr(&priority->value, (void *)entry->value);
		ck_pr_fence_store();
		ck_pr_store_ptr(&priority->key, (void *)entry->key);
		ck_pr_fence_store();
		ck_pr_store_64(&map->deletions, map->deletions + 1);
		ck_pr_fence_store();
		ck_pr_store_ptr(&candidate->key, (void *)CK_HT_KEY_TOMBSTONE);
	} else {
		/*
		 * In this case we are inserting a new entry or replacing
		 * an existing entry.
		 */
		bool replace = candidate->key != CK_HT_KEY_EMPTY;

		if (priority != NULL)
			candidate = priority;

#ifdef CK_HT_PP
		ck_pr_store_ptr(&candidate->value, (void *)entry->value);
		ck_pr_fence_store();
		ck_pr_store_ptr(&candidate->key, (void *)entry->key);
#else
		ck_pr_store_64(&candidate->key_length, entry->key_length);
		ck_pr_store_64(&candidate->hash, entry->hash);
		ck_pr_store_ptr(&candidate->value, (void *)entry->value);
		ck_pr_fence_store();
		ck_pr_store_ptr(&candidate->key, (void *)entry->key);
#endif

		/*
		 * If we are insert a new entry then increment number
		 * of entries associated with map.
		 */
		if (replace == false)
			ck_pr_store_64(&map->n_entries, map->n_entries + 1);
	}

	/* Enforce a load factor of 0.5. */
	if (map->n_entries * 2 > map->capacity)
		ck_ht_grow_spmc(table, map->capacity << 1);

	*entry = snapshot;
	return true;
}

bool
ck_ht_put_spmc(ck_ht_t *table,
	       ck_ht_hash_t h,
	       ck_ht_entry_t *entry)
{
	struct ck_ht_entry snapshot, *candidate, *priority;
	struct ck_ht_map *map;
	uint64_t probes;

	for (;;) {
		map = table->map;

		if (table->mode == CK_HT_MODE_BYTESTRING) {
			candidate = ck_ht_map_probe_wr(map, h, &snapshot, &priority,
					ck_ht_entry_key(entry),
					ck_ht_entry_key_length(entry),
					&probes);
		} else {
			candidate = ck_ht_map_probe_wr(map, h, &snapshot, &priority,
					(void *)entry->key,
					sizeof(entry->key),
					&probes);
		}

		if (candidate != NULL)
			break;

		if (ck_ht_grow_spmc(table, map->capacity << 1) == false)
			return false;
	}

	/*
	 * If the snapshot key is non-empty and the value field is not
	 * a tombstone then an identical key was found. As store does
	 * not implement replacement, we will fail.
	 */
	if (candidate->key != CK_HT_KEY_EMPTY && candidate->key != CK_HT_KEY_TOMBSTONE)
		return false;

	if (probes > map->probe_maximum)
		ck_pr_store_64(&map->probe_maximum, probes);

	/*
	 * If an earlier tombstone value was found, then store into that slot instead.
	 * It is earlier in the probe sequence to begin with.
	 */
	if (priority != NULL)
		candidate = priority;

#ifdef CK_HT_PP
	ck_pr_store_ptr(&candidate->value, (void *)entry->value);
	ck_pr_fence_store();
	ck_pr_store_ptr(&candidate->key, (void *)entry->key);
#else
	ck_pr_store_64(&candidate->key_length, entry->key_length);
	ck_pr_store_64(&candidate->hash, entry->hash);
	ck_pr_store_ptr(&candidate->value, (void *)entry->value);
	ck_pr_fence_store();
	ck_pr_store_ptr(&candidate->key, (void *)entry->key);
#endif

	ck_pr_store_64(&map->n_entries, map->n_entries + 1);

	/* Enforce a load factor of 0.5. */
	if (map->n_entries * 2 > map->capacity)
		ck_ht_grow_spmc(table, map->capacity << 1);

	return true;
}

void
ck_ht_destroy(struct ck_ht *table)
{

	ck_ht_map_destroy(table->m, table->map, false);
	return;
}

#endif /* CK_F_HT */
