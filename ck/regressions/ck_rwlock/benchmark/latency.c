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

#include <ck_rwlock.h>
#include <inttypes.h>
#include <stdio.h>

#include "../../common.h"

#ifndef STEPS
#define STEPS 1000000
#endif

int
main(void)
{
	uint64_t s_b, e_b, i;
	ck_rwlock_t rwlock = CK_RWLOCK_INITIALIZER;

	for (i = 0; i < STEPS; i++) {
		ck_rwlock_write_lock(&rwlock);
		ck_rwlock_write_unlock(&rwlock);
	}

	s_b = rdtsc();
	for (i = 0; i < STEPS; i++) {
		ck_rwlock_write_lock(&rwlock);
		ck_rwlock_write_unlock(&rwlock);
	}
	e_b = rdtsc();
	printf("WRITE: rwlock   %15" PRIu64 "\n", (e_b - s_b) / STEPS);

	for (i = 0; i < STEPS; i++) {
		ck_rwlock_read_lock(&rwlock);
		ck_rwlock_read_unlock(&rwlock);
	}

	s_b = rdtsc();
	for (i = 0; i < STEPS; i++) {
		ck_rwlock_read_lock(&rwlock);
		ck_rwlock_read_unlock(&rwlock);
	}
	e_b = rdtsc();
	printf("READ:  rwlock   %15" PRIu64 "\n", (e_b - s_b) / STEPS);

	return (0);
}

