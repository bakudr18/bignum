#include <assert.h>
#include <limits.h>
#include <stdio.h>
#include <stdlib.h>
#include <time.h>
#include <unistd.h>
#include "mlock_check.h"

#include "bn.h"
#define PRE_ALLOCATION_SIZE \
    (50 * 1024 * 1024)  // ulimit -l to check the maxinum size may lock into
                        // memory in process
static inline long long elapsed(struct timespec *t1, struct timespec *t2)
{
    return (long long) (t2->tv_sec - t1->tv_sec) * 1e9 +
           (long long) (t2->tv_nsec - t1->tv_nsec);
}

static void (*lshift)(const bn *, unsigned int, bn *);
int main(int argc, char **argv)
{
    configure_malloc_behavior();
    /* malloc and touch generated */
    reserve_process_memory(PRE_ALLOCATION_SIZE);
    check_pagefault(INT_MAX, INT_MAX);
    /* 2nd malloc and use gnenrated */
    reserve_process_memory(PRE_ALLOCATION_SIZE);

    /* Check all pages are loaded to memory */
    assert(check_pagefault(0, 0));
    // struct timespec t1, t2;

    // if (argc != 2)
        // return -1;

    // lshift = atoi(argv[1]) == 0 ? &bn_lshift_original : &bn_lshift;

    bn *n, *dst, *c;
    n = bn_alloc(1);
    dst = bn_alloc(1);
    c = bn_alloc(1);
    bn_set_num(n, 0xaaaaULL, 0);
    bn_set_num(dst, 0xccccULL, 0);
    // bn_set_num(n, 0x7UL, 1);

    // bn_to_dec_string(n);
    // bn_to_dec_string(dst);

    // bn_add(n, dst, c);
    // bn_to_dec_string(c);
    // bn_lshift(n, 63, dst);
    // clock_gettime(CLOCK_MONOTONIC, &t1);
    // bn_lshift_original(n, 0, dst);
    // clock_gettime(CLOCK_MONOTONIC, &t2);
    // check_pagefault(0, 0);

    for (unsigned int i = 1; i < 256; i++) {
        bn_add(n, dst, c);
        lshift(c, i, dst);
        bn_add(c, dst, n);
       // n = bn_alloc(100);
       // dst = bn_alloc(100);
       // bn_set_num(n, 0x7777ULL, 0);
       // clock_gettime(CLOCK_MONOTONIC, &t1);
       // lshift(n, i, dst);
       // clock_gettime(CLOCK_MONOTONIC, &t2);
       // printf("%d %lld\n", i, elapsed(&t1, &t2));
       // if(i >= 104){
       char *dec = bn_to_dec_string(n);
       printf("%s\n", dec);
       free(dec);
       // }
       // bn_free(n);
       // bn_free(dst);
       // assert(check_pagefault(0, 0));
    }

    bn_free(n);
    bn_free(dst);
    return 0;
}
