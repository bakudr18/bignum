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

int main(int argc, char **argv)
{
    // configure_malloc_behavior();
    /* malloc and touch generated */
    // reserve_process_memory(PRE_ALLOCATION_SIZE);
    // check_pagefault(INT_MAX, INT_MAX);
    /* 2nd malloc and use gnenrated */
    // reserve_process_memory(PRE_ALLOCATION_SIZE);

    /* Check all pages are loaded to memory */
    // assert(check_pagefault(0, 0));
    // struct timespec t1, t2;

    unsigned int k = 0;
    if (argc == 2)
        k = atoi(argv[1]);

    bn *n;
    n = bn_alloc(1);

    // clock_gettime(CLOCK_MONOTONIC, &t1);
    bn_fib(k, n);
    // clock_gettime(CLOCK_MONOTONIC, &t2);
    bn_free(n);
    // printf("%d %lld\n", 96, elapsed(&t1, &t2));
    // bn_print_dec(n);
    // check_pagefault(0, 0);

    // for (unsigned int i = 1; i <= 100000; i++) {
    //     n = bn_alloc(4);
    //     clock_gettime(CLOCK_MONOTONIC, &t1);
    //     bn_fib(i, n);
    //     clock_gettime(CLOCK_MONOTONIC, &t2);
    //     printf("%d %lld\n", i, elapsed(&t1, &t2));
    //     bn_free(n);
    // }

    // bn_free(n);
    return 0;
}
