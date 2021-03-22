#include "mlock_check.h"
#include <assert.h>
#include <malloc.h>
#include <stdio.h>
#include <sys/mman.h>      // Needed for mlockall()
#include <sys/resource.h>  // needed for getrusage
#include <sys/time.h>      // needed for getrusage
#include <unistd.h>        // needed for sysconf(int name);

void configure_malloc_behavior(void)
{
    /* Now lock all current and future pages
       from preventing of being paged */
    if (mlockall(MCL_CURRENT | MCL_FUTURE))
        perror("mlockall failed:");

    /* Turn off malloc trimming.*/
    mallopt(M_TRIM_THRESHOLD, -1);

    /* Turn off mmap usage. */
    mallopt(M_MMAP_MAX, 0);
}

void reserve_process_memory(int size)
{
    int i;
    char *buffer;

    buffer = malloc(size);
    assert(buffer);

    /* Touch each page in this piece of memory to get it mapped into RAM */
    for (i = 0; i < size; i += sysconf(_SC_PAGESIZE)) {
        /* Each write to this buffer will generate a pagefault.
           Once the pagefault is handled a page will be locked in
           memory and never given back to the system. */
        buffer[i] = 0;
    }

    /* buffer will now be released. As Glibc is configured such that it
       never gives back memory to the kernel, the memory allocated above is
       locked for this process. All malloc() and new() calls come from
       the memory pool reserved and locked above. Issuing free() and
       delete() does NOT make this locking undone. So, with this locking
       mechanism we can build C++ applications that will never run into
       a major/minor pagefault, even with swapping enabled. */
    free(buffer);
}

bool check_pagefault(int allowed_maj, int allowed_min)
{
    static int last_majflt = 0, last_minflt = 0;
    struct rusage usage;
    bool res = true;

    getrusage(RUSAGE_SELF, &usage);

    // printf("major: %ld minor: %ld\n", usage.ru_majflt - last_majflt,
    // usage.ru_minflt - last_minflt);
    if ((usage.ru_majflt - last_majflt > allowed_maj) |
        (usage.ru_minflt - last_minflt > allowed_min))
        res = false;

    last_majflt = usage.ru_majflt;
    last_minflt = usage.ru_minflt;
    return res;
}
