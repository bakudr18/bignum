#ifndef _MEMORY_H
#define _MEMORT_H

#include <stdio.h>
#include <stdlib.h>
#include <string.h>

static void *(*orig_malloc)(size_t) = malloc;
static void *(*orig_realloc)(void *, size_t) = realloc;
static void (*orig_free)(void *) = free;

static inline void *wrap_malloc(size_t size)
{
    void *p;
    if (!(p = (*orig_malloc)(size))) {
        fprintf(stderr, "Out of memory.\n");
        abort();
    }
    return p;
}

static inline void *wrap_realloc(void *ptr, size_t size)
{
    void *p;
    if (!(p = (*orig_realloc)(ptr, size)) && size != 0) {
        fprintf(stderr, "Out of memory.\n");
        abort();
    }
    return p;
}

static inline void wrap_free(void *ptr)
{
    (*orig_free)(ptr);
}

#define MALLOC(n) wrap_malloc(n)
#define REALLOC(p, n) wrap_realloc(p, n)
#define FREE(p) wrap_free(p)

#endif /* _MEMORY_H */
