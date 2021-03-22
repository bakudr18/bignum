#ifndef _MLOCK_CHECK_H
#define _MLOCK_CHECK_H

#include <stdbool.h>

void configure_malloc_behavior(void);
void reserve_process_memory(int size);
bool check_pagefault(int allowed_maj, int allowed_min);

#endif /* _MLOCK_CHECK_H */
