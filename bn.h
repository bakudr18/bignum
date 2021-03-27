#ifndef _BN_H
#define _BN_H

#include <stdbool.h>
#include <stddef.h>
#include <stdint.h>

#define BN_DEBUG

typedef struct bn bn;
typedef uint64_t bn_digit;

void bn_print_dec(const bn *src);

bn *bn_alloc(uint64_t size);

void bn_free(bn *src);

void bn_set_num(bn *num, bn_digit n, uint64_t offset, bool sign);

void bn_lshifti(bn *src, unsigned int bits);

void bn_lshift(const bn *src, unsigned int bits, bn *dst);

void bn_lshift_original(const bn *src, unsigned int bits, bn *dst);

void bn_add(const bn *a, const bn *b, bn *c);

void bn_mul(const bn *a, const bn *b, bn *c);

void bn_sqr(const bn *a, bn *c);

void bn_fib(uint64_t n, bn *fib);

#endif /* _BN_H */
