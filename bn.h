#ifndef _BN_H
#define _BN_H

#include <stddef.h>
#include <stdint.h>

#define BN_DEBUG

typedef struct bn bn;
typedef uint64_t bn_digit;

char *bn_to_dec_string(const bn *src);

bn *bn_alloc(uint64_t size);

void bn_free(bn *src);

void bn_set_num(bn *num, bn_digit n, uint64_t offset);

void bn_lshifti(bn *src, unsigned int bits);

void bn_lshift(const bn *src, unsigned int bits, bn *dst);

void bn_lshift_original(const bn *src, unsigned int bits, bn *dst);

void bn_add(const bn *a, const bn *b, bn *c);



#endif /* _BN_H */
