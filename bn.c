#include "bn.h"
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include "memory.h"

#ifdef BN_DEBUG
#include <assert.h>
#define ASSERT(expr) assert(expr)
#else
#define ASSERT(expr) (void) (expr)
#endif

#ifndef unlikely
#define unlikely(x) __builtin_expect((x), 0)
#endif

#ifndef MAX
#define MAX(a, b) ((a) > (b) ? (a) : (b))
#endif

#ifndef SWAP
#define SWAP(x, y)           \
    do {                     \
        typeof(x) __tmp = x; \
        x = y;               \
        y = __tmp;           \
    } while (0)
#endif

#define BN_DIGIT_SIZE sizeof(bn_digit)
#define BN_DIGIT_BITS (BN_DIGIT_SIZE * 8)

struct bn {
    uint64_t size : 57, /* count of num. bytes length = count * BN_DIGIT_SIZE */
        capacity : 6, /* actual bytes allocated is (2^capacity) * BN_DIGIT_SIZE
                       */
        sign : 1;
    bn_digit *num;
};

/* lowerbound (floor log2) */
/* Note that n = 0 is undefined */
static inline int ilog2(uint64_t n)
{
    return 63 - __builtin_clzll(n);
}

#define bn_trim_size(bn)                        \
    while (bn->size && !bn->num[bn->size - 1])  \
        bn->size--;

char *bn_to_dec_string(const bn *src)
{
    /**
     * log10(2^(size * 64)) = (size * 64) / log2(10) ~= (size * 64) / 3.322
     * ~= (size * 64) / 3 + 1
     * append with a sign and a '\0'
     */
    size_t len = (BN_DIGIT_BITS * src->size) / 3 + 1 + src->sign + 1;
    char *s = MALLOC(len);
    if (!s)
        return NULL;

    char *p = s;
    memset(s, '0', len - 1);
    s[len - 1] = '\0';

    /* convert from higher order */
    for (int i = src->size - 1; i >= 0; i--) {
        /* convert from higher bit */
        for (bn_digit d = 1ULL << (BN_DIGIT_BITS - 1); d; d >>= 1) {
            int carry = !!(d & src->num[i]);
            // printf("%d", carry);
            for (int j = len - 2; j >= 0; j--) {
                s[j] += s[j] - '0' + carry;
                carry = (s[j] > '9');
                if (carry)
                    s[j] -= 10;
            }
        }
        // printf(" ");
    }
    // printf("\n");

    // skip leading zero
    while (p[0] == '0' && p[1] != '\0') {
        p++;
    }
    if (src->sign)
        *(--p) = '-';
    // printf("%s", p);
    memmove(s, p, len - (p - s));
    return s;
}

bn *bn_alloc(uint64_t size)
{
    ASSERT(size != 0);
    ASSERT(size < (1ULL << 57));

    int capacity = ilog2(size) + 1;
    if (capacity > (1 << 6))
        return NULL;
    bn *new = MALLOC(sizeof(bn));
    if (!new)
        return NULL;
    new->num = MALLOC(BN_DIGIT_SIZE * (1ULL << capacity));
    if (!new->num) {
        free(new);
        return NULL;
    }
    memset(new->num, 0, BN_DIGIT_SIZE * (1ULL << capacity));
    new->size = size;
    new->capacity = capacity;
    new->sign = 0;
    return new;
}

void bn_free(bn *src)
{
    if (src) {
        FREE(src->num);
        FREE(src);
        src = NULL;
    }
}

static int bn_cmp(const bn_digit *a,
                  uint64_t asize,
                  const bn_digit *b,
                  uint64_t bsize)
{
    if (asize > bsize)
        return 1;
    if (asize < bsize)
        return -1;

    while (asize--) {
        if (*a > *b)
            return 1;
        if (*a < *b)
            return -1;
        a++;
        b++;
    }
    return 0;
}

static void bn_resize(bn *src, uint64_t size)
{
    ASSERT(src != NULL);
    ASSERT(size != 0);

    int capacity = ilog2(size) + 1;
    if (src->capacity >= capacity) {
        src->size = size;
        return;
    }

    /* Note that the added memory is not initialized */
    bn_digit *tmp = REALLOC(src->num, BN_DIGIT_SIZE * (1ULL << capacity));
    ASSERT(tmp != NULL);
    // memset(tmp + src->size, 0, BN_DIGIT_SIZE * ((1ULL << capacity) - src->size));

    src->num = tmp;
    src->size = size;
    src->capacity = capacity;
}


void bn_set_num(bn *src, bn_digit n, uint64_t offset)
{
    if (offset > src->size - 1)
        bn_resize(src, offset + 1);
    src->num[offset] = n;
}

static void bn_cpy(bn *dst, const bn *src)
{
    ASSERT(dst != NULL);
    ASSERT(src != NULL);

    if (unlikely(dst == src))
        return;

    bn_resize(dst, src->size);

    memcpy(dst->num, src->num, src->size * BN_DIGIT_SIZE);
    dst->sign = src->sign;
}

static bn_digit bn_lshift_mod(const bn_digit *src,
                              uint64_t size,
                              unsigned int shift,
                              bn_digit *dst)
{
    // ASSERT(src != dst);
    // ASSERT(shift < BN_DIGIT_BITS);

    if (!size)
        return 0;

    shift &= BN_DIGIT_BITS - 1;
    if (!shift) {
        memcpy(dst, src, BN_DIGIT_SIZE * size);
        return 0;
    }

    const unsigned int subp = BN_DIGIT_BITS - shift;
    bn_digit carry = 0;

    do {
        const bn_digit p = *src++;
        *dst++ = (p << shift) | carry;
        carry = p >> subp;
    } while (--size);
    return carry;
}

static bn_digit bn_lshifti_mod(bn_digit *src, uint64_t size, unsigned int shift)
{
    shift &= BN_DIGIT_BITS - 1;
    if (!size || !shift) {
        return 0;
    }

    const unsigned int subp = BN_DIGIT_BITS - shift;
    bn_digit carry = 0;

    do {
        const bn_digit p = *src++;
        *src++ = (p << shift) | carry;
        carry = p >> subp;
    } while (--size);
    return carry;
}

void bn_lshifti(bn *src, unsigned int bits)
{
    ASSERT(src->size != 0);

    if (unlikely(bits == 0)) {
        return;
    }

    const unsigned int digits = bits / BN_DIGIT_BITS;
    bits %= BN_DIGIT_BITS;

    uint64_t orig_size = src->size;
    uint64_t new_size = src->size + digits;
    const unsigned int subp = BN_DIGIT_BITS - bits;
    if (bits > 0 && src->num[src->size - 1] >> subp != 0)
        new_size++;
    bn_resize(src, new_size);

    if ((bits & 7) == 0) {
        src->num[new_size - 1] = 0; /* clean uninitialized block */
        uint8_t *dst_head = (uint8_t *) (src->num + digits) + (bits >> 3);
        memmove(dst_head, src->num, BN_DIGIT_SIZE * orig_size);
        memset(src->num, 0, BN_DIGIT_SIZE * digits + (bits >> 3));
        return;
    }

    bn_digit *src_tail = &src->num[orig_size - 1];
    bn_digit *dst_tail = &src->num[src->size - 1];
    if (new_size - orig_size - digits == 1) {
        *dst_tail-- = *src_tail >> subp;
    }
    while (--orig_size) {
        const bn_digit p = *src_tail--;
        *dst_tail-- = (p << bits) | (*src_tail >> subp);
    }
    *dst_tail = *src_tail << bits;
    memset(src->num, 0, BN_DIGIT_SIZE * digits);
}

/* Can not pass same pointer of src and dst */
void bn_lshift(const bn *src, unsigned int bits, bn *dst)
{
    ASSERT(src->size != 0);
    if (src == dst) {
        bn_lshifti(dst, bits);
        return;
    }

    if (unlikely(bits == 0)) {
        bn_cpy(dst, src);
        return;
    }

    const unsigned int digits = bits / BN_DIGIT_BITS;
    bits %= BN_DIGIT_BITS;
    const unsigned int subp = BN_DIGIT_BITS - bits;

    uint64_t orig_size = src->size;
    uint64_t new_size = src->size + digits;
    if (bits > 0 && src->num[src->size - 1] >> subp != 0)
        new_size++;
    bn_resize(dst, new_size);

    if ((bits & 7) == 0) {
        dst->num[new_size - 1] = 0; /* clean uninitialized block */
        uint8_t *dst_head = (uint8_t *) (dst->num + digits) + (bits >> 3);
        memcpy(dst_head, src->num, BN_DIGIT_SIZE * src->size);
        memset(dst->num, 0, BN_DIGIT_SIZE * digits + (bits >> 3));
        return;
    }

    bn_digit *src_tail = &src->num[src->size - 1];
    bn_digit *dst_tail = &dst->num[dst->size - 1];
    if (src->size + digits + 1 == dst->size) {
        *dst_tail-- = *src_tail >> subp;
    }
    while (--orig_size) {
        const bn_digit p = *src_tail--;
        *dst_tail-- = (p << bits) | (*src_tail >> subp);
    }
    *dst_tail = *src_tail << bits;
    memset(dst->num, 0, BN_DIGIT_SIZE * digits);
}

/* Can not pass same pointer of src and dst */
void bn_lshift_original(const bn *src, unsigned int bits, bn *dst)
{
    ASSERT(src != dst);
    ASSERT(src->size != 0);

    if (unlikely(bits == 0)) {
        bn_cpy(dst, src);
        return;
    }

    const unsigned int digits = bits / BN_DIGIT_BITS;
    bits %= BN_DIGIT_BITS;

    bn_digit cy;
    bn_resize(dst, src->size + digits);
    cy = bn_lshift_mod(src->num, src->size, bits, dst->num + digits);
    memset(dst->num, 0, BN_DIGIT_SIZE * digits);
    if (cy) {
        bn_resize(dst, dst->size + 1);
        dst->num[dst->size - 1] = cy;
    }
}

/* Set c[size] = a[size] + b[size] and return the carry. */
static bn_digit bn_add_partial(const bn_digit *a,
                               const bn_digit *b,
                               uint64_t size,
                               bn_digit *c)
{
    ASSERT(a != NULL);
    ASSERT(b != NULL);
    ASSERT(c != NULL);

    bn_digit carry = 0;
    while (size--) {
        bn_digit tmp = *a++;
        const bn_digit tmp2 = *b++;
        carry = (tmp += carry) < carry;
        carry += (*c = tmp + tmp2) < tmp2;
        ++c;
    }
    return carry;
}

/* Set c[size] = a[size] - b[size] and return the carry. */
static bn_digit bn_sub_partial(const bn_digit *a,
                               const bn_digit *b,
                               uint64_t size,
                               bn_digit *c)
{
    ASSERT(a != NULL);
    ASSERT(b != NULL);
    ASSERT(c != NULL);
    bn_digit carry = 0;
    while (size--) {
        const bn_digit tmp = *a++;
        bn_digit tmp2 = *b++;
        carry = (tmp2 += carry) < carry;
        carry += (*c = tmp - tmp2) > tmp;
        ++c;
    }
    return carry;
}

/* |c| = |a| + |b| */
static void bn_abs_add(const bn *a, const bn *b, bn *c)
{
    ASSERT(a != b);

    if (a->size < b->size)
        SWAP(a, b);
    uint64_t asize = a->size, bsize = b->size;
    bn_resize(c, asize);

    bn_digit carry = bn_add_partial(a->num, b->num, bsize, c->num);
    if (asize != bsize) {
        for (uint64_t i = bsize; i < asize; i++) {
            bn_digit tmp = a->num[i];
            carry = (tmp += carry) < carry;
            c->num[i] = tmp;
        }
    }
    if (carry) {
        bn_resize(c, c->size + 1);
        c->num[asize] = carry;
    }
}


/* |c| = |a| - |b|, only works when |a| > |b| */
static void bn_abs_sub(const bn *a, const bn *b, bn *c)
{
    ASSERT(a->size >= b->size);

    uint64_t asize = a->size, bsize = b->size;
    bn_resize(c, asize);

    bn_digit carry = bn_sub_partial(a->num, b->num, bsize, c->num);
    if (asize != bsize) {
        for (uint64_t i = bsize; i < asize; i++) {
            bn_digit tmp = a->num[i];
            carry = (tmp -= carry) > carry;
            c->num[i] = tmp;
        }
    }

    bn_trim_size(c);
}

void bn_add(const bn *a, const bn *b, bn *c)
{
    ASSERT(a->size != 0);
    ASSERT(b->size != 0);
    ASSERT(c->size != 0);

    if (a == b) {
        bn_lshift(a, 1, c);
        return;
    }

    if (a->sign == b->sign) {
        bn_abs_add(a, b, c);
        return;
    }

    /* Differing signs */
    if (a->sign)
        SWAP(a, b);

    int cmp = bn_cmp(a->num, a->size, b->num, b->size);
    if (cmp > 0) { /* |A| > |B| */
        /* If B < 0 and |A| > |B|, then C = A - |B| */
        bn_abs_sub(a, b, c);
        c->sign = 0;
    } else if (cmp < 0) {
        bn_abs_sub(b, a, c);
        c->sign = 1;
    } else {
        /* |a| == |b| */
        bn_resize(c, 1);
        c->num[0] = 0;
        c->sign = 0;
    }
}
