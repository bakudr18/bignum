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

#define KARATSUBA_MUL_THRESHOLD 32
#define KARATSUBA_SQR_THRESHOLD 64

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

static inline bool is_power_of_2(uint64_t n)
{
    return (n != 0 && ((n & (n - 1)) == 0));
}

#define bn_digit_zero(u, size) memset((u), 0, BN_DIGIT_SIZE *(size))

#define bn_digit_alloc(size) MALLOC(BN_DIGIT_SIZE *(size))

#define bn_digit_free(u) FREE(u)

#define bn_digit_cpy(src, size, dst) \
    memmove((dst), (src), BN_DIGIT_SIZE *(size))

#define bn_digit_mul(u, v, hi, lo) \
    __asm__("mulq %3" : "=a"(lo), "=d"(hi) : "%0"(u), "rm"(v))

#define bn_trim_size(bn)                       \
    while (bn->size && !bn->num[bn->size - 1]) \
        bn->size--;

void bn_print_dec(const bn *src)
{
    /**
     * log10(2^(size * 64)) = (size * 64) / log2(10) ~= (size * 64) / 3.322
     * ~= (size * 64) / 3 + 1
     * append with a sign and a '\0'
     */
    size_t len = (BN_DIGIT_BITS * src->size) / 3 + 1 + src->sign + 1;
    char *s = MALLOC(len);

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
    printf("%s\n", p);
    // memmove(s, p, len - (p - s));
    FREE(s);
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

    a += asize;
    b += bsize;
    while (asize--) {
        --a;
        --b;
        if (*a > *b)
            return 1;
        if (*a < *b)
            return -1;
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
    // memset(tmp + src->size, 0, BN_DIGIT_SIZE * ((1ULL << capacity) -
    // src->size));

    src->num = tmp;
    src->size = size;
    src->capacity = capacity;
}


void bn_set_num(bn *src, bn_digit n, uint64_t offset, bool sign)
{
    if (offset > src->size - 1)
        bn_resize(src, offset + 1);
    src->num[offset] = n;
    src->sign = sign;
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
    bn_digit_zero(src->num, digits);
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
    bn_digit_zero(dst->num, digits);
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
    bn_digit_zero(dst->num, digits);
    if (cy) {
        bn_resize(dst, dst->size + 1);
        dst->num[dst->size - 1] = cy;
    }
}

/* Set u[size] = u[size] + 1, and return the carry. */
static bn_digit bn_increment_partial(bn_digit *u, uint64_t size)
{
    if (size == 0)
        return 1;
    for (; size--; ++u) {
        if (++*u)
            return 0;
    }
    return 1;
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
#define bn_addi_partial(a, b, size) bn_add_partial(a, b, size, a)

/* Set u[size] = u[size] - v[size] and return the carry. */
static bn_digit bn_subi_partial(bn_digit *u, const bn_digit *v, uint64_t size)
{
    ASSERT(u != NULL);
    ASSERT(v != NULL);
    bn_digit carry = 0;
    while (size--) {
        bn_digit vd = *v++;
        const bn_digit ud = *u;
        carry = (vd += carry) < carry;
        carry += (*u -= vd) > ud;
        ++u;
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

static bn_digit bn_mul_partial(const bn_digit *a,
                               uint64_t size,
                               const bn_digit k,
                               bn_digit *c)
{
    if (k <= 1) {
        if (k == 0)
            bn_digit_zero(c, size);
        else
            bn_digit_cpy(a, size, c);
        return 0;
    }

    if (is_power_of_2(k))
        return bn_lshift_mod(a, size, ilog2(k), c);

    bn_digit carry = 0;
    for (uint64_t i = 0; i < size; i++) {
        bn_digit high, low;
        bn_digit_mul(a[i], k, high, low);
        carry = high + ((low += carry) < carry);
        carry += ((c[i] += low) < low);
    }
    return carry;
}

/* c[asize + bsize] = a[asize] x b[bsize]
 * TODO: check if c should be clean up first */
static void bn_mul_base(const bn_digit *a,
                        uint64_t asize,
                        const bn_digit *b,
                        uint64_t bsize,
                        bn_digit *c)
{
    if (!asize || !bsize)
        return;
    for (uint64_t i = 0; i < bsize; i++)
        c[asize + i] = bn_mul_partial(a, asize, b[i], c + i);
}

/* Karatsuba multiplication [cf. Knuth 4.3.3, vol.2, 3rd ed, pp.294-295]
 * Given U = U1*2^N + U0 and V = V1*2^N + V0,
 * we can recursively compute U*V with
 * (2^2N + 2^N)U1*V1 + (2^N)(U1-U0)(V0-V1) + (2^N + 1)U0*V0
 *
 * We might otherwise use
 * (2^2N - 2^N)U1*V1 + (2^N)(U1+U0)(V1+V0) + (1 - 2^N)U0*V0
 * except that (U1+U0) or (V1+V0) may become N+1 bit numbers if there is carry
 * in the additions, and this will slow down the routine.  However, if we use
 * the first formula the middle terms will not grow larger than N bits.
 */
static void bn_mul_karatsuba(const bn_digit *u,
                             const bn_digit *v,
                             uint64_t size,
                             bn_digit *w)
{
    if (size < KARATSUBA_MUL_THRESHOLD) {
        bn_mul_base(u, size, v, size, w);
        return;
    }

    const bool odd = size & 1;
    const uint64_t even_size = size - odd;
    const uint64_t half_size = even_size / 2;

    const bn_digit *u0 = u, *u1 = u + half_size;
    const bn_digit *v0 = v, *v1 = v + half_size;
    bn_digit *w0 = w, *w1 = w + even_size;

    /* U0 * V0 => w[0..even_size-1]; */
    /* U1 * V1 => w[even_size..2*even_size-1]. */
    if (half_size >= KARATSUBA_MUL_THRESHOLD) {
        bn_mul_karatsuba(u0, v0, half_size, w0);
        bn_mul_karatsuba(u1, v1, half_size, w1);
    } else {
        bn_mul_base(u0, half_size, v0, half_size, w0);
        bn_mul_base(u1, half_size, v1, half_size, w1);
    }

    /* Since we cannot add w[0..even_size-1] to w[half_size ...
     * half_size+even_size-1] in place, we have to make a copy of it now.
     * This later gets used to store U1-U0 and V0-V1.
     */
    bn_digit *tmp = bn_digit_alloc(even_size);
    bn_digit_cpy(w0, even_size, tmp);

    bn_digit carry = 0;
    /* w[half_size..half_size+even_size-1] += U1*V1. */
    carry = bn_add_partial(w + half_size, w1, even_size, w + half_size);
    /* w[half_size..half_size+even_size-1] += U0*V0. */
    carry += bn_add_partial(w + half_size, tmp, even_size, w + half_size);

    /* Get |U1 - U0| */
    bn_digit *u_tmp = tmp;
    bool prod_neg = bn_cmp(u1, half_size, u0, half_size) < 0;
    if (prod_neg)
        bn_sub_partial(u0, u1, half_size, u_tmp);
    else
        bn_sub_partial(u1, u0, half_size, u_tmp);

    /* Get |V0 - V1| */
    bn_digit *v_tmp = tmp + half_size;
    if (bn_cmp(v0, half_size, v1, half_size) < 0)
        bn_sub_partial(v1, v0, half_size, v_tmp), prod_neg ^= 1;
    else
        bn_sub_partial(v0, v1, half_size, v_tmp);

    /* tmp = (U1 - U0) * (V0 - V1) */
    tmp = bn_digit_alloc(even_size);
    bn_digit_zero(tmp, even_size);
    if (half_size >= KARATSUBA_MUL_THRESHOLD)
        bn_mul_karatsuba(u_tmp, v_tmp, half_size, tmp);
    else
        bn_mul_base(u_tmp, half_size, v_tmp, half_size, tmp);
    bn_digit_free(u_tmp);

    /* Now add / subtract (U1-U0)*(V0-V1) from
     * w[half_size..half_size+even_size-1] based on whether it is negative or
     * positive.
     */
    if (prod_neg)
        carry -= bn_sub_partial(w + half_size, tmp, even_size, w + half_size);
    else
        carry += bn_add_partial(w + half_size, tmp, even_size, w + half_size);
    bn_digit_free(tmp);

    /* Now if there was any carry from the middle digits (which is at most 2),
     * add that to w[even_size+half_size..2*even_size-1]. */
    if (carry) {
        for (uint64_t i = even_size + half_size; i < even_size << 1; i++) {
            bn_digit tmp1 = w[i];
            carry = (tmp1 += carry) < carry;
            w[i] = tmp1;
        }
        ASSERT(carry == 0);
    }

    if (odd) {
        /* We have the product U[0..even_size-1] * V[0..even_size-1] in
         * W[0..2*even_size-1].  We need to add the following to it:
         * V[size-1] * U[0..size-2]
         * U[size-1] * V[0..size-1] */
        w[even_size << 1] =
            bn_mul_partial(u, even_size, v[even_size], w + even_size);
        w[(even_size << 1) + 1] =
            bn_mul_partial(v, size, u[even_size], w + even_size);
    }
}

void bn_mul(const bn *a, const bn *b, bn *c)
{
    ASSERT(a->size != 0);
    ASSERT(b->size != 0);

    if (a->size < b->size)
        SWAP(a, b);

    uint64_t asize = a->size;
    uint64_t bsize = b->size;
    uint64_t csize = a->size + b->size;
    bn *tmp = NULL;

    if (a == c || b == c) {
        tmp = c;  // save c
        c = bn_alloc(csize);
        bn_digit_zero(c->num, csize);
    } else {
        ASSERT(a->num[a->size - 1] != 0);
        ASSERT(b->num[b->size - 1] != 0);
        bn_resize(c, csize);
        bn_digit_zero(c->num, csize);
    }

    bn_digit *adigit = a->num;
    bn_digit *bdigit = b->num;
    bn_digit *cdigit = c->num;
    if (b->size < KARATSUBA_MUL_THRESHOLD) {
        bn_mul_base(adigit, asize, bdigit, bsize, cdigit);
    } else {
        bn_mul_karatsuba(adigit, bdigit, bsize, cdigit);
        /* it's assumed that a and b are equally length in
         * Karatsuba multiplication, therefore we have to
         * deal with the remaining part after hand
         */
        if (asize == bsize)
            goto end;

        /* we have to calc a[bsize ~ asize-1] * b */
        // bn_digit_zero(c + (bsize * 2), csize - (bsize * 2));
        cdigit += bsize;
        csize -= bsize;
        adigit += bsize;
        asize -= bsize;
        bn_digit *tmp2 = NULL;
        /* if asize = n * bsize, multiply it with same method */
        if (asize >= bsize) {
            tmp2 = bn_digit_alloc(bsize * 2);
            bn_digit_zero(tmp2, bsize * 2);
            do {
                bn_mul_karatsuba(adigit, bdigit, bsize, tmp2);
                bn_digit carry;
                carry = bn_addi_partial(cdigit, tmp2, bsize * 2);
                carry = carry ? bn_increment_partial(cdigit + (bsize * 2),
                                                     csize - (bsize * 2))
                              : 0;
                ASSERT(carry == 0);
                cdigit += bsize;
                csize -= bsize;
                adigit += bsize;
                asize -= bsize;
            } while (asize >= bsize);
        }
        /* if asize != n * bsize, simply calculate the remaining part */
        if (asize) {
            if (!tmp2) {
                tmp2 = bn_digit_alloc(asize + bsize);
                bn_digit_zero(tmp2, asize + bsize);
            }
            bn_mul_base(bdigit, bsize, adigit, asize, tmp2);
            bn_digit carry;
            carry = bn_add_partial(cdigit, tmp2, asize + bsize, cdigit);
            carry = carry ? bn_increment_partial(cdigit + (asize + bsize),
                                                 csize - (asize + bsize))
                          : 0;
            ASSERT(carry == 0);
        }
        if (tmp2)
            bn_digit_free(tmp2);
    }

end:
    c->sign = a->sign ^ b->sign;
    bn_trim_size(c);
    if (tmp) {
        SWAP(tmp, c);
        bn_free(c);
    }
}


void bn_fib(uint64_t n, bn *fib)
{
    if (unlikely(n <= 2)) {
        bn_set_num(fib, n, 0, 0);
        return;
    }

    bn *a1 = fib;

    bn *a0, *tmp, *a;
    a0 = bn_alloc(1);
    bn_set_num(a0, 0, 0, 0);
    // a1 = bn_alloc(1);
    bn_set_num(a1, 1, 0, 0);
    tmp = bn_alloc(1);
    bn_set_num(tmp, 0, 0, 0);

    a = bn_alloc(1);

    for (uint64_t k = ((uint64_t) 1) << (62 - __builtin_clzll(n)); k; k >>= 1) {
        bn_lshift(a0, 1, a);
        bn_add(a, a1, a);
        bn_mul(a1, a1, tmp);
        bn_mul(a0, a0, a0);
        bn_add(a0, tmp, a0);
        bn_mul(a1, a, a1);
        if (k & n) {
            SWAP(a1, a0);
            bn_add(a0, a1, a1);
        }
    }

    bn_free(a0);
    bn_free(tmp);
    bn_free(a);
}
