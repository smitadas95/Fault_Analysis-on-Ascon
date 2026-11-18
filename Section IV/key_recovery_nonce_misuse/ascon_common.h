#ifndef ASCON_COMMON_H
#define ASCON_COMMON_H

#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <math.h>
#include <inttypes.h>

#define MASK64 UINT64_MAX

static const uint64_t ASCON_IV128 = UINT64_C(0x80400C0600000000);

static const uint8_t ASCON_RC[12] = {
    0xf0, 0xe1, 0xd2, 0xc3, 0xb4, 0xa5,
    0x96, 0x87, 0x78, 0x69, 0x5a, 0x4b
};

static inline uint64_t ror64(uint64_t x, unsigned n) {
    return (x >> n) | (x << (64 - n));
}

/* Ascon substitution layer. */
static inline void ascon_sbox(uint64_t s[5]) {
    uint64_t x0 = s[0], x1 = s[1], x2 = s[2];
    uint64_t x3 = s[3], x4 = s[4];

    x0 ^= x4;
    x4 ^= x3;
    x2 ^= x1;

    uint64_t t0 = (~x0) & x1;
    uint64_t t1 = (~x1) & x2;
    uint64_t t2 = (~x2) & x3;
    uint64_t t3 = (~x3) & x4;
    uint64_t t4 = (~x4) & x0;

    x0 ^= t1;
    x1 ^= t2;
    x2 ^= t3;
    x3 ^= t4;
    x4 ^= t0;

    x1 ^= x0;
    x0 ^= x4;
    x3 ^= x2;
    x2 = ~x2;

    s[0] = x0;
    s[1] = x1;
    s[2] = x2;
    s[3] = x3;
    s[4] = x4;
}

/* Ascon linear diffusion layer. */
static inline void ascon_lin(uint64_t s[5]) {
    s[0] ^= ror64(s[0], 19) ^ ror64(s[0], 28);
    s[1] ^= ror64(s[1], 61) ^ ror64(s[1], 39);
    s[2] ^= ror64(s[2], 1)  ^ ror64(s[2], 6);
    s[3] ^= ror64(s[3], 10) ^ ror64(s[3], 17);
    s[4] ^= ror64(s[4], 7)  ^ ror64(s[4], 41);
}

static inline void ascon_round(uint64_t s[5], uint8_t rc) {
    s[2] ^= rc;
    ascon_sbox(s);
    ascon_lin(s);
}

static inline void ascon_perm(uint64_t s[5], int rounds) {
    for (int i = 12 - rounds; i < 12; i++) {
        ascon_round(s, ASCON_RC[i]);
    }
}

static inline uint64_t load64be(const uint8_t *p) {
    uint64_t x = 0;

    for (int i = 0; i < 8; i++) {
        x = (x << 8) | p[i];
    }

    return x;
}

static inline void store64be(uint8_t *p, uint64_t x) {
    for (int i = 7; i >= 0; i--) {
        p[i] = (uint8_t)x;
        x >>= 8;
    }
}

/*
 * Load n bytes in big-endian order and append the Ascon 10* padding.
 * Valid for n = 0,...,7.
 */
static inline uint64_t load_partial(const uint8_t *p, size_t n) {
    uint64_t x = 0;

    for (size_t i = 0; i < n; i++) {
        x |= ((uint64_t)p[i]) << (56 - 8 * i);
    }

    x |= UINT64_C(0x80) << (56 - 8 * n);

    return x;
}

static inline void xor_bytes(
    uint8_t *a,
    const uint8_t *b,
    size_t n
) {
    for (size_t i = 0; i < n; i++) {
        a[i] ^= b[i];
    }
}

/* Absorb associated data using the rate-8, p[6] construction. */
static inline void ascon_absorb_data(
    uint64_t s[5],
    const uint8_t *data,
    size_t len
) {
    while (len >= 8) {
        s[0] ^= load64be(data);
        ascon_perm(s, 6);

        data += 8;
        len -= 8;
    }

    s[0] ^= load_partial(data, len);
    ascon_perm(s, 6);
}

/*
 * Obtain the state immediately before the final Ascon round's
 * S-box and linear layer.
 *
 * The final round constant is added, but the final S-box and
 * linear layer are deliberately not applied here.
 */
static inline void ascon_last_input(
    uint64_t out[5],
    uint64_t *k0out,
    uint64_t *k1out,
    const uint8_t key[16],
    const uint8_t nonce[16],
    const uint8_t *ad,
    size_t adlen,
    const uint8_t *pt,
    size_t ptlen
) {
    uint64_t k0 = load64be(key);
    uint64_t k1 = load64be(key + 8);

    uint64_t n0 = load64be(nonce);
    uint64_t n1 = load64be(nonce + 8);

    uint64_t s[5] = {
        ASCON_IV128, k0, k1, n0, n1
    };

    /* Initialization. */
    ascon_perm(s, 12);

    s[3] ^= k0;
    s[4] ^= k1;

    /* Associated data. */
    if (adlen != 0) {
        ascon_absorb_data(s, ad, adlen);
    }

    /* Domain separation. */
    s[4] ^= 1;

    /* Plaintext absorption. */
    size_t off = 0;

    while (ptlen - off >= 8) {
        s[0] ^= load64be(pt + off);
        off += 8;

        ascon_perm(s, 6);
    }

    s[0] ^= load_partial(pt + off, ptlen - off);

    /* Final key addition. */
    s[1] ^= k0;
    s[2] ^= k1;

    /* First eleven rounds of finalization. */
    for (int i = 0; i < 11; i++) {
        ascon_round(s, ASCON_RC[i]);
    }

    /* Add the final round constant only. */
    s[2] ^= ASCON_RC[11];

    memcpy(out, s, sizeof(s));

    *k0out = k0;
    *k1out = k1;
}

/* Apply the final S-box and linear layer. */
static inline void ascon_finish(uint64_t s[5]) {
    ascon_sbox(s);
    ascon_lin(s);
}

/* Extract a tag from the selected state words. */
static inline void ascon_tag(
    const uint64_t sf[5],
    uint64_t k0,
    uint64_t k1,
    int i,
    int j,
    uint64_t *t0,
    uint64_t *t1
) {
    *t0 = sf[i] ^ k0;
    *t1 = sf[j] ^ k1;
}

/* Complete Ascon-128 v1.2 encryption. */
static inline void ascon_encrypt(
    uint8_t *ct,
    uint8_t tag[16],
    const uint8_t key[16],
    const uint8_t nonce[16],
    const uint8_t *ad,
    size_t adlen,
    const uint8_t *pt,
    size_t ptlen
) {
    uint64_t k0 = load64be(key);
    uint64_t k1 = load64be(key + 8);

    uint64_t n0 = load64be(nonce);
    uint64_t n1 = load64be(nonce + 8);

    uint64_t s[5] = {
        ASCON_IV128, k0, k1, n0, n1
    };

    /* Initialization. */
    ascon_perm(s, 12);

    s[3] ^= k0;
    s[4] ^= k1;

    /* Associated data. */
    if (adlen != 0) {
        ascon_absorb_data(s, ad, adlen);
    }

    /* Domain separation. */
    s[4] ^= 1;

    /* Plaintext encryption. */
    size_t off = 0;

    while (ptlen - off >= 8) {
        s[0] ^= load64be(pt + off);
        store64be(ct + off, s[0]);

        off += 8;

        /*
         * Apply p[6] after every full block, including when
         * the plaintext length is an exact multiple of 8.
         */
        ascon_perm(s, 6);
    }

    /* Final partial block, including an empty block if needed. */
    size_t rem = ptlen - off;

    s[0] ^= load_partial(pt + off, rem);

    if (rem != 0) {
        uint8_t tmp[8];

        store64be(tmp, s[0]);
        memcpy(ct + off, tmp, rem);
    }

    /* Finalization. */
    s[1] ^= k0;
    s[2] ^= k1;

    ascon_perm(s, 12);

    s[3] ^= k0;
    s[4] ^= k1;

    store64be(tag, s[3]);
    store64be(tag + 8, s[4]);
}

#endif