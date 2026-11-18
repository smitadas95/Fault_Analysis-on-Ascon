#include "ascon_common.h"

#include <inttypes.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#define NCOLS 64
#define NFAULTS 5
#define MAX_SIG_IF 32
#define MAX_SIG_EF 1024

/* Ascon 5-bit S-box, with x[4] as the MSB and x[0] as the LSB. */
static const uint8_t S[32] = {
    0x04, 0x0B, 0x1F, 0x14, 0x1A, 0x15, 0x09, 0x02,
    0x1B, 0x05, 0x08, 0x12, 0x1D, 0x03, 0x06, 0x1C,
    0x1E, 0x13, 0x07, 0x0E, 0x00, 0x0D, 0x11, 0x18,
    0x10, 0x0C, 0x01, 0x19, 0x16, 0x0A, 0x0F, 0x17
};

typedef struct {
    int i;
    int j;
    const char *name;
} Placement;

static const Placement placements[3] = {
    {4, 3, "(4,3)"},
    {4, 0, "(4,0)"},
    {3, 2, "(3,2)"}
};

typedef struct {
    int valid;
    uint8_t yi;
    uint8_t yj;
} LookupEntry;

static uint64_t invrows[5][64];

/* Deterministic xorshift* generator, matching the earlier experiment style. */
static uint64_t rng_state = UINT64_C(23);

static uint64_t rnd64(void)
{
    rng_state ^= rng_state >> 12;
    rng_state ^= rng_state << 25;
    rng_state ^= rng_state >> 27;
    return rng_state * UINT64_C(2685821657736338717);
}

static void random_bytes(uint8_t *p, size_t n)
{
    for (size_t i = 0; i < n; i++)
        p[i] = (uint8_t)rnd64();
}

static size_t choose_size(const size_t *values, size_t n)
{
    return values[rnd64() % n];
}

static void random_input(uint8_t nonce[16], uint8_t ad[24], size_t *adlen,
                         uint8_t pt[24], size_t *ptlen)
{
    static const size_t ad_sizes[] = {0, 8, 16};
    static const size_t pt_sizes[] = {8, 16, 24};

    random_bytes(nonce, 16);
    *adlen = choose_size(ad_sizes, 3);
    *ptlen = choose_size(pt_sizes, 3);
    random_bytes(ad, *adlen);
    random_bytes(pt, *ptlen);
}

static int bit_y(uint8_t y, int coordinate)
{
    return (y >> (4 - coordinate)) & 1;
}

static int rbit(int coordinate)
{
    return 1 << (4 - coordinate);
}

/* The Ascon linear diffusion map for one 64-bit state word. */
static uint64_t apply_lin(int reg, uint64_t x)
{
    static const int rotations[5][2] = {
        {19, 28}, {61, 39}, {1, 6}, {10, 17}, {7, 41}
    };

    return x ^ ror64(x, (unsigned)rotations[reg][0])
             ^ ror64(x, (unsigned)rotations[reg][1]);
}

/* Build the inverse linear map using the same basis/elimination method
 * as the supplied e2e_v2.c. */
static void make_inverse(int reg)
{
    static const int rotations[5][2] = {
        {19, 28}, {61, 39}, {1, 6}, {10, 17}, {7, 41}
    };
    uint64_t a[64], b[64];

    for (int i = 0; i < 64; i++) {
        uint64_t e = UINT64_C(1) << i;
        a[i] = e ^ ror64(e, (unsigned)rotations[reg][0])
                 ^ ror64(e, (unsigned)rotations[reg][1]);
        b[i] = e;
    }

    for (int c = 0; c < 64; c++) {
        int pivot = c;
        while (pivot < 64 && !((a[pivot] >> c) & 1))
            pivot++;

        if (pivot == 64) {
            fprintf(stderr, "Singular linear layer for word %d\n", reg);
            exit(EXIT_FAILURE);
        }

        uint64_t tmp = a[c];
        a[c] = a[pivot];
        a[pivot] = tmp;
        tmp = b[c];
        b[c] = b[pivot];
        b[pivot] = tmp;

        for (int r = 0; r < 64; r++) {
            if (r != c && ((a[r] >> c) & 1)) {
                a[r] ^= a[c];
                b[r] ^= b[c];
            }
        }
    }

    for (int i = 0; i < 64; i++)
        invrows[reg][i] = b[i];
}

static uint64_t apply_inv(int reg, uint64_t x)
{
    uint64_t y = 0;
    for (int i = 0; i < 64; i++) {
        if ((x >> i) & 1)
            y ^= invrows[reg][i];
    }
    return y;
}

/* Encode a two-coordinate S-box output difference as 00, 01, 10, or 11. */
static uint8_t response_for_x(uint8_t x, int fault_position,
                              int i, int j)
{
    uint8_t xf = (uint8_t)(x | (1u << (4 - fault_position)));
    uint8_t dy = (uint8_t)(S[x] ^ S[xf]);
    return (uint8_t)((bit_y(dy, i) << 1) | bit_y(dy, j));
}

/* Signature key for ordered IF: bit k is one exactly when d_k == 00. */
static int ordered_if_key_from_x(uint8_t x, int i, int j)
{
    int key = 0;
    for (int k = 0; k < NFAULTS; k++) {
        if (response_for_x(x, k, i, j) == 0)
            key |= 1 << k;
    }
    return key;
}

/* Signature key for ordered EF: preserve all five two-bit responses. */
static int ordered_ef_key_from_x(uint8_t x, int i, int j)
{
    int key = 0;
    for (int k = 0; k < NFAULTS; k++)
        key |= (int)response_for_x(x, k, i, j) << (2 * k);
    return key;
}

static void build_lookup(const Placement *p, int use_ordered_ef,
                         LookupEntry *table, int table_size,
                         int *conflicts)
{
    memset(table, 0, (size_t)table_size * sizeof(*table));
    *conflicts = 0;

    for (int x = 0; x < 32; x++) {
        int key = use_ordered_ef
                    ? ordered_ef_key_from_x((uint8_t)x, p->i, p->j)
                    : ordered_if_key_from_x((uint8_t)x, p->i, p->j);

        if (key < 0 || key >= table_size) {
            fprintf(stderr, "Internal signature-key range error\n");
            exit(EXIT_FAILURE);
        }

        uint8_t yi = (uint8_t)bit_y(S[x], p->i);
        uint8_t yj = (uint8_t)bit_y(S[x], p->j);

        if (!table[key].valid) {
            table[key].valid = 1;
            table[key].yi = yi;
            table[key].yj = yj;
        } else if (table[key].yi != yi || table[key].yj != yj) {
            (*conflicts)++;
        }
    }
}

static void inject_set(uint64_t state[5], int column, int input_position)
{
    state[input_position] |= UINT64_C(1) << column;
}

static void tag_for(const uint64_t state[5], uint64_t k0, uint64_t k1,
                    int i, int j, uint64_t *t0, uint64_t *t1)
{
    *t0 = state[i] ^ k0;
    *t1 = state[j] ^ k1;
}

/* Recover one key using the signature-to-output lookup. Each column uses
 * five faults, one SET fault at each of the five S-box input positions. */
static int recover_one(const Placement *p, int use_ordered_ef,
                       const LookupEntry *table, int table_size,
                       const uint8_t key[16], int verbose)
{
    uint8_t nonce[16], ad[24], pt[24];
    size_t adlen, ptlen;
    uint64_t state[5], k0, k1;
    uint64_t clean[5];
    uint64_t tag0, tag1;
    uint64_t recovered_invk0 = 0;
    uint64_t recovered_invk1 = 0;
    int observations = 0;
    int bad_signatures = 0;

    random_input(nonce, ad, &adlen, pt, &ptlen);
    ascon_last_input(state, &k0, &k1, key, nonce, ad, adlen, pt, ptlen);

    memcpy(clean, state, sizeof(clean));
    ascon_finish(clean);
    tag_for(clean, k0, k1, p->i, p->j, &tag0, &tag1);

    for (int col = 0; col < NCOLS; col++) {
        int if_key = 0;
        int ef_key = 0;

        for (int fault_position = 0; fault_position < NFAULTS;
             fault_position++) {
            uint64_t faulty[5];
            uint64_t faulty_tag0, faulty_tag1;
            uint64_t dy_i_word, dy_j_word;
            int d;

            memcpy(faulty, state, sizeof(faulty));
            inject_set(faulty, col, fault_position);
            ascon_finish(faulty);
            tag_for(faulty, k0, k1, p->i, p->j,
                    &faulty_tag0, &faulty_tag1);

            /* Remove the linear diffusion layer from the tag differences.
             * The key addition cancels in the clean/faulty difference. */
            dy_i_word = apply_inv(p->i, tag0 ^ faulty_tag0);
            dy_j_word = apply_inv(p->j, tag1 ^ faulty_tag1);
            d = (int)((((dy_i_word >> col) & 1) << 1)
                    | ((dy_j_word >> col) & 1));

            if (d == 0)
                if_key |= 1 << fault_position;
            ef_key |= d << (2 * fault_position);
            observations++;
        }

        int signature = use_ordered_ef ? ef_key : if_key;
        if (signature < 0 || signature >= table_size ||
            !table[signature].valid) {
            bad_signatures++;
            continue;
        }

        /* The signature reveals the selected two S-box output bits. */
        uint64_t u0 = apply_inv(p->i, tag0);
        uint64_t u1 = apply_inv(p->j, tag1);
        uint64_t ki_bit = ((u0 >> col) & 1) ^ table[signature].yi;
        uint64_t kj_bit = ((u1 >> col) & 1) ^ table[signature].yj;

        recovered_invk0 |= ki_bit << col;
        recovered_invk1 |= kj_bit << col;
    }

    if (bad_signatures != 0) {
        if (verbose)
            printf("  Invalid/unmapped signatures: %d\n", bad_signatures);
        return 0;
    }

    /* u = L^{-1}(k); invert that relation to obtain the key words. */
    uint64_t recovered_k0 = apply_lin(p->i, recovered_invk0);
    uint64_t recovered_k1 = apply_lin(p->j, recovered_invk1);
    uint64_t true_k0 = load64be(key);
    uint64_t true_k1 = load64be(key + 8);
    int success = (recovered_k0 == true_k0 && recovered_k1 == true_k1);

    if (verbose) {
        printf("  Observed fault responses: %d (5 x 64)\n", observations);
        printf("  Recovered K0: %016" PRIx64 "\n", recovered_k0);
        printf("  Actual    K0: %016" PRIx64 "\n", true_k0);
        printf("  Recovered K1: %016" PRIx64 "\n", recovered_k1);
        printf("  Actual    K1: %016" PRIx64 "\n", true_k1);
        printf("  Key recovery: %s\n", success ? "SUCCESS" : "FAILURE");
    }

    return success;
}

static void run_placement(const Placement *p, int trials)
{
    LookupEntry if_table[MAX_SIG_IF];
    LookupEntry ef_table[MAX_SIG_EF];
    int if_conflicts, ef_conflicts;
    int if_success = 0;
    int ef_success = 0;

    build_lookup(p, 0, if_table, MAX_SIG_IF, &if_conflicts);
    build_lookup(p, 1, ef_table, MAX_SIG_EF, &ef_conflicts);

    printf("\n==================================================\n");
    printf("Tag placement %s\n", p->name);
    printf("==================================================\n");
    printf("Ordered IF: %s for recovering the selected S-box output bits\n",
       if_conflicts == 0 ? "SUFFICIENT" : "INSUFFICIENT");

    printf("Ordered EF: %s for recovering the selected S-box output bits\n",
       ef_conflicts == 0 ? "SUFFICIENT" : "INSUFFICIENT");

    if (if_conflicts != 0 || ef_conflicts != 0) {
        printf("At least one signature does not determine both selected output bits.\n");
        printf("Full key recovery from that signature model is not justified.\n");
        return;
    }

    for (int tr = 0; tr < trials; tr++) {
        uint8_t key[16];
        random_bytes(key, sizeof(key));

        if_success += recover_one(p, 0, if_table, MAX_SIG_IF,
                                  key, tr == 0);
        ef_success += recover_one(p, 1, ef_table, MAX_SIG_EF,
                                  key, tr == 0);
    }

    printf("\nSummary over %d independent keys/inputs:\n", trials);
    printf("  Ordered IF: %d/%d complete 128-bit keys recovered\n",
           if_success, trials);
    printf("  Ordered EF: %d/%d complete 128-bit keys recovered\n",
           ef_success, trials);
    printf("  Faulted tag evaluations per run and model: %d\n",
           NFAULTS * NCOLS);
}

int main(int argc, char **argv)
{
    int trials = 20;

    if (argc > 1) {
        char *end = NULL;
        long value = strtol(argv[1], &end, 10);
        if (end == argv[1] || *end != '\0' || value < 1 || value > 100000) {
            fprintf(stderr, "Usage: %s [number-of-trials]\n", argv[0]);
            return EXIT_FAILURE;
        }
        trials = (int)value;
    }

    for (int r = 0; r < 5; r++)
        make_inverse(r);

    printf("Ascon-128 v1.2: ordered IF/EF key-recovery experiment\n");
    printf("Fault sequence: SET(0), SET(1), SET(2), SET(3), SET(4)\n");
    printf("S-box coordinate convention: y4 is MSB, y0 is LSB\n");
    printf("Trials: %d\n", trials);
    printf("Model: same clean Ascon state is reused for the five fault positions\n");

    for (int p = 0; p < 3; p++)
        run_placement(&placements[p], trials);

    return EXIT_SUCCESS;
}
