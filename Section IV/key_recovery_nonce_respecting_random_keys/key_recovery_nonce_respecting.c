/*
 * Nonce-respecting software fault-injection experiment for selected custom
 * tag placements (4,3), (4,0), and (3,2).
 *
 * One encryption transcript fixes N, AD, C, and the original custom tag.
 * For each of 64 S-box columns and five SET fault positions, the attacker
 * makes three verification queries with tag differences (0,1), (1,0),
 * and (1,1). The original tag (0,0) is not submitted.
 *
 * A response 00 means none of the three modified tags was accepted. The
 * fault caused no observable change in the two selected tag coordinates;
 * the full S-box output may or may not have changed.
 *
 * The attacker receives only the public transcript and a Boolean oracle.
 * The target-side oracle owns the key and performs decryption/verification.
 */

#define _GNU_SOURCE
#include "ascon_common.h"

#include <inttypes.h>
#include <errno.h>
#include <sys/random.h>

#include <stdint.h>

#include <stdio.h>

#include <stdlib.h>

#include <string.h>

#define NCOLS       64

#define NFAULTS     5

#define NFORGERIES  3

#define MAX_SIG_IF  32

#define MAX_SIG_EF  1024

#define MAX_AD_LEN  24

#define MAX_PT_LEN  24

typedef struct {

    int i;

    int j;

    const char *name;

} Placement;

static const Placement placements[] = {

    {4, 3, "(4,3)"},

    {4, 0, "(4,0)"},

    {3, 2, "(3,2)"}

};

#define NPLACEMENTS (sizeof(placements) / sizeof(placements[0]))

typedef struct {

    int valid;

    uint8_t yi;

    uint8_t yj;

} LookupEntry;

static uint64_t invrows[5][64];

/* Five-bit Ascon S-box: x[4] is MSB and x[0] is LSB. */

static const uint8_t S[32] = {

    0x04, 0x0B, 0x1F, 0x14, 0x1A, 0x15, 0x09, 0x02,

    0x1B, 0x05, 0x08, 0x12, 0x1D, 0x03, 0x06, 0x1C,

    0x1E, 0x13, 0x07, 0x0E, 0x00, 0x0D, 0x11, 0x18,

    0x10, 0x0C, 0x01, 0x19, 0x16, 0x0A, 0x0F, 0x17

};

/*
 * Obtain fresh random bytes from the operating system.
 * This is intended for the Linux/WSL GCC environment used for the experiment.
 */
static void random_bytes(uint8_t *p, size_t n)
{
    while (n > 0) {
        ssize_t received = getrandom(p, n, 0);

        if (received < 0) {
            if (errno == EINTR) {
                continue;
            }
            perror("getrandom");
            exit(EXIT_FAILURE);
        }

        if (received == 0) {
            fprintf(stderr, "getrandom returned zero bytes\n");
            exit(EXIT_FAILURE);
        }

        p += (size_t)received;
        n -= (size_t)received;
    }
}

/* Random value used for selecting the tested input lengths. */
static uint64_t rnd64(void)
{
    uint64_t value;
    random_bytes((uint8_t *)&value, sizeof(value));
    return value;
}

static size_t choose_size(const size_t *values, size_t n)

{

    return values[rnd64() % n];

}

static void random_input(

    uint8_t nonce[16],

    uint8_t ad[MAX_AD_LEN],

    size_t *adlen,

    uint8_t pt[MAX_PT_LEN],

    size_t *ptlen)

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

/* Ascon linear diffusion map for one 64-bit state word. */

static uint64_t apply_lin(int reg, uint64_t x)

{

    static const int rotations[5][2] = {

        {19, 28}, {61, 39}, {1, 6}, {10, 17}, {7, 41}

    };

    return x ^ ror64(x, (unsigned)rotations[reg][0])

             ^ ror64(x, (unsigned)rotations[reg][1]);

}

/* Build the inverse linear map by Gaussian elimination over GF(2). */

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

        while (pivot < 64 && (((a[pivot] >> c) & 1U) == 0U)) {

            pivot++;

        }

        if (pivot == 64) {

            fprintf(stderr, "Singular linear layer for word %d\n", reg);

            exit(EXIT_FAILURE);

        }

        if (pivot != c) {

            uint64_t tmp = a[c];

            a[c] = a[pivot];

            a[pivot] = tmp;

            tmp = b[c];

            b[c] = b[pivot];

            b[pivot] = tmp;

        }

        for (int r = 0; r < 64; r++) {

            if (r != c && ((a[r] >> c) & 1U)) {

                a[r] ^= a[c];

                b[r] ^= b[c];

            }

        }

    }

    for (int i = 0; i < 64; i++) {

        invrows[reg][i] = b[i];

    }

}

static uint64_t apply_inv(int reg, uint64_t x)

{

    uint64_t y = 0;

    for (int i = 0; i < 64; i++) {

        if ((x >> i) & 1U) {

            y ^= invrows[reg][i];

        }

    }

    return y;

}

/*
* Response encoding:
*   00 -> 0
*   01 -> 1
*   10 -> 2
*   11 -> 3
*
* A SET fault in input position p sets input bit (4-p).
*/

static uint8_t response_for_x(

    uint8_t x,

    int fault_position,

    int i,

    int j)

{

    /* Fault position p sets coordinate x_p, represented by integer bit 4-p. */
    uint8_t xf = (uint8_t)(x | (1U << (4 - fault_position)));

    uint8_t dy = (uint8_t)(S[x] ^ S[xf]);

    return (uint8_t)((bit_y(dy, i) << 1) | bit_y(dy, j));

}

static int ordered_if_key_from_x(uint8_t x, int i, int j)

{

    int key = 0;

    for (int k = 0; k < NFAULTS; k++) {

        if (response_for_x(x, k, i, j) == 0) {

            key |= 1 << k;

        }

    }

    return key;

}

static int ordered_ef_key_from_x(uint8_t x, int i, int j)

{

    int key = 0;

    for (int k = 0; k < NFAULTS; k++) {

        key |= (int)response_for_x(x, k, i, j) << (2 * k);

    }

    return key;

}

static void build_lookup(

    const Placement *p,

    int use_ordered_ef,

    LookupEntry *table,

    int table_size,

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

/*
* The selected custom tag words are:
*
*   T_i = final_state[i] XOR K0
*   T_j = final_state[j] XOR K1
*
* The linear diffusion is already included in final_state because
* ascon_finish() applies both the S-box and the linear layer.
*/

static void tag_for(

    const uint64_t state[5],

    uint64_t k0,

    uint64_t k1,

    int i,

    int j,

    uint64_t *t0,

    uint64_t *t1)

{

    *t0 = state[i] ^ k0;

    *t1 = state[j] ^ k1;

}

/*
* Reconstruct the state immediately before the final S-box and linear
* layer from the fixed ciphertext.
*
* This is the decryption-side path for full 8-byte plaintext blocks.
* For every full ciphertext block:
*   P_block = rate_state XOR C_block;
*   rate_state = C_block;
*   apply p[6].
*
* After the final full block, the empty padded final block is absorbed.
* The final key addition and first eleven finalization rounds follow.
*/

static void decrypt_last_input(

    uint64_t out[5],

    const uint8_t key[16],

    const uint8_t nonce[16],

    const uint8_t *ad,

    size_t adlen,

    const uint8_t *ct,

    size_t ctlen)

{

    uint64_t k0 = load64be(key);

    uint64_t k1 = load64be(key + 8);

    uint64_t n0 = load64be(nonce);

    uint64_t n1 = load64be(nonce + 8);

    uint64_t s[5] = {ASCON_IV128, k0, k1, n0, n1};

    if ((ctlen % 8U) != 0U || ctlen > MAX_PT_LEN) {

        fprintf(stderr, "decrypt_last_input: unsupported ciphertext length\n");

        exit(EXIT_FAILURE);

    }
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
    /* Decrypt full ciphertext blocks and restore the rate state. */

    for (size_t off = 0; off < ctlen; off += 8U) {

        uint64_t c = load64be(ct + off);

        uint64_t plaintext_block = s[0] ^ c;

        (void)plaintext_block; /* Plaintext is not needed for state recovery. */

        s[0] = c;

        ascon_perm(s, 6);

    }
    /* The final partial block is empty because ctlen is block-aligned. */

    s[0] ^= load_partial(NULL, 0);
    /* Final key addition. */

    s[1] ^= k0;

    s[2] ^= k1;
    /* First eleven rounds of finalization. */

    for (int r = 0; r < 11; r++) {

        ascon_round(s, ASCON_RC[r]);

    }
    /* Add the final round constant, but do not apply final S-box yet. */

    s[2] ^= ASCON_RC[11];

    memcpy(out, s, sizeof(s));

}

/*
* Explicit software fault hook. The hook is placed immediately before
* the final-round S-box in the decryption-side finalization path.
* It models a deterministic SET of one selected S-box input bit in
* one bitslice column. It is not a physical glitch model.
*/

typedef struct {

    int enabled;

    int column;

    int input_position;

} FaultHook;

static void apply_fault_hook(uint64_t state[5], const FaultHook *fault)

{

    if (fault != NULL && fault->enabled) {

        if (fault->column < 0 || fault->column >= 64 ||

            fault->input_position < 0 || fault->input_position >= 5) {

            fprintf(stderr, "Invalid fault-hook parameters\n");

            exit(EXIT_FAILURE);

        }

        /* State word p is S-box input coordinate x_p; x_0 is the MSB
         * in the 5-bit lookup-table integer, hence lookup bit 4-p. */
        state[fault->input_position] |= UINT64_C(1) << fault->column;

    }

}

/*
* Integrated decryption + tag verification for the custom two-word
* tag construction under test.
*
* This routine performs the normal Ascon-128 v1.2 initialization,
* associated-data absorption, ciphertext decryption, final key addition,
* and finalization. The fault is applied at the final-round S-box
* input. The routine then generates the custom tag internally and
* returns only the tag-comparison result.
*
* For this experiment, ciphertext lengths are restricted to positive
* multiples of the 8-byte rate. The final padded plaintext block is
* therefore empty, matching the encryption routine used by the test.
*/

static int ascon_decrypt_verify_custom(

    const uint8_t key[16],

    const uint8_t nonce[16],

    const uint8_t *ad,

    size_t adlen,

    const uint8_t *ct,

    size_t ctlen,

    int tag_i,

    int tag_j,

    uint64_t submitted_tag0,

    uint64_t submitted_tag1,

    const FaultHook *fault)

{

    uint64_t k0 = load64be(key);

    uint64_t k1 = load64be(key + 8);

    uint64_t n0 = load64be(nonce);

    uint64_t n1 = load64be(nonce + 8);

    uint64_t state[5] = {ASCON_IV128, k0, k1, n0, n1};

    uint8_t recovered_plaintext[MAX_PT_LEN];

    uint64_t computed_tag0, computed_tag1;

    if ((ctlen % 8U) != 0U || ctlen == 0U || ctlen > MAX_PT_LEN) {

        fprintf(stderr, "Unsupported ciphertext length in verifier\\\n");

        exit(EXIT_FAILURE);

    }
    /* Initialization and associated-data processing. */

    ascon_perm(state, 12);

    state[3] ^= k0;

    state[4] ^= k1;

    if (adlen != 0U) {

        ascon_absorb_data(state, ad, adlen);

    }

    state[4] ^= 1;
    /* Actual ciphertext decryption: recover P and restore C to state. */

    for (size_t off = 0; off < ctlen; off += 8U) {

        uint64_t c = load64be(ct + off);

        uint64_t plaintext_block = state[0] ^ c;

        store64be(recovered_plaintext + off, plaintext_block);

        state[0] = c;

        ascon_perm(state, 6);

    }
    /* Absorb the mandatory empty padded final block. */

    state[0] ^= load_partial(NULL, 0);
    /* Finalization before the last round. */

    state[1] ^= k0;

    state[2] ^= k1;

    for (int r = 0; r < 11; r++) {

        ascon_round(state, ASCON_RC[r]);

    }

    state[2] ^= ASCON_RC[11];
    /* The only fault-injection point: final-round S-box input. */

    apply_fault_hook(state, fault);

    ascon_finish(state);
    /* Normal custom-tag generation and exact verification. */

    tag_for(state, k0, k1, tag_i, tag_j,

            &computed_tag0, &computed_tag1);
    /* Keep the recovered plaintext local to the implementation. */

    (void)recovered_plaintext;

    return (computed_tag0 == submitted_tag0 &&

            computed_tag1 == submitted_tag1);

}

/* Public data handed to the attacker after one encryption. */

typedef struct {

    uint8_t nonce[16];

    uint8_t ad[MAX_AD_LEN];

    size_t adlen;

    uint8_t ct[MAX_PT_LEN];

    size_t ctlen;

    uint64_t tag0;

    uint64_t tag1;

    int tag_i;

    int tag_j;

} PublicTranscript;

/* Secret state belongs to the target, not to the attack routine. */

typedef struct {

    uint8_t key[16];

} TargetContext;

typedef int (*VerifyOracle)(

    void *target_context,

    const PublicTranscript *transcript,

    int column,

    int fault_position,

    int diff_i,

    int diff_j);

/*
* Target-side encryption interface for the selected custom tag layout.
* The target computes ciphertext and the selected tag from the same
* Ascon-128 v1.2 encryption state. The caller receives no key material.
*
* This deliberately defines a custom two-word tag layout; it is not the
* standard Ascon-128 (3,4) tag format.
*/

static void target_encrypt_custom(

    const uint8_t key[16],

    const uint8_t nonce[16],

    const uint8_t *ad,

    size_t adlen,

    const uint8_t *pt,

    size_t ptlen,

    int tag_i,

    int tag_j,

    uint8_t *ct,

    uint64_t *tag0,

    uint64_t *tag1)

{

    uint64_t k0 = load64be(key);

    uint64_t k1 = load64be(key + 8);

    uint64_t n0 = load64be(nonce);

    uint64_t n1 = load64be(nonce + 8);

    uint64_t state[5] = {ASCON_IV128, k0, k1, n0, n1};

    size_t off = 0;

    if ((ptlen % 8U) != 0U || ptlen == 0U || ptlen > MAX_PT_LEN ||

        adlen > MAX_AD_LEN || (adlen % 8U) != 0U) {

        fprintf(stderr, "Unsupported input length in custom encryption\n");

        exit(EXIT_FAILURE);

    }
    /* Initialization and associated-data processing. */

    ascon_perm(state, 12);

    state[3] ^= k0;

    state[4] ^= k1;

    if (adlen != 0U) ascon_absorb_data(state, ad, adlen);

    state[4] ^= 1;
    /* Full-block encryption; the p[6] call also follows the last block. */

    while (off < ptlen) {

        state[0] ^= load64be(pt + off);

        store64be(ct + off, state[0]);

        off += 8U;

        ascon_perm(state, 6);

    }
    /* Mandatory empty padded final plaintext block. */

    state[0] ^= load_partial(NULL, 0);
    /* Final key addition and all twelve finalization rounds. */

    state[1] ^= k0;

    state[2] ^= k1;

    ascon_perm(state, 12);
    /* The selected two-word tag is emitted by this target interface. */

    tag_for(state, k0, k1, tag_i, tag_j, tag0, tag1);

}

/*
* Target-side verification oracle. It owns the secret key and returns
* exactly one bit: whether the submitted modified tag is accepted.
*/

static int target_verify_query(

    void *opaque,

    const PublicTranscript *tr,

    int column,

    int fault_position,

    int diff_i,

    int diff_j)

{

    const TargetContext *target = (const TargetContext *)opaque;

    uint64_t submitted0 = tr->tag0;

    uint64_t submitted1 = tr->tag1;

    uint64_t basis = UINT64_C(1) << column;

    FaultHook fault = {1, column, fault_position};

    if (diff_i) submitted0 ^= apply_lin(tr->tag_i, basis);

    if (diff_j) submitted1 ^= apply_lin(tr->tag_j, basis);

    return ascon_decrypt_verify_custom(

        target->key, tr->nonce, tr->ad, tr->adlen,

        tr->ct, tr->ctlen, tr->tag_i, tr->tag_j,

        submitted0, submitted1, &fault);

}

/* A separate target-side clean verifier used only by the test harness. */

static int target_verify_clean(

    const TargetContext *target,

    const PublicTranscript *tr,

    uint64_t submitted0,

    uint64_t submitted1)

{

    FaultHook no_fault = {0, 0, 0};

    return ascon_decrypt_verify_custom(

        target->key, tr->nonce, tr->ad, tr->adlen,

        tr->ct, tr->ctlen, tr->tag_i, tr->tag_j,

        submitted0, submitted1, &no_fault);

}

/*
* Decode the three verification outcomes for one fault location:
*   query (0,1) accepted -> response 01
*   query (1,0) accepted -> response 10
*   query (1,1) accepted -> response 11
*   no query accepted    -> response 00
* Multiple acceptances are inconsistent with this deterministic model.
*/

static int query_signature_to_response(int query_signature)

{

    switch (query_signature) {

    case 0: return 0;

    case 1: return 1;

    case 2: return 2;

    case 4: return 3;

    default: return -1;

    }

}

/*
* Attacker-side recovery. Notice that this function has no key argument
* and does not access target internals: it receives only the public
* transcript and an oracle returning accept/reject.
*/

static int attack_recover(

    const Placement *p,

    const LookupEntry *if_table,

    int if_table_size,

    const LookupEntry *ef_table,

    int ef_table_size,

    const PublicTranscript *tr,

    VerifyOracle oracle,

    void *oracle_context,

    uint64_t *if_k0_out,

    uint64_t *if_k1_out,

    uint64_t *ef_k0_out,

    uint64_t *ef_k1_out,

    int *queries_out,

    int *bad_if_out,

    int *bad_ef_out)

{

    uint64_t if_invk0 = 0, if_invk1 = 0;

    uint64_t ef_invk0 = 0, ef_invk1 = 0;

    int queries = 0, bad_if = 0, bad_ef = 0;

    static const int query_diffs[NFORGERIES][2] = {

        {0, 1}, {1, 0}, {1, 1}

    };

    for (int col = 0; col < NCOLS; col++) {

        int if_key = 0, ef_key = 0;

        for (int fault_position = 0; fault_position < NFAULTS;

             fault_position++) {

            int query_signature = 0;

            for (int q = 0; q < NFORGERIES; q++) {

                int accepted = oracle(

                    oracle_context, tr, col, fault_position,

                    query_diffs[q][0], query_diffs[q][1]);

                if (accepted) query_signature |= 1 << q;

                queries++;

            }

            int response = query_signature_to_response(query_signature);

            if (response < 0) {

                bad_if++;

                bad_ef++;

                continue;

            }

            if (response == 0) if_key |= 1 << fault_position;

            ef_key |= response << (2 * fault_position);

        }
       /* L_i^{-1}(T_i) = S_i(x) XOR L_i^{-1}(K0), and likewise for j. */

        uint64_t u0 = apply_inv(p->i, tr->tag0);

        uint64_t u1 = apply_inv(p->j, tr->tag1);

        if (if_key < 0 || if_key >= if_table_size || !if_table[if_key].valid) {

            bad_if++;

        } else {

            uint64_t yi = if_table[if_key].yi;

            uint64_t yj = if_table[if_key].yj;

            if_invk0 |= ((((u0 >> col) & 1U) ^ yi) << col);

            if_invk1 |= ((((u1 >> col) & 1U) ^ yj) << col);

        }

        if (ef_key < 0 || ef_key >= ef_table_size || !ef_table[ef_key].valid) {

            bad_ef++;

        } else {

            uint64_t yi = ef_table[ef_key].yi;

            uint64_t yj = ef_table[ef_key].yj;

            ef_invk0 |= ((((u0 >> col) & 1U) ^ yi) << col);

            ef_invk1 |= ((((u1 >> col) & 1U) ^ yj) << col);

        }

    }

    *if_k0_out = apply_lin(p->i, if_invk0);

    *if_k1_out = apply_lin(p->j, if_invk1);

    *ef_k0_out = apply_lin(p->i, ef_invk0);

    *ef_k1_out = apply_lin(p->j, ef_invk1);

    *queries_out = queries;

    *bad_if_out = bad_if;

    *bad_ef_out = bad_ef;

    return (bad_if == 0 && bad_ef == 0);

}

/*
* Test harness: creates a target key and public transcript, invokes the
* attacker with no key parameter, then compares recovered values with
* the target key only after attack_recover() has returned.
*/

static void recover_one(

    const Placement *p,

    const LookupEntry *if_table,

    int if_table_size,

    const LookupEntry *ef_table,

    int ef_table_size,

    int *if_success,

    int *ef_success,

    int verbose)

{

    uint8_t pt[MAX_PT_LEN] = {0};

    PublicTranscript tr;

    TargetContext target;

    uint64_t if_k0, if_k1, ef_k0, ef_k1;

    int queries, bad_if, bad_ef;

    memset(&tr, 0, sizeof(tr));

    random_bytes(target.key, sizeof(target.key));

    random_input(tr.nonce, tr.ad, &tr.adlen, pt, &tr.ctlen);

    tr.tag_i = p->i;

    tr.tag_j = p->j;
    /* The encryption target returns only C and the selected custom tag. */

    target_encrypt_custom(target.key, tr.nonce, tr.ad, tr.adlen,

                          pt, tr.ctlen, tr.tag_i, tr.tag_j,

                          tr.ct, &tr.tag0, &tr.tag1);
    /* The custom target must produce the same ciphertext as Ascon-128 v1.2. */

    {

        uint8_t reference_ct[MAX_PT_LEN] = {0};

        uint8_t reference_tag[16];

        ascon_encrypt(reference_ct, reference_tag, target.key, tr.nonce,

                      tr.ad, tr.adlen, pt, tr.ctlen);

        if (memcmp(reference_ct, tr.ct, tr.ctlen) != 0) {

            fprintf(stderr, "ERROR: custom encryption ciphertext differs from Ascon reference\n");

            *if_success = *ef_success = 0;

            return;

        }

    }
    /* Check the decryption-side state against the encryption-side state. */

    {

        uint64_t dec_state[5], enc_state[5], k0, k1;

        decrypt_last_input(dec_state, target.key, tr.nonce, tr.ad,

                           tr.adlen, tr.ct, tr.ctlen);

        ascon_last_input(enc_state, &k0, &k1, target.key, tr.nonce,

                         tr.ad, tr.adlen, pt, tr.ctlen);

        if (memcmp(enc_state, dec_state, sizeof(enc_state)) != 0) {

            fprintf(stderr, "ERROR: encryption/decryption pre-final state mismatch\n");

            *if_success = *ef_success = 0;

            return;

        }

    }

    if (!target_verify_clean(&target, &tr, tr.tag0, tr.tag1) ||

        target_verify_clean(&target, &tr, tr.tag0 ^ UINT64_C(1), tr.tag1)) {

        fprintf(stderr, "ERROR: clean-tag/wrong-tag verifier self-test failed\n");

        *if_success = *ef_success = 0;

        return;

    }
    /* Attacker gets tr and oracle only. Secret key is not an argument. */

    (void)attack_recover(p, if_table, if_table_size, ef_table,

                         ef_table_size, &tr, target_verify_query, &target,

                         &if_k0, &if_k1, &ef_k0, &ef_k1,

                         &queries, &bad_if, &bad_ef);
    /* The harness performs the only comparison against the true key. */

    uint64_t true_k0 = load64be(target.key);

    uint64_t true_k1 = load64be(target.key + 8);

    *if_success = (bad_if == 0 && if_k0 == true_k0 && if_k1 == true_k1);

    *ef_success = (bad_ef == 0 && ef_k0 == true_k0 && ef_k1 == true_k1);

    if (verbose) {

        printf("  Clean-tag acceptance and wrong-tag rejection: PASS\n");

        printf("  Modified-tag verification queries: %d (3 x 5 x 64)\n", queries);

        printf("  Ordered IF recovered K0: %016" PRIx64 "\n", if_k0);

        printf("  Ordered IF recovered K1: %016" PRIx64 "\n", if_k1);

        printf("  Ordered IF key recovery: %s (unmapped=%d)\n",

               *if_success ? "SUCCESS" : "FAILURE", bad_if);

        printf("  Ordered EF recovered K0: %016" PRIx64 "\n", ef_k0);

        printf("  Ordered EF recovered K1: %016" PRIx64 "\n", ef_k1);

        printf("  Ordered EF key recovery: %s (unmapped=%d)\n",

               *ef_success ? "SUCCESS" : "FAILURE", bad_ef);

        printf("  Actual key K0/K1 (harness only): %016" PRIx64 " %016" PRIx64 "\n",

               true_k0, true_k1);

    }

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

    printf("Ordered IF lookup conflicts: %d\n", if_conflicts);

    printf("Ordered EF lookup conflicts: %d\n", ef_conflicts);

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

        int one_if_success = 0;

        int one_ef_success = 0;

        recover_one(

            p,

            if_table, MAX_SIG_IF,

            ef_table, MAX_SIG_EF,

            &one_if_success,

            &one_ef_success,

            tr == 0

        );

        if_success += one_if_success;

        ef_success += one_ef_success;

    }

    printf("\nSummary over %d independent keys/inputs:\n", trials);

    printf("  Ordered IF: %d/%d complete 128-bit keys recovered\n",

           if_success, trials);

    printf("  Ordered EF: %d/%d complete 128-bit keys recovered\n",

           ef_success, trials);

    printf("  Modified-tag decryption queries per transcript: %d\n",

           NFORGERIES * NFAULTS * NCOLS);

}


static int check_sbox_truth_table(void)
{
    for (unsigned x = 0; x < 32; x++) {
        uint64_t state[5] = {0, 0, 0, 0, 0};
        for (int p = 0; p < 5; p++) {
            state[p] = (uint64_t)((x >> (4 - p)) & 1U);
        }
        ascon_sbox(state);
        uint8_t y = 0;
        for (int p = 0; p < 5; p++) {
            y |= (uint8_t)((state[p] & 1U) << (4 - p));
        }
        if (y != S[x]) {
            fprintf(stderr, "S-box truth-table mismatch at input %u\n", x);
            return 0;
        }
    }
    return 1;
}

static int check_linear_inverses(void)
{
    for (int reg = 0; reg < 5; reg++) {
        for (int bit = 0; bit < 64; bit++) {
            uint64_t basis = UINT64_C(1) << bit;
            if (apply_inv(reg, apply_lin(reg, basis)) != basis) {
                fprintf(stderr,
                        "Linear inverse mismatch: word %d, bit %d\n",
                        reg, bit);
                return 0;
            }
        }
    }
    return 1;
}

static int hex_to_bytes(const char *hex, uint8_t *out, size_t out_len)
{
    for (size_t i = 0; i < out_len; i++) {
        unsigned value;
        if (sscanf(hex + 2 * i, "%2x", &value) != 1) {
            return 0;
        }
        out[i] = (uint8_t)value;
    }
    return hex[2 * out_len] == '\0';
}

static int check_standard_ascon_kats(void)
{
    uint8_t key[16], nonce[16], pt[16], ad[8];
    uint8_t ct[16], tag[16], expected[32], got[32];

    if (!hex_to_bytes("000102030405060708090a0b0c0d0e0f", key, 16)) {
        return 0;
    }
    memcpy(nonce, key, sizeof(nonce));

    /* Ascon-128 v1.2 KAT: empty plaintext and empty associated data. */
    ascon_encrypt(ct, tag, key, nonce, NULL, 0, NULL, 0);
    if (!hex_to_bytes("e355159f292911f794cb1432a0103a8a", expected, 16) ||
        memcmp(tag, expected, 16) != 0) {
        fprintf(stderr, "Ascon-128 v1.2 empty-message KAT failed\n");
        return 0;
    }

    /* Ascon-128 v1.2 KAT: 8-byte plaintext, empty associated data. */
    if (!hex_to_bytes("0001020304050607", pt, 8) ||
        !hex_to_bytes("bc820dbdf7a4631c01a8807a44254b42ac6bb490da1e000a",
                      expected, 24)) {
        return 0;
    }
    ascon_encrypt(ct, tag, key, nonce, NULL, 0, pt, 8);
    memcpy(got, ct, 8);
    memcpy(got + 8, tag, 16);
    if (memcmp(got, expected, 24) != 0) {
        fprintf(stderr, "Ascon-128 v1.2 8-byte-message KAT failed\n");
        return 0;
    }

    /* Ascon-128 v1.2 KAT: 16-byte plaintext and 8-byte associated data. */
    if (!hex_to_bytes("0001020304050607", ad, 8) ||
        !hex_to_bytes("000102030405060708090a0b0c0d0e0f", pt, 16) ||
        !hex_to_bytes("69ffee6f5505a4897e2ec80cbdff67ce"
                      "31614dac97643c45940a8f9e7964613a",
                      expected, 32)) {
        return 0;
    }
    ascon_encrypt(ct, tag, key, nonce, ad, 8, pt, 16);
    memcpy(got, ct, 16);
    memcpy(got + 16, tag, 16);
    if (memcmp(got, expected, 32) != 0) {
        fprintf(stderr, "Ascon-128 v1.2 16-byte-message KAT failed\n");
        return 0;
    }

    return 1;
}

int main(int argc, char **argv)

{

    int trials = 20;

    if (argc > 1) {

        char *end = NULL;

        long value = strtol(argv[1], &end, 10);

        if (end == argv[1] || *end != '\0' ||

            value < 1 || value > 100000) {

            fprintf(stderr, "Usage: %s [number-of-trials]\n", argv[0]);

            return EXIT_FAILURE;

        }

        trials = (int)value;

    }

    for (int r = 0; r < 5; r++) {

        make_inverse(r);

    }

    if (!check_sbox_truth_table() || !check_linear_inverses() ||
        !check_standard_ascon_kats()) {
        fprintf(stderr, "Primitive/KAT self-test failed; aborting attack tests.\n");
        return EXIT_FAILURE;
    }
    printf("Primitive checks: S-box truth table, five inverse linear maps, and 3 Ascon-128 v1.2 KATs PASS\n");

    printf("Category 2 software fault-injection: Ascon-128 v1.2 custom-tag verification\n");

    printf("Fault sequence: SET(0), SET(1), SET(2), SET(3), SET(4)\n");

    printf("S-box coordinate convention: y4 is MSB, y0 is LSB\n");

    printf("Trials: %d\n", trials);

    printf("Model: integrated decrypt/verify target; SET faults at final-round S-box\n");

    printf("Three modified-tag queries per fault position and S-box column\n");

    printf("Modified tag differences: (0,1), (1,0), (1,1); original (0,0) omitted\n");

    for (size_t p = 0; p < NPLACEMENTS; p++) {

        run_placement(&placements[p], trials);

    }

    return EXIT_SUCCESS;

}