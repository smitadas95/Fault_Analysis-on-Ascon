#include <stdio.h>
#include <stdint.h>

#define NINPUTS 32
#define NFAULTS 5
#define MAX_CLASSES 32

/* Ascon 5-bit S-box. */
static const uint8_t S[32] = {
    0x04, 0x0B, 0x1F, 0x14, 0x1A, 0x15, 0x09, 0x02,
    0x1B, 0x05, 0x08, 0x12, 0x1D, 0x03, 0x06, 0x1C,
    0x1E, 0x13, 0x07, 0x0E, 0x00, 0x0D, 0x11, 0x18,
    0x10, 0x0C, 0x01, 0x19, 0x16, 0x0A, 0x0F, 0x17
};

typedef struct {
    int i, j;
    const char *name;
} Placement;

static const Placement placements[3] = {
    {4, 3, "(4,3)"},
    {4, 0, "(4,0)"},
    {3, 2, "(3,2)"}
};

typedef struct {
    int ef_key;       /* Multiset EF: counts of 01, 10, and 11. */
    int if_key;       /* Ordered IF: bit k is 1 iff d_k == 00. */
    int pair_key;     /* Partial EF+IF: (ef_key, if_key). */
    int ordered_key;  /* Ordered EF: complete (d_0,...,d_4). */
    uint8_t response[NFAULTS];
} InputSignature;

typedef struct {
    int key;
    int members[NINPUTS];
    int size;
} EquivClass;

/* Coordinate convention: y_4 is MSB and y_0 is LSB. */
static int bit_y(uint8_t y, int coordinate)
{
    return (y >> (4 - coordinate)) & 1;
}

/* Apply SET(k): force input bit k to one. */
static uint8_t set_fault(uint8_t x, int k)
{
    return (uint8_t)(x | (1u << k));
}

/*
 * Return the two observed output-difference bits.
 * Encoding: 00 -> 0, 01 -> 1, 10 -> 2, 11 -> 3.
 * The first response coordinate is the high bit.
 */
static uint8_t observed_difference(uint8_t x, int k, int i, int j)
{
    uint8_t xf = set_fault(x, k);
    uint8_t dy = S[x] ^ S[xf];
    int di = bit_y(dy, i);
    int dj = bit_y(dy, j);
    return (uint8_t)((di << 1) | dj);
}

/* Construct all four signature representations. */
static void make_signature(uint8_t x, int i, int j, InputSignature *sig)
{
    int count[4] = {0, 0, 0, 0};
    int if_key = 0;
    int ordered_key = 0;

    for (int k = 0; k < NFAULTS; k++) {
        uint8_t d = observed_difference(x, k, i, j);

        sig->response[k] = d;
        count[d]++;

        if (d == 0)
            if_key |= (1 << k);

        /* Two bits per response preserve both value and fault position. */
        ordered_key |= ((int)d << (2 * k));
    }

    /* Multiset EF: zero responses are discarded; multiplicities remain. */
    sig->ef_key = count[1] + 6 * count[2] + 36 * count[3];

    /* Ordered IF: retain only the zero/nonzero pattern. */
    sig->if_key = if_key;

    /* Partial EF+IF: multiset EF together with ordered IF. */
    sig->pair_key = sig->ef_key * 32 + sig->if_key;

    /* Ordered EF: retain the complete ordered response vector, including 00. */
    sig->ordered_key = ordered_key;
}

static int find_or_add_class(EquivClass classes[], int *nclasses, int key)
{
    for (int c = 0; c < *nclasses; c++) {
        if (classes[c].key == key)
            return c;
    }

    int c = (*nclasses)++;
    classes[c].key = key;
    classes[c].size = 0;
    return c;
}

/*
 * mode:
 *   0 = multiset EF
 *   1 = ordered IF
 *   2 = partial EF+IF
 *   3 = ordered EF
 */
static void build_classes(const InputSignature sigs[NINPUTS],
                          int mode,
                          EquivClass classes[],
                          int *nclasses,
                          int class_of_input[NINPUTS])
{
    *nclasses = 0;

    for (int x = 0; x < NINPUTS; x++) {
        int key;

        if (mode == 0)
            key = sigs[x].ef_key;
        else if (mode == 1)
            key = sigs[x].if_key;
        else if (mode == 2)
            key = sigs[x].pair_key;
        else
            key = sigs[x].ordered_key;

        int c = find_or_add_class(classes, nclasses, key);
        classes[c].members[classes[c].size++] = x;
        class_of_input[x] = c;
    }
}

/* Check whether an output XOR mask is constant in every signature class. */
static int mask_is_recoverable(const EquivClass classes[],
                               int nclasses,
                               int mask)
{
    for (int c = 0; c < nclasses; c++) {
        int first_value = -1;

        for (int t = 0; t < classes[c].size; t++) {
            int x = classes[c].members[t];
            uint8_t y = S[x];
            int value = 0;

            for (int b = 0; b < 5; b++) {
                if ((mask >> b) & 1)
                    value ^= bit_y(y, b);
            }

            if (first_value < 0)
                first_value = value;
            else if (value != first_value)
                return 0;
        }
    }

    return 1;
}

/* Determine all recoverable masks and an independent GF(2) basis. */
static int get_mask_basis(const EquivClass classes[],
                          int nclasses,
                          int recoverable[32],
                          int basis[5])
{
    int pivots[5] = {0};
    int rank = 0;

    recoverable[0] = 1;
    for (int m = 1; m < 32; m++)
        recoverable[m] = mask_is_recoverable(classes, nclasses, m);

    /* Gaussian elimination over GF(2). */
    for (int m = 1; m < 32; m++) {
        if (!recoverable[m])
            continue;

        int v = m;
        for (int b = 4; b >= 0; b--) {
            if (!((v >> b) & 1))
                continue;

            if (pivots[b]) {
                v ^= pivots[b];
            } else {
                pivots[b] = v;
                basis[rank++] = v;
                break;
            }
        }
    }

    return rank;
}

static void print_mask(int mask)
{
    int first = 1;
    for (int b = 4; b >= 0; b--) {
        if ((mask >> b) & 1) {
            if (!first)
                printf(" XOR ");
            printf("y_%d", b);
            first = 0;
        }
    }
    if (first)
        printf("0");
}

static void print_ef_signature(int key)
{
    int c01 = key % 6;
    int c10 = (key / 6) % 6;
    int c11 = (key / 36) % 6;
    printf("{01:%d, 10:%d, 11:%d}", c01, c10, c11);
}

static void print_response_vector(const InputSignature *sig)
{
    printf("[");
    for (int k = 0; k < NFAULTS; k++) {
        int d = sig->response[k];
        printf("%s%d%d", k ? ", " : "", (d >> 1) & 1, d & 1);
    }
    printf("]");
}

static const char *mode_name(int mode)
{
    if (mode == 0) return "DFA-EF (multiset)";
    if (mode == 1) return "DFA-IF (ordered zero/nonzero pattern)";
    if (mode == 2) return "DFA-EF+IF (partial signature)";
    return "DFA-EF (ordered response vector)";
}

static void print_mode_signature(const InputSignature *sig, int mode)
{
    if (mode == 0) {
        print_ef_signature(sig->ef_key);
    } else if (mode == 1) {
        printf("IF=0x%02X", sig->if_key);
    } else if (mode == 2) {
        print_ef_signature(sig->ef_key);
        printf(" + IF=0x%02X", sig->if_key);
    } else {
        print_response_vector(sig);
    }
}

static void analyze_placement(const Placement *p)
{
    InputSignature sigs[NINPUTS];

    printf("\n============================================\n");
    printf("Tag placement %s\n", p->name);
    printf("Faults: SET(0), SET(1), SET(2), SET(3), SET(4)\n");
    printf("============================================\n");

    /* Generate the five-fault response vector for every S-box input. */
    for (int x = 0; x < NINPUTS; x++)
        make_signature((uint8_t)x, p->i, p->j, &sigs[x]);

    /* Analyze all four observation models independently. */
    for (int mode = 0; mode < 4; mode++) {
        EquivClass classes[MAX_CLASSES];
        int nclasses = 0;
        int class_of_input[NINPUTS];
        int recoverable[32] = {0};
        int basis[5] = {0};

        build_classes(sigs, mode, classes, &nclasses, class_of_input);
        int rank = get_mask_basis(classes, nclasses, recoverable, basis);

        printf("\n--------------------------------------------\n");
        printf("%s\n", mode_name(mode));
        printf("--------------------------------------------\n");
        printf("Number of equivalence classes: %d\n", nclasses);

        printf("\nAll recoverable XOR masks:\n");
        int first = 1;
        for (int m = 1; m < 32; m++) {
            if (recoverable[m]) {
                if (!first)
                    printf(", ");
                print_mask(m);
                first = 0;
            }
        }
        if (first)
            printf("None");
        printf("\n");

        printf("Leakage rank: %d\n", rank);
        printf("Independent leakage basis: ");
        if (rank == 0)
            printf("None");
        for (int b = 0; b < rank; b++) {
            if (b)
                printf("; ");
            print_mask(basis[b]);
        }
        printf("\n");

        printf("\nSignature-equivalence classes:\n");
        for (int c = 0; c < nclasses; c++) {
            printf("C%02d: ", c);
            for (int t = 0; t < classes[c].size; t++)
                printf("%s%d", t ? ", " : "", classes[c].members[t]);
            printf("\n");
        }

        printf("\nInput-to-signature table:\n");
        printf(" x   S(x)   Class   Signature\n");
        for (int x = 0; x < NINPUTS; x++) {
            printf("%2d   %02X     C%02d     ",
                   x, S[x], class_of_input[x]);
            print_mode_signature(&sigs[x], mode);
            printf("\n");
        }

        /* Always print the full vector as an audit trail. */
        printf("\nOrdered five-fault responses (audit):\n");
        for (int x = 0; x < NINPUTS; x++) {
            printf("x=%2d: ", x);
            print_response_vector(&sigs[x]);
            printf("\n");
        }
    }
}

int main(void)
{
    printf("Ascon SET-fault DFA leakage analysis\n");
    printf("====================================\n");
    printf("S-box inputs: 0,...,31\n");
    printf("Number of faults: 5\n");
    printf("Fault order: SET(0), SET(1), SET(2), SET(3), SET(4)\n");
    printf("Coordinate convention: y_4 is MSB; y_0 is LSB\n");

    printf("\nSignature definitions:\n");
    printf("EF multiset = counts of nonzero two-bit responses\n");
    printf("IF ordered  = five-bit zero/nonzero response pattern\n");
    printf("EF+IF       = EF multiset together with ordered IF\n");
    printf("EF ordered  = complete ordered vector (d_0,...,d_4)\n");

    for (int p = 0; p < 3; p++)
        analyze_placement(&placements[p]);

    return 0;
}
