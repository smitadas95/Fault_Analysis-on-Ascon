/*
 * combined_analysis.c
 *
 * Exhaustive leakage analysis for Ascon's 5-bit S-box.
 *
 * Section 2.B:
 *   Differential leakage from five input-bit-flip faults.
 *
 * Section 2.C:
 *   Symmetry-derived XOR leakage from ineffective SET/RESET faults.
 *   Combination of both leakage sources using GF(2) rank.
 *
 * The program analyzes all ten two-bit tag-position choices.
 *
 * Compile:
 *   gcc combined_analysis.c -o combined_analysis
 *
 * Run:
 *   ./combined_analysis
 */

#include <stdio.h>
#include <stdint.h>
#include <stdlib.h>
#include <string.h>
#include <math.h>
#include <inttypes.h>

#define N_INPUTS 32
#define N_FAULTS 5
#define N_PAIRS 10

/* Ascon 5-bit S-box. */
static const uint8_t S[32] = {
    4, 11, 31, 20, 26, 21, 9, 2,
    27, 5, 8, 18, 29, 3, 6, 28,
    30, 19, 7, 14, 0, 13, 17, 24,
    16, 12, 1, 25, 22, 10, 15, 23
};

/* All ten tag-position choices. */
static const int pairs[N_PAIRS][2] = {
    {4,3}, {4,2}, {4,1}, {4,0}, {3,2},
    {3,1}, {3,0}, {2,1}, {2,0}, {1,0}
};

/* Five input-bit-flip fault masks. */
static const int flip_bits[5] = {
    1, 2, 4, 8, 16
};

/* Fault types. */
enum {
    FAULT_FLIP = 0,
    FAULT_SET  = 1,
    FAULT_RST  = 2
};

typedef struct {
    int pair_i;
    int pair_j;

    /* Differential leakage, represented in global S-box bits. */
    int diff_masks[32];
    int ndiff;

    /* Best ineffective-fault configuration. */
    int best_type;
    int best_input_bit;
    int best_n;
    int best_counts[4];
    double best_imbalance;

    /* IF leakage masks in local pair coordinates:
       bit 1 = kappa_i, bit 0 = kappa_j. */
    int if_masks[4];
    int nif;

    /* Translation symmetries in local pair coordinates. */
    int symmetries[4];
    int nsym;

    int combined_rank;
} PairResult;


/* --------------------------------------------------------- */
/* Basic bit operations                                      */
/* --------------------------------------------------------- */

static int rbit(int i)
{
    return 1 << (4 - i);
}

static int parity5(int x)
{
    return __builtin_parity((unsigned)x);
}

static int apply_fault(int type, int bit, int x)
{
    if (type == FAULT_FLIP)
        return x ^ bit;

    if (type == FAULT_SET)
        return x | bit;

    return x & (31 ^ bit);
}

static int tag_mask(int i, int j)
{
    return rbit(i) | rbit(j);
}


/* --------------------------------------------------------- */
/* Differential signature analysis                           */
/* --------------------------------------------------------- */

/*
 * Construct equivalence classes induced by the five
 * input-bit-flip fault signatures.
 *
 * Two inputs belong to the same class if all five observed
 * output differences on the selected tag bits agree.
 */
static int make_flip_classes(
    int output_mask,
    int group_of[32],
    int representatives[32],
    int class_sizes[32]
)
{
    int ng = 0;

    memset(class_sizes, 0, 32 * sizeof(int));

    for (int x = 0; x < 32; x++) {

        int signature[5];

        for (int q = 0; q < 5; q++) {
            int xx = apply_fault(
                FAULT_FLIP,
                flip_bits[q],
                x
            );

            signature[q] =
                (S[x] ^ S[xx]) & output_mask;
        }

        int g;

        for (g = 0; g < ng; g++) {

            int y = representatives[g];
            int same = 1;

            for (int q = 0; q < 5; q++) {

                int yy = apply_fault(
                    FAULT_FLIP,
                    flip_bits[q],
                    y
                );

                int candidate =
                    (S[y] ^ S[yy]) & output_mask;

                if (candidate != signature[q]) {
                    same = 0;
                    break;
                }
            }

            if (same)
                break;
        }

        if (g == ng) {
            representatives[ng] = x;
            ng++;
        }

        group_of[x] = g;
        class_sizes[g]++;
    }

    return ng;
}


/*
 * A mask l is differentially leaked if parity(S[x] & l)
 * is constant within every differential signature class.
 *
 * The constants may differ between classes.
 */
static void differential_analysis(
    int i,
    int j,
    PairResult *result
)
{
    int m = tag_mask(i, j);

    int group_of[32];
    int representatives[32];
    int class_sizes[32];

    int ng = make_flip_classes(
        m,
        group_of,
        representatives,
        class_sizes
    );

    result->ndiff = 0;

    for (int l = 1; l < 32; l++) {

        /* Only consider masks observable through this pair. */
        if ((l & m) != l)
            continue;

        int leaked = 1;

        for (int g = 0; g < ng && leaked; g++) {

            int first = representatives[g];
            int reference = parity5(S[first] & l);

            for (int x = 0; x < 32; x++) {

                if (group_of[x] != g)
                    continue;

                if (parity5(S[x] & l) != reference) {
                    leaked = 0;
                    break;
                }
            }
        }

        if (leaked) {
            result->diff_masks[result->ndiff++] = l;
        }
    }
}


/* --------------------------------------------------------- */
/* Ineffective-fault statistical analysis                    */
/* --------------------------------------------------------- */

/*
 * Collect inputs for which a SET/RESET fault is ineffective:
 *
 *     S[act(x)] restricted to the tag pair
 *       =
 *     S[x] restricted to the tag pair.
 *
 * The four bins correspond to:
 *
 *     00, 01, 10, 11
 *
 * The first coordinate is tag bit i.
 * The second coordinate is tag bit j.
 */
static int ineffective_distribution(
    int i,
    int j,
    int type,
    int input_bit,
    int counts[4]
)
{
    int m = tag_mask(i, j);
    int n = 0;

    memset(counts, 0, 4 * sizeof(int));

    for (int x = 0; x < 32; x++) {

        int xx = apply_fault(type, input_bit, x);

        if ((S[xx] & m) != (S[x] & m))
            continue;

        int v = S[x];

        int first =
            (v & rbit(i)) ? 1 : 0;

        int second =
            (v & rbit(j)) ? 1 : 0;

        int index = (first << 1) | second;

        counts[index]++;
        n++;
    }

    return n;
}


/*
 * Squared distance from the uniform distribution.
 *
 * A larger value indicates a stronger departure from
 * uniformity. This matches the selection criterion in
 * the original tables.c implementation.
 */
static double distribution_imbalance(
    const int counts[4],
    int n
)
{
    if (n == 0)
        return 0.0;

    double q = 0.0;

    for (int v = 0; v < 4; v++) {

        double p = (double)counts[v] / (double)n;
        double d = p - 0.25;

        q += d * d;
    }

    return q;
}


/*
 * Walsh coefficient for parity mask a:
 *
 *     W[a] = sum_v (-1)^(a.v) count[v].
 *
 * A nonzero coefficient means that the distribution has
 * a bias for the corresponding XOR parity.
 *
 * This is the relation that can be recovered statistically
 * from translated observations u = y XOR kappa.
 */
static int walsh_coefficient(
    const int counts[4],
    int a
)
{
    int w = 0;

    for (int v = 0; v < 4; v++) {

        if (parity5(a & v))
            w -= counts[v];
        else
            w += counts[v];
    }

    return w;
}


/*
 * Identify all nonzero statistically biased parity masks.
 *
 * Local coordinates:
 *     10 -> kappa_i
 *     01 -> kappa_j
 *     11 -> kappa_i XOR kappa_j
 */
static void find_if_masks(
    const int counts[4],
    int n,
    PairResult *result
)
{
    result->nif = 0;

    if (n == 0)
        return;

    for (int a = 1; a <= 3; a++) {

        int w = walsh_coefficient(counts, a);

        if (w != 0) {
            result->if_masks[result->nif++] = a;
        }
    }
}


/*
 * Check all translation symmetries:
 *
 *     P(v) = P(v XOR d).
 *
 * The equality is tested using integer counts, so no
 * floating-point tolerance is required.
 */
static void find_symmetries(
    const int counts[4],
    PairResult *result
)
{
    result->nsym = 0;

    for (int d = 1; d <= 3; d++) {

        int symmetric = 1;

        for (int v = 0; v < 4; v++) {

            if (counts[v] != counts[v ^ d]) {
                symmetric = 0;
                break;
            }
        }

        if (symmetric) {
            result->symmetries[result->nsym++] = d;
        }
    }
}


/*
 * Exhaustively evaluate all ten SET/RESET configurations:
 *
 *     SET input bit 0,...,4
 *     RESET input bit 0,...,4
 *
 * Select the configuration with maximum imbalance.
 *
 * Ties are resolved by enumeration order:
 * SET before RESET, then input bits 0,...,4.
 */
static void ineffective_analysis(
    int i,
    int j,
    PairResult *result
)
{
    double best_score = -1.0;

    int best_type = FAULT_SET;
    int best_bit = 0;
    int best_n = 0;
    int best_counts[4] = {0, 0, 0, 0};

    for (int type = FAULT_SET;
         type <= FAULT_RST;
         type++) {

        for (int r = 0; r < 5; r++) {

            int bit = rbit(r);
            int counts[4];

            int n = ineffective_distribution(
                i,
                j,
                type,
                bit,
                counts
            );

            double score =
                distribution_imbalance(counts, n);

            if (score > best_score) {

                best_score = score;
                best_type = type;
                best_bit = bit;
                best_n = n;

                memcpy(
                    best_counts,
                    counts,
                    sizeof(best_counts)
                );
            }
        }
    }

    result->best_type = best_type;
    result->best_input_bit = best_bit;
    result->best_n = best_n;
    result->best_imbalance = best_score;

    memcpy(
        result->best_counts,
        best_counts,
        sizeof(best_counts)
    );

    find_if_masks(
        best_counts,
        best_n,
        result
    );

    find_symmetries(
        best_counts,
        result
    );
}


/* --------------------------------------------------------- */
/* GF(2) combination                                         */
/* --------------------------------------------------------- */

/*
 * Rank of two-bit vectors over GF(2).
 *
 * Vectors are represented by integers:
 *     10, 01, 11.
 */
static int gf2_rank(
    const int *rows,
    int nrows
)
{
    int basis[2] = {0, 0};
    int rank = 0;

    for (int z = 0; z < nrows; z++) {

        int x = rows[z];

        for (int bit = 1; bit >= 0; bit--) {

            int pivot = 1 << bit;

            if (!(x & pivot))
                continue;

            if (basis[bit]) {
                x ^= basis[bit];
            } else {
                basis[bit] = x;
                rank++;
                break;
            }
        }
    }

    return rank;
}


/*
 * Convert a global differential mask into local pair
 * coordinates.
 *
 * For pair (i,j):
 *     global bit i -> local bit 1
 *     global bit j -> local bit 0
 */
static int global_to_local(
    int global_mask,
    int i,
    int j
)
{
    int local = 0;

    if (global_mask & rbit(i))
        local |= 2;

    if (global_mask & rbit(j))
        local |= 1;

    return local;
}


static void calculate_combined_rank(
    int i,
    int j,
    PairResult *result
)
{
    int rows[40];
    int nrows = 0;

    for (int z = 0; z < result->ndiff; z++) {

        rows[nrows++] = global_to_local(
            result->diff_masks[z],
            i,
            j
        );
    }

    for (int z = 0; z < result->nif; z++) {
        rows[nrows++] = result->if_masks[z];
    }

    result->combined_rank = gf2_rank(rows, nrows);
}


/* --------------------------------------------------------- */
/* Printing helpers                                          */
/* --------------------------------------------------------- */

static void print_y_mask(int mask)
{
    int first = 1;

    for (int b = 4; b >= 0; b--) {

        if (!(mask & rbit(b)))
            continue;

        if (!first)
            printf("\\oplus");

        printf("y_%d", b);
        first = 0;
    }
}


static void print_kappa_mask(
    int mask,
    int i,
    int j
)
{
    int first = 1;

    if (mask & 2) {
        printf("\\kappa_%d", i);
        first = 0;
    }

    if (mask & 1) {

        if (!first)
            printf("\\oplus");

        printf("\\kappa_%d", j);
    }
}


static void print_differential_masks(
    const PairResult *result
)
{
    if (result->ndiff == 0) {
        printf("None");
        return;
    }

    for (int z = 0; z < result->ndiff; z++) {

        if (z)
            printf(", ");

        print_y_mask(result->diff_masks[z]);
    }
}


static void print_if_masks(
    const PairResult *result,
    int i,
    int j
)
{
    if (result->nif == 0) {
        printf("None");
        return;
    }

    for (int z = 0; z < result->nif; z++) {

        if (z)
            printf(", ");

        print_kappa_mask(
            result->if_masks[z],
            i,
            j
        );
    }
}


static void print_local_mask(
    int mask,
    int i,
    int j
)
{
    if (mask == 0) {
        printf("0");
        return;
    }

    print_kappa_mask(mask, i, j);
}


/* --------------------------------------------------------- */
/* Detailed output                                           */
/* --------------------------------------------------------- */

static const char *fault_name(int type)
{
    return type == FAULT_SET ? "SET" : "RESET";
}


static void print_pair_details(
    int i,
    int j,
    const PairResult *r
)
{
    printf("\n==================================================\n");
    printf("Tag pair (%d,%d)\n", i, j);
    printf("==================================================\n");

    printf("\n[B] Differential signature analysis\n");

    printf("Differentially leaked masks: ");
    print_differential_masks(r);
    printf("\n");

    printf("\n[B] Ineffective-fault distribution\n");

    printf(
        "Best fault: %s, input bit mask = %d\n",
        fault_name(r->best_type),
        r->best_input_bit
    );

    printf(
        "Ineffective inputs: %d\n",
        r->best_n
    );

    printf(
        "Counts (00,01,10,11) = (%d,%d,%d,%d)\n",
        r->best_counts[0],
        r->best_counts[1],
        r->best_counts[2],
        r->best_counts[3]
    );

    printf(
        "Imbalance = %.8f\n",
        r->best_imbalance
    );

    printf("Translation symmetries: ");

    if (r->nsym == 0) {
        printf("None");
    } else {
        for (int z = 0; z < r->nsym; z++) {
            if (z)
                printf(", ");

            print_local_mask(r->symmetries[z], i, j);
        }
    }

    printf("\n");

    printf("IF leakage masks: ");
    print_if_masks(r, i, j);
    printf("\n");

    printf("\n[C] Combined leakage\n");

    printf(
        "Independent relation rank = %d\n",
        r->combined_rank
    );

    printf(
        "Residual candidates = 2^%d\n",
        64 * (2 - r->combined_rank)
    );
}


/* --------------------------------------------------------- */
/* LaTeX table generation                                    */
/* --------------------------------------------------------- */

static void print_latex_header(void)
{
    printf("\\begin{table}[t]\n");
    printf("\\centering\n");
    printf("\\caption{Combined differential and "
           "ineffective-fault leakage for all ten "
           "tag-position choices.}\n");
    printf("\\label{tab:combined-leakage}\n");

    printf("\\begin{tabular}{c|c|c|c|c}\n");
    printf("\\toprule\n");

    printf("\\makecell{Tag\\\\pair} & ");
    printf("\\makecell{Differential\\\\leakage ($y$)} & ");
    printf("\\makecell{Ineffective-fault\\\\leakage "
           "($\\kappa$)} & ");

    printf("\\makecell{\\# independent\\\\relations "
           "on $\\kappa$} & ");

    printf("\\makecell{Residual key\\\\candidates} "
           "\\\\\n");

    printf("\\midrule\n");
}


static void print_latex_row(
    int i,
    int j,
    const PairResult *r
)
{
    printf("$({%d},{%d})$ & ", i, j);

    printf("$");
    print_differential_masks(r);
    printf("$ & ");

    printf("$");
    print_if_masks(r, i, j);
    printf("$ & ");

    printf("%d & ", r->combined_rank);

    printf("$2^{%d}$ \\\\\n",
           64 * (2 - r->combined_rank));
}


static void print_latex_footer(void)
{
    printf("\\bottomrule\n");
    printf("\\end{tabular}\n");

    printf("\\begin{minipage}{0.96\\columnwidth}\n");
    printf("\\footnotesize\n");

    printf(
        "The differential relations on $y$ are converted "
        "into relations on $\\kappa$ using the corresponding "
        "clean inverse-diffused observation "
        "$u_i=y_i\\oplus\\kappa_i$. "
        "Ineffective-fault relations are obtained from "
        "nonzero Walsh coefficients of the conditional "
        "output distribution.\n"
    );

    printf("\\end{minipage}\n");
    printf("\\end{table}\n");
}


/* --------------------------------------------------------- */
/* Main                                                       */
/* --------------------------------------------------------- */

int main(void)
{
    PairResult results[N_PAIRS];

    memset(results, 0, sizeof(results));

    printf("Ascon 5-bit S-box exhaustive leakage analysis\n");
    printf("==============================================\n");

    /*
     * Analyze all ten tag-position choices.
     */
    for (int p = 0; p < N_PAIRS; p++) {

        int i = pairs[p][0];
        int j = pairs[p][1];

        PairResult *r = &results[p];

        r->pair_i = i;
        r->pair_j = j;

        differential_analysis(i, j, r);

        ineffective_analysis(i, j, r);

        calculate_combined_rank(i, j, r);

        print_pair_details(i, j, r);
    }

    /*
     * Print the complete LaTeX table.
     */
    printf("\n\n");
    printf("==================================================\n");
    printf("LATEX TABLE\n");
    printf("==================================================\n\n");

    print_latex_header();

    for (int p = 0; p < N_PAIRS; p++) {

        print_latex_row(
            pairs[p][0],
            pairs[p][1],
            &results[p]
        );
    }

    print_latex_footer();

    /*
     * Summary.
     */
    printf("\n\nCombined leakage summary\n");
    printf("------------------------\n");

    for (int p = 0; p < N_PAIRS; p++) {

        int i = pairs[p][0];
        int j = pairs[p][1];

        printf(
            "(%d,%d): rank %d, residual 2^%d\n",
            i,
            j,
            results[p].combined_rank,
            64 * (2 - results[p].combined_rank)
        );
    }

    return EXIT_SUCCESS;
}
