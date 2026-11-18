#include "ascon_common.h"

#include <stdint.h>
#include <stdio.h>
#include <string.h>


static const uint8_t S[32] = {
    4, 11, 31, 20, 26, 21, 9, 2,
    27, 5, 8, 18, 29, 3, 6, 28,
    30, 19, 7, 14, 0, 13, 17, 24,
    16, 12, 1, 25, 22, 10, 15, 23
};

static int rb(int i)
{
    return 1 << (4 - i);
}

static int tagmask(int i, int j)
{
    return rb(i) | rb(j);
}

static int act(int f, int bit, int x)
{
    return f == 0 ? (x ^ bit) :
           f == 1 ? (x | bit) :
                    (x & (31 ^ bit));
}

static int flipdiffs[5] = {1, 2, 4, 8, 16};

static int placements[10][2] = {
    {4, 3},
    {4, 2},
    {4, 1},
    {4, 0},
    {3, 2},
    {3, 1},
    {3, 0},
    {2, 1},
    {2, 0},
    {1, 0}
};

static int parity(int x)
{
    return __builtin_parity((unsigned)x);
}

static int signatures[32][32];

/*
 * Construct equivalence classes of S-box inputs.
 *
 * Two inputs belong to the same class if all selected
 * fault configurations produce identical observable
 * output differences under mask m.
 */

static int make_classes(
    int m,
    int nFault,
    const int *ftype,
    const int *fbit,
    int groups[32][32],
    int sizes[32])
{
    int ng = 0;

    memset(sizes, 0, 32 * sizeof(int));

    for (int x = 0; x < 32; x++) {
        int sig[32];
        int ns = 0;

        for (int q = 0; q < nFault; q++) {
            int xx = act(ftype[q], fbit[q], x);

            sig[ns++] = (S[x] ^ S[xx]) & m;
        }

        int g;

        for (g = 0; g < ng; g++) {
            int y = groups[g][0];
            int same = 1;

            for (int q = 0; q < nFault; q++) {
                if (((S[y] ^ S[act(ftype[q], fbit[q], y)]) & m)
                    != sig[q]) {
                    same = 0;
                    break;
                }
            }

            if (same)
                break;
        }

        if (g == ng)
            ng++;

        groups[g][sizes[g]++] = x;
    }

    return ng;
}

/*
 * Display all linear masks that are constant within
 * every equivalence class.
 */

static void show_masks(
    int m,
    int nFault,
    const int *ft,
    const int *fb)
{
    int groups[32][32];
    int sz[32];

    int ng = make_classes(m, nFault, ft, fb, groups, sz);
    int found = 0;

    for (int l = 1; l < 32; l++) {
        if ((l & m) == l) {
            int ok = 1;

            for (int g = 0; g < ng; g++) {
                int v = parity(S[groups[g][0]] & l);

                for (int z = 1; z < sz[g]; z++) {
                    if (parity(S[groups[g][z]] & l) != v) {
                        ok = 0;
                        break;
                    }
                }

                if (!ok)
                    break;
            }

            if (ok) {
                printf(" ");

                for (int b = 4; b >= 0; b--) {
                    if (l & rb(b))
                        printf("y%d", b);
                }

                printf(" ");
                found++;
            }
        }
    }

    if (!found)
        printf(" None");
}

/*
 * Check whether an output register is completely
 * determined by the observable fault signatures.
 */

static int free_reg(
    int m,
    int nf,
    const int *ft,
    const int *fb,
    int r)
{
    int gr[32][32];
    int sz[32];

    int ng = make_classes(m, nf, ft, fb, gr, sz);
    int mask = rb(r);

    for (int g = 0; g < ng; g++) {
        int v = S[gr[g][0]] & mask;

        for (int z = 1; z < sz[g]; z++) {
            if ((S[gr[g][z]] & mask) != v)
                return 0;
        }
    }

    return 1;
}

/*
 * Find the maximum number of distinct observable
 * output values remaining in any equivalence class.
 */

static int candidate_max(
    int m,
    int nf,
    const int *ft,
    const int *fb)
{
    int gr[32][32];
    int sz[32];

    int ng = make_classes(m, nf, ft, fb, gr, sz);
    int mx = 0;

    for (int g = 0; g < ng; g++) {
        int seen = 0;

        for (int z = 0; z < sz[g]; z++) {
            int v = S[gr[g][z]] & m;
            int bit = 1 << v;

            if (!(seen & bit))
                seen |= bit;
        }

        int n = __builtin_popcount((unsigned)seen);

        if (n > mx)
            mx = n;
    }

    return mx;
}

/*
 * Measure the imbalance of the observable output
 * distribution over a set of ineffective inputs.
 */

static double imbalance(int m, const int *xs, int n)
{
    if (!n)
        return 0;

    int cnt[32] = {0};

    for (int z = 0; z < n; z++)
        cnt[S[xs[z]] & m]++;

    double q = 0;

    for (int v = 0; v < 32; v++) {
        if ((v & m) == v) {
            double d = (double)cnt[v] / n - 0.25;
            q += d * d;
        }
    }

    return q;
}

/*
 * Enumerate inputs for which the selected fault
 * does not change the observable output bits.
 */

static int ineffective_inputs(
    int m,
    int f,
    int bit,
    int *xs)
{
    int n = 0;

    for (int x = 0; x < 32; x++) {
        int xx = act(f, bit, x);

        if ((S[xx] & m) == (S[x] & m))
            xs[n++] = x;
    }

    return n;
}

/*
 * Find the best SET/RESET fault configuration for
 * each of the three selected tag-position pairs.
 */

static void ineffective_table(void)
{
    const char *names[] = {"SET", "RST"};

    int bestreg[] = {2, 3, 1};

    int pairs[3][2] = {
        {4, 3},
        {4, 0},
        {3, 2}
    };

    puts("Observable ineffective-fault distributions:");

    for (int p = 0; p < 3; p++) {
        int m = tagmask(pairs[p][0], pairs[p][1]);

        int bestf = 1;
        int bestb = 0;
        int bestn = 0;

        int xs[32];

        double best = -1;

        for (int f = 1; f <= 2; f++) {
            for (int r = 0; r < 5; r++) {
                int n = ineffective_inputs(
                    m,
                    f,
                    rb(r),
                    xs
                );

                double q = imbalance(m, xs, n);

                if (q > best) {
                    best = q;
                    bestf = f;
                    bestb = rb(r);
                    bestn = n;
                }
            }
        }

        ineffective_inputs(m, bestf, bestb, xs);

        int cnt[4] = {0};

        for (int z = 0; z < bestn; z++) {
            int v = S[xs[z]] & m;

            int ix =
                ((v & rb(pairs[p][0])) ? 2 : 0) |
                ((v & rb(pairs[p][1])) ? 1 : 0);

            cnt[ix]++;
        }

        printf(
            "(%d,%d): %s bit %d, n=%d, "
            "counts (00,01,10,11)=(%d,%d,%d,%d), "
            "imbalance=%.6f\n",
            pairs[p][0],
            pairs[p][1],
            names[bestf - 1],
            bestb,
            bestn,
            cnt[0],
            cnt[1],
            cnt[2],
            cnt[3],
            best
        );
    }
}

int main(void)
{
    int ft[5], fb[5];

    for (int i = 0; i < 5; i++) {
        ft[i] = 0;
        fb[i] = 1 << i;
    }

    puts("=== Differential signature analysis: five input-bit flips ===");

    for (int p = 0; p < 10; p++) {
        int i = placements[p][0];
        int j = placements[p][1];

        int m = tagmask(i, j);

        printf("pair (%d,%d): leaked masks:", i, j);

        show_masks(m, 5, ft, fb);

        printf("\n");

        printf("  free output registers:");

        for (int r = 0; r < 5; r++) {
            if (free_reg(m, 5, ft, fb, r))
                printf(" y%d", r);
        }

        printf(
            "; max candidates/class=%d\n",
            candidate_max(m, 5, ft, fb)
        );
    }

    puts("\n=== Ineffective-fault distributions (best SET/RESET) ===");

    ineffective_table();

    puts("\n=== Deterministic five-fault SET signature: ordered IF bits ===");

    int pairs[3][2] = {
        {4, 3},
        {4, 0},
        {3, 2}
    };

    for (int p = 0; p < 3; p++) {
        int i = pairs[p][0];
        int j = pairs[p][1];

        int m = tagmask(i, j);

        for (int q = 0; q < 5; q++) {
            ft[q] = 1;
            fb[q] = 1 << (4 - q);
        }

        /* SET bit q in input-index convention. */

        int gr[32][32];
        int sz[32];

        int ng = make_classes(m, 5, ft, fb, gr, sz);

        printf(
            "pair (%d,%d): %d signature classes; selected tag bits:",
            i, j, ng
        );

        printf(
            " y%d=%s y%d=%s\n",
            i,
            free_reg(m, 5, ft, fb, i) ? "YES" : "NO",
            j,
            free_reg(m, 5, ft, fb, j) ? "YES" : "NO"
        );
    }

    return 0;
}