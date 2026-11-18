#include "ascon_common.h"

#define MAX_DATA_SIZE (1U << 20)
#define MAX_LINE_SIZE (2U * MAX_DATA_SIZE + 256U)

typedef struct {
    uint8_t key[16];
    uint8_t nonce[16];

    uint8_t pt[MAX_DATA_SIZE];
    uint8_t ad[MAX_DATA_SIZE];
    uint8_t ct[MAX_DATA_SIZE + 16];

    size_t ptlen;
    size_t adlen;
    size_t ctlen;

    int have_key;
    int have_nonce;
    int have_pt;
    int have_ad;
    int have_ct;
} KAT;

static int hex_value(char c) {
    if (c >= '0' && c <= '9') return c - '0';
    if (c >= 'a' && c <= 'f') return c - 'a' + 10;
    if (c >= 'A' && c <= 'F') return c - 'A' + 10;

    return -1;
}

static int hex_decode(
    const char *str,
    uint8_t *out,
    size_t capacity,
    size_t *outlen
) {
    size_t n = 0;

    while (*str == ' ' || *str == '\t') {
        str++;
    }

    while (*str != '\0' && *str != '\r' && *str != '\n') {
        int hi = hex_value(str[0]);

        if (hi < 0) {
            return 0;
        }

        if (str[1] == '\0' || str[1] == '\r' || str[1] == '\n') {
            return 0;
        }

        int lo = hex_value(str[1]);

        if (lo < 0 || n >= capacity) {
            return 0;
        }

        out[n++] = (uint8_t)((hi << 4) | lo);
        str += 2;
    }

    *outlen = n;
    return 1;
}

static void kat_reset(KAT *kat) {
    memset(kat, 0, sizeof(*kat));
}

static int kat_is_empty(const KAT *kat) {
    return !kat->have_key &&
           !kat->have_nonce &&
           !kat->have_pt &&
           !kat->have_ad &&
           !kat->have_ct;
}

static int kat_complete(const KAT *kat) {
    return kat->have_key &&
           kat->have_nonce &&
           kat->have_pt &&
           kat->have_ad &&
           kat->have_ct;
}

static int process_kat(const KAT *kat, unsigned count) {
    if (!kat_complete(kat)) {
        fprintf(stderr,
                "Incomplete KAT block %u\n",
                count);
        return -1;
    }

    if (kat->ctlen != kat->ptlen + 16) {
        fprintf(stderr,
                "Invalid ciphertext length in KAT block %u: "
                "expected %zu bytes, got %zu bytes\n",
                count,
                kat->ptlen + 16,
                kat->ctlen);
        return -1;
    }

    uint8_t *generated = malloc(kat->ptlen + 16);

    if (generated == NULL) {
        fprintf(stderr, "Memory allocation failed\n");
        return -1;
    }

    uint8_t *generated_ct = generated;
    uint8_t *generated_tag = generated + kat->ptlen;

    ascon_encrypt(
        generated_ct,
        generated_tag,
        kat->key,
        kat->nonce,
        kat->ad,
        kat->adlen,
        kat->pt,
        kat->ptlen
    );

    int match = (memcmp(generated, kat->ct, kat->ctlen) == 0);

    if (!match) {
        size_t mismatch = 0;

        while (mismatch < kat->ctlen &&
               generated[mismatch] == kat->ct[mismatch]) {
            mismatch++;
        }

        fprintf(stderr,
                "First mismatch in KAT block %u at byte %zu\n",
                count,
                mismatch);

        fprintf(stderr, "Expected: ");

        for (size_t i = 0; i < kat->ctlen; i++) {
            fprintf(stderr, "%02X", kat->ct[i]);
        }

        fprintf(stderr, "\nGenerated: ");

        for (size_t i = 0; i < kat->ctlen; i++) {
            fprintf(stderr, "%02X", generated[i]);
        }

        fprintf(stderr, "\n");
    }

    free(generated);

    return match ? 1 : 0;
}

int main(int argc, char **argv) {
    if (argc != 2) {
        fprintf(stderr,
                "Usage: %s <KAT-file>\n",
                argv[0]);
        return EXIT_FAILURE;
    }

    FILE *fp = fopen(argv[1], "r");

    if (fp == NULL) {
        perror("Cannot open KAT file");
        return EXIT_FAILURE;
    }

    char *line = malloc(MAX_LINE_SIZE);

    if (line == NULL) {
        fprintf(stderr, "Memory allocation failed\n");
        fclose(fp);
        return EXIT_FAILURE;
    }

    KAT kat;
    kat_reset(&kat);

    unsigned count = 0;
    unsigned passed = 0;
    unsigned failed = 0;

    while (fgets(line, (int)MAX_LINE_SIZE, fp) != NULL) {
        char *p = line;

        while (*p == ' ' || *p == '\t') {
            p++;
        }

        /* Blank line: end of a KAT block. */
        if (*p == '\n' || *p == '\r' || *p == '\0') {
            if (!kat_is_empty(&kat)) {
                count++;

                int result = process_kat(&kat, count);

                if (result > 0) {
                    passed++;
                } else {
                    failed++;
                }

                kat_reset(&kat);
            }

            continue;
        }

        char *eq = strchr(p, '=');

        if (eq == NULL) {
            continue;
        }

        *eq = '\0';

        char *name = p;
        char *value = eq + 1;

        /* Trim trailing whitespace from the field name. */
        char *end = name + strlen(name);

        while (end > name &&
               (end[-1] == ' ' || end[-1] == '\t' ||
                end[-1] == '\r' || end[-1] == '\n')) {
            *--end = '\0';
        }

        while (*value == ' ' || *value == '\t') {
            value++;
        }

        size_t decoded_len = 0;
        int ok = 1;

        if (strcmp(name, "Key") == 0) {
            ok = hex_decode(value, kat.key,
                            sizeof(kat.key), &decoded_len);

            if (ok && decoded_len == 16) {
                kat.have_key = 1;
            } else {
                ok = 0;
            }
        } else if (strcmp(name, "Nonce") == 0) {
            ok = hex_decode(value, kat.nonce,
                            sizeof(kat.nonce), &decoded_len);

            if (ok && decoded_len == 16) {
                kat.have_nonce = 1;
            } else {
                ok = 0;
            }
        } else if (strcmp(name, "PT") == 0) {
            ok = hex_decode(value, kat.pt,
                            sizeof(kat.pt), &kat.ptlen);

            if (ok) {
                kat.have_pt = 1;
            }
        } else if (strcmp(name, "AD") == 0) {
            ok = hex_decode(value, kat.ad,
                            sizeof(kat.ad), &kat.adlen);

            if (ok) {
                kat.have_ad = 1;
            }
        } else if (strcmp(name, "CT") == 0) {
            ok = hex_decode(value, kat.ct,
                            sizeof(kat.ct), &kat.ctlen);

            if (ok) {
                kat.have_ct = 1;
            }
        }

        if (!ok) {
            fprintf(stderr,
                    "Invalid or oversized field in KAT input "
                    "near block %u\n",
                    count + 1);

            free(line);
            fclose(fp);
            return EXIT_FAILURE;
        }
    }

    /* Process the final block if the file has no trailing blank line. */
    if (!kat_is_empty(&kat)) {
        count++;

        int result = process_kat(&kat, count);

        if (result > 0) {
            passed++;
        } else {
            failed++;
        }
    }

    free(line);
    fclose(fp);

    printf("Official Ascon-128 v1.2 KAT: "
           "%u passed, %u failed\n",
           passed, failed);

    if (failed != 0) {
        return EXIT_FAILURE;
    }

    return EXIT_SUCCESS;
}