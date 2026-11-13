/* Infinitesimal symmetries of a UOV public map at full size.
 *
 * lean/docs/security/ompr-shift-algebra.md, section 8.  For a uniform key over GF(256) in normal
 * form (oil space = the last M coordinates; the statement is invariant under a change of basis),
 * compute the rank of the linear system
 *
 *     B(s, X s) = Y P(s)   for all s,        unknowns X (N x N) and Y (M x M),
 *
 * by incremental Gaussian elimination over the M N (N+1)/2 equations taken in a scrambled order.
 * (I, 0) is always a solution.  The program stops when the rank reaches N^2 + M^2 - 1, which
 * proves that the solution space of this key is F·(I, 0).
 *
 * Build:  gcc -O3 -march=native -o lie_fullsize lie_fullsize.c
 * Run:    ./lie_fullsize [N M [seed]]          default 119 45 1; about 262 MB and a few minutes.
 */
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#ifdef __AVX2__
#include <immintrin.h>
#endif

static uint8_t MUL[256][256], INV[256];
static uint8_t LO[256][16], HI[256][16];

static uint8_t gmul(uint8_t a, uint8_t b) {
    uint8_t r = 0;
    while (b) {
        if (b & 1) r ^= a;
        a = (uint8_t)((a << 1) ^ ((a & 0x80) ? 0x1b : 0));
        b >>= 1;
    }
    return r;
}

static void init_tables(void) {
    for (int a = 0; a < 256; a++)
        for (int b = 0; b < 256; b++) MUL[a][b] = gmul((uint8_t)a, (uint8_t)b);
    for (int a = 1; a < 256; a++)
        for (int b = 1; b < 256; b++)
            if (MUL[a][b] == 1) INV[a] = (uint8_t)b;
    for (int c = 0; c < 256; c++)
        for (int x = 0; x < 16; x++) {
            LO[c][x] = MUL[c][x];
            HI[c][x] = MUL[c][x << 4];
        }
}

/* dst[0..n) ^= c * src[0..n) */
static void addmul(uint8_t *dst, const uint8_t *src, uint8_t c, size_t n) {
    size_t i = 0;
#ifdef __AVX2__
    __m256i lo = _mm256_broadcastsi128_si256(_mm_loadu_si128((const __m128i *)LO[c]));
    __m256i hi = _mm256_broadcastsi128_si256(_mm_loadu_si128((const __m128i *)HI[c]));
    __m256i mask = _mm256_set1_epi8(0x0f);
    for (; i + 32 <= n; i += 32) {
        __m256i s = _mm256_loadu_si256((const __m256i *)(src + i));
        __m256i d = _mm256_loadu_si256((const __m256i *)(dst + i));
        __m256i l = _mm256_shuffle_epi8(lo, _mm256_and_si256(s, mask));
        __m256i h = _mm256_shuffle_epi8(hi, _mm256_and_si256(_mm256_srli_epi64(s, 4), mask));
        _mm256_storeu_si256((__m256i *)(dst + i), _mm256_xor_si256(d, _mm256_xor_si256(l, h)));
    }
#endif
    const uint8_t *t = MUL[c];
    for (; i < n; i++) dst[i] ^= t[src[i]];
}

static uint64_t rng_state;
static uint64_t splitmix(void) {
    uint64_t z = (rng_state += 0x9e3779b97f4a7c15ULL);
    z = (z ^ (z >> 30)) * 0xbf58476d1ce4e5b9ULL;
    z = (z ^ (z >> 27)) * 0x94d049bb133111ebULL;
    return z ^ (z >> 31);
}

int main(int argc, char **argv) {
    int N = argc > 2 ? atoi(argv[1]) : 119;
    int M = argc > 2 ? atoi(argv[2]) : 45;
    rng_state = argc > 3 ? strtoull(argv[3], 0, 10) : 1;
    int V = N - M;
    size_t ncols = (size_t)N * N + (size_t)M * M;
    size_t neq = (size_t)M * N * (N + 1) / 2;
    init_tables();

    /* coefficients c[k][i][j], i <= j, zero on the oil-oil block; polar matrices b[k][i][j] */
    uint8_t *c = calloc((size_t)M * N * N, 1), *b = calloc((size_t)M * N * N, 1);
    for (int k = 0; k < M; k++)
        for (int i = 0; i < N; i++)
            for (int j = i; j < N; j++)
                if (i < V) c[((size_t)k * N + i) * N + j] = (uint8_t)(splitmix() >> 32);
    for (int k = 0; k < M; k++)
        for (int i = 0; i < N; i++)
            for (int j = i + 1; j < N; j++) {
                uint8_t x = c[((size_t)k * N + i) * N + j];
                b[((size_t)k * N + i) * N + j] = x;
                b[((size_t)k * N + j) * N + i] = x;
            }

    uint8_t **piv = calloc(ncols, sizeof(uint8_t *));
    uint8_t *row = malloc(ncols + 32);
    size_t rank = 0, used = 0, target = ncols - 1;
    /* scrambled order: idx = (t * step) mod neq with gcd(step, neq) = 1 */
    size_t step = (size_t)(0.6180339887 * (double)neq) | 1;
    for (;;) {
        size_t a = step, bb = neq;
        while (bb) { size_t tt = a % bb; a = bb; bb = tt; }
        if (a == 1) break;
        step += 2;
    }
    for (size_t t = 0; t < neq && rank < target; t++, used++) {
        size_t idx = (t * step) % neq;
        /* decode idx -> (k, i, j) with i <= j */
        int k = (int)(idx / ((size_t)N * (N + 1) / 2));
        size_t rem = idx % ((size_t)N * (N + 1) / 2);
        int i = 0;
        while (rem >= (size_t)(N - i)) { rem -= (size_t)(N - i); i++; }
        int j = i + (int)rem;
        memset(row, 0, ncols);
        const uint8_t *bk = b + (size_t)k * N * N;
        for (int a2 = 0; a2 < N; a2++) {
            row[(size_t)a2 * N + j] ^= bk[(size_t)i * N + a2];
            if (i != j) row[(size_t)a2 * N + i] ^= bk[(size_t)j * N + a2];
        }
        for (int l = 0; l < M; l++)
            row[(size_t)N * N + (size_t)k * M + l] ^= c[((size_t)l * N + i) * N + j];
        /* reduce */
        for (size_t col = 0; col < ncols; col++) {
            uint8_t x = row[col];
            if (!x) continue;
            if (piv[col]) {
                addmul(row + col, piv[col] + col, x, ncols - col);
            } else {
                uint8_t iv = INV[x];
                uint8_t *p = malloc(ncols);
                const uint8_t *tb = MUL[iv];
                for (size_t u = 0; u < ncols; u++) p[u] = tb[row[u]];
                piv[col] = p;
                rank++;
                if (rank % 2000 == 0) {
                    fprintf(stderr, "  rank %zu after %zu equations\n", rank, used + 1);
                }
                break;
            }
        }
    }
    printf("(N, M) = (%d, %d), seed %llu: %zu unknowns, %zu equations, %zu used, rank %zu, "
           "solution space dimension %s%zu\n",
           N, M, (unsigned long long)(argc > 3 ? strtoull(argv[3], 0, 10) : 1), ncols, neq, used,
           rank, used < neq ? "" : "", ncols - rank);
    if (used < neq)
        printf("  (stopped early: rank N^2 + M^2 - 1 reached, and (I, 0) is a solution)\n");
    return 0;
}
