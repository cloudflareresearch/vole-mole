/* Independent check of the class attack P1 (lean/docs/security/ompr-cryptanalysis-2.md, sections
 * 3.1 and 8).  Written for the review; shares no code with scripts/ompr-shift-algebra/c1_toy.c.
 *
 * A toy UOV key (N, M) over F_q, q = 16 or 256, a uniform target t != 0.  Four forgery attacks:
 *
 *   direct, plain:  P(s) = t on a random affine subspace of dimension M - g.
 *   P1, plain:      pi_t(P(s)) = 0 (M - 1 homogeneous quadrics) on a random affine subspace of
 *                   dimension M - 1 - g; a solution has P(s) = nu t and is scaled by nu^(-1/2).
 *   direct, TW:     Thomae-Wolf with alpha = 1 first.  Take M vectors u_i that are pairwise
 *                   orthogonal for the polar form of the first equation and a point w orthogonal
 *                   to all of them.  On w + span(u) the first equation is sum x_i^2 p(u_i) = c,
 *                   the square of a linear equation.  On that hyperplane: M - 1 quadrics in M - 1
 *                   variables.  Then a random affine subspace of dimension M - 1 - g.
 *   P1, TW:         the same for the M - 1 quadrics of P1: M - 2 quadrics, dimension M - 2 - g.
 *
 * In all four a call has a solution with probability about q^(-g).  Each call is solved by XL
 * at degree D with dense elimination; D is the smallest degree at which XL decides at least 90%
 * of a sample (rank T: no solution; corank 1: one candidate point).  The program counts field
 * multiplications in the elimination.  Every forgery is checked against the public map.
 *
 * Build:  gcc -O3 -march=native -fopenmp -o p1_review_toy p1_review_toy.c
 * Usage:  p1_review_toy q N M seed gmin gmax seconds_per_cell [max_columns]
 * Output: one line per (attack, g):
 *   @ q N M tw p1 g eqs vars D T calls decided solutions forgeries mults
 */
#include <omp.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

enum { MAXN = 40, MAXM = 16, MAXV = 14, MAXD = 8 };

static int Q, QBITS;
static uint8_t MUL[256][256], INV[256], SQRT[256];

static void field_init(int q) {
    Q = q;
    QBITS = q == 16 ? 4 : 8;
    int poly = q == 16 ? 0x13 : 0x11B;
    for (int a = 0; a < q; a++) {
        for (int b = 0; b < q; b++) {
            int r = 0, x = a;
            for (int i = 0; i < QBITS; i++) {
                if ((b >> i) & 1) {
                    r ^= x;
                }
                x <<= 1;
                if (x & q) {
                    x ^= poly;
                }
            }
            MUL[a][b] = (uint8_t)r;
            if (r == 1) {
                INV[a] = (uint8_t)b;
            }
        }
    }
    for (int a = 0; a < q; a++) {
        SQRT[MUL[a][a]] = (uint8_t)a;
    }
}

/* xoshiro256** */
typedef struct {
    uint64_t s[4];
} rng_t;

static uint64_t rotl(uint64_t x, int k) { return (x << k) | (x >> (64 - k)); }

static uint64_t rng_next(rng_t* r) {
    uint64_t* s = r->s;
    uint64_t res = rotl(s[1] * 5, 7) * 9, t = s[1] << 17;
    s[2] ^= s[0];
    s[3] ^= s[1];
    s[1] ^= s[2];
    s[0] ^= s[3];
    s[2] ^= t;
    s[3] = rotl(s[3], 45);
    return res;
}

static void rng_seed(rng_t* r, uint64_t seed) {
    for (int i = 0; i < 4; i++) {
        seed += 0x9E3779B97F4A7C15ULL;
        uint64_t z = seed;
        z = (z ^ (z >> 30)) * 0xBF58476D1CE4E5B9ULL;
        z = (z ^ (z >> 27)) * 0x94D049BB133111EBULL;
        r->s[i] = z ^ (z >> 31);
    }
}

static uint8_t rng_f(rng_t* r) { return (uint8_t)(rng_next(r) >> 40) & (uint8_t)(Q - 1); }

/* ---------- the public map: M upper triangular N x N matrices ---------- */
static int N, M;
static uint8_t PUB[MAXM][MAXN][MAXN];

static uint8_t quad_eval(uint8_t A[MAXN][MAXN], const uint8_t* x) {
    uint8_t r = 0;
    for (int i = 0; i < N; i++) {
        if (x[i] == 0) {
            continue;
        }
        uint8_t acc = 0;
        for (int j = i; j < N; j++) {
            acc ^= MUL[A[i][j]][x[j]];
        }
        r ^= MUL[acc][x[i]];
    }
    return r;
}

static uint8_t polar(uint8_t A[MAXN][MAXN], const uint8_t* x, const uint8_t* y) {
    uint8_t z[MAXN];
    for (int i = 0; i < N; i++) {
        z[i] = x[i] ^ y[i];
    }
    return quad_eval(A, z) ^ quad_eval(A, x) ^ quad_eval(A, y);
}

static void keygen(rng_t* r) {
    static uint8_t F[MAXM][MAXN][MAXN];
    uint8_t T[MAXN][MAXN];
    int V = N - M;
    memset(F, 0, sizeof F);
    for (int k = 0; k < M; k++) {
        for (int i = 0; i < V; i++) {
            for (int j = i; j < N; j++) {
                F[k][i][j] = rng_f(r);
            }
        }
    }
    /* T = L * U with unit diagonals: invertible */
    uint8_t L[MAXN][MAXN], U[MAXN][MAXN];
    for (int i = 0; i < N; i++) {
        for (int j = 0; j < N; j++) {
            L[i][j] = i == j ? 1 : (j < i ? rng_f(r) : 0);
            U[i][j] = i == j ? 1 : (j > i ? rng_f(r) : 0);
        }
    }
    for (int i = 0; i < N; i++) {
        for (int j = 0; j < N; j++) {
            uint8_t a = 0;
            for (int l = 0; l < N; l++) {
                a ^= MUL[L[i][l]][U[l][j]];
            }
            T[j][i] = a; /* T[j] = image of e_j */
        }
    }
    for (int k = 0; k < M; k++) {
        for (int i = 0; i < N; i++) {
            PUB[k][i][i] = quad_eval(F[k], T[i]);
            for (int j = i + 1; j < N; j++) {
                PUB[k][i][j] = polar(F[k], T[i], T[j]);
            }
        }
    }
}

/* ---------- linear algebra helpers ---------- */

/* A uniform element of the solution space of rows[0..nr) . x = 0 (x in F^N).  Returns 0 if the
 * space is {0}. */
static int random_kernel(uint8_t rows[][MAXN], int nr, uint8_t* x, rng_t* r) {
    uint8_t A[MAXN + MAXM][MAXN];
    int piv[MAXN], np = 0, is_piv[MAXN] = {0};
    memcpy(A, rows, (size_t)nr * MAXN);
    for (int c = 0; c < N && np < nr; c++) {
        int p = -1;
        for (int i = np; i < nr; i++) {
            if (A[i][c]) {
                p = i;
                break;
            }
        }
        if (p < 0) {
            continue;
        }
        uint8_t tmp[MAXN];
        memcpy(tmp, A[p], MAXN);
        memcpy(A[p], A[np], MAXN);
        memcpy(A[np], tmp, MAXN);
        uint8_t inv = INV[A[np][c]];
        for (int j = 0; j < N; j++) {
            A[np][j] = MUL[inv][A[np][j]];
        }
        for (int i = 0; i < nr; i++) {
            if (i != np && A[i][c]) {
                uint8_t f = A[i][c];
                for (int j = 0; j < N; j++) {
                    A[i][j] ^= MUL[f][A[np][j]];
                }
            }
        }
        piv[np++] = c;
        is_piv[c] = 1;
    }
    if (np == N) {
        return 0;
    }
    for (int c = 0; c < N; c++) {
        x[c] = is_piv[c] ? 0 : rng_f(r);
    }
    for (int i = 0; i < np; i++) {
        uint8_t a = 0;
        for (int c = 0; c < N; c++) {
            if (!is_piv[c]) {
                a ^= MUL[A[i][c]][x[c]];
            }
        }
        x[piv[i]] = a;
    }
    return 1;
}

static int rank_of(uint8_t vecs[][MAXN], int k) {
    uint8_t A[MAXN][MAXN];
    int rk = 0;
    memcpy(A, vecs, (size_t)k * MAXN);
    for (int c = 0; c < N && rk < k; c++) {
        int p = -1;
        for (int i = rk; i < k; i++) {
            if (A[i][c]) {
                p = i;
                break;
            }
        }
        if (p < 0) {
            continue;
        }
        uint8_t tmp[MAXN];
        memcpy(tmp, A[p], MAXN);
        memcpy(A[p], A[rk], MAXN);
        memcpy(A[rk], tmp, MAXN);
        uint8_t inv = INV[A[rk][c]];
        for (int i = rk + 1; i < k; i++) {
            if (A[i][c]) {
                uint8_t f = MUL[A[i][c]][inv];
                for (int j = 0; j < N; j++) {
                    A[i][j] ^= MUL[f][A[rk][j]];
                }
            }
        }
        rk++;
    }
    return rk;
}

/* ---------- XL ---------- */
typedef struct {
    int n, D, T, nmult, n2;
    int* col;      /* [nmult * n2]: column of (multiplier * monomial of degree <= 2) */
    int lin[MAXV]; /* columns of x_i */
    int one;
} xl_t;

static int mono_count(int n, int d) { /* monomials of degree <= d in n variables */
    long r = 1;
    for (int i = 1; i <= n; i++) {
        r = r * (d + i) / i;
    }
    return (int)r;
}

static uint64_t* MONO; /* scratch for xl_build */
static int mono_n;

static void mono_enum(int n, int d, int var, uint64_t code) {
    if (var == n) {
        MONO[mono_n++] = code;
        return;
    }
    for (int e = 0; e <= d; e++) {
        mono_enum(n, d - e, var + 1, code | ((uint64_t)e << (4 * var)));
    }
}

static int cmp_u64(const void* a, const void* b) {
    uint64_t x = *(const uint64_t*)a, y = *(const uint64_t*)b;
    return x < y ? -1 : x > y;
}

static int mono_find(const uint64_t* tab, int T, uint64_t code) {
    const uint64_t* p = bsearch(&code, tab, (size_t)T, sizeof *tab, cmp_u64);
    return (int)(p - tab);
}

/* Monomials of degree <= 2 in the order: 1, x_i (i < n), x_i x_j (i <= j). */
static void xl_build(xl_t* X, int n, int D) {
    X->n = n;
    X->D = D;
    X->T = mono_count(n, D);
    X->nmult = mono_count(n, D - 2);
    X->n2 = mono_count(n, 2);
    uint64_t* all = malloc((size_t)X->T * sizeof *all);
    MONO = all;
    mono_n = 0;
    mono_enum(n, D, 0, 0);
    qsort(all, (size_t)X->T, sizeof *all, cmp_u64);
    uint64_t* mult = malloc((size_t)X->nmult * sizeof *mult);
    MONO = mult;
    mono_n = 0;
    mono_enum(n, D - 2, 0, 0);
    uint64_t* two = malloc((size_t)X->n2 * sizeof *two);
    int c = 0;
    two[c++] = 0;
    for (int i = 0; i < n; i++) {
        two[c++] = 1ULL << (4 * i);
    }
    for (int i = 0; i < n; i++) {
        for (int j = i; j < n; j++) {
            two[c++] = (1ULL << (4 * i)) + (1ULL << (4 * j));
        }
    }
    X->col = malloc((size_t)X->nmult * (size_t)X->n2 * sizeof *X->col);
    for (int a = 0; a < X->nmult; a++) {
        for (int b = 0; b < X->n2; b++) {
            X->col[a * X->n2 + b] = mono_find(all, X->T, mult[a] + two[b]);
        }
    }
    X->one = mono_find(all, X->T, 0);
    for (int i = 0; i < n; i++) {
        X->lin[i] = mono_find(all, X->T, 1ULL << (4 * i));
    }
    free(all);
    free(mult);
    free(two);
}

static void xl_free(xl_t* X) { free(X->col); }

/* eqs[e][b]: coefficient of the b-th monomial of degree <= 2.  Returns 0: no solution, 1: one
 * candidate (in x), 2: undecided.  Adds the multiplications to *mults. */
static int xl_solve(const xl_t* X, int me, uint8_t eqs[][MAXV * MAXV], uint8_t* x, double* mults,
                    uint8_t* mat, uint8_t** piv, uint8_t* row) {
    int T = X->T, rank = 0;
    double work = 0;
    memset(piv, 0, (size_t)T * sizeof *piv);
    for (int a = 0; a < X->nmult && rank < T; a++) {
        for (int e = 0; e < me && rank < T; e++) {
            memset(row, 0, (size_t)T);
            const int* col = X->col + a * X->n2;
            for (int b = 0; b < X->n2; b++) {
                row[col[b]] = eqs[e][b];
            }
            for (int c = 0; c < T; c++) {
                uint8_t f = row[c];
                if (!f) {
                    continue;
                }
                if (piv[c]) {
                    const uint8_t* p = piv[c];
                    const uint8_t* mf = MUL[f];
                    for (int k = c; k < T; k++) {
                        row[k] ^= mf[p[k]];
                    }
                    work += T - c;
                } else {
                    const uint8_t* mf = MUL[INV[f]];
                    uint8_t* dst = mat + (size_t)rank * (size_t)T;
                    for (int k = 0; k < T; k++) {
                        dst[k] = mf[row[k]];
                    }
                    work += T - c;
                    piv[c] = dst;
                    rank++;
                    break;
                }
            }
        }
    }
    *mults += work;
    if (rank == T) {
        return 0;
    }
    if (rank < T - 1) {
        return 2;
    }
    /* corank 1: the kernel vector v, with v[free] = 1 */
    int fr = 0;
    while (piv[fr]) {
        fr++;
    }
    memset(row, 0, (size_t)T);
    row[fr] = 1;
    for (int c = fr - 1; c >= 0; c--) {
        const uint8_t* p = piv[c];
        uint8_t a = 0;
        for (int k = c + 1; k <= fr; k++) {
            a ^= MUL[p[k]][row[k]];
        }
        row[c] = a;
    }
    *mults += (double)fr * fr / 2;
    if (row[X->one] == 0) {
        return 0; /* the point is at infinity */
    }
    uint8_t inv = INV[row[X->one]];
    for (int i = 0; i < X->n; i++) {
        x[i] = MUL[inv][row[X->lin[i]]];
    }
    return 1;
}

/* ---------- one call ---------- */
typedef struct {
    int me;                      /* equations before Thomae-Wolf */
    uint8_t A[MAXM][MAXN][MAXN]; /* their quadratic forms */
    uint8_t rhs[MAXM];
} system_t;

static uint8_t TARGET[MAXM];

/* Fills w and u[0..dim): a random affine subspace for the attack.  Returns its dimension, or -1
 * to retry. */
static int choose_space(const system_t* S, int tw, int g, uint8_t* w, uint8_t u[][MAXN], rng_t* r) {
    int dim;
    static _Thread_local uint8_t rows[MAXN + MAXM][MAXN], A0[MAXN][MAXN];
    if (!tw) {
        dim = S->me - g;
        for (int i = 0; i < N; i++) {
            w[i] = rng_f(r);
        }
        for (int k = 0; k < dim; k++) {
            for (int i = 0; i < N; i++) {
                u[k][i] = rng_f(r);
            }
        }
        return rank_of(u, dim) == dim ? dim : -1;
    }
    /* Thomae-Wolf, alpha = 1, on equation 0 */
    int k0 = S->me;
    uint8_t v[MAXM][MAXN], e[MAXN];
    memcpy(A0, S->A[0], sizeof A0);
    for (int k = 0; k <= k0; k++) { /* v[0..k0) pairwise orthogonal, then w orthogonal to all */
        for (int j = 0; j < k; j++) {
            for (int i = 0; i < N; i++) { /* row j: the linear form B(v_j, .) */
                memset(e, 0, sizeof e);
                e[i] = 1;
                rows[j][i] = polar(A0, v[j], e);
            }
        }
        if (!random_kernel(rows, k, k < k0 ? v[k] : w, r)) {
            return -1;
        }
    }
    if (rank_of(v, k0) != k0) {
        return -1;
    }
    /* on w + sum x_i v_i: sum x_i^2 p(v_i) = rhs + p(w), i.e. sum c_i x_i = c0 */
    uint8_t c[MAXM], c0 = SQRT[S->rhs[0] ^ quad_eval(A0, w)];
    int p = -1;
    for (int i = 0; i < k0; i++) {
        c[i] = SQRT[quad_eval(A0, v[i])];
        if (c[i] && p < 0) {
            p = i;
        }
    }
    if (p < 0) {
        return -1;
    }
    /* particular solution x_p = c0 / c_p; kernel basis v_i + (c_i / c_p) v_p, i != p */
    uint8_t ip = INV[c[p]], h[MAXM][MAXN];
    int nh = 0;
    for (int i = 0; i < N; i++) {
        w[i] ^= MUL[MUL[c0][ip]][v[p][i]];
    }
    for (int k = 0; k < k0; k++) {
        if (k == p) {
            continue;
        }
        uint8_t f = MUL[c[k]][ip];
        for (int i = 0; i < N; i++) {
            h[nh][i] = v[k][i] ^ MUL[f][v[p][i]];
        }
        nh++;
    }
    /* a random affine subspace of dimension nh - g inside w + span(h) */
    dim = nh - g;
    for (int k = 0; k < nh; k++) {
        uint8_t f = rng_f(r);
        for (int i = 0; i < N; i++) {
            w[i] ^= MUL[f][h[k][i]];
        }
    }
    for (int k = 0; k < dim; k++) {
        memset(u[k], 0, MAXN);
        for (int l = 0; l < nh; l++) {
            uint8_t f = rng_f(r);
            for (int i = 0; i < N; i++) {
                u[k][i] ^= MUL[f][h[l][i]];
            }
        }
    }
    return rank_of(u, dim) == dim ? dim : -1;
}

/* Restrict equations e0..me of S to w + span(u): coefficients in the order of xl_build. */
static void restrict_sys(const system_t* S, int e0, int dim, const uint8_t* w, uint8_t u[][MAXN],
                         uint8_t eqs[][MAXV * MAXV]) {
    static _Thread_local uint8_t A[MAXN][MAXN];
    for (int e = e0; e < S->me; e++) {
        uint8_t* q = eqs[e - e0];
        int c = 0;
        memcpy(A, S->A[e], sizeof A);
        q[c++] = quad_eval(A, w) ^ S->rhs[e];
        for (int i = 0; i < dim; i++) {
            q[c++] = polar(A, w, u[i]);
        }
        for (int i = 0; i < dim; i++) {
            q[c++] = quad_eval(A, u[i]);
            for (int j = i + 1; j < dim; j++) {
                q[c++] = polar(A, u[i], u[j]);
            }
        }
    }
}

/* Is s (after scaling for P1) a preimage of the target under the public map? */
static int check_forgery(int p1, const uint8_t* s) {
    uint8_t y[MAXM], x[MAXN];
    memcpy(x, s, MAXN);
    if (p1) {
        int rr = 0;
        while (TARGET[rr] == 0) {
            rr++;
        }
        uint8_t nu = MUL[quad_eval(PUB[rr], s)][INV[TARGET[rr]]];
        if (nu == 0) {
            return 0;
        }
        uint8_t f = INV[SQRT[nu]];
        for (int i = 0; i < N; i++) {
            x[i] = MUL[f][s[i]];
        }
    }
    for (int k = 0; k < M; k++) {
        y[k] = quad_eval(PUB[k], x);
    }
    return memcmp(y, TARGET, (size_t)M) == 0;
}

typedef struct {
    long calls, decided, sols, forg;
    double mults;
} stat_t;

static void run_calls(const system_t* S, int tw, int p1, int g, int D, long ncalls, double secs,
                      uint64_t seed, stat_t* out) {
    int dim = S->me - tw - g, me = S->me - tw;
    stat_t tot = {0, 0, 0, 0, 0};
    double t0 = omp_get_wtime();
#pragma omp parallel
    {
        xl_t X;
        rng_t r;
        rng_seed(&r, seed * 1000003ULL + (uint64_t)omp_get_thread_num());
#pragma omp critical
        xl_build(&X, dim, D);
        uint8_t* mat = malloc((size_t)X.T * (size_t)X.T);
        uint8_t** piv = malloc((size_t)X.T * sizeof *piv);
        uint8_t* row = malloc((size_t)X.T);
        stat_t st = {0, 0, 0, 0, 0};
        uint8_t w[MAXN], u[MAXV][MAXN], x[MAXV], s[MAXN];
        uint8_t eqs[MAXM][MAXV * MAXV];
        for (;;) {
            long done;
#pragma omp atomic read
            done = tot.calls;
            if (done + st.calls >= ncalls || omp_get_wtime() - t0 > secs) {
                break;
            }
            for (int rep = 0; rep < 8; rep++) {
                if (choose_space(S, tw, g, w, u, &r) != dim) {
                    continue;
                }
                restrict_sys(S, tw, dim, w, u, eqs);
                int res = xl_solve(&X, me, eqs, x, &st.mults, mat, piv, row);
                st.calls++;
                st.decided += res != 2;
                if (res == 1) {
                    memcpy(s, w, MAXN);
                    for (int k = 0; k < dim; k++) {
                        for (int i = 0; i < N; i++) {
                            s[i] ^= MUL[x[k]][u[k][i]];
                        }
                    }
                    int ok = 1; /* a solution of the system the attack solves? */
                    for (int e = 0; e < S->me; e++) {
                        static _Thread_local uint8_t A[MAXN][MAXN];
                        memcpy(A, S->A[e], sizeof A);
                        ok &= quad_eval(A, s) == S->rhs[e];
                    }
                    st.sols += ok;
                    st.forg += ok && check_forgery(p1, s);
                }
            }
#pragma omp atomic
            tot.calls += st.calls;
#pragma omp critical
            {
                tot.decided += st.decided;
                tot.sols += st.sols;
                tot.forg += st.forg;
                tot.mults += st.mults;
            }
            st = (stat_t){0, 0, 0, 0, 0};
        }
        free(mat);
        free(piv);
        free(row);
        xl_free(&X);
    }
    *out = tot;
}

int main(int argc, char** argv) {
    if (argc < 8) {
        fprintf(stderr, "usage: %s q N M seed gmin gmax seconds_per_cell [max_columns]\n", argv[0]);
        return 2;
    }
    int q = atoi(argv[1]);
    N = atoi(argv[2]);
    M = atoi(argv[3]);
    uint64_t seed = strtoull(argv[4], 0, 10);
    int gmin = atoi(argv[5]), gmax = atoi(argv[6]);
    double secs = atof(argv[7]);
    int tmax = argc > 8 ? atoi(argv[8]) : 1400; /* skip cells whose Macaulay matrix is wider */
    if ((q != 16 && q != 256) || N >= MAXN || M >= MAXM || N < 2 * M + 1) {
        fprintf(stderr, "bad parameters\n");
        return 2;
    }
    field_init(q);
    rng_t r;
    rng_seed(&r, seed);
    keygen(&r);
    do {
        for (int k = 0; k < M; k++) {
            TARGET[k] = rng_f(&r);
        }
    } while (TARGET[0] == 0); /* nonzero first coordinate, to keep the projection simple */
    static system_t S[2];
    S[0].me = M;
    memcpy(S[0].A, PUB, sizeof PUB);
    memcpy(S[0].rhs, TARGET, sizeof TARGET);
    /* P1: P_k - (t_k / t_0) P_0 = 0 for k >= 1 */
    S[1].me = M - 1;
    for (int k = 1; k < M; k++) {
        uint8_t f = MUL[TARGET[k]][INV[TARGET[0]]];
        for (int i = 0; i < N; i++) {
            for (int j = 0; j < N; j++) {
                S[1].A[k - 1][i][j] = PUB[k][i][j] ^ MUL[f][PUB[0][i][j]];
            }
        }
        S[1].rhs[k - 1] = 0;
    }
    for (int tw = 0; tw < 2; tw++) {
        for (int p1 = 0; p1 < 2; p1++) {
            for (int g = gmin; g <= gmax; g++) {
                int me = S[p1].me - tw, dim = me - g;
                if (dim < 1 || dim > MAXV - 1) {
                    continue;
                }
                int D = 2;
                stat_t st;
                for (; D <= MAXD; D++) {
                    if (mono_count(dim, D) > tmax) {
                        D = MAXD + 1;
                        break;
                    }
                    run_calls(&S[p1], tw, p1, g, D, 24, 1e9, seed + 77, &st);
                    if (st.decided * 10 >= st.calls * 9) {
                        break;
                    }
                }
                if (D > MAXD) {
                    continue;
                }
                run_calls(&S[p1], tw, p1, g, D, 1L << 40, secs, seed + 1, &st);
                printf("@ %d %d %d %d %d %d %d %d %d %d %ld %ld %ld %ld %.6g\n", q, N, M, tw, p1, g,
                       me, dim, D, mono_count(dim, D), st.calls, st.decided, st.sols, st.forg,
                       st.mults);
                fflush(stdout);
            }
        }
    }
    return 0;
}
