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
 *   H(a, c):        Hashimoto's reduction (JSIAM Letters 15, 2023, section 4; the round-3 UOV
 *                   specification, section 4.2), applied to the M equations (direct) or to the
 *                   M - 1 homogeneous quadrics of P1; m' is their number, r = m' - a - c + 1.
 *                   Once per key: X = r vectors spanning a space that is totally singular for the
 *                   first a quadrics (vector i: a (i - 1) linear and a quadratic conditions; the
 *                   quadratic ones are solved by enumeration on a random affine a-flat); Y = a - 1
 *                   vectors and the space K2 that are orthogonal to X for the first a - 1 polar
 *                   forms.  Per restart: a uniform w in K2 (for P1 outside span(X, Y)); on
 *                   w + span(Y) the first a - 1 equations involve only y: a - 1 quadrics in a - 1
 *                   variables, solved by enumeration; for each root the a-th equation is linear on
 *                   the flat over X and removes one variable.  Left: m' - a quadrics in
 *                   r - 1 = m' - a - c variables, restricted to a random affine subflat of
 *                   dimension r - 1 - g.  A restart has a solution with probability q^(-c-g).
 *
 * In all four a call has a solution with probability about q^(-g).  Each call is solved by XL
 * at degree D with dense elimination; D is the smallest degree at which XL decides at least 90%
 * of a sample (rank T: no solution; corank 1: one candidate point).  The program counts field
 * multiplications in the elimination.  Every forgery is checked against the public map.
 *
 * Build:  gcc -O3 -march=native -fopenmp -o p1_review_toy p1_review_toy.c
 * Usage:  p1_review_toy q N M seed gmin gmax seconds_per_cell [max_columns [run_seed [attacks]]]
 *   seed fixes the key and the target; run_seed (default seed + 1) the random choices of the
 *   attack.  attacks: comma-separated, from p (plain), t (Thomae-Wolf) and h<a>.<c>.<c'> (Hashimoto
 *   with c guesses for the direct attack and c' for P1; a negative c or c' skips that run);
 *   default "p,t".
 *   With P1_PRINT set in the environment every forgery is printed to stderr, with the number of
 *   the thread and the index of the call in that thread.
 * Output: one line per (attack, g):
 *   @ q N M prep p1 g eqs vars D T calls decided solutions forgeries mults restarts
 *   prep is 0 (plain), 1 (TW) or 100 a + c (Hashimoto).  calls counts XL calls; restarts counts the
 *   choices of the flat (for Hashimoto, of w: a restart makes one call per root of step 4).
 * For Hashimoto a line "# H ..." first reports the setup: r, dim K2, the dimension it needs, and
 * the shape check of the restricted equations on random flats (violations must be 0).
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

/* The linear form B_A(v, .) of the polar form of A (upper triangular), as a row. */
static void polar_row(uint8_t A[MAXN][MAXN], const uint8_t* v, uint8_t* row) {
    for (int i = 0; i < N; i++) {
        uint8_t a = 0;
        for (int j = 0; j < N; j++) {
            if (j != i) {
                a ^= MUL[j > i ? A[i][j] : A[j][i]][v[j]];
            }
        }
        row[i] = a;
    }
}

/* A basis of the solution space of rows[0..nr) . x = 0; returns its dimension. */
static int kernel_basis(uint8_t rows[][MAXN], int nr, uint8_t basis[][MAXN]) {
    static _Thread_local uint8_t A[MAXN * MAXM][MAXN];
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
    int k = 0;
    for (int c = 0; c < N; c++) {
        if (is_piv[c]) {
            continue;
        }
        memset(basis[k], 0, MAXN);
        basis[k][c] = 1;
        for (int i = 0; i < np; i++) {
            basis[k][piv[i]] = A[i][c];
        }
        k++;
    }
    return k;
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
/* Restrict the equations e0..e1 of S to w + span(u): coefficients in the order of xl_build.  With
 * rhs == 0 only the forms are restricted (no right-hand side). */
static void restrict_range(const system_t* S, int e0, int e1, int dim, const uint8_t* w,
                           uint8_t u[][MAXN], uint8_t eqs[][MAXV * MAXV], const uint8_t* rhs) {
    static _Thread_local uint8_t A[MAXN][MAXN];
    for (int e = e0; e < e1; e++) {
        uint8_t* q = eqs[e - e0];
        int c = 0;
        memcpy(A, S->A[e], sizeof A);
        q[c++] = quad_eval(A, w) ^ (rhs ? rhs[e] : 0);
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

static void restrict_sys(const system_t* S, int e0, int dim, const uint8_t* w, uint8_t u[][MAXN],
                         uint8_t eqs[][MAXV * MAXV]) {
    restrict_range(S, e0, S->me, dim, w, u, eqs, S->rhs);
}

static uint8_t eval_restricted(const uint8_t* q, int d, const uint8_t* y) {
    int c = 0;
    uint8_t r = q[c++];
    for (int i = 0; i < d; i++) {
        r ^= MUL[q[c++]][y[i]];
    }
    for (int i = 0; i < d; i++) {
        for (int j = i; j < d; j++) {
            r ^= MUL[q[c++]][MUL[y[i]][y[j]]];
        }
    }
    return r;
}

enum { NRT = 16 };

/* The points y of F^d where the restricted equations eqs[0..ne) vanish, by enumeration.  Stores at
 * most cap of them; returns their number. */
static int enum_roots(uint8_t eqs[][MAXV * MAXV], int ne, int d, uint8_t roots[][MAXM], int cap) {
    long tot = 1;
    int nr = 0;
    uint8_t y[MAXM];
    for (int i = 0; i < d; i++) {
        tot *= Q;
    }
    for (long z = 0; z < tot; z++) {
        long t = z;
        int ok = 1;
        for (int i = 0; i < d; i++) {
            y[i] = (uint8_t)(t % Q);
            t /= Q;
        }
        for (int e = 0; e < ne && ok; e++) {
            ok = eval_restricted(eqs[e], d, y) == 0;
        }
        if (ok) {
            if (nr < cap) {
                memcpy(roots[nr], y, MAXM);
            }
            nr++;
        }
    }
    return nr;
}

/* ---------- Hashimoto's reduction ---------- */
typedef struct {
    int a, c, r, nk2, need, shape_bad;
    uint8_t X[MAXM][MAXN], Y[4][MAXN], K2[MAXN][MAXN];
} hsetup_t;

static hsetup_t HS;

static void random_combination(uint8_t basis[][MAXN], int k, uint8_t* v, rng_t* r) {
    memset(v, 0, MAXN);
    for (int l = 0; l < k; l++) {
        uint8_t f = rng_f(r);
        for (int i = 0; i < N; i++) {
            v[i] ^= MUL[f][basis[l][i]];
        }
    }
}

/* Steps 1 and 2 of Hashimoto's algorithm for the system S.  Returns 0 on failure. */
static int h_setup(const system_t* S, int a, int c, int p1, rng_t* r) {
    static uint8_t rows[MAXN * MAXM][MAXN], B[MAXN][MAXN], z[MAXM][MAXN], all[MAXN][MAXN];
    static uint8_t eqs[MAXM][MAXV * MAXV], roots[NRT][MAXM];
    hsetup_t* H = &HS;
    H->a = a;
    H->c = c;
    H->r = S->me - a - c + 1;
    H->nk2 = 0;
    H->need = H->r + a - 1 + c + (p1 ? 1 : 0);
    H->shape_bad = -1;
    if (a < 1 || a > 3 || H->r < 2 || H->r + a > MAXM) {
        return 0;
    }
    /* Step 1: X totally singular for the forms 0..a-1 */
    for (int i = 0; i < H->r; i++) {
        int nr = 0, found = 0;
        for (int j = 0; j < i; j++) {
            for (int l = 0; l < a; l++) {
                polar_row((uint8_t (*)[MAXN])S->A[l], H->X[j], rows[nr++]);
            }
        }
        int kd = kernel_basis(rows, nr, B);
        if (kd < i + a + 1) {
            return 0;
        }
        for (int tries = 0; tries < 1000 && !found; tries++) {
            for (int k = 0; k <= a; k++) {
                random_combination(B, kd, z[k], r);
            }
            restrict_range(S, 0, a, a, z[0], z + 1, eqs, 0);
            int nroot = enum_roots(eqs, a, a, roots, NRT);
            if (nroot == 0) {
                continue;
            }
            int pick = (int)(rng_next(r) % (uint64_t)(nroot < NRT ? nroot : NRT));
            memcpy(H->X[i], z[0], MAXN);
            for (int k = 0; k < a; k++) {
                for (int l = 0; l < N; l++) {
                    H->X[i][l] ^= MUL[roots[pick][k]][z[k + 1][l]];
                }
            }
            found = rank_of(H->X, i + 1) == i + 1;
        }
        if (!found) {
            return 0;
        }
    }
    /* Step 2: K2 = vectors orthogonal to X for the polar forms 0..a-2; Y in K2 */
    int nr = 0;
    for (int i = 0; i < H->r; i++) {
        for (int l = 0; l < a - 1; l++) {
            polar_row((uint8_t (*)[MAXN])S->A[l], H->X[i], rows[nr++]);
        }
    }
    H->nk2 = kernel_basis(rows, nr, H->K2);
    int found = a == 1;
    for (int tries = 0; tries < 100 && !found; tries++) {
        memcpy(all, H->X, (size_t)H->r * MAXN);
        for (int j = 0; j < a - 1; j++) {
            random_combination(H->K2, H->nk2, H->Y[j], r);
            memcpy(all[H->r + j], H->Y[j], MAXN);
        }
        found = rank_of(all, H->r + a - 1) == H->r + a - 1;
    }
    if (!found) {
        return 0;
    }
    /* Shape check: on w + span(X, Y), w in K2, the equations 0..a-2 do not involve X, and
     * equation a-1 has no monomial of degree 2 in X. */
    int d = H->r + a - 1;
    H->shape_bad = 0;
    for (int trial = 0; trial < 20; trial++) {
        uint8_t w[MAXN];
        random_combination(H->K2, H->nk2, w, r);
        restrict_range(S, 0, a, d, w, all, eqs, S->rhs);
        for (int l = 0; l < a; l++) {
            int cc = 1 + d;
            for (int i = 0; i < H->r; i++) {
                if (l < a - 1) {
                    H->shape_bad += eqs[l][1 + i] != 0;
                }
            }
            for (int i = 0; i < d; i++) {
                for (int j = i; j < d; j++, cc++) {
                    int xi = i < H->r, xj = j < H->r;
                    if ((l < a - 1 && (xi || xj)) || (l == a - 1 && xi && xj)) {
                        H->shape_bad += eqs[l][cc] != 0;
                    }
                }
            }
        }
    }
    return 1;
}

/* Step 3 (a uniform w in K2), step 4 (the first a - 1 equations on w + span(Y)) and the linear
 * equation a - 1 on the flat over X, for each root; then a random affine subflat of dimension
 * r - 1 - g.  Fills w[k], u[k] for k < returned count. */
static int h_spaces(const system_t* S, int p1, int g, uint8_t w[][MAXN], uint8_t u[][MAXV][MAXN],
                    rng_t* r) {
    static _Thread_local uint8_t all[MAXN][MAXN], eqs[MAXM][MAXV * MAXV], roots[NRT][MAXM];
    static _Thread_local uint8_t A[MAXN][MAXN], h[MAXM][MAXN];
    const hsetup_t* H = &HS;
    int a = H->a, rr = H->r, dim = rr - 1 - g, nroot = 1, out = 0;
    uint8_t w0[MAXN];
    random_combination((uint8_t (*)[MAXN])H->K2, H->nk2, w0, r);
    if (p1) { /* a flat through 0 would contain the trivial solution */
        memcpy(all, H->X, (size_t)rr * MAXN);
        memcpy(all[rr], H->Y, (size_t)(a - 1) * MAXN);
        memcpy(all[rr + a - 1], w0, MAXN);
        if (rank_of(all, rr + a) != rr + a) {
            return -1;
        }
    }
    if (a > 1) {
        restrict_range(S, 0, a - 1, a - 1, w0, (uint8_t (*)[MAXN])H->Y, eqs, S->rhs);
        nroot = enum_roots(eqs, a - 1, a - 1, roots, NRT);
        nroot = nroot < NRT ? nroot : NRT;
    }
    memcpy(A, S->A[a - 1], sizeof A);
    for (int k = 0; k < nroot; k++) {
        uint8_t wp[MAXN], beta[MAXM];
        memcpy(wp, w0, MAXN);
        for (int j = 0; j < a - 1; j++) {
            for (int i = 0; i < N; i++) {
                wp[i] ^= MUL[roots[k][j]][H->Y[j][i]];
            }
        }
        /* f_{a-1}(wp + x) = f_{a-1}(wp) + B(wp, x) on span(X): sum beta_i x_i = gam */
        uint8_t gam = quad_eval(A, wp) ^ S->rhs[a - 1];
        int p = -1, nh = 0;
        for (int i = 0; i < rr; i++) {
            beta[i] = polar(A, wp, H->X[i]);
            if (beta[i] && p < 0) {
                p = i;
            }
        }
        if (p < 0) {
            continue;
        }
        uint8_t ip = INV[beta[p]];
        for (int i = 0; i < N; i++) {
            wp[i] ^= MUL[MUL[gam][ip]][H->X[p][i]];
        }
        for (int j = 0; j < rr; j++) {
            if (j == p) {
                continue;
            }
            uint8_t f = MUL[beta[j]][ip];
            for (int i = 0; i < N; i++) {
                h[nh][i] = H->X[j][i] ^ MUL[f][H->X[p][i]];
            }
            nh++;
        }
        random_combination(h, nh, w[out], r);
        for (int i = 0; i < N; i++) {
            w[out][i] ^= wp[i];
        }
        for (int j = 0; j < dim; j++) {
            random_combination(h, nh, u[out][j], r);
        }
        if (rank_of(u[out], dim) == dim) {
            out++;
        }
    }
    return out;
}

/* One restart: the flats to solve (1 for plain and TW), or -1 to retry. */
static int choose_spaces(const system_t* S, int prep, int p1, int g, uint8_t w[][MAXN],
                         uint8_t u[][MAXV][MAXN], rng_t* r) {
    if (prep >= 100) {
        return h_spaces(S, p1, g, w, u, r);
    }
    return choose_space(S, prep, g, w[0], u[0], r) < 0 ? -1 : 1;
}

/* Is s (after scaling for P1) a preimage of the target under the public map?  The preimage is
 * left in x. */
static int check_forgery(int p1, const uint8_t* s, uint8_t* x) {
    uint8_t y[MAXM];
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
    long calls, decided, sols, forg, restarts;
    double mults;
} stat_t;

static void run_calls(const system_t* S, int prep, int p1, int g, int D, long ncalls, double secs,
                      uint64_t seed, stat_t* out) {
    int e0 = prep >= 100 ? HS.a : prep, me = S->me - e0;
    int dim = prep >= 100 ? HS.r - 1 - g : me - g;
    int print = getenv("P1_PRINT") != 0;
    stat_t tot = {0, 0, 0, 0, 0, 0};
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
        stat_t st = {0, 0, 0, 0, 0, 0};
        long mycalls = 0; /* calls of this thread, for P1_PRINT */
        uint8_t w[NRT][MAXN], u[NRT][MAXV][MAXN], x[MAXV], s[MAXN], f[MAXN];
        uint8_t eqs[MAXM][MAXV * MAXV];
        for (;;) {
            long done;
#pragma omp atomic read
            done = tot.calls;
            if (done + st.calls >= ncalls || omp_get_wtime() - t0 > secs) {
                break;
            }
            for (int rep = 0; rep < 8; rep++) {
                int ns = choose_spaces(S, prep, p1, g, w, u, &r);
                if (ns < 0) {
                    continue;
                }
                st.restarts++;
                for (int k = 0; k < ns; k++) {
                    restrict_sys(S, e0, dim, w[k], u[k], eqs);
                    int res = xl_solve(&X, me, eqs, x, &st.mults, mat, piv, row);
                    st.calls++;
                    mycalls++;
                    st.decided += res != 2;
                    if (res != 1) {
                        continue;
                    }
                    memcpy(s, w[k], MAXN);
                    for (int j = 0; j < dim; j++) {
                        for (int i = 0; i < N; i++) {
                            s[i] ^= MUL[x[j]][u[k][j][i]];
                        }
                    }
                    int ok = 1; /* a solution of the system the attack solves? */
                    for (int e = 0; e < S->me; e++) {
                        static _Thread_local uint8_t A[MAXN][MAXN];
                        memcpy(A, S->A[e], sizeof A);
                        ok &= quad_eval(A, s) == S->rhs[e];
                    }
                    st.sols += ok;
                    int fg = ok && check_forgery(p1, s, f);
                    st.forg += fg;
                    if (fg && print) {
#pragma omp critical
                        {
                            fprintf(stderr, "F %d %d %d %d %ld ", prep, p1, g, omp_get_thread_num(),
                                    mycalls);
                            for (int i = 0; i < N; i++) {
                                fprintf(stderr, "%02x", f[i]);
                            }
                            fprintf(stderr, "\n");
                        }
                    }
                }
            }
#pragma omp atomic
            tot.calls += st.calls;
#pragma omp critical
            {
                tot.decided += st.decided;
                tot.sols += st.sols;
                tot.forg += st.forg;
                tot.restarts += st.restarts;
                tot.mults += st.mults;
            }
            st = (stat_t){0, 0, 0, 0, 0, 0};
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
        fprintf(stderr,
                "usage: %s q N M seed gmin gmax seconds_per_cell [max_columns [run_seed "
                "[attacks]]]\n",
                argv[0]);
        return 2;
    }
    int q = atoi(argv[1]);
    N = atoi(argv[2]);
    M = atoi(argv[3]);
    uint64_t seed = strtoull(argv[4], 0, 10);
    int gmin = atoi(argv[5]), gmax = atoi(argv[6]);
    double secs = atof(argv[7]);
    int tmax = argc > 8 ? atoi(argv[8]) : 1400; /* skip cells whose Macaulay matrix is wider */
    uint64_t rseed = argc > 9 ? strtoull(argv[9], 0, 10) : seed + 1;
    char attacks[256];
    snprintf(attacks, sizeof attacks, "%s", argc > 10 ? argv[10] : "p,t");
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
    for (char* tok = strtok(attacks, ","); tok; tok = strtok(0, ",")) {
        int prep, ha = 0, hc[2] = {0, 0};
        if (tok[0] == 'p') {
            prep = 0;
        } else if (tok[0] == 't') {
            prep = 1;
        } else if (tok[0] == 'h' && sscanf(tok + 1, "%d.%d.%d", &ha, &hc[0], &hc[1]) == 3) {
            prep = 100 * ha;
        } else {
            fprintf(stderr, "bad attack %s\n", tok);
            return 2;
        }
        for (int p1 = 0; p1 < 2; p1++) {
            int pr = prep;
            if (prep >= 100 && hc[p1] < 0) { /* h<a>.<c>.-1: no P1 run, and so on */
                continue;
            }
            if (prep >= 100) {
                rng_t hr;
                rng_seed(&hr, rseed * 7919ULL + (uint64_t)p1);
                int ok = h_setup(&S[p1], ha, hc[p1], p1, &hr);
                printf("# H %d %d %d a=%d c=%d p1=%d r=%d dimK2=%d need=%d shape_violations=%d%s\n",
                       q, N, M, ha, hc[p1], p1, HS.r, HS.nk2, HS.need, HS.shape_bad,
                       ok ? (HS.nk2 >= HS.need ? "" : " CONDITION FAILS") : " SETUP FAILED");
                fflush(stdout);
                if (!ok) {
                    continue;
                }
                pr = 100 * ha + hc[p1];
            }
            for (int g = gmin; g <= gmax; g++) {
                int me = prep >= 100 ? S[p1].me - ha : S[p1].me - prep;
                int dim = prep >= 100 ? HS.r - 1 - g : me - g;
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
                    run_calls(&S[p1], pr, p1, g, D, 24, 1e9, rseed + 76, &st);
                    if (st.decided * 10 >= st.calls * 9) {
                        break;
                    }
                }
                if (D > MAXD) {
                    continue;
                }
                run_calls(&S[p1], pr, p1, g, D, 1L << 40, secs, rseed, &st);
                printf("@ %d %d %d %d %d %d %d %d %d %d %ld %ld %ld %ld %.6g %ld\n", q, N, M, pr,
                       p1, g, me, dim, D, mono_count(dim, D), st.calls, st.decided, st.sols,
                       st.forg, st.mults, st.restarts);
                fflush(stdout);
            }
        }
    }
    return 0;
}
