/* Toy forgery experiments for lean/docs/security/ompr-shift-algebra.md, section 4.1 (C1).
 *
 * A toy UOV key (N, M) over F_q, q = 16 or 256.  Two forgery attacks by hybrid XL:
 *
 *   direct:  P(s) = h.  Fix N - M + j coordinates at random, solve M quadrics in n = M - j
 *            variables by XL at degree D (dense elimination of the Macaulay matrix).
 *   C1:      shifts lambda_a * c.  Solve pi_c(P(s)) = pi_c(h): M - 1 quadrics in n = M - j
 *            variables.  A solution has P(s) = h + mu * c; it is a forgery iff mu is one of the
 *            tau values lambda_a.
 *
 * For every j the program measures
 *   - the smallest degree at which XL decides a system (inconsistent, or one solution), on a
 *     sample of calls, against the degree predicted by the series (1-t^2)^m / (1-t)^(n+1)
 *     (first coefficient <= 0: the usual model; <= 1: what this XL needs);
 *   - on batches of calls at the measured degree: the fraction of calls with a solution, the
 *     field multiplications and the time per call, the law of mu over the solutions found, and
 *     for each tau the number of landings in a fixed list of tau values.
 * Work per forgery = total work / number of forgeries.  Every forgery is checked against the
 * public map.
 *
 * Build:  gcc -O3 -march=native -fopenmp -o c1_toy c1_toy.c -lm
 * Usage:  c1_toy q N M seed jmin jmax target_solutions max_seconds_per_batch [degree_slack]
 * The driver c1_experiments.py builds and runs it.
 */
#include <math.h>
#include <omp.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#ifdef __AVX2__
#include <immintrin.h>
#endif

/* ---------- field ---------- */
static int Q, QBITS;
static uint8_t MUL[256][256], INV[256];
static uint8_t NIB_LO[256][16], NIB_HI[256][16];

static void field_init(int q) {
    Q = q;
    QBITS = q == 16 ? 4 : 8;
    int poly = q == 16 ? 0x13 : 0x11B; /* x^4+x+1; x^8+x^4+x^3+x+1 (as in pqov) */
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
    for (int f = 0; f < q; f++) {
        for (int i = 0; i < 16; i++) {
            NIB_LO[f][i] = MUL[f][i];
            NIB_HI[f][i] = q == 256 ? MUL[f][i << 4] : 0;
        }
    }
}

/* dst ^= f * src; returns nothing, the caller counts n multiplications */
static void axpy(uint8_t* dst, const uint8_t* src, uint8_t f, size_t n) {
    size_t k = 0;
#ifdef __AVX2__
    const __m256i lo = _mm256_broadcastsi128_si256(_mm_loadu_si128((const __m128i*)NIB_LO[f]));
    const __m256i hi = _mm256_broadcastsi128_si256(_mm_loadu_si128((const __m128i*)NIB_HI[f]));
    const __m256i mask = _mm256_set1_epi8(0x0f);
    for (; k + 32 <= n; k += 32) {
        __m256i x = _mm256_loadu_si256((const __m256i*)(src + k));
        __m256i l = _mm256_and_si256(x, mask);
        __m256i h = _mm256_and_si256(_mm256_srli_epi16(x, 4), mask);
        __m256i r = _mm256_xor_si256(_mm256_shuffle_epi8(lo, l), _mm256_shuffle_epi8(hi, h));
        __m256i d = _mm256_loadu_si256((const __m256i*)(dst + k));
        _mm256_storeu_si256((__m256i*)(dst + k), _mm256_xor_si256(d, r));
    }
#endif
    const uint8_t* mt = MUL[f];
    for (; k < n; k++) {
        dst[k] ^= mt[src[k]];
    }
}

/* ---------- rng (xoshiro256**, seeded by splitmix64) ---------- */
typedef struct {
    uint64_t s[4];
} Rng;
static uint64_t splitmix(uint64_t* x) {
    uint64_t z = (*x += 0x9E3779B97F4A7C15ULL);
    z = (z ^ (z >> 30)) * 0xBF58476D1CE4E5B9ULL;
    z = (z ^ (z >> 27)) * 0x94D049BB133111EBULL;
    return z ^ (z >> 31);
}
static void rng_seed(Rng* r, uint64_t a, uint64_t b) {
    uint64_t x = a * 0x2545F4914F6CDD1DULL + b + 1;
    for (int i = 0; i < 4; i++) {
        r->s[i] = splitmix(&x);
    }
}
static uint64_t rotl(uint64_t x, int k) { return (x << k) | (x >> (64 - k)); }
static uint64_t rng_next(Rng* r) {
    uint64_t *s = r->s, res = rotl(s[1] * 5, 7) * 9, t = s[1] << 17;
    s[2] ^= s[0];
    s[3] ^= s[1];
    s[1] ^= s[2];
    s[0] ^= s[3];
    s[2] ^= t;
    s[3] = rotl(s[3], 45);
    return res;
}
static uint8_t rng_fe(Rng* r) { return (uint8_t)(rng_next(r) >> 32) & (uint8_t)(Q - 1); }

/* ---------- toy UOV key ---------- */
#define MAXN 40
#define MAXM 16
static int N, M, V;
/* public map: PUB[k][i][j], i <= j: coefficient of s_i s_j in P_k */
static uint8_t PUB[MAXM][MAXN][MAXN];

static void keygen(Rng* r) {
    static uint8_t F[MAXM][MAXN][MAXN], O[MAXN][MAXM], T[MAXN][MAXN];
    memset(F, 0, sizeof F);
    memset(T, 0, sizeof T);
    for (int i = 0; i < V; i++) {
        for (int j = 0; j < M; j++) {
            O[i][j] = rng_fe(r);
        }
    }
    for (int k = 0; k < M; k++) {
        for (int i = 0; i < V; i++) { /* no oil-oil terms */
            for (int j = i; j < N; j++) {
                F[k][i][j] = rng_fe(r);
            }
        }
    }
    for (int i = 0; i < N; i++) {
        T[i][i] = 1;
    }
    for (int i = 0; i < V; i++) {
        for (int j = 0; j < M; j++) {
            T[i][V + j] = O[i][j];
        }
    }
    /* P_k(s) = F_k(T s): PUB_k = upper-triangular form of T^t F_k T */
    for (int k = 0; k < M; k++) {
        static uint8_t FT[MAXN][MAXN], G[MAXN][MAXN];
        for (int i = 0; i < N; i++) {
            for (int j = 0; j < N; j++) {
                uint8_t acc = 0;
                for (int a = 0; a < N; a++) {
                    acc ^= MUL[F[k][i][a]][T[a][j]];
                }
                FT[i][j] = acc;
            }
        }
        for (int i = 0; i < N; i++) {
            for (int j = 0; j < N; j++) {
                uint8_t acc = 0;
                for (int a = 0; a < N; a++) {
                    acc ^= MUL[T[a][i]][FT[a][j]];
                }
                G[i][j] = acc;
            }
        }
        for (int i = 0; i < N; i++) {
            for (int j = i; j < N; j++) {
                PUB[k][i][j] = i == j ? G[i][i] : (G[i][j] ^ G[j][i]);
            }
        }
    }
    /* sanity: P vanishes on the oil space {(O x, x)} */
    for (int t = 0; t < 20; t++) {
        uint8_t x[MAXM], s[MAXN];
        for (int j = 0; j < M; j++) {
            x[j] = rng_fe(r);
        }
        for (int i = 0; i < V; i++) {
            uint8_t acc = 0;
            for (int j = 0; j < M; j++) {
                acc ^= MUL[O[i][j]][x[j]];
            }
            s[i] = acc;
        }
        for (int j = 0; j < M; j++) {
            s[V + j] = x[j];
        }
        for (int k = 0; k < M; k++) {
            uint8_t acc = 0;
            for (int i = 0; i < N; i++) {
                for (int j = i; j < N; j++) {
                    acc ^= MUL[PUB[k][i][j]][MUL[s[i]][s[j]]];
                }
            }
            if (acc) {
                fprintf(stderr, "keygen: P does not vanish on the oil space\n");
                exit(1);
            }
        }
    }
}

static void eval_pub(const uint8_t* s, uint8_t* out) {
    for (int k = 0; k < M; k++) {
        uint8_t acc = 0;
        for (int i = 0; i < N; i++) {
            if (!s[i]) {
                continue;
            }
            uint8_t t = 0;
            for (int j = i; j < N; j++) {
                t ^= MUL[PUB[k][i][j]][s[j]];
            }
            acc ^= MUL[s[i]][t];
        }
        out[k] = acc;
    }
}

/* ---------- quadratic systems in n variables ----------
 * term layout: 0 = constant, 1 + i = x_i, tq(n, i, j) = x_i x_j (i <= j) */
static int nterms(int n) { return 1 + n + n * (n + 1) / 2; }
static int tq(int n, int i, int j) { return 1 + n + i * n - i * (i - 1) / 2 + (j - i); }

/* P(a + sum x_i e_{N-n+i}) - h for the M public quadrics: polys[k * nterms(n) + t] */
static void restrict_system(const uint8_t* a, int n, const uint8_t* h, uint8_t* polys) {
    int nt = nterms(n), off = N - n;
    uint8_t pa[MAXM];
    eval_pub(a, pa); /* a is zero on the last n coordinates */
    for (int k = 0; k < M; k++) {
        uint8_t* p = polys + k * nt;
        p[0] = pa[k] ^ h[k];
        for (int i = 0; i < n; i++) {
            uint8_t acc = 0; /* B_k(a, e_{off+i}) */
            for (int l = 0; l < off; l++) {
                acc ^= MUL[PUB[k][l][off + i]][a[l]];
            }
            p[1 + i] = acc;
            for (int j = i; j < n; j++) {
                p[tq(n, i, j)] = PUB[k][off + i][off + j];
            }
        }
    }
}

/* ---------- XL context for (n, D) ---------- */
typedef struct {
    int n, D, T, U, nt;
    int* prod;   /* prod[u * nt + t] = column of (multiplier u) * (term t) */
    int* lincol; /* lincol[i] = column of x_i; constant is column T - 1 */
} Ctx;

static long binom(int a, int b) {
    if (b < 0 || b > a) {
        return 0;
    }
    long r = 1;
    for (int i = 1; i <= b; i++) {
        r = r * (a - b + i) / i;
    }
    return r;
}

/* monomials as exponent vectors packed 4 bits per variable (n <= 16, degree <= 15) */
static int cmp_u64(const void* a, const void* b) {
    uint64_t x = *(const uint64_t*)a, y = *(const uint64_t*)b;
    return x < y ? -1 : x > y;
}
typedef struct {
    uint64_t key;
    int idx;
} KeyIdx;
static int cmp_ki(const void* a, const void* b) { return cmp_u64(a, b); }

static void gen_mons(int n, int d, int pos, uint64_t cur, uint64_t* out, int* cnt) {
    if (pos == n - 1) {
        out[(*cnt)++] = cur | ((uint64_t)d << (4 * pos));
        return;
    }
    for (int e = 0; e <= d; e++) {
        gen_mons(n, d - e, pos + 1, cur | ((uint64_t)e << (4 * pos)), out, cnt);
    }
}

static Ctx* ctx_new(int n, int D) {
    Ctx* c = calloc(1, sizeof *c);
    c->n = n;
    c->D = D;
    c->nt = nterms(n);
    c->T = (int)binom(n + D, D);
    c->U = (int)binom(n + D - 2, D - 2);
    uint64_t* mons = malloc(sizeof(uint64_t) * (size_t)c->T);
    int cnt = 0;
    for (int d = D; d >= 0; d--) { /* columns: degree descending, constant last */
        if (n == 0) {
            if (d == 0) {
                mons[cnt++] = 0;
            }
            continue;
        }
        gen_mons(n, d, 0, 0, mons, &cnt);
    }
    KeyIdx* ki = malloc(sizeof(KeyIdx) * (size_t)c->T);
    for (int i = 0; i < c->T; i++) {
        ki[i].key = mons[i];
        ki[i].idx = i;
    }
    qsort(ki, (size_t)c->T, sizeof(KeyIdx), cmp_ki);
    uint64_t* terms = malloc(sizeof(uint64_t) * (size_t)c->nt);
    terms[0] = 0;
    for (int i = 0; i < n; i++) {
        terms[1 + i] = (uint64_t)1 << (4 * i);
        for (int j = i; j < n; j++) {
            terms[tq(n, i, j)] = ((uint64_t)1 << (4 * i)) + ((uint64_t)1 << (4 * j));
        }
    }
    c->prod = malloc(sizeof(int) * (size_t)c->U * (size_t)c->nt);
    c->lincol = malloc(sizeof(int) * (size_t)(n + 1));
    int first_mult = c->T - c->U; /* multipliers: the monomials of degree <= D - 2 */
    for (int u = 0; u < c->U; u++) {
        for (int t = 0; t < c->nt; t++) {
            uint64_t key = mons[first_mult + u] + terms[t];
            KeyIdx* f = bsearch(&key, ki, (size_t)c->T, sizeof(KeyIdx), cmp_ki);
            c->prod[u * c->nt + t] = f->idx;
        }
    }
    for (int i = 0; i < n; i++) {
        uint64_t key = (uint64_t)1 << (4 * i);
        KeyIdx* f = bsearch(&key, ki, (size_t)c->T, sizeof(KeyIdx), cmp_ki);
        c->lincol[i] = f->idx;
    }
    free(mons);
    free(ki);
    free(terms);
    return c;
}

enum { INCONS = 0, UNIQUE = 1, UNDET = 2 };

typedef struct {
    uint8_t* A;
    uint8_t** row;
    size_t cap, rcap;
    double mults; /* field multiplications in eliminations */
    long calls;
} Work;

/* XL at the degree of cx on m quadrics; on UNIQUE the solution is written to sol */
static int xl(const Ctx* cx, const uint8_t* polys, int m, uint8_t* sol, Work* w) {
    int n = cx->n, T = cx->T, nt = cx->nt;
    w->calls++;
    if (n == 0) {
        for (int k = 0; k < m; k++) {
            if (polys[k]) {
                return INCONS;
            }
        }
        return UNIQUE;
    }
    size_t R = (size_t)m * (size_t)cx->U;
    if (R * (size_t)T > w->cap) {
        free(w->A);
        w->cap = R * (size_t)T;
        w->A = malloc(w->cap);
    }
    if (R > w->rcap) {
        free(w->row);
        w->rcap = R;
        w->row = malloc(sizeof(uint8_t*) * R);
    }
    memset(w->A, 0, R * (size_t)T);
    uint8_t** row = w->row;
    for (size_t r = 0; r < R; r++) {
        row[r] = w->A + r * (size_t)T;
    }
    for (int u = 0; u < cx->U; u++) {
        for (int k = 0; k < m; k++) {
            uint8_t* a = row[(size_t)u * (size_t)m + (size_t)k];
            const uint8_t* p = polys + k * nt;
            const int* pr = cx->prod + u * nt;
            for (int t = 0; t < nt; t++) {
                a[pr[t]] = p[t];
            }
        }
    }
    size_t rank = 0;
    int nlin = 0, linrow[32], linpiv[32];
    for (int col = 0; col < T && rank < R; col++) {
        size_t p = rank;
        while (p < R && !row[p][col]) {
            p++;
        }
        if (p == R) {
            continue;
        }
        uint8_t* t = row[p];
        row[p] = row[rank];
        row[rank] = t;
        uint8_t* pr = row[rank];
        size_t len = (size_t)(T - col);
        if (pr[col] != 1) {
            const uint8_t* mt = MUL[INV[pr[col]]];
            for (size_t k = (size_t)col; k < (size_t)T; k++) {
                pr[k] = mt[pr[k]];
            }
            w->mults += (double)len;
        }
        for (size_t r = p + 1; r < R; r++) {
            if (row[r][col]) {
                axpy(row[r] + col, pr + col, row[r][col], len);
                w->mults += (double)len;
            }
        }
        if (col == T - 1) {
            return INCONS; /* the polynomial 1 */
        }
        if (col >= T - 1 - n) {
            linrow[nlin] = (int)rank;
            linpiv[nlin] = col;
            nlin++;
        }
        rank++;
    }
    if (nlin < n) {
        return UNDET;
    }
    /* n linear polynomials with distinct leading variables: back-substitute */
    uint8_t val[32];
    for (int i = nlin - 1; i >= 0; i--) {
        const uint8_t* r = row[linrow[i]];
        uint8_t acc = r[T - 1];
        for (int c2 = linpiv[i] + 1; c2 < T - 1; c2++) {
            if (r[c2]) {
                acc ^= MUL[r[c2]][val[c2 - (T - 1 - n)]];
            }
        }
        val[linpiv[i] - (T - 1 - n)] = acc;
    }
    for (int i = 0; i < n; i++) {
        sol[i] = val[cx->lincol[i] - (T - 1 - n)];
    }
    /* check: linear polynomials of an inconsistent ideal can also show up */
    for (int k = 0; k < m; k++) {
        const uint8_t* p = polys + k * nt;
        uint8_t acc = p[0];
        for (int i = 0; i < n; i++) {
            acc ^= MUL[p[1 + i]][sol[i]];
            for (int j = i; j < n; j++) {
                acc ^= MUL[p[tq(n, i, j)]][MUL[sol[i]][sol[j]]];
            }
        }
        if (acc) {
            return INCONS;
        }
    }
    return UNIQUE;
}

/* all solutions: XL, and on UNDET branch on the last variable (several solutions, or D too
 * small).  cxs[n] is the context for n variables.  Calls emit(sol, n0, arg) per solution. */
typedef void (*Emit)(const uint8_t* sol, void* arg);
static void solve_all(Ctx** cxs, const uint8_t* polys, int n, int m, uint8_t* sol, int n0, Work* w,
                      long* undet, Emit emit, void* arg) {
    int st = xl(cxs[n], polys, m, sol, w);
    if (st == INCONS) {
        return;
    }
    if (st == UNIQUE) {
        emit(sol, arg);
        return;
    }
    (*undet)++;
    int nt = nterms(n), nt1 = nterms(n - 1);
    uint8_t* sub = malloc((size_t)m * (size_t)nt1);
    for (int v = 0; v < Q; v++) {
        uint8_t v2 = MUL[v][v];
        for (int k = 0; k < m; k++) {
            const uint8_t* p = polys + k * nt;
            uint8_t* s = sub + k * nt1;
            s[0] = p[0] ^ MUL[p[1 + n - 1]][v] ^ MUL[p[tq(n, n - 1, n - 1)]][v2];
            for (int i = 0; i < n - 1; i++) {
                s[1 + i] = p[1 + i] ^ MUL[p[tq(n, i, n - 1)]][v];
                for (int j = i; j < n - 1; j++) {
                    s[tq(n - 1, i, j)] = p[tq(n, i, j)];
                }
            }
        }
        sol[n - 1] = (uint8_t)v;
        solve_all(cxs, sub, n - 1, m, sol, n0, w, undet, emit, arg);
    }
    free(sub);
}

/* ---------- the series (1 - t^2)^m / (1 - t)^(n + 1) ---------- */
/* first d whose coefficient is <= thr.  thr = 0 is the usual model.  thr = 1 is what this XL
 * needs: with corank 1 it still gets n linear polynomials, hence one candidate point to test. */
static int operating_degree(int n, int m, int thr) {
    for (int d = 2; d <= 60; d++) {
        long double c = 0, b = 1; /* b = (-1)^i binom(m, i) */
        for (int i = 0; 2 * i <= d && i <= m; i++) {
            long double t = 1; /* binom(n + d - 2i, d - 2i) */
            for (int l = 1; l <= d - 2 * i; l++) {
                t = t * (n + l) / l;
            }
            c += b * t;
            b = -b * (m - i) / (i + 1);
        }
        if (c <= thr + 0.5) {
            return d;
        }
    }
    return -1;
}

/* ---------- experiment ---------- */
typedef struct {
    uint8_t h[MAXM], c[MAXM], cinv;
    int piv;
} Target;

/* projected system: for k != piv, E_k + (c_k / c_piv) E_piv; M - 1 polynomials */
static void project(const Target* tg, const uint8_t* polys, int nt, uint8_t* proj) {
    const uint8_t* pp = polys + tg->piv * nt;
    int o = 0;
    for (int k = 0; k < M; k++) {
        if (k == tg->piv) {
            continue;
        }
        const uint8_t* mt = MUL[MUL[tg->c[k]][tg->cinv]];
        const uint8_t* p = polys + k * nt;
        uint8_t* d = proj + o * nt;
        for (int t = 0; t < nt; t++) {
            d[t] = p[t] ^ mt[pp[t]];
        }
        o++;
    }
}

typedef struct {
    const Target* tg;
    const uint8_t* a;
    int n;
    int projected;
    long nsol;
    long hist[256];
    long bad;
} EmitArg;

static void emit_solution(const uint8_t* sol, void* argp) {
    EmitArg* e = argp;
    uint8_t s[MAXN], y[MAXM];
    memcpy(s, e->a, (size_t)N);
    for (int i = 0; i < e->n; i++) {
        s[N - e->n + i] = sol[i];
    }
    eval_pub(s, y);
    /* P(s) = h + mu c ? */
    uint8_t mu = MUL[y[e->tg->piv] ^ e->tg->h[e->tg->piv]][e->tg->cinv];
    int ok = 1;
    for (int k = 0; k < M; k++) {
        if ((y[k] ^ e->tg->h[k]) != MUL[mu][e->tg->c[k]]) {
            ok = 0;
        }
    }
    if (!e->projected && mu) {
        ok = 0;
    }
    if (!ok) {
        e->bad++;
        return;
    }
    e->nsol++;
    e->hist[mu]++;
}

typedef struct {
    long calls_top, calls_all, undet, nsol, bad, with_sol;
    long hist[256];
    double mults, secs;
} Batch;

/* calls b0 .. b0 + B - 1 of the stream `seed`; results are added to *out */
static void run_batch(const Target* tg, int n, int m_proj, int D, long b0, long B, uint64_t seed,
                      Batch* out) {
    Ctx* cxs[MAXM + 1];
    for (int i = 0; i <= n; i++) {
        cxs[i] = ctx_new(i, D);
    }
    double t0 = omp_get_wtime();
#pragma omp parallel
    {
        Work w = {0};
        EmitArg ea = {0};
        long undet = 0, with_sol = 0;
        int nt = nterms(n);
        uint8_t *polys = malloc((size_t)M * (size_t)nt), *proj = malloc((size_t)M * (size_t)nt);
        uint8_t a[MAXN], sol[MAXM];
        ea.tg = tg;
        ea.n = n;
        ea.projected = m_proj;
        ea.a = a;
#pragma omp for schedule(dynamic, 16)
        for (long b = b0; b < b0 + B; b++) {
            Rng r;
            rng_seed(&r, seed, (uint64_t)b);
            memset(a, 0, sizeof a);
            for (int i = 0; i < N - n; i++) {
                a[i] = rng_fe(&r);
            }
            restrict_system(a, n, tg->h, polys);
            long before = ea.nsol;
            if (m_proj) {
                project(tg, polys, nt, proj);
                solve_all(cxs, proj, n, M - 1, sol, n, &w, &undet, emit_solution, &ea);
            } else {
                solve_all(cxs, polys, n, M, sol, n, &w, &undet, emit_solution, &ea);
            }
            if (ea.nsol > before) {
                with_sol++;
            }
        }
#pragma omp critical
        {
            out->calls_all += w.calls;
            out->undet += undet;
            out->nsol += ea.nsol;
            out->bad += ea.bad;
            out->with_sol += with_sol;
            out->mults += w.mults;
            for (int i = 0; i < Q; i++) {
                out->hist[i] += ea.hist[i];
            }
        }
        free(polys);
        free(proj);
        free(w.A);
        free(w.row);
    }
    out->calls_top += B;
    out->secs += omp_get_wtime() - t0;
    for (int i = 0; i <= n; i++) {
        free(cxs[i]->prod);
        free(cxs[i]->lincol);
        free(cxs[i]);
    }
}

/* smallest degree at which XL decides, on K sample systems; hist[d] counts; returns the
 * smallest degree deciding at least 95% of the sample, and the mean time of one call there */
static int min_degree(const Target* tg, int n, int m_proj, int K, int Dmax, uint64_t seed,
                      long* hist, double* secs_at) {
    int nt = nterms(n);
    memset(hist, 0, sizeof(long) * 64);
    int* need = malloc(sizeof(int) * (size_t)K);
    for (int i = 0; i < K; i++) {
        need[i] = 0;
    }
    int result = -1;
    for (int D = 2; D <= Dmax; D++) {
        Ctx* cx = ctx_new(n, D);
        long decided = 0;
        double t0 = omp_get_wtime();
#pragma omp parallel
        {
            Work w = {0};
            uint8_t *polys = malloc((size_t)M * (size_t)nt), *proj = malloc((size_t)M * (size_t)nt);
            uint8_t a[MAXN], sol[MAXM];
#pragma omp for schedule(dynamic, 1) reduction(+ : decided)
            for (int b = 0; b < K; b++) {
                if (need[b]) {
                    decided++;
                    continue;
                }
                Rng r;
                rng_seed(&r, seed, (uint64_t)b);
                memset(a, 0, sizeof a);
                for (int i = 0; i < N - n; i++) {
                    a[i] = rng_fe(&r);
                }
                restrict_system(a, n, tg->h, polys);
                int st;
                if (m_proj) {
                    project(tg, polys, nt, proj);
                    st = xl(cx, proj, M - 1, sol, &w);
                } else {
                    st = xl(cx, polys, M, sol, &w);
                }
                if (st != UNDET) {
                    need[b] = D;
                    decided++;
                }
            }
            free(polys);
            free(proj);
            free(w.A);
            free(w.row);
        }
        double dt = omp_get_wtime() - t0;
        free(cx->prod);
        free(cx->lincol);
        free(cx);
        if (result < 0 && decided * 100 >= 95L * K) {
            result = D;
            *secs_at = dt;
        }
        if (decided == K) {
            break;
        }
        if (result >= 0 && D >= result + 1) {
            break;
        }
    }
    for (int i = 0; i < K; i++) {
        hist[need[i]]++;
    }
    free(need);
    return result;
}

int main(int argc, char** argv) {
    if (argc < 9) {
        fprintf(stderr, "usage: %s q N M seed jmin jmax target_solutions max_seconds [slack]\n",
                argv[0]);
        return 2;
    }
    int q = atoi(argv[1]);
    N = atoi(argv[2]);
    M = atoi(argv[3]);
    V = N - M;
    uint64_t seed = strtoull(argv[4], 0, 10);
    int jmin = atoi(argv[5]), jmax = atoi(argv[6]);
    double target = atof(argv[7]), maxsec = atof(argv[8]);
    int slack = argc > 9 ? atoi(argv[9]) : 0;
    if ((q != 16 && q != 256) || N >= MAXN || M >= MAXM || M < 3) {
        fprintf(stderr, "bad parameters\n");
        return 2;
    }
    field_init(q);
    Rng r;
    rng_seed(&r, seed, 0xabcdef);
    keygen(&r);
    Target tg;
    memset(&tg, 0, sizeof tg);
    for (int k = 0; k < M; k++) {
        tg.h[k] = rng_fe(&r);
    }
    do {
        for (int k = 0; k < M; k++) {
            tg.c[k] = rng_fe(&r);
        }
        tg.piv = (int)(rng_next(&r) % (uint64_t)M);
    } while (!tg.c[tg.piv]);
    tg.cinv = INV[tg.c[tg.piv]];
    /* a fixed random order of F: the list of tau values is its first tau entries */
    uint8_t order[256];
    for (int i = 0; i < q; i++) {
        order[i] = (uint8_t)i;
    }
    for (int i = q - 1; i > 0; i--) {
        int j = (int)(rng_next(&r) % (uint64_t)(i + 1));
        uint8_t t = order[i];
        order[i] = order[j];
        order[j] = t;
    }
    int threads = omp_get_max_threads();
    printf("# q=%d N=%d M=%d V=%d seed=%llu threads=%d\n", q, N, M, V, (unsigned long long)seed,
           threads);
    printf("# columns: kind j n eqs D_model D_meas(95%%) hist | calls with_sol sols undet "
           "mults/call sec/call chi2(df)\n");
    for (int j = jmin; j <= jmax; j++) {
        int n = M - j;
        if (n < 1) {
            break;
        }
        for (int proj = 0; proj <= 1; proj++) {
            int m = proj ? M - 1 : M;
            int Dm = operating_degree(n, m, 0), D1 = operating_degree(n, m, 1);
            if (m <= n) {
                printf("%s j=%d n=%d eqs=%d: not overdetermined, skipped\n",
                       proj ? "C1    " : "direct", j, n, m);
                continue;
            }
            if (Dm < 0 || binom(n + Dm, Dm) > 6000) {
                printf("%s j=%d n=%d eqs=%d D_model=%d: too large, skipped\n",
                       proj ? "C1    " : "direct", j, n, m, Dm);
                continue;
            }
            long hist[64];
            double sec_md = 0;
            int K = binom(n + Dm, Dm) > 1500 ? 48 : 240;
            int Dmeas = min_degree(&tg, n, proj, K, Dm + 2, seed * 1000 + (uint64_t)(j * 2 + proj),
                                   hist, &sec_md);
            printf("%s j=%d n=%d eqs=%d D_model=%d D_model1=%d D_meas=%d hist:",
                   proj ? "C1    " : "direct", j, n, m, Dm, D1, Dmeas);
            for (int d = 0; d < 64; d++) {
                if (hist[d]) {
                    printf(" %d:%ld", d, hist[d]);
                }
            }
            /* batches at the measured degree (+ slack), doubling, until `target` solutions or
             * `maxsec` seconds */
            int D = (Dmeas > 0 ? Dmeas : Dm) + slack;
            Batch bt;
            memset(&bt, 0, sizeof bt);
            long B = 64L * threads;
            while (bt.nsol < target && bt.secs < maxsec) {
                run_batch(&tg, n, proj, D, bt.calls_top, B, seed * 7919 + (uint64_t)(j * 2 + proj),
                          &bt);
                if (bt.secs * 2 < maxsec) {
                    B *= 2;
                }
            }
            double chi2 = 0, e = (double)bt.nsol / q;
            if (proj && bt.nsol) {
                for (int i = 0; i < q; i++) {
                    chi2 += (bt.hist[i] - e) * (bt.hist[i] - e) / e;
                }
            }
            printf(" | D=%d calls=%ld with_sol=%ld sols=%ld bad=%ld undet=%ld mults/call=%.4g "
                   "sec/call=%.3g",
                   D, bt.calls_top, bt.with_sol, bt.nsol, bt.bad, bt.undet,
                   bt.mults / (double)bt.calls_top, bt.secs * threads / (double)bt.calls_top);
            if (proj) {
                printf(" chi2=%.1f(%d)", chi2, q - 1);
            }
            printf("\n");
            /* machine-readable line */
            printf("@ %d %d %d %d %d %d %d %d %d %ld %ld %ld %.6g %.6g", q, N, M, proj, j, Dm, D1,
                   Dmeas, D, bt.calls_top, bt.with_sol, bt.nsol, bt.mults, bt.secs * threads);
            if (proj) {
                printf(" land");
                long acc = 0;
                for (int t = 1; t <= q; t++) {
                    acc += bt.hist[order[t - 1]];
                    if (t == 1 || t == 2 || t == 4 || t == 8 || t == 16 || t == 17 || t == 32 ||
                        t == 64 || t == 128 || t == 256) {
                        printf(" %d:%ld", t, acc);
                    }
                }
            }
            printf("\n");
            fflush(stdout);
        }
    }
    return 0;
}
