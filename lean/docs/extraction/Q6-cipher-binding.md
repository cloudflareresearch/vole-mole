# Q6: binding of the `aes_ctr` leaf commitment against quantum adversaries (`ε_multi`)

Status: **[paper]**, with **[Lean]** for the counting and real-number cores and the numbers
(`lean/VoleMole/Seed/CipherBinding.lean`; check with
`cd lean && lake env lean VoleMole/Seed/CipherBinding.lean`; no `sorry`, no `axiom`). Part of
README §L9. Builds on Q1 (key-level compressed ideal cipher), Q2 (Lemma T, Theorem 7.1), Q4
(`S*`), Q5 (SE) and Q7 (Lemma K). Notation as in Q1: `N = 2^128`, `p = 1/(N(N−1))`,
`ι = (iv, twk)`, `x_c(ι) = iv ⊞ (c,0,0,twk)`, `f_ι(σ) = σ(x₀(ι)) ‖ σ(x₁(ι))`.

## 0. Verdict

The event to bound is Q1's
`Bad_T`: some `(w, iv)` in the H₄ database and some `twk ∈ T` have two distinct database keys
whose permutations agree on `{x₀(ι), x₁(ι)}`. Q2's `MULTI_end` and Q5's case (P) both imply it.

| target | result | confidence |
|---|---|---|
| **(a) mixed classical/quantum** | **Theorem 2.** Classical cipher work (simulator, honest parties; one *fetch* per key by Q7's Lemma K) enters the agreement count probability-additively, `Q_C·S/N`. Only the quantum queries pay the coherent `(Q_A√(S/N))²` term. SE at `Q_S = q = 2^{30}` is now `2^{−60.4}` (weak and strong), instead of vacuous. | medium-high |
| **(b) beyond 2^40** | **Theorem 1.** A level-free all-`q` replacement for Q1 Thms 5.1/5.2: `ε_multi ≤ 8|T|q₄²·E_Z/N + …` with `E_Z ≤ min(a², 1.0005a)`, `a = (4√2/3)Q_E^{3/2}/√N`. No `θ ≤ 1/2` condition, and the constant drops from `1.8·10⁷` to `≈ 484`. Q2's theorem is main-term-limited up to `q ≈ 2^{41.2}` and non-vacuous up to `q ≈ 2^{51.7}` (it was limited to about `2^{37}`). The list-binding route **does not help**: §6.1. Point-level/LZ route: not closed, and capped near `2^{53}`–`2^{56}` by current soundness bounds (§6.2). | high (Thm 1); high (list-binding negative); medium (point-level assessment) |
| **(c) obstruction** | **Theorem 3.** Theorem 1 is **tight**, up to constants, for every argument that uses only Q1's key-level abstraction ("a query is a unitary controlled on one key's register"). That abstraction admits full-value queries, and against those a real attack achieves `Ω(q₄²|T|·min(a,a²)/N)`. To go past `2^{52}` a proof must use that AES queries are *point evaluations*. The precise missing lemma is in §7.3. | high |

**New end-to-end numbers** (λ = 128, `d = 9`; Q2's main term is `Σ² = 200q²/N`):

| setting | before (Q1/Q2/Q5/Q7) | now |
|---|---|---|
| Q2, one proof, `q = 2^{30}` | `2^{−60.4}` (`ε_multi = 2^{−70.3}`) | `2^{−60.4}` (`ε_multi = 2^{−93.9}`) |
| Q2, `q = 2^{40}` | `2^{−6.2}` | `2^{−40.2}` |
| Q2, `q = 2^{45}` | vacuous | `2^{−23.3}` |
| Q2, `q = 2^{50}` | vacuous | `2^{−5.8}` |
| Q2, `q_E = 2^{40}`, hashes `2^{50}` | vacuous | `2^{−20.4}` (Σ²); `ε_multi ≈ 2^{−23.9}` |
| SE, `Q_S = 2^{20}`, `q = 2^{30}`, weak / strong | vacuous (Q5); Q7 Lemma K + Q1: `2^{−62.9}` / `2^{−55.8}` for `ε_bind` | `ε_bind = 2^{−90.3}` / `2^{−83.2}`; **total `2^{−60.4}` / `2^{−60.4}`** |
| SE, `Q_S = 2^{30}`, `q = 2^{30}`, weak / strong | vacuous (also with Lemma K + Q1) | `ε_bind = 2^{−77.7}` / `2^{−70.6}`; **total `2^{−60.4}` / `2^{−60.4}`** (unpunctured `Sim`: `2^{−59.4}`) |

The SE totals are Q5's `Σ_SE² = 2^{−60.4}` (with `Sim°`) plus the new `ε_bind^C`. `ε_rec'` and
`ε_Sim` (now `2^{−172}`, §8) are negligible.

---

## 1. Setting

**Oracles.** H₄ is a compressed random oracle with range `{0,1}^128`. The cipher is Q1's key-level
compressed oracle `S^IC`, or Q4's `S*` for a fixed shuffle `ρ` (§8). The database `D = (D_E, D₄)`.
For a basis database let

    Z(D_E) := { z : ∃ k ≠ k' in D_E with σ_k, σ_{k'} agreeing on {z, z ⊞ e₀} },
    Ẑ := Σ_D |Z(D_E)|·|D⟩⟨D|          (diagonal),     E_Z(ψ) := ⟨ψ|Ẑ|ψ⟩,
    Bad_T := { D : ∃ (w,iv) ∈ D₄, twk ∈ T: x₀(iv,twk) ∈ Z(D_E) }.

`E_Z` is the expected number of agreement points, in the quantum sense. Q1 Thm 5.2 controlled the
*amplitudes* `α_j` of the levels `|Z| ≥ j` by induction, which needs `θ ≤ 1/2`. Here a single
first-moment potential is enough, because the H₄ transition charges `|Z|` linearly and the levels
are orthogonal (§3, step 3).

**Counts.** `Q_A` = quantum (compressed) cipher queries, including any classical query that is
not treated as an insertion (§4). `Q_C` = classical insertions (Lemma K fetches on classical keys).
`S_t` = database size bound before step `t` (`≤ Q_A + Q_C`). `q₄` = all H₄ queries, counted as
quantum (Q2 §3.1 adds `2Q₂₁ + 1`).

## 2. Two local lemmas

**Lemma 2.1 (commutator with a diagonal weight).** Fix a key `k` and the rest `D_{−k}`. Let `g` be
diagonal on `D_k`, real, with `g(⊥) = 0`. Then for forward and inverse queries,

    ‖[g, cO_k]‖ ≤ 2√2·(E_{σ ← Sym} g(σ)²)^{1/2}.

*Proof.* `F = 1 − 2|w⟩⟨w|`, `w = (|⊥⟩ − |u⟩)/√2`, and `gw = −g|u⟩/√2`. Then
`[g,F] = −2(|gw⟩⟨w| − |w⟩⟨gw|)`, a real antisymmetric rank-2 operator of norm
`2(‖gw‖²‖w‖² − ⟨w,gw⟩²)^{1/2} ≤ 2‖gw‖ = √2‖gu‖`. Next, `cO_k = F O_k F` with `O_k` controlled on
`D_k`'s value basis, so `[g, O_k] = 0` and `[g, FOF] = [g,F]OF + FO[g,F]`. ∎

This is Q2 Lemma T step 5 with an indicator replaced by a general weight. For `g = 1_S` it gives
`2√(2μ)`. CM26's Lemma 5.2 does the same algebra for the point-level oracle.

**Lemma 2.2 (agreement moments).** Let `n_σ` be the number of points `z ∉ Z(D_{−k})` at which `σ`
agrees with some key of `D_{−k}` (`s` keys). Then

    E_σ n_σ ≤ s/(N−1),      E_σ n_σ² ≤ (1 + 4s/N)·s/(N−1).

*Proof.* For a fixed other key and `z`, agreement on the pair has probability `p` (Q1 (F1)), and
there are `N` values of `z`. That gives the first moment (Q1 (F2)). Second moment:
- for `z ∉ Z(D_{−k})`, two different keys cannot both agree with `σ` at `z`, since they would agree
  with each other;
- for `z ≠ z'`, prescribing the values at 3 distinct points (`z' = z ⊞ ±e₀`; `z ⊞ 2e₀ ≠ z`
  because the lane has size `2^32`) has probability `≤ 1/(N)₃`, and at 4 points `≤ 1/(N)₄`.

Summing gives the bound. Also `(√(i+n) − √i)² ≤ n` [**Lean** `sqrt_add_sub_sq_le`]. ∎

## 3. Theorem 1 (all `q`, quantum queries only)

**Theorem 1.** For any algorithm making `Q_E` forward or inverse cipher queries and `q₄` H₄
queries (both possibly in superposition), with arbitrary diagonal measurements in between,

    √Pr[Bad_T at the end]  ≤  Σ_{H₄ steps t} √(8|T|·E_Z(t)/N)  +  Σ_{cipher steps t} 2√2·√(S_t·q₄·|T|·p),
    E_Z(t)  ≤  min( a_t², (1 + 2^{−60})·a_t ),     a_t := 2√2·Σ_{s<t} √(S_s/(N−1)) ≤ (4√2/3)·Q_E^{3/2}/√(N−1).

In particular

    ε_multi ≤ ( q₄·√(8|T|·min(a², 1.0005a)/N) + 2√2·Q_E·√(Q_E q₄|T| p) )²   (+ ε_rec readback, already in Q2).

*Proof.*
1. **Amplitude regime.** Let `W = Ẑ^{1/2}`. On the block `(k, D_{−k})`, `W = √i₀ + g` with
   `i₀ = |Z(D_{−k})|`, `g = √(i₀+n̂) − √i₀`, `g(⊥) = 0` and `g² ≤ n̂`. By Lemmas 2.1 and 2.2,
   `‖[W, cO]‖ ≤ 2√2√(S/(N−1))`, since the query is block-diagonal in `(k, D_{−k})`. Hence
   `‖Wψ_{t+1}‖ ≤ ‖Wψ_t‖ + 2√2√(S_t/(N−1))`. Everything else commutes with `W`: H₄ and hash
   queries, adversary unitaries, and diagonal measurements such as `Ext` (which does not increase
   `E[W²]`). So `√E_Z ≤ a`.
2. **Count regime.** `⟨cOψ|Ẑ|cOψ⟩ − ⟨ψ|Ẑ|ψ⟩ = ⟨ψ|cO†[Ẑ,cO]|ψ⟩ ≤ ‖[n̂, cO_k]‖`. By Lemmas 2.1 and
   2.2 this is `≤ 2√2√((1+2^{−60})S/(N−1))`. Summing gives `E_Z ≤ (1+2^{−60})a`. This regime is
   better once `a > 1`, i.e. `Q_E ≳ 2^{42.4}`. It is the analogue of "finding `K` collisions costs
   `K^{2/3}N^{1/3}`".
3. **H₄ steps.** On the block `(w, D_{4,−w}, D_E)`: if `Bad` already holds with `D₄(w) = ⊥`, the
   step is neutral. Otherwise the non-⊥ bad set is `{iv : ∃twk, x₀(iv,twk) ∈ Z(D_E)}`, of density
   `≤ |T||Z(D_E)|/N`, so the block transition is `≤ 2√(2|T||Z|/N)` (DFMS Lemma 3.3; Lemma T step
   5). The blocks are orthogonal and preserved, so the squared norms add:
   `‖Bad·cO₄(1−Bad)ψ‖² ≤ (8|T|/N)·⟨(1−Bad)ψ|Ẑ|(1−Bad)ψ⟩ ≤ (8|T|/N)·E_Z`. This state-dependent sum
   of squares is what replaces Q1's `Σ_i √i·α_i` level sum.
4. **Cipher steps.** A new value `σ` creates `Bad` only by agreeing with one of `S` keys at one of
   `≤ q₄|T|` points `x₀(ι)`. That has density `≤ S q₄|T| p`, and Lemma T step 5 applies.
5. **Telescoping.** `‖Badψ_{t+1}‖ ≤ ‖Badψ_t‖ + ‖Bad·U_t(1−Bad)ψ_t‖` (CFHL Lemma 5.6;
   **[Lean]** `QROM.telescope`). ∎

**Remarks.**
- The only properties of the cipher oracle used are: queries are controlled on one key's register
  (Q1 §2); (F1); and Lemma 2.2's moments of a uniform permutation. Theorem 3 exploits exactly this.
- It also covers Q2's free-iv bound: `Pr[Z ≠ ∅] ≤ E_Z ≤ (32/9)Q_E³/(N−1)` (Q2 §6.3).
- For `S*` with a fixed `ρ`, the amplitude regime and steps 3–4 hold verbatim. They need only the
  first moment and the density `p` at fixed points, both exact for AGL(1)-whitening (Q4 Thm B).
  The count regime needs Lemma 2.2's second moment, which fails for adversarial `ρ`: AGL(1) is
  only 2-transitive. So for `q > 2^{42.4}` use `S^IC` plus Q4 Thm C. That costs
  `2^{−172} + L·q·δ`, which is negligible at these `q` for `L ≤ 2^{10}`.

## 4. Theorem 2 (mixed classical/quantum) — target (a)

### 4.1 The hybrid representation

Keep a classical set `S` of *frozen* keys. A key enters `S` at the first classical fetch under it
(Lemma K, Q7 §2.5). The oracle state is `(⊗_{k∉S} F_k)·Ψ_pur`: compressed off `S`, purified on
`S`.
- **Insertion of `k`** applies `F_k` once and puts `k` in `S`. This is a change of representation,
  exactly equivalent to the real oracle, because `F_k² = 1` and `S` is classical.
- **Queries on `k ∈ S`** are the purified `O_k`. They are diagonal, so they commute with every
  diagonal property and cost **zero** in any telescoping.
- **Queries on `k ∉ S`** are the compressed `F_kO_kF_k`.
- Frozen keys are always in the database (with their full permutation). `Ẑ`, `Bad`, `Ext` and the
  final measurement are read on this hybrid database. `Ext` and the bookkeeping of Q2/Q5 run in the
  same representation (§8).

### 4.2 The insertion identity

Write `ψ = |⊥⟩_k φ_⊥ + χ`, with `χ = Σ_σ |σ⟩φ_σ` and `Σ_σ φ_σ = 0`. Compressed states have no
`|u⟩` component (Q1 §2). For a diagonal `G` with `Δ_σ := G(σ,·) − G(⊥,·)`:

    ⟨F_kψ|G|F_kψ⟩ = ⟨ψ|G|ψ⟩ + E_σ⟨φ_⊥|Δ_σ|φ_⊥⟩ + 2Re (N!)^{−1/2} Σ_σ ⟨φ_⊥|Δ_σ|φ_σ⟩.

The `G(⊥)` part of the cross term vanishes because `Σ_σ φ_σ = 0`. By Cauchy–Schwarz,

    ⟨G⟩' ≤ ⟨G⟩ + g_k + 2√(g_k h_k),   g_k := E_σ⟨φ_⊥|Δ_σ|φ_⊥⟩,   h_k := ⟨χ||Δ||χ⟩.

**Lemma 4.1.** For `G = Ẑ`, `g_k ≤ S/(N−1)`. For `G = Bad`, `g_k ≤ S·q₄|T|·p`.

The `g`-term is the classical probability that a fresh uniform permutation creates an agreement
(or a bad iv-point agreement). The cross term `2√(gh)` is where Q7's remark — "classical queries
enjoy no advantage in Lemma T" — bites: with `h` up to `Pr`, the increment is the
amplitude-additive `2√(g·Pr)`. What rescues us is that `h_k` is the bad mass *carried by the key
`k` itself before it was frozen*. That is tiny when `k` is a key the adversary had no reason to
touch.

### 4.3 Combining the two kinds of step

**Lemma 4.3 (mixed telescoping) [Lean `mixed_combine`].** If `A_0 = 0`, `A_{t+1} ≤ A_t + a_t` at
quantum steps and `A_{t+1}² ≤ A_t² + b_t` at classical steps, then `A_T ≤ Σ a_t + √(Σ b_t)`.

Apply it to `A = √E_Z` (with `b_k = g_k + 2√(g_k h_k)`) and to `A = ‖Bad·ψ‖`.

### 4.4 Freshness: bounding `Σ h_k` for the simulator's keys

**Lemma 4.4 (pivotality) [Lean `pivotal_card_le_two`].** Each agreement point is pivotal for at
most two keys, so `Σ_k Δ_k^{Ẑ} ≤ 2Ẑ`. Here "pivotal for `k`" means every witness pair contains `k`.

**Lemma 4.5 (fresh and derived keys).** Let `η̃_k := ⟨ψ|Q_k Ẑ|ψ⟩ ≥ h_k`, the Ẑ-weighted mass on
"`k` is already a compressed database key".
1. A key drawn uniformly and independently of `ψ` (a `Sim°` co-path seed) has
   `E η̃_k ≤ (S/N)·E_Z`, since `Σ_k Q_k ≤ S` and `Q_k` commutes with `Ẑ`.
2. A key obtained as a measured output `σ_{k'}(x)` of an already frozen key `k'`, within the same
   `Prove` call, has `E η̃ ≤ 2(S/N)(E_Z + 2) + 2η̃_{k'}`. The first part comes from the `|u⟩`-branch
   of `k'`, whose output is uniform. The `+2` covers agreements of `k'` with the database, which
   is up to `O(1)` per point for AGL(1)-whitened `S*` (2-transitivity only). The second part comes
   from the `χ`-branch of `k'`, by `(x+y)² ≤ 2x² + 2y²`.

With GGM depth `≤ 12`, every key of a simulated proof has `E h ≤ 2^{15}(S/N)(E_Z + 2)`. By Cauchy–
Schwarz over all insertions [**Lean** `cross_terms_le`],

    X := Σ_k 2√(g_k h_k) ≤ 2√(Σ g)·√(Σ h) ≤ 2^{8.5}·G·√(E_Z+2) ≤ 2^9·G,   G := Q_C·S/(N−1),

and likewise for `Bad`, with `G_B := Q_C·S·q₄|T|·p`. Verifier and extractor keys are adversarial,
so their fetches are counted in `Q_A` (as quantum steps). That is `n_out·4607`, which is
harmless.

### 4.5 The theorem

**Theorem 2.** In the hybrid representation, with the simulator's fetches as insertions and
everything else as quantum steps,

    √Pr[Bad_T] ≤ q₄·√(8|T|·E_Z^max/N) + 2√2·Q_A·√(S·q₄|T|p) + √(G_B(1 + 2^9)),
    E_Z^max ≤ min( (a_A + √(G + X))²,  1.0005·a_A + G + X ),   a_A := 2√2·Q_A·√(S/(N−1)),

with `S = Q_A + Q_C`, `G = Q_C S/(N−1)` and `X ≤ 2^9 G`.

*Proof.* Theorem 1's steps 1–5 for the quantum steps. §4.2–4.4 for insertions. Lemma 4.3 to
combine. ∎

**Reading.** The coherent term is `a_A² ≈ 8Q_A²·S/N`: a quantum query may create a key agreeing
with any of the `S` frozen keys. The `Q_C²/N` growth that made Q5 vacuous now enters only as
`G ≈ Q_C S/N`, i.e. classically.

## 5. Numbers

Script: `scratchpad/q6/nums.py`. **[Lean]** checks rational relaxations
(`thm1_at_2_30`, `thm1_at_2_40`, `count_regime_*_at_2_50`, `thm2_SE_weak_at_2_30` `≤ 2^{−74}`,
`thm2_SE_strong_at_2_30` `≤ 2^{−67}`, `thm1_SE_strong_without_mixed_exceeds`).

**Q2 (one proof; `q₄ = 3q+1`, `Q_E = q`, `|T| = 17`).**

| `q` | `Σ² = 200q²/N` | old `ε_multi` (Q1 min) | **new `ε_multi` (Thm 1)** | total |
|---|---|---|---|---|
| `2^{30}` | `2^{−60.4}` | `2^{−70.3}` | `2^{−93.9}` | `2^{−60.4}` |
| `2^{35}` | `2^{−50.4}` | `2^{−45.3}` | `2^{−68.9}` | `2^{−50.4}` |
| `2^{40}` | `2^{−40.4}` | `2^{−6.2}` | `2^{−43.9}` | `2^{−40.2}` |
| `2^{42}` | `2^{−36.4}` | vacuous | `2^{−33.9}` | `2^{−33.7}` |
| `2^{45}` | `2^{−30.4}` | vacuous | `2^{−23.3}` (count regime) | `2^{−23.3}` |
| `2^{48}` | `2^{−24.4}` | vacuous | `2^{−12.8}` | `2^{−12.8}` |
| `2^{50}` | `2^{−20.4}` | vacuous | `2^{−5.8}` | `2^{−5.8}` |
| `≥ 2^{51.7}` | | | vacuous | vacuous |

- The crossover with the main term is at `q ≈ 2^{41.2}`.
- Separate budgets: with `q_E = 2^{40}` and hashes at `2^{50}`, `q₄ ≈ 3·2^{50}`, so
  `ε_multi ≈ 2^{−23.9}` against `Σ² = 2^{−20.4}`.
- Q7's multi-instance Theorem M at `n = 2^{20}` (`Q_E = 2^{32.5}`) gets
  `ε_multi ≈ 2^{−86.5}` instead of `2^{−62.9}`. At `n = 2^{30}` (`Q_E = 2^{42.2}`) it gets
  `≈ 2^{−57}` with all verifications counted as quantum. Treating the honest parties' fetches as
  insertions (§4) would lower this further, but their keys are adversarial, so §4.4's freshness
  does not apply. I did not claim it.

**SE (Q5; `q = 2^{30}` on every oracle; Lemma K: 4607 fetches per simulated proof and per
verification; `q₄ = q₄ + 2Q₂₁ + 3Q_S + n_out + 1`).**

| `Q_S` | `Q_A + Q_C` | `E_Z` | `ε_bind^C(T)` weak: Q1+K / Thm 1+K / **Thm 2** | `ε_bind^C(T')` strong: Q1+K / Thm 1+K / **Thm 2** | **total strong** |
|---|---|---|---|---|---|
| `2^{12}` | `2^{30.0}` | `2^{−35}` | `2^{−70.3}` / `2^{−93.8}` / `2^{−92.7}` | `2^{−63.2}` / `2^{−86.7}` / `2^{−85.6}` | `2^{−60.4}` |
| `2^{20}` | `2^{32.5}` | `2^{−32.5}` | `2^{−62.9}` / `2^{−86.5}` / `2^{−90.3}` | `2^{−55.8}` / `2^{−79.4}` / `2^{−83.2}` | `2^{−60.4}` |
| `2^{25}` | `2^{37.2}` | `2^{−27.8}` | `2^{−40.9}` / `2^{−72.2}` / `2^{−85.4}` | `2^{−33.8}` / `2^{−65.1}` / `2^{−78.3}` | `2^{−60.4}` |
| `2^{30}` | `2^{42.2}` | `2^{−22.8}` | vacuous / `2^{−54.7}` / **`2^{−77.7}`** | vacuous / `2^{−47.6}` / **`2^{−70.6}`** | **`2^{−60.4}`** |

The results are insensitive to `n_out ≤ 2^{10}`.
- **Lemma K alone** (Q7) already rescues SE up to `Q_S ≈ 2^{20}` with Q1's bounds.
- **Theorem 1** (all-`q`) with Lemma K reaches `Q_S = 2^{25}` comfortably. At `Q_S = 2^{30}` it
  leaves strong SE at `2^{−47.6}`, which dominates.
- **Theorem 2** (mixed) makes `ε_bind` negligible at `Q_S = 2^{30}`. SE is then `Σ_SE²`-limited:
  `2^{−60.4}` (`Sim°`) or `2^{−59.4}` (`Sim`).
- Without Lemma K (`c_E = 2^{18}` blocks per simulated proof as queries), Theorem 2 alone gives
  `≈ 2^{−64.5}` (strong; `2^{−71.6}` weak) at `Q_S = 2^{30}`, because `S = 2^{48}` makes `a_A ≈ 2^{−8.5}`. So the two
  improvements are complementary, but each suffices at this scale for weak SE.

## 6. Target (b): routes that do not get past `2^{52}`

### 6.1 List-binding does not shrink the overcount

The proposal: allow `≤ t` committed keys per leaf, run L3's KOS triple argument over all
combinations, and bound the number of affected leaves. It fails for structural reasons.
1. **All leaves of tree `i` share `ι = (iv, twk_i)`** (Q1 §0: the leaf tweak is fixed per tree).
   One agreeing pair `k, k'` at `ι` lets the prover set *any number* of tree `i`'s leaf
   commitments to `f_ι(σ_k)`. All of them become ambiguous, so there are up to `2^{L/τ} ≈ 2^{136}`
   combinations.
2. **The selection is made after the challenges.** Opened seeds are revealed after `chall₃`. So
   B₁, B₂ and B₃ must hold for *all* combinations: `ρ₂₁ ≤ 2^{#amb}·ε_KOS` (margin `2^{26}`),
   but `ρ₂₂ ≤ 2^{#amb}·ε_QS` and `ρ₂₃ ≤ 2^{#amb}·d·2^{−128}`, which multiply Q2's main term by
   `2^{#amb}`.
3. Hence even one ambiguous leaf is unaffordable, and the event to exclude is again "some iv-point
   of a chain lies in `Z`", i.e. `Bad_T`. **The quantum overcount survives unchanged**: it lives in
   `E_Z`, not in the number of affected leaves.
4. Classically the route is moot: ambiguity needs a real 256-bit collision at `ι` (`≈ q²/N²`).

Design remark, outside the maintainer's decision: with a distinct tweak per leaf, one agreement
would affect one leaf, and "≥ 2 ambiguous leaves on one chain" costs about an extra factor
`|T|·E_Z/N`.

### 6.2 Point-level compressed cipher and Liu–Zhandry multiplicity

Q4 §5.3 named the route: (L-a) a multiplicity bound "a value occurs at one position under `> m`
keys", plus (L-b) worst-case sparsity `≤ 4|T|m` for completions. This would give
`p_db = O(m|T|q²/N)`. I re-checked it against CM26, read from the copy saved by Q4.
- **Lemma 2.1 transfers to CM26's oracle.** `cpO_x = C_x U_x C_x` with `C_x` swapping
  `|h⟩ ↔ |+_{x,h}⟩` (CM26 Def. 3.6, Lemma 5.2's proof). So my first-moment potentials work at point
  level too. They give an LZ-type recursion: `⟨M_j⟩ ≤ min(q²·8⟨M_{j−1}⟩/N, q√(8⟨M_{j−1}⟩/N))` for
  the expected number `M_j` of `j`-fold same-position value coincidences across keys.
  - At `q = 2^{57}`: `⟨M_5⟩ ≈ 2^{−16.8}`. So (L-a) holds with `m = 4` at `2^{57}`, with **this
    proof sketch** (medium confidence; inverse queries handled by the flip `F`).
  - This is weaker than LZ19's `q^{2^k−1}/N^{2^{k−1}−1}` but enough here.
- **What still caps the route:**
  1. CM26's search loss `δ_N(T)² ≈ 7744T²/N` (CM26 (80), Lemma 5.1) with `T ≈ 2q` is
     `≈ 2^{14.9}q²/N`, which is vacuous at `2^{56.5}`. Kim's `4q/√N` (ePrint 2026/2135; constant as
     reported in BH26 and Kim's abstract) would help.
  2. Q4 §5.2's reduction from the key-level `multi` to the QICM search problem makes the search
     algorithm evaluate every database key at the `τ` iv-points, so `q' ≈ (1 + 2τ)q ≈ 35q`. That
     adds `2^{10.3}` to every `q²/N` term.
  3. `m|T|` sparsity: `32·17·4 ≈ 2^{11}`.

  Net: `≈ 2^{21–25}·q²/N`, vacuous by `q ≈ 2^{52}–2^{53}`. That is no better than Theorem 1's
  `2^{51.7}`. **I did not write this up as a theorem.** It is an assessment (medium confidence).

## 7. Target (c): the obstruction is inherent to key-level recording

### 7.1 Theorem 3 (Theorem 1 is tight for the key-level abstraction)

Call an oracle *key-level* if each query is `Σ_k |k⟩⟨k| ⊗ O_k`, with `O_k` any unitary controlled
on the value basis of `D_k` (Q1 §2: "the only property used"). This includes the **full-value
fetch** `|σ⟩|r⟩ ↦ |σ⟩|r ⊕ σ⟩`. Theorem 1, Q1 Thms 5.1/5.2, Q4 Thm B and Lemma K are all proved for
this whole class.

**Theorem 3.** Some key-level algorithm (using fetches) with `Q` cipher and `q₄` H₄ queries
achieves

    Pr[Bad_T] ≥ c·min{1, q₄²|T|·K(Q)/N},     K(Q) = Q³/N for Q ≤ N^{1/3},   K(Q) = Q^{3/2}/N^{1/2} for Q ≥ N^{1/3},

with `c` an absolute constant. Since `min(a, a²) = Θ(K(Q))`, no proof that uses only key-level
structure can beat Theorem 1 by more than a constant factor.

*Proof sketch.*
1. Fetch `t = Q/3` full permutations.
2. Run BHT-style Grover searches over fresh keys for "agrees with some stored permutation on some
   adjacent pair". The relation has density `≈ t/N`, and marking costs two fetches. This yields
   one agreeing pair with probability `Ω(Q³/N)`, or `Ω(Q^{3/2}/√N)` pairs in the regime
   `Q ≥ N^{1/3}` (repeat the search). Each pair comes with its point `z`, which is known because the
   permutations are known.
3. Grover over `w` for `H₄(w) ⊞ (0,0,0,twk) ∈ {z's}`, with target density `K|T|/N`.
4. The fetched keys sit in the database with exactly the fetched values (a fetch is
   `D_k`-controlled), so `Bad_T` holds. ∎

The constants are not optimised. The `K ~ Q^{3/2}/√N` count regime is by analogy with LZ19's
"`K` collisions cost `K^{2/3}N^{1/3}`" (medium confidence on that regime; high for
`Q ≤ N^{1/3}`). Note that this attacker finds a **real** two-key two-block collision at an
H₄-derived `ι`: against full-value oracles the bound is the truth.

### 7.2 Point-level telescoping overcounts fixed-input completions

At point level the `q⁵/N²`-type loss of Q1/Q4 comes from completing a half-agreement
`(k, k', z)` at the *fixed* input `(k, z ⊞ e₀)`. Lemma T, CM26 Lemma 5.2 and Theorem 1 all bound
`‖Bψ_T‖` by `Σ_t ‖B·U_t(1−B)ψ_t‖`.

Consider the adversary that, holding a half-agreement, queries `(k, z⊞e₀)` and uncomputes, `q`
times. Each step's honest transition norm is `≈ √(2/N)`, so the telescoped sum is `≈ q√(2/N)`. The
true completion probability is `O(1/N)`: by Zhandry's lemma, `Pr[D(x) = v] ≤ (1+√2)²/N` for fixed
`(x, v)`, whatever the queries. So **any** amplitude-additive telescoping over this property
certifies at best `q²/N` per half-agreement where `1/N` is true. This is evidence that the missing
step must be global (purified-vs-compressed, Lemma-5-style) rather than step-by-step.

### 7.3 What is missing, precisely

To reach `ε_multi = O(q²/N)` up to `2^{57}`, or `Θ(q³/N²)`, a proof must use point evaluation.
Any one of the following would do it.
- **(M1) Key-level, evaluation-aware.** For evaluation (not fetch) queries,
  `E_Z ≤ C·(Q²/N + Q³/N² + K'(Q))`, where `K'` is the count of *recorded* two-point agreements.
  This would give `ε_multi = O(q₄²|T|Q²/N²)` (`≈ q⁴/N²`, non-vacuous to `≈ 2^{61}`). It is false
  for fetch oracles (Theorem 3), so its proof must exploit that `O_{k,x}` reveals only `σ_k(x)`.
  CM26's level decomposition `H_{≤t}` (permutation degree) is the natural tool: an evaluation
  query raises the degree by at most one (CM26 Lemma 4.5), and agreements at "unrecorded" pairs of
  a degree-`t` state should have probability `≈ p`.
- **(M2) Point-level, non-telescoping completions.** In a compressed ideal cipher (CM26 or BH26),
  `Pr[DB holds a full two-point agreement at an iv-point] ≤ C·(E[#half-agreements]·|T|q₄²/N² + q³/N²)`,
  charging each half-agreement's completion once (`1/N`), not once per query. Together with Kim's
  soundness and a direct point-level extractor (avoiding Q4 §5.2's `35q` overhead), this would give
  `O(q²/N)` with a small constant.
- **(M3)** Any QICM bound for the search problem of Q4 §5.2 (two-block cross-key collision at an
  H₄-derived `ι`, forward and inverse access) of the form `O(q³/N²) + O(q⁴|T|/N²)` transfers to
  `S*` (Q4 (S4)). It would need the `35q` accounting, or an `Ext` that does not evaluate the
  database.

## 8. How this plugs into Q1/Q2/Q4/Q5/Q7

| where | old term | new term |
|---|---|---|
| Q1 (I5), Thms 5.1/5.2 | `min((320/9)q₁³/(N−1), 1.8·10⁷q⁵2^{−256}+2^{−127})`, the latter only while `θ ≤ 1/2` | Theorem 1: `(q₄√(8|T|min(a²,1.0005a)/N) + 2√2Q_E√(Q_E q₄|T|p))²`, all `q`. Q1 Thm 5.2 is superseded. |
| Q2 §6.3, Thm 7.1 | `ε_multi` as above, with `q₄ ↦ q₄+2q₂₁+1` and `2Q_E` | the same, with cipher and H₄ counted separately (no full-value doubling). Theorem 7.1 is meaningful for `q ≲ 2^{45}` (≈ `2^{−23}`) and below the main term for `q ≲ 2^{41}`. |
| Q4 (S3) | needed Thm C for the H₄ version | Theorem 1's amplitude regime holds for `S*` for every fixed `ρ` (Thm B-style). The count regime uses `S^IC` + Thm C. |
| Q5 Thm Q5, `ε_bind^C(T)`, `ε_bind^C(T')` | vacuous at `Q_S ≳ 2^{20}` | Theorem 2 with Lemma K counts (§5 table). The extractor and the bookkeeping run in the hybrid representation (§4.1). Q1's (I1)–(I7) hold there with the same or better constants: frozen keys contribute zero commutator, records on them persist exactly. |
| Q5 `ε_Sim` | `2^{−172} + τ n_out Q_E δ` (from Thm C for Thm 5.2) | `2^{−172}`. Theorem 2 needs no Thm C, and hybrid `S*` (lazy-sampled `F(k)` on frozen keys) is efficient. |
| Q7 Thm M | `ε_multi^{H₄}(2Q_E+Q₄+1)` | Theorem 1 with `Q_E = q_E + n·4607`: `2^{−86.5}` at `n = 2^{20}`, `≈ 2^{−57}` at `n = 2^{30}` |
| README §L9 | "`ε_multi` open above about `2^{40}`" | "`ε_multi` proved for all `q`; non-vacuous to `2^{51.7}`, tight for key-level techniques (Q6)" |

The hybrid representation changes nothing in Q2's `P` analysis.
- Insertions are steps that touch the `E` register. For `P` (alignment with chain targets) each
  costs `≤ √(2Q₂₁Lp)` in amplitude, which is negligible (`2^{42.2}·2^{−106.4}`).
- Queries on frozen keys are neutral.

## 9. Confidence

| step | status | confidence |
|---|---|---|
| Lemma 2.1 (weighted commutator) | proof; same algebra as Lemma T / CM26 Lemma 5.2 | high |
| Lemma 2.2 (moments) | proof | high |
| Theorem 1, amplitude regime | proof | high |
| Theorem 1, count regime | proof (`⟨ψ|cO†[Ẑ,cO]|ψ⟩` bound) | high for `S^IC`; for `S*` only via Thm C |
| H₄ step as a sum of squares over blocks | proof | high |
| Hybrid representation equals the real oracle | proof (`F_k² = 1`, classical `S`) | high |
| Insertion identity (§4.2) | proof | high |
| Lemma 4.3 (mixed telescoping) | Lean | high |
| Lemma 4.5 (freshness of derived GGM keys) | proof sketch, generous constants (`2^{15}`) | medium |
| Theorem 2 numbers | script + Lean rational relaxations | high given Lemma 4.5 and `c_E` = 4607 fetches (Q7) |
| Theorem 3 (technique lower bound) | sketch | high for `Q ≤ N^{1/3}`; medium for the count regime |
| §6.1 list-binding negative | argument | high |
| §6.2 point-level assessment | estimate | medium |

**Margins.** Lemma 4.5 enters only through `X`. Even `X = 2^{30}G` would leave
`ε_bind^C(T') ≤ 2^{−66}` at `Q_S = 2^{30}`.

## 10. Literature

- **[CM26]** Carolan–Majenz, *Compressed Permutation Oracles Revisited*, arXiv 2609.28469. Read
  (Q4's saved copy): Def. 3.6–3.7, Thm 4.2, Cor. 4.3/4.17, Lemma 5.1 (fundamental lemma; `δ_N(T)`
  eq. (80)), Lemma 5.2 (`‖[B, C_x]‖ ≤ √(2b/s)`, the point-level twin of Lemma 2.1), Thm 5.3. No
  multi-collision result.
- **[Kim26]** S. Kim, ePrint 2026/2135: soundness `4q/√N` for `q ≤ N/4`. Known from the abstract
  and search snippet only.
- **[Car25]** Carolan, arXiv 2509.18586 / ePrint 2025/1734: original oracle, `O(q³/N^{1/4})`.
  Known via CM26/Kim's description; not re-read.
- **[BH26]** Bhaumik–Huang, ePrint 2026/2324 / arXiv 2610.04674: compressed ideal cipher with
  `8q²Δ_cpO`. As summarised in Q4; not re-read.
- **[MMW24]** Majenz–Malavolta–Walter, arXiv 2407.09655: permutation superposition oracles; no
  list-of-pairs database (per Q4). Not re-read.
- **[LZ19]** Liu–Zhandry, *On finding quantum multi-collisions*: k-collision threshold
  `N^{(2^{k−1}−1)/(2^k−1)}`. Cited from memory.
- **[Gao15]** Gao, *Quantum union bounds for sequential projective measurements*, arXiv 1410.5688;
  also O'Donnell–Venkateswaran arXiv 2103.07827. Not used. Gao's bound is for sequential
  measurements on a *fixed* state and does not handle interleaved unitaries. The insertion
  identity (§4.2) plus freshness is the route that works here.
- **[CHH26]** Choi–Hhan–Jang, ePrint 2026/2241 (XOR of permutations in the QICM, Fourier
  analysis): found by search, not read; not obviously relevant.
- Unruh's quantum-permutation work and Alagic et al.: not re-checked beyond Q1/Q4's summaries.
- No 2024–2026 paper I found gives a multi-collision or two-block-collision bound for compressed
  permutation or ideal-cipher oracles.

Papers: `scratchpad/papers/q4/` (CM26, BH26, Car25 texts saved by Q4). No new downloads were
needed for `papers/q6/`.
