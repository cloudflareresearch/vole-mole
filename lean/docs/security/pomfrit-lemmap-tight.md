# Lemma P's `2⁵⁷`: inherent, or an artefact?

This note continues `pomfrit.md` §5–§6. Theorem U1 (one-more unforgeability from OMPR, Lean
`pomfrit_U1_sim`) carries the term `(Q₃+ℓ+1)·2⁻⁷¹` of Lemma P, where `2⁻⁷¹ = 2⁵⁷·2⁻¹²⁸`. Ordinary
extraction pays `2·2⁻¹²⁸` per `H₂³` query. At `2⁶⁴` queries U1 gives only `2⁻⁷`. The question:
is the factor `2⁵⁷` inherent, or can Lemma P be tightened?

Notation is that of `pomfrit.md` §1 and `extraction/L3-kos.md`: `F = GF(2¹²⁸)`, a challenge is
`Δ' ∈ F₂¹²⁰` with blocks `Δ_i` (tree 0 has 8 bits, trees 1..16 have 7), `e(Δ') ∈ F` is the CRT
lift, `S` is the set of challenges that hide every dead leaf, `r(Δ') = (Q(Δ'), D(Δ'))` is the
verifier's KOS input computed from the committed data, `H_c` is VOLEHash under `c = chall₁`, and

    K_c^ũ(Δ') := H_c(Q(Δ')) + D(Δ') + e(Δ')·ũ ∈ F⁴

is the check value. A chain passes the KOS check iff `K_c^ũ(Δ') = h_V`, the value in its `H₂²`
query. A tree is *alive* if all its leaves are; an alive tree `i` has corrected rows `u^{(i)}`.
The *prefix group* of a bit vector `u*` on the witness rows is the set of alive trees with
`u^{(i)} = u*` on the first `8M = 360` rows.

**Status labels.** *Proved*: full proof here. *Lean*: machine-checked (`Seed/KOSUnique.lean`
unless another file is named). *Code*: read off the C++ (`vole_commit.inc`,
`kos_vole_check.hpp`), not mechanized. *Heuristic*: argument with a stated unproved step.
*Estimate*: a size or cost figure. *Experimental*: checked on a toy model by
`scripts/pomfrit-lemmap-tight/toy.py`. *Open*: no proof and no attack.

## 0. Answer

| # | Statement | Status | § |
|---|---|---|---|
| O | `2⁵⁷` is the largest total width of a group of trees that is not a widest one: `57 = 8 + 7·7`, against `63 = 9·7`. `2⁻⁷¹ = 2⁻⁶³·2⁻⁸`: guess the 63 challenge bits of the other group, and pass the 8 grinding bits | proved; Lean (`minority_weight_le`, `Protocols/PomFRIT.lean`) | §2 |
| A1 | **Lemma P's bound is tight for `E₁`.** A forger makes `Shift` happen with probability `2⁻⁷¹` per `H₂³` query. It is not a forgery: it spends one Issuer query per signature | proved; experimental | §3.1 |
| A2 | **`E₁` is optimal among extractors that do not read `ũ`**: every first-phase extractor that is a function of the first message, `chall₁`, `d_pre`, `msg` and the query log fails with probability `≥ 2⁻⁷²` per `H₂³` query against some forger. If the target hash did not bind `ũ` (the paper's Algorithm 2 as `pomfrit.md` D2 reads it), this holds for **every** first-phase extractor | proved | §3.2 |
| D | **The code binds `ũ` into `h` (D2), and `ũ` determines the witness.** Except with probability `2³⁷⁷·ε_v < 2⁻¹³⁴` per `H₂¹` query, all accepting sets of all chains with the same first message and the same `ũ`, whatever their `h_V`, `d`, `chall₂`, have the same witness slope `u*`. So after the `H_T` query the forger has no choice of prefix group left. `pomfrit.md` §4's "after seeing `h`, it may complete either one" does not apply to the implementation | proved; Lean (`witness_determined`, `card_not_kosPar_le`, `pomfrit_disjQuads_le`, `pomfrit_par_count`); experimental | §4 |
| P∞ | Lemma P holds with `Pr[Shift] ≤ q₁·2⁻¹³⁴ + Q_T·q₁·2⁻⁷⁰⁴` for the extractor `E₁^∞` that outputs the determined prefix. `E₁^∞` is not known to be efficient, so this does **not** improve U1 | proved (from D and Lemma P's steps 1–4) | §4.3 |
| L | **Affine first messages: efficient, no loss.** If the alive trees agree on the λ label rows, `r` is `F₂`-affine on `S`, and `E₁^lin` (linear algebra on 121 evaluations of the verifier's check value) outputs the prefix of every accepting chain. No event beyond `ε_ext` is used: for such first messages `Shift` cannot happen | proved; Lean for the core (`exists_slope_of_kosGood_affine`, `witness_determined_affine`, `consistent_slope_eq`); affinity of the masks: code; experimental | §5 |
| H | **Hidden slices.** If the trees disagree on the label rows, the masks are affine only on the slice the forger prepared (`c_mult` is tuned to a guess of the other trees' challenge bits). `E₁^lin` with `E₁` as fallback then fails with probability `2⁻⁷¹` per `H₂³` query, as before. An efficient extractor must find the slice from `c_mult` and the `H₅` table | attack: proved; experimental. Efficient decoding in general: open | §6 |
| M | The loss cannot be moved into the OMPR experiment (more targets): a wrong prefix gives a preimage of `t_j ⊕ r ⊕ r'`, which is not a target, and combining preimages across shifts is Theorem R's obstacle (`ompr-shift-algebra.md` §2). By D, PomFRIT needs less than A-OMPR⊕17: the shift index is fixed, though hidden, when the target is requested | proved (first part); remark | §7 |
| C | Protocol: (i) keep `ũ` in `hash_to_target`: it is what makes D true; (ii) binding `h_V` as well adds nothing; (iii) per-tree affine masks (no CRT masks) would make L unconditional, at about `+1.1 kB` per signature; (iv) more grinding or other tree shapes move `2⁵⁷` by a few bits only | (i), (ii): proved; (iii): proved given the layout, size: estimate; (iv): proved | §8 |

**In one paragraph.** The `2⁵⁷` is tight for Lemma P's extractor and for every extractor that
ignores `ũ`. It is not inherent in the protocol as implemented: `hash_to_target` hashes `ũ`, and
`ũ` commits the forger to one prefix group, up to `2⁻¹³⁴` per `H₂¹` query. What remains is
computational: the reduction must *find* that group when `H_T` is queried. For first messages
whose trees agree on the label rows this is linear algebra and U1's extra term vanishes. For the
others the group can hide in one of up to `2⁶³` slices, and we have neither an efficient decoder
with a proof nor an attack that would rule one out. So U1 stays as stated, `(Q₃+ℓ+1)·2⁻⁷¹`
included, and no new `pomEps'` is claimed.

---

## 1. What an `H₂³` query fixes

The proof is `com, c_1..c_16, c_mult → chall₁ → ũ, (h_V), d → chall₂ → ã, b̃ → chall₃`.
`chall₃ = H₂³(y)` is 128 uniform bits: the top `w_grind = 8` must be zero, the other 120 are `Δ'`.
The input `y` contains `chall₂` and the QuickSilver messages, so it fixes the whole chain:
the `H₂¹` input (the first message), `ũ`, `h_V`, `d`, hence the statement's target
`h = H_T(dig, chall₁, ũ, d_pre, msg)` (`pomfrit.cpp:96-111`: `vole_check_proof()` is `ũ`).

For a chain let `𝒜 ⊆ S` be its accepting set (`pomfrit.md` §5, README Claims 1–4). The fresh
answer lands in `𝒜` with probability `|𝒜|·2⁻¹²⁸`. What the existing analysis gives on a chain,
outside the events of `ε_ext`:

- (K) `K_c^ũ ≡ h_V` on `𝒜`, and `r` lies on one line on `𝒜`: `r(Δ') = V* + e(Δ')·(u_Q, u_D)`
  (L3, Lean `KOSGood`). The witness part of `u_Q` is `u*`.
- (B) if `|𝒜| ≥ 3`, `u*` is a bit vector, and `u* ⊕ d` satisfies the relation (L4, L7).
- (T) every alive tree with `u^{(i)} ≠ u*` on some witness row is fixed on `𝒜`, and so is every
  tree with a dead leaf (Claim 4, Lean `free_tree_holds_witness`, `fixed_of_prefix_ne`).

So `|𝒜| ≤ 2^{w(G)}`, with `G` the prefix group of `u*` and `w(G) = Σ_{i∈G} k_i`.

## 2. Where `2⁵⁷` comes from [proved, Lean]

`E₁` outputs the prefix of a widest prefix group `g*` (`majP`). `Shift` is the event that an
accepted chain has `G ≠ g*`. Then `G` and `g*` are disjoint and `w(G) ≤ w(g*)`, so
`w(G) ≤ ⌊120/2⌋ = 60`. The widths are `8` once and `7` sixteen times, so `w(G) ∈ {7a, 7a + 8}`;
the largest such value `≤ 60` whose complement can hold a group at least as wide is
`57 = 7·7 + 8`, against `63 = 9·7` (`minority_weight_le`). The next split is `56` against `64`.

    2⁻⁷¹ = 2⁵⁷/2¹²⁸ = 2^{−(120−57)} · 2⁻⁸.

The first factor is the probability that the 63 challenge bits of the trees outside `G` take the
one value on which they are fixed (T). The second is the grinding: only `2¹²⁰` of the `2¹²⁸`
answers are admissible. Neither the majority rule nor the tie-break loses anything: every rule
that picks one group from the first message alone leaves some group of width up to 57 (§3.2).

## 3. Lower bounds

### 3.1 A forger that makes `E₁` fail with probability `2⁻⁷¹` per query [proved; experimental]

1. Run the honest commitment. Choose `c_i` so that trees `G_A = {1..9}` (width 63) carry the
   corrected rows `u_A` and trees `G_B = {0, 10..16}` (width 57) carry `u_B`, where `u_A`, `u_B`
   differ in the prefix rows only. Label rows and masks are honest and equal in all trees.
2. Query `H₂¹`, get `c`. Send the honest `ũ_B = H_c(u_B, labels, masks) + u_D` and `d_pre`.
   Query `H_T`. `E₁` answers with `G_A`'s prefix `r_A`, so the reduction programs
   `h = t_j ⊕ r_A`.
3. Ask the Issuer for `s` with `P(s) = h ⊕ r_B`. One query.
4. Guess `g ∈ F₂⁶³` for the blocks of `G_A`. Replace the VOLE tag `V[j]` by
   `V[j] + (u_A − u_B)[j]·e_A(g)` on the prefix rows, and run the honest prover with `(u_B, V')`
   and witness `(r_B, s)`. On the slice `{Δ_A = g}` this is an honest proof.
5. Grind `chall₃`. Each `H₂³` query is admissible with probability `2⁻⁸` and then has `Δ_A = g`
   with probability `2⁻⁶³`. All openings succeed (every leaf is known to the prover).

The accepted signature has witness prefix `r_B ≠ E₁(x)`: `Shift`. The cost is `2⁷¹` `H₂³` queries
per expected success, so `Pr[Shift] ≈ Q₃·2⁻⁷¹` for `Q₃ ≪ 2⁷¹`. Lemma P's bound is tight for `E₁`,
and the opening-success factor of `pomfrit.md` §5's tightness remark is 1.

This is not an attack on unforgeability: step 3 spends an Issuer query, and the forger ends with
one signature per query. It only makes the reduction's extracted `s` a preimage of
`t_j ⊕ r_A ⊕ r_B`, which is useless to it.

The toy run (E1) shows the two families of level sets: with `ũ_B`, the level sets of `K_c^ũ` are
exactly the slices `{Δ_A = g}`, each a line with witness slope `u_B`.

### 3.2 No extractor that ignores `ũ` does better [proved]

Let `E` be any first-phase extractor whose output on `x` does not depend on the `ũ` field of `x`,
but may depend on the first message, `chall₁`, `d_pre`, `msg`, the whole query log, and coins.
The forger of §3.1 can also send `ũ_A` in step 2 and complete with `G_A` (cost `2⁻⁶⁵` per query).
Up to step 2 its two variants differ only in `ũ`, so `E`'s output has the same distribution in
both. One of the two prefixes is output with probability `≤ 1/2`; the forger uses that variant.
So `Pr[Shift per H₂³ query] ≥ ½·2⁻⁷¹`. For a deterministic `E` the forger evaluates `E` itself
and the bound is `2⁻⁷¹`.

The same argument applies to **every** first-phase extractor if `ũ` is not an input of the target
hash: then the forger chooses between `ũ_A` and `ũ_B` after it has seen `h`, as `pomfrit.md` §4
describes. `pomfrit.md` D2 lists "`h` also binds `ũ`" as a deviation of the code from Algorithm 2.
If that reading of the paper is right, then for the paper's protocol `2⁻⁷¹` per query is the best
any first-phase extractor achieves with FAEST-EM-128f shapes, and U2's assumption (or a different
proof) is needed for a tight bound.

So an improvement must use `ũ`. §4 shows that `ũ` carries the information.

## 4. `ũ` determines the witness

### 4.1 Parallel lines [proved, Lean]

L3's good event concerns one level set: three points of `S` with the same check value are
collinear. Two chains with the same first message and `ũ` but different `h_V` live on two level
sets. For a quadruple `q = (Δ₀, Δ₁, Δ₂, Δ₃)` define the parallelism defect (Lean `pcross`)

    π(q) := (e₃ − e₂)·(r₁ − r₀) − (e₁ − e₀)·(r₃ − r₂) ∈ F^{L+4},

zero iff the secants through `(Δ₀, Δ₁)` and `(Δ₂, Δ₃)` have the same slope. If `K_c^ũ(Δ₀) =
K_c^ũ(Δ₁)` and `K_c^ũ(Δ₂) = K_c^ũ(Δ₃)`, then `K(π(q)) = 0` for `K(x, y) = H_c(x) + y`
(`map_pcross_eq_zero`): `ũ` cancels, and the two values `h_V`, `h_V'` never enter.

**Definition.** `c` is *good for parallelism* on a set `𝒫` of quadruples (Lean `KOSPar`) if no
`q ∈ 𝒫` has `π_Q(q) ≠ 0` and `H_c(π_Q(q)) = −π_D(q)`.

**Lemma D1** (`pcross_eq_zero_of_kosPar`). If `c` is good on `𝒫`, `q ∈ 𝒫`, and the two pairs of
`q` each pass the KOS check with the same `ũ`, each with its own `h_V`, then `π(q) = 0`.

**Lemma D2** (`card_not_kosPar_le`). For `r` fixed before `chall₁`, at most
`|𝒫|·(|F|⁴|T| + (L−1)⁵|F|⁴)` of the `|F|⁸|T|` values of `c` are not good on `𝒫`. As a
probability: `|𝒫|·ε_v`, with L3's `ε_v = 2⁻⁵¹² + (L−1)⁵·2⁻⁵⁷⁶`. The proof is Lemma A of L3 per
quadruple and a union bound.

With `𝒫` all quadruples of `S`, `|𝒫|·ε_v = 2⁴⁸⁰·2⁻⁵¹² = 2⁻³²`: useless. VOLEHash's 512 bits are
sized for triples. The structure of the witness rows cuts `𝒫` down.

### 4.2 Theorem D [proved, Lean]

Let `𝒫_⊥` (Lean `DisjQuads`) be the quadruples whose pairs differ on disjoint sets of trees: for
every tree `i`, `Δ₀,i = Δ₁,i` or `Δ₂,i = Δ₃,i`.

**Theorem D** (`witness_determined`). Let `c` be good for parallelism on `𝒫_⊥`. Let `𝒜`, `𝒜'` be
the accepting sets of two chains with the same first message and the same `ũ` (any `h_V`, `h_V'`),
each with (K), a bit slope `u*`, `u*'` and a free tree. Then `u* = u*'`, and the free trees of
`𝒜` and of `𝒜'` hold the same witness rows.

*Proof* (`uStar_eq_of_parallel`). Suppose `u* ≠ u*'`. Take `Δ₀, Δ₁ ∈ 𝒜` that differ in a free
tree and `Δ₂, Δ₃ ∈ 𝒜'` likewise. A tree in which both pairs differ is free on `𝒜` and on `𝒜'`,
so by (T) it holds `u*` and `u*'`: impossible. So the quadruple is in `𝒫_⊥`, and Lemma D1 gives
`π_Q = 0`. On witness row `j`, `Q[j] = v + u*[j]·e` on `𝒜` and `v' + u*'[j]·e` on `𝒜'`, so
`(e₁−e₀)(e₃−e₂)(u*[j] − u*'[j]) = 0`. The lift is injective, so `u*[j] = u*'[j]`. ∎

**Count** (`card_disjQuads_le`, `pomfrit_disjQuads_le`, `pomfrit_par_count`). Choose `Δ₀`, `Δ₂`
and per tree the two differences, one of them zero: `|𝒫_⊥| ≤ 2¹²⁰·2¹²⁰·∏_i 2·2^{k_i} = 2³⁷⁷`.
With `L = 1441`: `2³⁷⁷·(|F|⁴|T| + 1440⁵|F|⁴) ≤ 2⁹⁵⁴` of `2¹⁰⁸⁸` challenges. So

    ε_par := Pr[chall₁ not good for parallelism on 𝒫_⊥] ≤ 2³⁷⁷·ε_v < 2⁻¹³⁴   per fresh H₂¹ query.

`r` is fixed before `chall₁` exactly as in L3 §2.2, so the event is charged like `ε_KOS`: once per
`H₂¹` query. For comparison `ε_KOS ≈ 2⁻¹⁵⁴`.

The toy run (E2) enumerates all pairs of challenges: every forced `ũ` has one witness slope.

### 4.3 Lemma P^∞ [proved from D; not an improvement of U1]

Define `E₁^∞(x)`: with `c`, `ũ`, `d_pre` from `x` and the committed data of the first `H₂¹` query
with output `c`: if some alive tree `i` and some set `A ⊆ S` with a free tree `i` exist such that
`K_c^ũ` is constant on `A` and `r` lies on a line on `A` with witness slope `u^{(i)}`, output
`u^{(i)}[0..360) ⊕ d_pre`; else `⊥`.

**Lemma P^∞.** Lemma P (`pomfrit.md` §5) holds with `E₁^∞` in place of `E₁` and

    Pr[Shift^∞] ≤ q₁·ε_par + Q_T·q₁·2⁻⁷⁰⁴ < q₁·2⁻¹³⁴ + Q_T·q₁·2⁻⁷⁰⁴,

with no term in `Q₃`.

*Proof.* Steps 1–4 of Lemma P's proof are unchanged: outside `ε_ext` an accepted chain has
`|𝒜| ≤ 2` (charged in `ε_ext`) or (K), (B), (T) and a free tree `i₀` holding `u*`. Then `(i₀, 𝒜)`
is a witness for the definition of `E₁^∞(x)`. By Theorem D every other witness `(i, A)` has
`u^{(i)} = u*` on the witness rows, so `E₁^∞(x)` is `u*`'s prefix. ∎

`E₁^∞` is a function of data that exist when `H_T` is queried (the response function also reads
`H₅` and the cipher, which a reduction samples lazily). But it is defined by a search over subsets
of `2¹²⁰` challenges. A reduction that runs it is not efficient, and Def. 3.1 against an unbounded
`B` is void. **So P^∞ does not give a better U1.** What it does show: `Shift` is not about an
ambiguity. The forger's group is fixed when it queries `H_T`; the loss in U1 is the price of the
reduction not *finding* it.

## 5. The affine case: an efficient extractor without loss

### 5.1 When the response function is affine [code]

On `S`, the witness and label rows are `Q[j](Δ') = V[j] + Σ_{i alive} u^{(i)}[j]·e_i(Δ_i)`: affine
over `F₂` in `Δ'`. The masks are (`vole_commit.inc:286-333`, `:534-580`, L3 §2.2)

    q̄_m(Δ') = W_tree(r̃_m(Δ')) + W_gate(g_m(Δ')),
    r̃_{m,i} = v_{m,i} + u_{m,i}·Δ_i mod M_i,
    g_m(Δ')[e] = bit_m H₅(iv, e, L0[e](Δ')) ⊕ γ_e(Δ')·c_mult[m][e],
    L0[e](Δ') = C_e ⊕ Σ_{columns c of alive trees} G[e][c]·Δ'_c·u^{(tree(c))}_lab,   γ = G·Δ'.

`r̃` is `F₂`-affine per tree and `γ` is `F₂`-linear. `H₅` is the only non-linear step. If **all
alive trees have the same label rows `u_lab`**, then `L0[e](Δ') = C_e ⊕ γ^{al}_e(Δ')·u_lab` takes
two values, `bit_m H₅(L0[e])` is affine in the bit `γ^{al}_e(Δ')`, and `q̄_m` is `F₂`-affine on
`S`. So:

> **(Aff)** If the alive trees agree on the λ label rows, `r = (Q, D)` is `F₂`-affine on the
> coset `S` (Lean `AffineOn`).

In the layout without dedicated label rows (`REUSE_CRT_WITNESS`) the labels are witness rows
`[0, λ)`, inside the prefix, and the condition reads "agree on the first λ witness rows".

### 5.2 Theorem L [proved; Lean for the core]

**Theorem L.** Let `c` be KOS-good (L3's event, already in `ε_ext`) and `r` affine on `S`. For
every `ũ` there is one slope `(u_Q, u_D)` such that every set `A ⊆ S` on which `K_c^ũ` is constant,
for any value `h_V`, lies on a line of slope `(u_Q, u_D)` (`exists_slope_of_kosGood_affine`). In
particular two accepting sets with the same `ũ` have the same `u*` (`witness_determined_affine`),
and `u*` is the witness part of `u_Q` (`consistent_slope_eq`).

*Proof* (`pcross_eq_zero_of_kosGood_affine`). Let `(Δ₀, Δ₁)` and `(Δ₂, Δ₃)` be two pairs, each
with equal check values. Put `Δ_t := Δ₀ + (Δ₃ − Δ₂) ∈ S`. By affinity `r(Δ_t) − r(Δ₀) = r(Δ₃) −
r(Δ₂)`, so `K_c^ũ(Δ_t) = K_c^ũ(Δ₀)`. Now `{Δ₀, Δ₁, Δ_t}` is in one level set, and L3 puts it on one
line. Its slope is the slope of both secants. ∎

No event beyond `KOSGood` is used: affinity lets one translate the second level set onto the
first.

**The extractor `E₁^lin`.** On `x` with (Aff):
1. Take a base point `Δ^b ∈ S`. For each challenge bit `k` of an alive tree compute
   `λ_k := K_c^ũ(Δ^b + ε_k) − K_c^ũ(Δ^b) ∈ F⁴`.
2. Solve for the kernel `N = {δ : Σ_k δ_k λ_k = 0}` (Gaussian elimination, at most 120 unknowns,
   512 equations). If `N = 0`, output `⊥`.
3. Take `δ ∈ N∖{0}` and output the bits `(Q[j](Δ^b + δ) − Q[j](Δ^b))/e(δ)`, `j < 360`, xored with
   `d_pre`; `⊥` if they are not bits.

By affinity the level sets of `K_c^ũ` are the cosets of `N`, so step 3 reads the one slope of
Theorem L. The cost is 121 evaluations of the verifier's response from seeds that `E₁` recovers
anyway; the per-tree `u`, `v` do not depend on `Δ'`, so this is linear algebra plus `2·n_mult`
`H₅` calls.

**Corollary (Lemma P^lin).** With `E₁'(x) := E₁^lin(x)` if (Aff) holds and `E₁(x)` otherwise,
Lemma P holds, and `Shift` can only happen on chains whose first message violates (Aff). For a
forger whose first messages all satisfy (Aff), U1 holds with U2's bound:
`Adv ≤ Adv^{ompr} + ε_ext + Q_T·q₁·2⁻⁷⁰⁴ + ε_DS`.

*Proof.* An accepted chain outside `ε_ext` has `|𝒜| ≤ 2`, or a line on `𝒜` with a bit slope `u*`
and two points. `𝒜` is inside a coset of `N`, so `N ≠ 0` and step 3 outputs `u*`'s prefix. ∎

The toy run (E3): the kernel slope is the committed group's `u` at every base point.

In Lean the core (Theorem L) is proved for any response function with `AffineOn`. (Aff) for the
executable verifier's masks, and the corollary in the one-more game, are not mechanized.

## 6. Hidden slices: why this does not yet improve U1

### 6.1 The attack on `E₁'` [proved; experimental]

The forger of §3.1, with one change: trees `G_A` also carry label rows `u_A,lab ≠ u_B,lab`, and
`c_mult` is computed for the guessed slice. With `g*` the guess for `Δ_A`:

    C'_e := C_e ⊕ γ^A_e(g*)·u_A,lab,
    c_mult[m][e] := bit_m H₅(iv, e, C'_e) ⊕ bit_m H₅(iv, e, C'_e ⊕ u_B,lab) ⊕ F(ū_m)[e].

On the slice `{Δ_A = g*}` the labels are `C'_e ⊕ γ^B_e·u_B,lab`, the gate terms are those of an
honest prover with mask slopes `ū`, and the CRT identity gives `q̄_m = const + ū_m·e(Δ')`. So the
slice is a level set of `K_c^ũ` for `ũ = H_c(u_B, u_B,lab, ū₀) + (ū₁..ū₄)`, with slope `u_B`. Off
the slice, every gate `e` with `γ^A_e(Δ_A) ≠ γ^A_e(g*)` contributes `H₅` values unrelated to
`c_mult`, and `K_c^ũ` has no linear structure in `Δ_B`.

(Aff) fails, so `E₁'` falls back to `E₁`, which outputs `r_A`. The forger completes with `G_B`
on the slice it guessed anyway: `Shift` with probability `2⁻⁷¹` per `H₂³` query. So **`E₁'` has
Lemma P's worst-case bound, no better.** Dropping the fallback does not help [heuristic, with `H₅`
a random oracle; experimental]: at a base point off the slice the kernel test finds `N = 0` (toy
run E4: one level set, the slice; no kernel at any of the 496 base points off it).

By Theorem D the forger is still committed: with this `ũ` only `G_B` can be completed. The
extractor's problem is to find `g*` among `2⁶³` slices.

### 6.2 What an efficient extractor would have to do [heuristic, open]

- **Two label classes.** If the alive trees outside the free class share one label vector, the
  two candidate hash differences per gate are computable, `c_mult ⊕ (those) = F(ū)` is linear in
  `(g*, ū)`, and `g*` is found by linear algebra. This needs "a slice is a level set only if
  `c_mult` has this form", i.e. injectivity facts about `W_gate`, `F` and `G` that we did not
  establish.
- **More label classes.** Per gate the label depends on up to 16 bits `γ^λ_e(g)`, through `H₅`.
  Finding `g*` is then a system of table constraints, linear only after guessing which table entry
  each gate uses. The log does not help: the forger can query all candidate labels.
- **Level sets that are not slices.** The label rows have no bit constraints, so an accepting set
  can also sit in a subspace `{δ : e_T(δ) = α·e(δ)}` on which label slopes are not bits (L3 §6.1).
  Such a set has at most `2^{⌊w(G)/2⌋}` points. An extractor must either find these too or charge
  them: `2^{28−128}` per query if `G` is a minority.

We have no proof that an efficient extractor finds every level set with more than, say, `2^k`
points, and no forger that provably defeats every efficient extractor. Either would settle the
question. A proof would give U1 with `2^{k−128}` per `H₂³` query.

## 7. Can the loss move into the OMPR experiment? [proved: no, for the obvious ways]

- **More targets.** `H_T(x)` has one value. If the reduction programs `t_j ⊕ r` and the forger
  completes with `r'`, the extracted `s` has `P(s) = t_j ⊕ r ⊕ r'`. That is a target only if the
  reduction can make `t_j ⊕ r ⊕ r'` a target for every other alive prefix `r'`, i.e. only in
  A-OMPR⊕17. With independent uniform targets, `t_j ⊕ r ⊕ r'` is another target with probability
  `≤ 16·n·256⁻⁴⁵` per `H_T` query.
- **Guessing.** By Theorem D exactly one of at most 17 prefixes is right at each `H_T` query. A
  reduction that guesses is right on all `ℓ + 1` forgeries with probability `17^{−(ℓ+1)}`: this
  is `advOMPRShift_le_guess`.
- **Combining preimages across shifts** is what `ompr-shift-algebra.md` Theorem R excludes for
  reductions that are black-box in the adversary, unless OMPR^free fails.

**Remark (a weaker assumption suffices).** Theorem R's adversary chooses its shift after it sees
the target. By Theorem D a PomFRIT forger cannot: its index is a function of its request, though
possibly a hidden one. So U2 holds under the variant of A-OMPR⊕17 in which the adversary must fix
the shift index of each request when it makes the request (statistically, not necessarily
extractably). We do not know a reduction from OMPR to that variant either: a reduction still has
to learn the index.

## 8. Protocol changes

- **(i) Keep `ũ` in `hash_to_target`.** `pomfrit.md` D2 calls it harmless. It is more: by §3.2,
  without it no first-phase extractor beats `2⁻⁷¹`, and by §4 with it the forger is committed.
  If the paper's Algorithm 2 hashes `π₁` without `ũ`, the paper's protocol should adopt this.
  Cost: none.
- **(ii) Binding `h_V` too.** Then the level set itself is fixed by `x` and L3 alone gives one
  line. But Theorem D already gives this up to `2⁻¹³⁴`, and `h_V` does not help to *find* the
  slice in general. Not recommended.
- **(iii) Affine masks.** If the masks were ordinary corrected VOLE rows (no CRT masks, no `H₅`
  gate terms), `r` would be affine for every first message, (Aff) would always hold, and
  Lemma P^lin would give U1 with U2's bound under plain OMPR. Cost [estimate]:
  `(d − 1 + 4)·λ = 640` more corrected rows, `16·80 = 1280` bytes of corrections, minus `c_mult`
  (`5·⌈n_mult/8⌉ ≈ 195` bytes): about `+1.1 kB` on `5643` bytes. The ZK proof (`zk.md`) would
  have to be redone for that layout. This is the one change we found that provably removes the
  term; it is not small.
- **(iv) Parameters.** The term is `2^{w_min − 128}` with `w_min` the largest non-widest group
  width, about `n_Δ/2 = (128 − w_grind)/2`. So it is about `2^{−64 − w_grind/2}` for any tree
  shapes: one more grinding bit doubles the prover's work and gains half a bit. Not a fix.
- **(v) Assumption.** U2 under A-OMPR⊕17 (or the committed variant of §7) is tight today.

## 9. Lean and script

`lean/VoleMole/Seed/KOSUnique.lean` (new; no existing file changed except the import list).
Axioms: `propext`, `Classical.choice`, `Quot.sound`.

| Paper | Lean |
|---|---|
| parallelism defect `π(q)`; the check hash kills it | `pcross`, `map_pcross_eq_zero` |
| equal slopes from `π = 0` in a row | `slope_eq_of_pcross` |
| good for parallelism on `𝒫` | `KOSPar` |
| Lemma D1 | `pcross_eq_zero_of_kosPar` |
| Lemma D2 (counting form); non-vacuity | `card_not_kosPar_le`, `exists_kosPar` |
| `𝒫_⊥` | `DisjQuads` |
| Theorem D: deterministic core; with the KOS check | `uStar_eq_of_parallel`, `witness_determined` |
| `|𝒫_⊥| ≤ |X|²·∏ 2|B_i|`; `≤ 2³⁷⁷` for PomFRIT; `2³⁷⁷·(…) ≤ 2⁹⁵⁴` | `card_disjQuads_le`, `pomfrit_disjQuads_le`, `pomfrit_par_count` |
| affine response function; non-vacuity | `AffineOn`, `affineOn_univ` |
| Theorem L per quadruple; one slope for all level sets; for two accepting sets | `pcross_eq_zero_of_kosGood_affine`, `exists_slope_of_kosGood_affine`, `witness_determined_affine` |
| `u*` is the witness part of the slope | `consistent_slope_eq` |
| `57` | `minority_weight_le` (`Protocols/PomFRIT.lean`, existing) |

Not mechanized: §3 (the forgers); (Aff) for the executable verifier's masks; Lemma P^∞ and
Lemma P^lin as statements about the one-more game (they would need `KOSPar` as a bad event at
`H₂¹` in `ROM/Chains.lean`'s style, and `E₁^lin` as a function of the log); §6.

`scripts/pomfrit-lemmap-tight/toy.py [seed]`: four trees of widths `(3, 2, 2, 2)`, `GF(2³²)`,
a KOS check of the same shape. E1: §3.1's level sets. E2: Theorem D over all pairs. E3: `E₁^lin`.
E4: §6.1's hidden slice. Runs in seconds.

## 10. Open

1. An efficient extractor for first messages without (Aff), with a proof (§6.2), or a forger
   that defeats every efficient one.
2. Mechanize Lemma P^lin in the one-more game: (Aff) for `Verifier`'s masks, `E₁^lin` on the log,
   and a `pomEps'` without the `2⁵⁷` for forgers restricted to (Aff). A restriction on forgers
   is not a security statement, so this was not attempted.
3. The committed-shift variant of A-OMPR⊕17 (§7): is it implied by OMPR?
