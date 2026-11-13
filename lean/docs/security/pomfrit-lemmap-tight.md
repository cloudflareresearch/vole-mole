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
`scripts/pomfrit-lemmap-tight/toy.py`, or, for §6, on a model with faest-arch-opt's CRT tables by
`scripts/pomfrit-lemmap-tight/slice.py`. *Open*: no proof and no attack.

## 0. Answer

| # | Statement | Status | § |
|---|---|---|---|
| O | `2⁵⁷` is the largest total width of a group of trees that is not a widest one: `57 = 8 + 7·7`, against `63 = 9·7`. `2⁻⁷¹ = 2⁻⁶³·2⁻⁸`: guess the 63 challenge bits of the other group, and pass the 8 grinding bits | proved; Lean (`minority_weight_le`, `Protocols/PomFRIT.lean`) | §2 |
| A1 | **Lemma P's bound is tight for `E₁`.** A forger makes `Shift` happen with probability `2⁻⁷¹` per `H₂³` query. It is not a forgery: it spends one Issuer query per signature | proved; experimental | §3.1 |
| A2 | **`E₁` is optimal among extractors that do not read `ũ`**: every first-phase extractor that is a function of the first message, `chall₁`, `d_pre`, `msg` and the query log fails with probability `≥ 2⁻⁷²` per `H₂³` query against some forger. If the target hash did not bind `ũ` (the paper's Algorithm 2 as `pomfrit.md` D2 reads it), this holds for **every** first-phase extractor | proved | §3.2 |
| D | **The code binds `ũ` into `h` (D2), and `ũ` determines the witness.** Except with probability `2³⁷⁷·ε_v < 2⁻¹³⁴` per `H₂¹` query, all accepting sets of all chains with the same first message and the same `ũ`, whatever their `h_V`, `d`, `chall₂`, have the same witness slope `u*`. So after the `H_T` query the forger has no choice of prefix group left. `pomfrit.md` §4's "after seeing `h`, it may complete either one" does not apply to the implementation | proved; Lean (`witness_determined`, `card_not_kosPar_le`, `pomfrit_disjQuads_le`, `pomfrit_par_count`); experimental | §4 |
| P∞ | Lemma P holds with `Pr[Shift] ≤ q₁·2⁻¹³⁴ + Q_T·q₁·2⁻⁷⁰⁴` for the extractor `E₁^∞` that outputs the determined prefix. `E₁^∞` is not known to be efficient, so this does **not** improve U1 | proved (from D and Lemma P's steps 1–4) | §4.3 |
| L | **Affine first messages: efficient, no loss.** If the alive trees agree on the λ label rows, `r` is `F₂`-affine on `S`, and `E₁^lin` (linear algebra on 121 evaluations of the verifier's check value) outputs the prefix of every accepting chain. No event beyond `ε_ext` is used: for such first messages `Shift` cannot happen | proved; Lean for the core (`exists_slope_of_kosGood_affine`, `witness_determined_affine`, `consistent_slope_eq`); affinity of the masks: code; experimental | §5 |
| H | **Hidden slices.** If the trees disagree on the label rows, the masks are affine only on slices (`c_mult` is tuned to a guess of the other trees' challenge bits). `E₁^lin` with `E₁` as fallback fails with probability `2⁻⁷¹` per `H₂³` query against the forger of §6.1 | attack: proved; experimental | §6.1 |
| S | **Structure of an accepting set.** A *class* is a set of alive trees with the same witness and label rows. An accepting set of a minority group has at most `2²⁸` points, or it lies in one slice of a class. On a slice of a class the response is affine. Any two challenges of one slice with the same check value certify the witness of every accepted chain with that `ũ`. So extraction is: find the slice | proved; Lean (`card_le_of_nonbit_slope`, `claim4Hyp_slice`, `translateOn_gate_slice`, `slice_collision_sound`, `slice_collision_sound_affine`); the executable verifier's masks: code | §6.2 |
| BB | An extractor that only evaluates a check value that hides one of `N` slices, and is the same function off the slice, detects at most `T` of the `N` slices with `T` evaluations. The query log does not name the slice either. So an extractor must read `c_mult` against the `H₅` table | proved; Lean (`DTree.card_detect_le`) | §6.3 |
| Dec | **A decoder finds the slice.** Two label classes: linear algebra (`512` equations in at most `112` unknowns per direction; `2^{a+1}` solves find level sets of codimension `≤ a`). Any number of label classes: the effective gate bits by linear algebra, then a search over the fixed trees that never discards the slice. §6.1's forger is decoded in `0.03 s` with faest-arch-opt's tables; with 9 different label vectors on the 9 fixed trees, in `2¹⁵`–`2¹⁷` search nodes | two classes: proved; completeness for full slices: proved; running time, wrong gates with more than two classes: heuristic; experimental | §6.4 |
| T | **Time against loss.** With a decoder for up to `J` label vectors among the fixed trees, Lemma P's `H₂³` term becomes `2^{−15−7J}` per query: `2⁻⁷⁸` at `J = 9` (`≈ 2¹⁷` search nodes per class and `H_T` query; `2²¹` with wrong gates), `2⁻⁸⁵` at `J = 10` (`2²²`), `2⁻⁹⁹` at `J = 12` (`≈ 2³⁵`, extrapolated). Floor `2⁻¹⁰⁰`. The decoder's completeness against every forger is not proved, and we have no reduction from a hard problem. **U1 is unchanged** | heuristic; experimental | §6.5 |
| M | The loss cannot be moved into the OMPR experiment (more targets): a wrong prefix gives a preimage of `t_j ⊕ r ⊕ r'`, which is not a target, and combining preimages across shifts is Theorem R's obstacle (`ompr-shift-algebra.md` §2). By D, PomFRIT needs less than A-OMPR⊕17: the shift index is fixed, though hidden, when the target is requested | proved (first part); remark | §7 |
| C | Protocol: (i) keep `ũ` in `hash_to_target`: it is what makes D true; (ii) binding `h_V` as well adds nothing; (iii) per-tree affine masks (no CRT masks) would make L unconditional, at about `+1.1 kB` per signature with the 512-bit check, about `+50 B` with a FAEST-style check and a different analysis; (iv) more grinding or other tree shapes move `2⁵⁷` by a few bits only; (vi) each extra direct mask (`+55 B`) lets the decoder handle one more label class at the same cost; (vii) bit constraints on the label rows (`0 B`) remove the `2⁻¹⁰⁰` floor; (viii) binding the group or the slice in a hash: no cheap variant works | (i), (ii): proved; (iii): proved given the layout, sizes: estimate; (iv): proved; (vi): heuristic, experimental; (vii): proved given L4 on those rows, ZK not redone; (viii): argued | §8 |

**In one paragraph.** The `2⁵⁷` is tight for Lemma P's extractor and for every extractor that
ignores `ũ`. It is not inherent in the protocol as implemented: `hash_to_target` hashes `ũ`, and
`ũ` commits the forger to one prefix group, up to `2⁻¹³⁴` per `H₂¹` query. What remains is
computational: the reduction must *find* that group when `H_T` is queried. For first messages
whose trees agree on the label rows this is linear algebra and U1's extra term vanishes. For the
others the group hides in one of up to `2⁶³` slices. §6 reduces extraction to finding the slice
(any collision of the check value inside a slice is a certificate), shows that this cannot be
done by evaluating the check value alone, and gives a decoder that reads `c_mult` against the
`H₅` table. The decoder is proved for two label classes and defeats every hiding strategy we
found, at a cost that grows by about `2⁷` per label class beyond 8. We could not prove that it
finds every slice, nor reduce slice finding from a hard problem. So U1 stays as stated,
`(Q₃+ℓ+1)·2⁻⁷¹` included, and no new `pomEps'` is claimed; the conditional statement is §6.5.

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

## 6. Hidden slices

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
Lemma P's worst-case bound, no better.** Dropping the fallback does not help: at a base point off
the slice the kernel test finds `N = 0` (toy run E4: one level set, the slice; no kernel at any of
the 496 base points off it. `slice.py` R1, real tables: no kernel direction off the slice).

By Theorem D the forger is still committed: with this `ũ` only `G_B` can be completed. The
extractor's problem is to find `g*` among `2⁶³` slices. §6.4 finds it.

### 6.2 Structure of an accepting set [proved; Lean for the core]

A *class* is a set `C` of alive trees whose corrected rows agree on the witness rows (`u_C`) and on
the label rows (`ℓ_C`). Its *slice* at `g` is `σ_C(g) := {Δ' ∈ S : Δ_i = g_i for all i ∉ C}` (Lean
`slice`). `w(C)` is its width.

**Lemma S1 (a slope that is not a bit; `card_le_of_nonbit_slope`).** Let `A` satisfy (K) and let
`G` contain every tree that is not fixed on `A`. If the slope `u*[j]` of a row `j` is neither 0 nor
1, then `|A| ≤ 2^{w(P)}` and `|A| ≤ 2^{w(G∖P)}` for `P := {i ∈ G alive : u^{(i)}[j] = 1}`. So
`|A| ≤ 2^{⌊w(G)/2⌋}`.

*Proof.* For `Δ, Δ' ∈ A` with difference `δ`: `e_P(δ) = u*[j]·e(δ)`, so
`(1 − u*[j])·e_P(δ) = u*[j]·e_{G∖P}(δ)`. Both coefficients are nonzero. If `δ` vanishes on `P`,
then `e_{G∖P}(δ) = 0`, and the lift is injective: `δ = 0`. Likewise for `G∖P`. ∎

Witness rows have bit slopes by (B). The label rows have no bit constraints, so Lemma S1 applies
to them: an accepting set with a label slope that is not a bit has at most `2²⁸` points if its
free trees are in a minority group (`w ≤ 57`). This replaces the third bullet of the old §6.2.

**Lemma S2 (slices are affine).** Let all slopes of `A` on the witness and label rows be bits.
Then the free trees of `A` agree on these rows (Claim 4 on the label rows too,
`free_tree_holds_witness`). Let `C` be their class and `g ∈ A`. Then `A ⊆ σ_C(g)`
(`subset_slice_of_fixed`), and on `σ_C(g)`:
- every witness and label row is `v + u_C·e(Δ')` (`claim4Hyp_slice`);
- the label of gate `e` takes two values, `C^g_e` and `C^g_e ⊕ ℓ_C`, selected by the bit
  `γ^C_e(Δ_C)`, where `C^g_e := C_e ⊕ Σ_{i∉C} γ^i_e(g_i)·u^{(i)}_lab`. So the gate term is

      g_m[e](Δ') = const_e ⊕ γ^C_e(Δ_C)·a^g_m[e],
      a^g_m[e] := c_mult[m][e] ⊕ bit_m( H₅(iv, e, C^g_e) ⊕ H₅(iv, e, C^g_e ⊕ ℓ_C) ),

  `F₂`-affine in `Δ_C` for every hash function and every `c_mult` (`translateOn_gate_slice`, a
  model of one gate; `sum_ite_bit`, `translateOn_bit`). With `r̃`, which is affine per tree,
  `r = (Q, D)` is `F₂`-affine on `σ_C(g)` [code for the executable verifier's masks, as (Aff)].

We call `a^g ∈ F₂^{5×312}` the *effective gate bits* of the slice. For an honest prover
`a_m = F·ū_m`.

**Theorem S (certificates).**
1. (`slice_collision_sound`) Let `chall₁` be good for parallelism on `𝒫_⊥` (§4.2). If two
   distinct challenges of one slice of a class `C` have the same check value `K_c^ũ`, then every
   accepting set with the same first message and `ũ` that has a bit slope and a free tree has
   `u* = u_C`.
2. (`slice_collision_sound_affine`) If the two challenges lie in the slice that contains the
   accepting set, and the response is affine on it, `KOSGood` suffices (no `ε_par`).

*Proof.* The two challenges form a set that passes the KOS check with `h_V` their common value.
By `claim4Hyp_slice` it has (K) with slope `u_C` on the witness rows, and the tree in which the
two differ is free and in `C`. Theorem D, respectively Theorem L on the slice. ∎

So a certificate is small and easy to check, and Lemma S2 says where to look: at a base point
`Δ^b ∈ σ_C(g)`, `E₁^lin` restricted to the directions of `C` computes the level set through `Δ^b`
(a coset of `N_g`, below). If the chain can be accepted at two challenges, `N_g ≠ 0`.

**Lemma P^dec.** Let `𝒟` be an algorithm that, at the `H_T` query, outputs `⊥` or a class `C` and
two challenges as in Theorem S.1. Put `E₁^𝒟(x) := u_C[0..360) ⊕ d_pre` in the second case and
`E₁(x)` in the first. Then Lemma P holds for `E₁^𝒟` with

    Pr[Shift^𝒟] ≤ q₁·ε_par + (Q₃ + n_out)·m_𝒟·2⁻¹²⁸ + Q_T·q₁·2⁻⁷⁰⁴,

where `m_𝒟 ≤ 2⁵⁷` is the largest accepting set of a group other than the widest one on a first
message, `chall₁` and `ũ` for which `𝒟` outputs `⊥`.

*Proof.* Steps 1–4 of Lemma P. If `𝒟` outputs a pair, Theorem S.1 gives the chain's prefix. If
not, the chain's prefix is `E₁(x)` or its accepting set has at most `m_𝒟` points. ∎

Lemma P^dec is not mechanized in the one-more game; its core is `slice_collision_sound`.

### 6.3 Extractors that do not use the tables [proved; Lean]

**Evaluations.** Let `f_g`, `g ∈ Γ`, be functions that agree with one function `f₀` outside
pairwise disjoint sets `σ_g`. A deterministic algorithm with oracle access that makes `T` queries
on `f₀` gives the same output on `f_g` as on `f₀` for all but at most `T` of the `g`
(`DTree.card_detect_le`; a randomized one on average over its coins). With `f` the check value,
`σ_g` the slices of `G_B` (`|Γ| = 2⁶³`) and of `G_A` (`|Γ| = 2⁵⁷`), and the two families' answers
`r_B ≠ r_A`: an extractor that sees the response function only through `T` evaluations is wrong
with probability at least `1 − T·2⁻⁵⁷` against one of the two forgers. This is the model of the toy
run E4 (noise off the slice that does not depend on the slice). For the real masks the hypothesis
is false: off the slice the check value depends on `c_mult`, gate by gate, and §6.4 uses that. What
the lemma shows is that sampling or collision search on the check value is hopeless (`slice.py` R5:
no collision off the slice).

**The query log.** The forger can query `H₅` at every label that any slice could use, in a fixed
order: `2·2^j` labels per gate for `j` label vectors among the fixed trees, at most `2²⁶` queries.
Then the log is a function of the committed trees and not of `g*`.

So an extractor has to evaluate `H₅` itself and compare with `c_mult`.

### 6.4 Decoding the slice

Fix a class `C`, a candidate for the free class, with `w = w(C)`. For `δ` supported on the blocks
of `C` and `Δ^b ∈ σ_C(g)`, Lemma S2 gives `K_c^ũ(Δ^b + δ) − K_c^ũ(Δ^b) = Λ(δ; a^g)` with

    Λ(δ; a)  := e(δ)·(H_c(u_C, ℓ_C, 0) + ũ) + H_c(0, 0, μ₀(δ; a)) + (μ₁, …, μ₄)(δ; a) ∈ F⁴,
    μ_m(δ; a) := W_tree(u_{m,i}·δ_i mod M_i, i ∈ C) + W_gate(γ(δ) ∧ a_m).

`Λ` is `F₂`-linear in `δ` and `F₂`-affine in `a`. The level sets of `K_c^ũ` in `σ_C(g)` are the
cosets of `N_g := ker Λ(·; a^g)`. The task: find `g` with `N_g ≠ 0`. The slice enters only through
`a^g`, i.e. through the labels `C^g_e = C_e ⊕ Σ_κ b_κ(e, g)·ℓ_κ`, where `ℓ_1, …, ℓ_j` are the
distinct label vectors of the trees outside `C` other than `ℓ_C` (a tree outside `C` with label
`ℓ_C` does not change `a^g`), and `b_κ(e, g) := Σ_{i : ℓ_i = ℓ_κ} γ^i_e(g_i)`.

**Two label classes [proved; experimental].** If `j = 1`, then
`a^g[e] = a⁰[e] ⊕ b_1(e, g)·d[e]` with `a⁰`, `d` computed from four `H₅` values per gate. So `a^g`
is affine in `g`, and for each `δ` the set `{g : Λ(δ; a^g) = 0}` is the solution set of 512
linear equations in at most 112 unknowns.

> `Dec₂(a)`: fix a subspace `U` of dimension `a + 1` of the directions of `C`. For each
> `δ ∈ U∖{0}` solve `Λ(δ; a^g) = 0` for `g`. Output the first solution found, with `δ`.

Every output is a pair as in Theorem S.1. If some slice has `|N_g| ≥ 2^{w−a}`, then `N_g` meets
`U`, and `Dec₂(a)` outputs a pair. Cost: `2^{a+1} − 1` linear systems. So for first messages with
two label classes, `m_{Dec₂(a)} ≤ max(2²⁸, 2^{56−a})`. No property of `H₅` is used.

`slice.py` R1 (§6.1's forger, `a = 0`, faest-arch-opt's `F`, `G`, `W_tree`, `W_gate`, `W_crt`):
one system, unique solution `g*`, `0.03 s`; `E₁^lin` on that slice returns a level set of `2⁵⁷`
points; the same decoder for the class `G_A` finds no slice. R4 (three wrong `c_mult` bits, level
set `2⁵⁴`): found after a few guessed directions.

**Any number of label classes, full slices [completeness: proved; running time: heuristic,
experimental].** A slice is *full* if `N_g` is all of `C`'s directions.

1. *Gate bits.* Solve `Λ(δ_t; a) = 0` for `a ∈ F₂^{1560}`, for a basis `δ_t` of `C`'s directions
   (12 to 16 random directions suffice in the experiments). The solutions form an affine space
   `𝒜` that contains `a^{g*}` for every full slice `g*`. With the real tables `𝒜` is one point
   for `w ≥ 28`, and it is `F·ū` (R3). The reason: `𝒜` corresponds to the mask slopes `ū_m` that
   agree with the trees of `C` (`ū_m ≡ u_{m,i} mod M_i`) and with `ũ`; that is `5·(128 − w)`
   unknown bits against `4·128` equations, so `dim 𝒜 = max(0, 128 − 5w)` generically (R3: 23 for
   `w = 21`, 53 for `w = 15`).
2. *Candidates.* For each gate let `P_e ⊆ F₂^j` be the patterns `b` with
   `bit_m(H₅(C_e ⊕ Σ b_κ ℓ_κ) ⊕ H₅(C_e ⊕ Σ b_κ ℓ_κ ⊕ ℓ_C)) = a_m[e] ⊕ c_mult[m][e]` for the `m`
   that `𝒜` determines. The pattern of `g*` is in `P_e`. With `H₅` a random oracle each other
   pattern is in `P_e` with probability `2⁻⁵`: `|P_e| ≈ 1 + 2^{j−5}` (measured: 17.1 of 512 for
   `j = 9`).
3. *The fixed blocks.* If most `P_e` are singletons (`j ≤ 5`, or label classes with several trees
   each), each such gate gives `j` linear equations in `g` (R2: 3 classes on 9 trees: 251 gates,
   unique solution; 5 classes: 110 gates). Otherwise search depth-first over the fixed trees, one
   block at a time, and cut a branch when some gate has no pattern in `P_e` that extends the
   blocks chosen so far.

Steps 1–3 never discard a full slice: `a^{g*} ∈ 𝒜`, the pattern of `g*` is in every `P_e`, and the
search cuts only branches without it. Every `g` found is checked with `E₁^lin` on its slice.

The running time of the search is heuristic. A wrong partial assignment of `t` blocks survives
gate `e` with probability about `1 − exp(−2^{j−5−t})`, so with 312 gates the search dies at
depth `t ≈ j − 7`, after about `2^{7(j−8)+10}` nodes. Measured (real tables, `slice.py` R2;
`--j=10`):

| `j` (fixed trees, one label vector each) | `w(C)` | search nodes | Python time |
|---|---|---|---|
| 5, 7, 8 | 85, 71, 64 | `2⁹·³`, `2⁹·⁸`, `2¹⁰·⁵` | `< 0.1 s` |
| 9 | 57 | `2¹⁵·⁴`–`2¹⁷·²` | `0.5 s` |
| 10 | 50 | `2²¹·⁶` | `11 s` |
| 9, 2 wrong gates / 6 wrong gates | 57 | `2¹⁸·⁷` / `2²⁰·⁹` | `1.5 s` / `11 s` |

Step 2 costs `2·2^j·312` hash calls.

**Wrong gates [heuristic; experimental].** A forger can make `a` gates wrong. Then
`N_g ⊇ {δ : γ^C_e(δ) = 0 on these gates}` has codimension at most `a`, the forger is accepted
`2^a` times less often, and step 1 fails for directions outside `N_g`. With two label classes
`Dec₂(a)` covers this, with proof. In general we replace step 1: the slopes `ū_m` with
`ū_m ≡ u_{m,i} mod M_i` for `i ∈ C` and `ũ = H_c(u_C, ℓ_C, ū₀) + (ū₁..ū₄)` are the solution of a
linear system (unique for `5w ≥ 128`, generically), `a := F·ū`, and the search of step 3
tolerates `a` gates without a pattern. This assumes that the slopes on a level set agree with the
trees' VOLE values. For a level set of `2^d` points that is `128·d` equations on 440 unknowns per
mask, so we expect it for `d ≥ 4`, without proof.

### 6.5 What this gives, and what it does not

Let `Dec(J)` run §6.4 for every class `C` of a group other than the widest one that has at most
`J` label vectors among the trees outside it, tolerating enough wrong gates to find level sets
of more than `m_J := 2^{120−7(J+1)}` points. A class with more than `J` label vectors outside has
`w(C) ≤ 120 − 7(J+1)`, so its accepting sets have at most `m_J` points anyway.

> **(H-dec)** If a slice of such a class has a level set of more than `max(m_J, 2²⁸)` points,
> `Dec(J)` outputs a pair of it.

With (H-dec), Lemma P^dec and Lemma S1 give Lemma P, hence U1, with
`(Q₃+ℓ+1)·max(2^{−15−7J}, 2⁻¹⁰⁰) + q₁·2⁻¹³⁴` in place of `(Q₃+ℓ+1)·2⁻⁷¹`, for a reduction that
runs `Dec(J)` at each `H_T` query:

| `J` | search nodes per class | largest set missed | `H₂³` term | at `2⁶⁴` queries |
|---|---|---|---|---|
| ≤ 8 | `≤ 2¹¹` | `2⁵⁷` (9 label vectors, §6.1 with 9 labels) | `2⁻⁷¹` | `2⁻⁷` |
| 9 | `2¹⁷` (`2²¹` with 6 wrong gates) | `2⁵⁰` | `2⁻⁷⁸` | `2⁻¹⁴` |
| 10 | `2²²` | `2⁴³` | `2⁻⁸⁵` | `2⁻²¹` |
| 11 | `≈ 2²⁸` (extrapolated) | `2³⁶` | `2⁻⁹²` | `2⁻²⁸` |
| 12 | `≈ 2³⁵` (extrapolated) | `2²⁹` | `2⁻⁹⁹` | `2⁻³⁵` |

Each step costs a factor of about `2⁷` in the reduction's work per `H_T` query and gains 7 bits.
Beyond `J = 12` Lemma S1's `2²⁸` takes over.

**Status of (H-dec).** Proved for first messages with two label classes (`Dec₂`). In general it is
a conjecture supported by the experiments above. What a proof lacks:
- The tables are `H₅` values at labels that the forger chooses. The candidate counts and the
  search bound treat them as independent random tables. A forger can try many first messages;
  that it cannot bias 312 gates enough is plausible and not proved.
- Level sets of positive codimension with more than two label classes use the slope assumption
  of §6.4.
- For `J ≥ 11` the cost is extrapolated.

**No hardness result.** We found no reduction from a hard problem, and do not expect one in the
range that matters. The two natural candidates are easy here. MinRank: "`Λ(·; a^g)` has a kernel"
with `a^g` affine in `g` is a MinRank instance, but with 512 rows against at most 57 columns, and
the kernel attack (guess `δ`, solve for `g`) is `Dec₂`. Planted constraint satisfaction: each gate
is a constraint of density `2⁻⁵` on a pattern of `j` bits, and there are 312 of them on at most
112 unknown bits; pruning works until `j` is so large that `w(C)` is small. A forger that forces
a search of `2^{7(j−8)+10}` nodes is accepted with probability at most `2^{−8−7j}` per `H₂³`
query: its work per expected `Shift` grows as fast as the decoder's.

**Rewinding.** An accepted forgery names its slice (the accepted `Δ'` lies in it). A reduction
could rewind to the `H_T` query and program the right prefix. But the forger then sees a new `h`
and need not complete that chain again, and the two runs together make up to `2ℓ` Issuer queries
for `ℓ + 1` forgeries. This is the forking loss on a one-more game; we see no bound better than
U1's from it.

### 6.6 Not mechanized

(Aff) on slices for the executable verifier's masks (Lean has the gate model,
`translateOn_gate_slice`). Lemma P^dec in the one-more game. The decoders and their analysis
(`Dec₂`'s proof is linear algebra on Lemma S2's formula; the search bound is heuristic).

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
- **(iii′) A FAEST-style check** [estimate]. The `+1.1 kB` of (iii) comes from keeping four
  direct masks of λ bits for the 512-bit check. With affine masks the response is affine for
  every first message, and FAEST's own check (a `λ + 16`-bit VOLEHash masked by `λ + 16` rows,
  one λ-bit QuickSilver mask) would do: 272 mask rows, `16·34 = 544` bytes of corrections, no
  `c_mult` (`−195`), no label rows (`−256`), an 18-byte `ũ` (`−46`): about `+50 B`. But L3's
  argument on triples needs `ε_v = 2⁻⁵¹²` and does not apply; the per-tree argument for affine
  responses would replace it, and `zk.md` would be redone. Not analyzed here.
- **(v) Assumption.** U2 under A-OMPR⊕17 (or the committed variant of §7) is tight today.
- **(vi) More direct masks** [heuristic; experimental]. Each mask adds one bit per gate to the
  decoder's test, so candidate sets halve and one more label class costs what the previous one
  did. A direct mask costs a 39-byte row of `c_mult` and 16 bytes of `ũ`: `+55 B`. With 8 masks
  (`+165 B`), `slice.py --masks=8 --j=12` decodes 12 label vectors in `2¹⁷·⁵` nodes: §6.5's
  `2⁻⁹⁹` row at the cost of today's `2⁻⁷⁸` row. The masks must be direct: a hashed mask adds
  unknown slopes without equations. This is still (H-dec), not a proof. VOLEHash would have
  `4 + x` outputs (L3 and `zk.md` to be re-instantiated).
- **(vii) Bit constraints on the label rows** [proved given L4 on these rows; ZK not redone].
  Add the QuickSilver constraints `Θ_j² = Θ_j` for the λ label rows (no bytes: the QuickSilver
  proof does not grow). Then (B) covers the label rows, Lemma S1's case cannot occur, and the
  `2⁻¹⁰⁰` floor of §6.5 goes away. On its own this does not help against hidden slices.
- **(viii) Binding the group or the slice in a hash** [argued; nothing cheap found].
  - A declared tree index, group or slice in `H_T`'s or `H₂¹`'s input: the verifier cannot check
    it (an honest prover has no slice), so a forger declares the widest group. No effect.
  - Anything the verifier recomputes from its own view depends on `Δ'`, and an honest prover can
    commit only to `Δ'`-independent values. For the labels there are none to bind: the linear
    functions of the verifier's labels that do not depend on `Δ'` are `a·L` with `a·G = 0`, and
    they vanish identically because `L = G·Q_lab`.
  - Digests of both labels of some gates in the first message, the verifier checking that its
    label's digest is one of the two. Then the labels used on the accepting set are in the log,
    and each such gate gives its pattern exactly. This needs two 16-byte digests per gate and
    about `n/j` gates for `n` fixed bits in `j` label classes (8 to 10 gates, `≈ 300 B`, when
    every fixed tree has its own label; many more when there are few classes, which `Dec₂`
    handles anyway). More bytes than (vi), a new leakage to argue in `zk.md` (a digest of the
    sibling label), and still no proof of completeness. Not pursued.

**Summary.** For a proved tight U1: (iii), (iii′) or (v). Without a protocol change, §6.5 is
the best statement we have, and it is conditional. (i) is mandatory in all cases.

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
| slice of a class; an accepting set with fixed trees outside `C` lies in one | `slice`, `subset_slice_of_fixed`, `isFixed_of_subset_slice`, `slice_translate` |
| Lemma S1: a slope that is not a bit | `card_le_of_nonbit_slope`, `card_sq_le_of_nonbit_slope` |
| Lemma S2: witness rows on a slice; a gate with two labels is affine; one gate of a CRT mask on a slice | `claim4Hyp_slice`; `TranslateOn`, `translateOn_bit`, `translateOn_gate`; `sum_ite_bit`, `translateOn_gate_slice`, `affineOn_of_translateOn` |
| Theorem S.1, S.2 | `slice_collision_sound`, `slice_collision_sound_affine` (`KOSGood.mono`) |
| §6.3: `T` evaluations detect at most `T` slices | `DTree`, `DTree.eval`, `DTree.queries`, `DTree.eval_congr`, `DTree.card_detect_le` |

Not mechanized: §3 (the forgers); (Aff) for the executable verifier's masks, on `S` and on
slices (the gate model `translateOn_gate_slice` is: any hash, any `c_mult`, labels and selection
bits as sums over the trees); Lemma P^∞, Lemma P^lin and Lemma P^dec as statements about the
one-more game (they would need `KOSPar` as a bad event at `H₂¹` in `ROM/Chains.lean`'s style, and
the extractor as a function of the log); §6.4–§6.5 (the decoders).

Non-vacuity. `slice_collision_sound` takes the hypotheses of `witness_determined` (`KOSPar`:
`exists_kosPar`) and the tree form of the witness rows on `S`, which is `Claim4Hyp.tree_form`'s
shape; `claim4Hyp_slice` derives `Claim4Hyp` on a slice from it, so the certificate's hypotheses
hold for every pair of points of a slice. `translateOn_gate_slice` has no hypothesis beyond
characteristic 2 and equal label offsets on `C`.

`scripts/pomfrit-lemmap-tight/toy.py [seed]`: four trees of widths `(3, 2, 2, 2)`, `GF(2³²)`,
a KOS check of the same shape. E1: §3.1's level sets. E2: Theorem D over all pairs. E3: `E₁^lin`.
E4: §6.1's hidden slice. Runs in seconds.

`scripts/pomfrit-lemmap-tight/slice.py [seed] [--quick] [--masks=N] [--j=J [--wrong=A]]`: the
verifier's response for FAEST-EM-128f shapes (17 trees, `GF(2¹²⁸)`, 312 gates, 5 masks) with
faest-arch-opt's matrices `F`, `G`, `W_tree`, `W_gate`, `W_crt` read from
`VoleMole/Verifier/CrtData.lean`. Not modelled: the GGM trees (per-tree VOLE values are sampled),
all but 8 witness rows, QuickSilver; VOLEHash is a polynomial hash of the same shape; `H₅` is
BLAKE2b. R0: the tables' identity, an honest first message. R1: §6.1's forger and `Dec₂`. R2: the
search, wrong gates, label classes of several trees. R3: uniqueness of the gate bits. R4: `Dec₂`
with wrong gates. R5: no collisions off the slice. About 20 s; `--j=10` adds 30 s.

## 10. Open

1. (H-dec) of §6.5: a proof that the decoder finds every large level set, for forgers that choose
   the labels (and so the `H₅` tables) adversarially; or a forger that defeats it at a cost below
   the decoder's. The two-class case is proved.
2. Mechanize Lemma P^lin and Lemma P^dec in the one-more game: (Aff) for `Verifier`'s masks on
   `S` and on slices, the extractor on the log, `KOSPar` as a bad event at `H₂¹`, and a `pomEps'`
   without the `2⁵⁷` for forgers with at most two label classes. A restriction on forgers is not a
   security statement, so this was not attempted.
3. The committed-shift variant of A-OMPR⊕17 (§7): is it implied by OMPR?
4. (iii′) of §8: the size and the consistency analysis of a FAEST-style check with affine masks.
