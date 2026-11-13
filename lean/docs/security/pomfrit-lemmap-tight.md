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
unless another file is named; §6A: `Seed/SliceDecode.lean`, `ROM/LemmaPClass.lean`). *Code*: read off the C++ (`vole_commit.inc`,
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
| T | **Time against loss, with `E₁`'s default** (the widest prefix group). With a decoder for up to `J` label vectors among the fixed trees, Lemma P's `H₂³` term becomes `2^{−15−7J}` per query: `2⁻⁷⁸` at `J = 9` (`≈ 2¹⁷` search nodes per class and `H_T` query; `2²¹` with wrong gates), `2⁻⁸⁵` at `J = 10` (`2²²`), `2⁻⁹⁹` at `J = 12` (`≈ 2³⁵`, extrapolated). The decoder's completeness against every forger is not proved (conjecture (H-dec)). Its treatment of wrong gates rests on an assumption that fails for some level sets of codimension `≥ 4` (row Rig). Superseded down to `2⁻⁸⁵` by row Cls | heuristic; experimental | §6.5 |
| Cls | **The class extractor: `2⁻⁷⁸` per `H₂³` query, no conjecture.** An accepting set lies in a slice of *one class*, or it has at most `2^{⌊w/2⌋}` points for the width `w` of its prefix group. So a prefix group that is split into many classes cannot be completed, and the default must be the widest class, not the widest prefix group. §6.1's forger with 9 label vectors is then extracted without any decoding. The default can be wrong only if two classes have width `≥ 51`; they leave at most one tree. `Dec^cls` exhausts that tree (`2⁸`), solves for the blocks of the other class by linear algebra and guesses 7 directions: fewer than `2¹⁵` linear systems per `H_T` query, with proof, and no property of `H₅`. **Lemma P holds for `E₁^cls` with `(Q₃ + n_out)·2⁻⁷⁸ + q₁·2⁻¹³⁴` in place of `(Q₃ + n_out)·2⁻⁷¹`**; U1's term at `2⁶⁴` queries becomes `2⁻¹⁴`. With `2²²` systems per `H_T` query: `2⁻⁷⁹`; with `2³⁶`: `2⁻⁸⁵` | proved; the masks' structure: code; Lean for the core (`class_or_small_dec`, `extract_or_class`, `dec_cert_sound`, `dec_cert_complete`, `card_decQ_le`); the one-more game: not mechanized, `pomfrit_U1_sim` is unchanged; experimental | §6A |
| Rig | **Table facts for wrong gates.** A level set that contains all directions of one tree has the trees' mask slopes and no wrong gate (17 rank computations). On level sets of codimension 4 (`deg D ≤ 115`) and 6 (`x⁶ | D`) there are first messages whose mask slopes differ from the trees' VOLE values on every tree, with more than 150 changed gates: §6.4's slope assumption and its "at most `a` gates without a pattern" are false there. `Dec^cls` does not use them | proved (the examples); experimental | §6A.6 |
| M | The loss cannot be moved into the OMPR experiment (more targets): a wrong prefix gives a preimage of `t_j ⊕ r ⊕ r'`, which is not a target, and combining preimages across shifts is Theorem R's obstacle (`ompr-shift-algebra.md` §2). By D, PomFRIT needs less than A-OMPR⊕17: the shift index is fixed, though hidden, when the target is requested | proved (first part); remark | §7 |
| C | Protocol: (i) keep `ũ` in `hash_to_target`: it is what makes D true; (ii) binding `h_V` as well adds nothing; (iii) per-tree affine masks (no CRT masks) would make L unconditional, at about `+1.1 kB` per signature with the 512-bit check, about `+50 B` with a FAEST-style check and a different analysis; (iv) more grinding or other tree shapes move `2⁵⁷` by a few bits only; (vi) each extra direct mask (`+55 B`) lets the decoder handle one more label class at the same cost; (vii) bit constraints on the label rows (`0 B`, ZK unchanged) remove Lemma S1's case; with `E₁^cls` they are not needed above `2⁻⁹²`; (viii) binding the group or the slice in a hash: no cheap variant works | (i), (ii): proved; (iii): proved given the layout, sizes: estimate; (iv): proved; (vi): heuristic, experimental; (vii): proved given L4 on those rows; ZK: the hybrids of `zk.md` go through, not re-mechanized; (viii): argued | §8 |

**In one paragraph.** The `2⁵⁷` is tight for Lemma P's extractor and for every extractor that
ignores `ũ`. It is not inherent in the protocol as implemented: `hash_to_target` hashes `ũ`, and
`ũ` commits the forger to one prefix group, up to `2⁻¹³⁴` per `H₂¹` query. What remains is
computational: the reduction must *find* that group when `H_T` is queried. For first messages
whose trees agree on the label rows this is linear algebra and U1's extra term vanishes. For the
others the group hides in one of up to `2⁶³` slices. §6 reduces extraction to finding the slice
(any collision of the check value inside a slice is a certificate), shows that this cannot be
done by an extractor for which the check value off the slice is noise, and gives a decoder that
reads `c_mult` against the `H₅` table. For `E₁`'s default that decoder is proved for two label
classes only, and its general case is the conjecture of §6.5.

§6A changes the default instead. An accepting set lies in a slice of one *class* (trees with the
same witness **and label** rows), so the forgers that hide a slice among many label vectors hide
it in the widest class, and `E₁^cls`, which outputs the widest class, needs no decoder against
them. Decoding is needed only between two classes of width at least 51, where at most one tree is
left over, and there the two-class decoder with one tree exhausted is complete, with proof. This
gives Lemma P, hence U1 on paper, with **`2⁻⁷⁸` per `H₂³` query in place of `2⁻⁷¹`** (`2⁻⁷⁹`,
`2⁻⁸⁵` for more work), for a reduction that solves fewer than `2¹⁵` small linear systems per `H_T`
query. The per-chain step is in Lean (`class_or_small_dec`), with the structure of the CRT masks
as a hypothesis. The one-more game with `E₁^cls` is not mechanized: `pomfrit_U1_sim` still has
`2⁻⁷¹`. Below `2⁻⁸⁵` the statement is conditional, as before (§6A.6).

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

*Correction (§6A.6).* The expectation is wrong for some level sets of codimension `≥ 4`: there
are first messages whose mask slopes differ from the trees' VOLE values on a level set of `2⁵³`
points, with more than 150 changed gates. This step of the heuristic decoder is not complete.

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
a conjecture supported by the experiments above, and the decoder's step for wrong gates rests on
an assumption that fails on the level sets of §6A.6 (codimension `≥ 4`, slopes that are not the
trees'). §6A obtains the rows `2⁻⁷⁸` and `2⁻⁸⁵`
of the table without it, by changing the default: the rows above are for `E₁`'s default and are
kept for the record. What a proof lacks:
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
`translateOn_gate_slice`). Lemma P^dec in the one-more game. The search of §6.4 and its analysis
(the search bound is heuristic). `Dec₂` with one tree exhausted is `Dec^cls`, in Lean (§6A.5).

## 6A. The class extractor [proved; Lean for the core; experimental]

§6 keeps `E₁`'s default, the widest *prefix group*, and asks a decoder to find the slices of
every class of every other group. That default is the mistake. Corrected, the hard case of §6.4
(many label vectors among the fixed trees) needs no decoder at all.

### 6A.1 An accepting set lives in one class

**Lemma C.** Let `A` be an accepting set with (K), a bit witness slope `u*` and a free tree, and
let `G` be the prefix group of `u*`. Then one of:

- (a) every label slope is a bit. The free trees are in one class `C ⊆ G`, every other tree is
  fixed, `A ⊆ σ_C(g)` and `|A| ≤ 2^{w(C)}`;
- (b) some label slope is not a bit, and `|A| ≤ 2^{⌊w(G)/2⌋}`.

*Proof.* (a) is Claim 4 on the label rows, which are hashed rows of tree form
(`free_tree_holds_witness`): a free tree holds the slope of every such row. (b) is Lemma S1 with
`G`: every tree outside `G` is fixed (T). ∎

So a prefix group counts through its widest class and through half its width, not through its
width. Take §6.1's forger with 9 label vectors on the 9 trees of `G_A`. `G_A` has width 63, but
its classes have width 7: completing with `G_A` is accepted with probability at most `2⁻⁹⁷` per
`H₂³` query (case (b), `2³¹` points). `E₁` outputs `G_A`'s prefix all the same. The widest class
is `G_B`, the forger's (`slice.py` R6, first line).

### 6A.2 `E₁^cls` and `Dec^cls`

**`E₁^cls(x)`** (Lean `clsExt`). Steps 1–4 of `E₁`, keeping the label rows of each alive tree.
Group the alive trees into classes. Let `C₁` be the widest class (ties: least index).

1. If `w(C₁) ≤ 50`, output `E₁(x)`.
2. Otherwise, if a class `C₂` with `w(C₂) ≥ 51` has a prefix other than `C₁`'s, run
   `Dec^cls(C₂)`. If it outputs a pair, output `C₂`'s prefix.
3. Otherwise output `C₁`'s prefix.

A set of trees of width `≥ 51` has at least 8 trees (`eight_le_card_of_wide`: 7 trees have width 49, or 50 with tree 0). So there are at most two
such classes (`not_three_wide`), `C₂` in step 2 is unique, `w(C₂) ≤ 57` (`minority_weight_le`),
and `C₁` and `C₂` leave at most one of the 17 trees.

**`Dec^cls(C₂)`** (Lean `dec`; `slice.py` `ClassDecoder`). Let `T₁` be the alive trees outside
`C₂` with `C₁`'s label vector, `R` the alive trees outside `C₂` with a third label vector (at most
one tree), and `U` the 127 nonzero directions in the first 7 bits of one tree of `C₂`. The other
blocks are fixed: a dead tree at the challenge that hides its dead leaf, an alive tree with `C₂`'s
label vector and another witness at 0.

> For each value `g_R` of the blocks of `R` and each `δ ∈ U`: solve `Λ(δ; a^{(g₁, g_R)}) = 0` for
> the blocks `g₁` of `T₁`. With `g_R` fixed, `a^g` is affine in `g₁` (§6.4, two label classes), so
> this is a linear system of 512 equations in at most 64 unknowns. For a solution, check
> `K_c^ũ(Δ^b + δ) = K_c^ũ(Δ^b)` at the base point `Δ^b` of the slice, and output the pair.

Cost: at most `127·2⁸ < 2¹⁵` linear systems and `4·312·2⁸ < 2¹⁹` values of `H₅` per `H_T` query.
Written as an algorithm that only evaluates the check value (the coefficients of each system are
`65` increments of `K_c^ũ`): at most `127·2⁸·2·65 + 2 < 2²²·¹` evaluations (`card_decQ_le`,
`card_basePts_le`), and its output depends on the check value at these points only (`dec_congr`).
This does not contradict §6.3: there the check value off the slice is the same function for every
hidden slice. For the real masks its increments along `C₂` are affine in `g₁`, and the decoder
reads the slice off them.

**Lemma Dec.**
1. (Soundness; `dec_sound`, `dec_cert_sound`.) Every output is a pair of distinct challenges of
   one slice of `C₂` with the same check value: a pair as in Theorem S.1. No hypothesis.
2. (Completeness; `dec_cert_complete`.) If some slice of `C₂` contains a set of more than `2⁵⁰`
   challenges with one check value, `Dec^cls(C₂)` outputs a pair.

*Proof of 2.* Let the set lie in the slice at `g = (g₁, g_R)`. By Lemma S2 the response is affine
on the slice. So `N := {δ in the blocks of C₂ : K(Δ + δ) = K(Δ)}` is the same for every `Δ` of the
slice, it is a subgroup, and the set lies in a coset of it: `|N| > 2⁵⁰`. The blocks of `C₂` have
`2^{w(C₂)} ≤ 2⁵⁷` elements and `|U ∪ {0}| = 2⁷`, so two sums `a + ν`, `a ∈ U ∪ {0}`, `ν ∈ N`,
coincide, and `N` contains some `δ ∈ U`. For this `δ` and this `g_R`, `g₁` solves the system. Every
solution `g₁'` of the system is a slice in which `δ` is a direction of a level set, because the
system *is* `Λ(δ; a^{(g₁', g_R)}) = 0`. So the check passes. ∎

`slice.py` R6 (real tables, classes of widths 56 and 56, tree 0 with a third label vector and a
third witness, 6 wrong gates so that the level set has `2⁵⁰` points): the pair is found after
`26811` systems, `17 s` in Python; for the other class all `32512` systems have no solution
(`--cls=6`).

### 6A.3 Lemma P^cls and Theorem U1^cls

**Lemma P^cls.** Lemma P (`pomfrit.md` §5) holds with `E₁^cls` in place of `E₁` and

    Pr[Shift^cls] ≤ q₁·ε_par + (Q₃ + n_out)·2⁻⁷⁸ + Q_T·q₁·2⁻⁷⁰⁴,      ε_par < 2⁻¹³⁴.

*Proof.* Steps 1–3 of Lemma P's proof. Discard also the event that `chall₁` is not good for
parallelism on `𝒫_⊥` (§4.2): `q₁·ε_par`. Take an accepted chain with `|𝒜| ≥ 3`, a bit witness
slope `u*` and a free tree `i₀`. We show that `E₁^cls(x)` is the prefix of `i₀`, or `|𝒜| ≤ 2⁵⁰`
(Lean `class_or_small`, `class_or_small_dec`). Then steps 7–8 with `2⁵⁰` for `2⁵⁷`.

- *`Dec^cls(C₂)` output a pair.* By Theorem S.1 `u*` is `C₂`'s witness, so the prefix of `i₀` is
  `C₂`'s.
- *Otherwise, and `w(C₁) ≥ 51`.* The output is `C₁`'s prefix. Suppose the prefix of `i₀` is
  another one. In case (a) of Lemma C, `𝒜` lies in a slice of the class `C` of `i₀`. If
  `w(C) ≤ 50`, done. If not, `C` is the class `C₂` of step 2, the decoder ran and output nothing,
  and by Lemma Dec.2 `|𝒜| ≤ 2⁵⁰`. In case (b), the prefix group of `i₀` is disjoint from `C₁`, so
  it has at most 9 trees and width at most 64 (`width_le_of_disjoint_wide`): `|𝒜| ≤ 2³²`.
- *`w(C₁) ≤ 50`.* The output is `E₁(x)`. Suppose the prefix group `G` of `i₀` is not the widest.
  In case (a), `|𝒜| ≤ 2^{w(C)} ≤ 2⁵⁰`. In case (b), `w(G) ≤ 57` and `|𝒜| ≤ 2²⁸`. ∎

**Theorem U1^cls.** For every classical adversary `A` against Def. 2.5 there is a `B` such that

    Adv^{omuf}_{PomFRIT}(A) ≤ Adv^{ompr}_{UOV}(B; Q_T + ℓ + 1, ℓ) + ε_ext(N; q₁, q₂, Q₃ + ℓ + 1)
                             + (Q₃ + ℓ + 1)·2⁻⁷⁸ + q₁·2⁻¹³⁴ + Q_T·q₁·2⁻⁷⁰⁴ + ε_DS.

`B` is U1's reduction with `E₁^cls` for `E₁`: per `H_T` query, `E₁`'s work on the label rows too
and, if two classes have width `≥ 51`, fewer than `2¹⁵` linear systems and `2¹⁹` values of `H₅`.
`B` samples `H₅` lazily; its own evaluations are entries that `A` may ask for later and gets
consistently, as for the cipher in U1. At `2⁶⁴` queries the term is `2⁻¹⁴` in place of `2⁻⁷`
(`loss_cls_at_2_64`).

*What the proof uses.* Lemma P's events (`ε_ext`); `ε_par` (§4.2, Lean); Claim 4 and Lemma S1 on
the label rows (Lean, generic; that the label rows of the executable verifier have the tree form:
code, `zk.md` H3); Lemma S2 and the two-label form of the gate terms (the masks of
`vole_commit.inc`: code; gate model in Lean, `translateOn_gate_slice`, `twoLabel_gate`). It uses
no property of `H₅`, no bound on the forger's label vectors, and no conjecture.

*Tightness for `E₁^cls`.* Classes of widths 56 and 50 (trees `1..8`, and tree 0 with six trees)
and two trees with two more label vectors: the slice of the second class hides among `2⁷⁰`, in
three label vectors on two classes and two trees, and `E₁^cls` does not look for it. `2⁻⁷⁸` per
`H₂³` query. Like §3.1 this is not a forgery.

### 6A.4 More work, a smaller term [proved; not mechanized]

The proof has two parameters: the least width `θ` of a class that is decoded, and the trees it
exhausts. Let `m` be the largest width below `θ`. The same argument, with a subgroup of `2^{57−m}`
directions, gives:

| `θ` | trees left over by two classes of width `≥ θ` | linear systems per `H_T` query | largest set missed | `H₂³` term | at `2⁶⁴` queries |
|---|---|---|---|---|---|
| 51 | 1 (8 bits) | `2⁷·2⁸ = 2¹⁵` | `2⁵⁰` | `2⁻⁷⁸` | `2⁻¹⁴` |
| 50 | 2 (14 bits) | `2⁸·2¹⁴ = 2²²` | `2⁴⁹` | `2⁻⁷⁹` | `2⁻¹⁵` |
| 49 | 3 (22 bits) | `2¹⁴·2²² = 2³⁶` | `2⁴³` | `2⁻⁸⁵` | `2⁻²¹` |
| 43 | 4 (28 bits) | `2¹⁵·2²⁸ = 2⁴³` | `2⁴²` | `2⁻⁸⁶` | `2⁻²²` |

Widths are `7k` or `7k + 1`, so the widths below 51, 50, 49, 43 are 50, 49, 43, 42. In each row
three classes of width `≥ θ` do not exist, and case (b) of Lemma C gives at most `2³⁸` points. The
Lean statements are for `θ = 51`. The last two rows are not a reasonable amount of work per `H_T`
query; they are what exhaustion costs. Below them the leftover trees must be decoded, not
exhausted, and that is §6.4's search with its conjecture (§6A.6).

### 6A.5 Lean

`Seed/SliceDecode.lean`, `ROM/LemmaPClass.lean` (§9). The decoder is a function `dec` of the check
value. `class_or_small_dec` is the per-chain statement: for trees of `2^{width i}` challenges,
`KOSPar`, Claim 4's hypotheses on the witness rows (bit slopes) and the label rows (any slopes),
the response affine on the slices of each class (`AffineOn`) and two-label in the blocks of `T₁`
(`TwoLabelOn`; both proved for the executable verifier, below), and decoder data that cover the
slices (`basePts_cover`), the output of `clsExt`
is the prefix of every free tree, or `|𝒜| ≤ 2⁵⁰`. `extract_or_class` is `extract_or_major` with
this conclusion. `per_query_bound_cls`: `2⁵⁰/2¹²⁸ = 2⁻⁷⁸`.

**For the executable verifier** (`Verifier/Bridge/MaskSlices.lean`, `ROM/LemmaPClassDet.lean`).
`AffineOn` and `TwoLabelOn` are no longer hypotheses:
- `qMask_form`: mask `m` of `crtReconstructAt` at the blocks `Δ` is
  `Σ_i treeTerm m i (Δ_i) + Σ_{e < 312} gateF m e Δ`. `treeTerm` is affine in the block
  (`treeTerm_translate`, from `polyMod_xor`). `gateF` is the gate model: a function of the label
  `C₀_e + Σ_i γ_{i,e}(Δ_i)·ℓ_i` (`label_form`) plus the selection bit times the `c_mult` bit. For
  any tables, gate hash, `c_mult` and committed keys.
- `chain_affineOn`, `chain_twoLabelOn`: Lemma S2 and the two-label identity for a chain of the
  verifier. One hypothesis: the trees of the set have the same label rows.
- `chain_claim4_lab`: Claim 4's hypotheses for the label rows (they are hashed rows).
- `pomfritT_extract_class_chain`: `pomfritT_extract_major_chain` with `clsExt` and `2⁵⁰`, from
  `KOSGood`, `KOSPar` and the blocks `hd` of the trees outside `S` on the accepting set. The
  decoder's data are fixed: directions `treeDirs i` (the challenges supported on one tree of the
  class, `2⁷` or `2⁸`), linear unknowns `clsT1` (the alive trees outside the class with the label
  rows of the widest class), generators `genOf` (unit vectors), base points `Seed.basePts`. The
  certificate `clsCert` is "the decoder has a candidate" (`Seed.decCand`). It reads the check
  value at `clsPts` only (`clsCertK_congr`, `card_clsPts_le`). For the verifier the prediction is
  exact, so a candidate is a pair (`clsCert_iff_dec`); the two extra evaluations of `Seed.dec` are
  not needed. The count in Lean uses `2⁸ − 1` directions and 120 generators (zero for the bits
  outside `clsT1`): at most `255·2⁸·2·121 < 2²⁴` points, against the paper's `2²²·¹`.

**In the random-oracle and ideal-cipher model** (`ROM/LemmaPCls.lean`, `ROM/LemmaPClsBound.lean`):
- `prU_kos_par_le`, `parEps_le`: a uniform 136-byte `chal1` is not good for parallelism with
  probability at most `2⁻¹³⁴` (at most 1441 hashed rows). `parBad` is the bad event at `H₂¹`.
- `combBad_of_acceptC`, `combBad_trace_icDC`: the deterministic step with a goal that reads the
  chain, with `KOSPar` and with the committed dead leaves that the accepting set hides.
- `GoalC`, `ClsExtracted`: Lemma P^cls's goal on a chain and on an output of the adaptive game.
  On an output the gate hash is read off the prover's log (`h5Of`), the dead blocks off its
  committed dead leaves (`deadR`, `hdOf`). `clsExt` reads its certificate at one tree
  (`clsTarget`, `clsExt_congr_cert`), and the goal reads `H₅` at the gate inputs of `clsPts` of
  that tree only (`goalC_withH5`). `ClsCovered`: these inputs are `H₅` queries of the prover's
  log. `clsExtracted_of_goalC`: for a covered log the goal at the verifier's chain is the goal
  at the output.
- **`pomfritT_accept_le_cls`**: for one adaptively chosen statement with any target function of
  `chal1`, `Pr[accept ∧ ClsCovered ∧ ¬ClsExtracted] ≤` the bound of `pomfritT_accept_le_major`
  with `(Q₃ + 1)·2⁵⁰/2¹²⁸` for `(Q₃ + 1)·2⁵⁷/2¹²⁸`, plus `(q₁ + 1)·2⁻¹³⁴`.
- `Audit/PomfritLemmaPCls.lean`: the hypotheses at real objects.

Not mechanized, and why:
- *The one-more game.* `pomfritT_accept_le_cls` is item (1) of `pomfrit.md` §6.4 for `E₁^cls`.
  Items (2)–(9) are not done: `E₁^cls` as a function of the log at the `H_T` query (`e1P` with
  the label rows, `ũ` from `x`, the dead blocks and `h5Of`), the ordering step (the hint at the
  ghost log is `clsExt` on the output; `e1P_eq_major`), `pfail_events` and the assembly. The
  decoder's `H₅` evaluations must be in the log. Planned route: the game is unchanged, and the
  forger is wrapped so that it makes the decoder's `H₅` queries before each `H_T` query and for
  each forgery before it stops; `ClsCovered` for the derived provers is then an invariant of the
  wrapped run. This invariant is not proved. **`pomfrit_U1_explicit` and `pomfrit_U1_sim` are
  unchanged, with `2⁻⁷¹`.** U1^cls is a paper theorem; its per-chain step and its adaptive bound
  for one statement are mechanized for the executable verifier.

### 6A.6 What remains of (H-dec), and a correction to §6.4

With `E₁^cls` the decoder never meets many label vectors on many trees: the trees outside a class
that is not the widest are the widest class (one label vector) and what the two leave over. (H-dec)
is needed only to go below §6A.4: to decode a second class when 3 or more trees are left over, and
third classes. For a second class the leftover trees carry at most 5 label vectors next to
`C₁`'s (`j ≤ 6`), the candidate sets of §6.4 step 2 have about `1 + 2^{j−5} ≤ 3` patterns, and the
search is short in the experiments (R2: at most `2¹¹` nodes for `j ≤ 8`). We have no proof. What a
proof needs:

- *A property of `H₅`.* For the label vectors and the slice a forger commits to, most gates must
  have few candidate patterns: `|P_e|` close to `1 + 2^{j−5}`, the count for a random table. The
  forger chooses its labels after it has seen the table, so this is not a statement about one
  random table. A union bound over all label vectors only gives candidate sets several times
  larger [estimate], and we know no better argument. `Dec^cls` needs no such property because for
  one label vector `a^g` is affine in the blocks, for every table.
- *Level sets of positive codimension.* §6.4 ("Wrong gates") assumes that the mask slopes on a
  level set are the trees' VOLE values, and that at most `a` gates lose their pattern on a level
  set of codimension `a`. Both fail (`slice.py` R7, faest-arch-opt's tables):
  - On `N = {δ : deg D(δ) ≤ 115}`, `D = W_crt·δ`, of codimension 4, the forger can commit trees
    with `u_{m,i} = (ū_m + P) mod M_i`, `P` the field polynomial, and gate bits for the
    product by `P`: for `δ ∈ N` the product `P·D(δ)` has degree below 247 and vanishes in the
    field, so the mask slope is still `ū_m`, while every tree's value differs and 173 gates
    change. The same with `P/x` on `{x⁶ | D}` (codimension 6, 156 gates). This uses the places
    of the tables' CRT (`vole_mult_tables.py`, `Verifier/CrtSearch.lean`): `∞³`, `x⁵`, `(x+1)⁵`,
    `(x²+x+1)²` and every irreducible of degree 3 to 6 and one of degree 8, of total degree
    `127 = 247 − 120`. The level set must kill a place beyond its multiplicity; `∞³` is the
    cheapest, at codimension 4. On `{deg D ≤ 116}` and `{x⁵ | D}` there is no such solution.
  - What does hold: if the level set contains all directions of one tree, the slopes are the
    trees' and no gate is wrong (the linear system `W_tree(d·δ) + W_gate(γ(δ) ∧ b) = 0` on one
    tree's directions has only the zero solution, for each of the 17 trees). On the level sets
    of codimension 1 to 3 that we tried (random ones, the kernels of gate forms, the two families
    above) the slopes are the trees'.

  So the heuristic decoder of §6.4 is incomplete against these first messages when the level set
  has codimension `≥ 4`, and §6.5's figures for wrong gates do not cover them. `Dec₂(a)` and
  `Dec^cls` guess a direction of the level set and are not affected.

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
- **(vii) Bit constraints on the label rows** [soundness: proved given L4 on these rows; ZK: the
  hybrids go through, not re-mechanized].
  - *The change.* QuickSilver gets the λ constraints `Θ_j² = Θ_j` on the label rows
    `[ℓ, ℓ+λ)`, with no `d` on these rows. The rows are corrected VOLE rows (`Q = V + Δ·u`,
    `zk.md` H3), so the prover has their `(u, v)` and the verifier their `q`. The proof does not
    grow: a degree-2 QuickSilver proof is one field element for any number of constraints. The
    constraint count goes from 1313 to 1441 (`ε_QS` changes in its last digits; about 10% more
    QuickSilver work).
  - *Soundness.* (B) then covers the label rows: on an accepting set of at least 3 points every
    label slope is a bit. Case (b) of Lemma C cannot occur and every such set lies in a slice of
    one class. In Lean this is `class_or_small` with the label rows among the witness rows.
  - *What it buys.* With `E₁`'s default (§6.5) it removes the bound `2²⁸` of Lemma S1, the
    `2⁻¹⁰⁰` floor. With `E₁^cls` case (b) is never the largest missed set in §6A.4 (`2³²` to `2³⁸`
    against `2⁵⁰` to `2⁴²`), so **no row of §6A.4 changes**. It would matter only with a decoder
    for third classes: without (vii), two label parts of width 36 in a group next to a class of
    width 42 leave `2³⁶` points to case (b), i.e. `2⁻⁹²`. We know no forger that attains Lemma
    S1's bound (on such a set every gate sees four labels, and its term is affine only if a 5-bit
    relation between four `H₅` values holds).
  - *Zero knowledge* (`zk.md` §5–§6). An honest `Θ` is a bit vector, so the constraints hold and
    H3 (the verifier's recomputation of `qs_check`) stays perfect. After H5, `Θ` enters the view
    through `c_mult`, `ũ` and now `ã`. H6's bad event is bounded in H7, where `ũ` and `ã` are
    uniform: the map from the masks to `(ã, ũ)` is a bijection for every value of the unmasked
    QuickSilver coefficients, which may depend on `Θ` and on the label rows' `V`
    (`qsResponse_bijective` for any `H`; `labelView_responses_theta_card`, whose `φ` "may depend on
    `Θ` and `w`"). So H7 holds as stated and `ε_lab` does not change. `Sim` step 8 evaluates the
    verifier's QuickSilver on the label rows of `Q` as well; it has them. The same holds for
    blindness (`pomfrit.md` §8.2), which uses the proof only through (ZK-fix). What is not done:
    the executable prover and verifier, the constraint system `pomfritRedeemSystem` and the
    known-answer tests are those of the current protocol.
  - *Verdict.* Free and harmless, and it simplifies the analysis (one case in Lemma C). It is not
    needed for §6A's bounds and does not help to find a slice.
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

**Summary.** For a proved tight U1: (iii), (iii′) or (v). Without a protocol change, §6A gives
`2⁻⁷⁸` per `H₂³` query (`2⁻⁷⁹`, `2⁻⁸⁵` for more work) on paper, unconditionally; below that the
statement is conditional (§6A.6). (i) is mandatory in all cases.

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

`lean/VoleMole/Seed/SliceDecode.lean`, `lean/VoleMole/ROM/LemmaPClass.lean` (§6A; new, no
existing file changed except the import list). Same axioms.

| Paper | Lean |
|---|---|
| `Dec^cls` as a function of the check value; its candidates and evaluation points | `dec`, `decCand`, `decPred`, `decPts`, `decQ` |
| Lemma Dec.1 (no hypothesis); for a chain: the output is a certificate | `dec_sound`; `dec_cert_sound` |
| Lemma Dec.2: affine increments give the prediction; a zero increment is found; for a chain | `incr_decPt`, `dec_complete`; `dec_cert_complete` |
| the evaluation count; the output reads the check value at these points only | `card_decPts_le`, `card_decQ_le`, `dec_congr` |
| the base points cover the slices; their number | `basePts`, `basePts_cover`, `card_basePts_le` |
| the check value under translations; its increments | `kosValue_translate`, `incr_kosValue`, `incr_kosValue_twoLabel` |
| two-label increments; the gate model has them; additive rows have them | `TwoLabelOn`; `twoLabel_bits`, `twoLabel_gate`; `twoLabelOn_additive` |
| width `≥ 51` means 8 trees; at most two such classes; a disjoint group has width `≤ 64` | `eight_le_card_of_wide`, `not_three_wide`, `width_le_of_disjoint_wide` |
| `E₁^cls` | `clsExt`, `clsCand` (`majTree_spec`) |
| Lemma C and Lemma P^cls per chain, for any sound and complete certificate; with `Dec^cls` | `class_or_small`; `class_or_small_dec` |
| the per-chain step with QuickSilver, as `extract_or_major` | `extract_or_class` |
| `2⁵⁰/2¹²⁸ = 2⁻⁷⁸`; `2⁶⁴·2⁻⁷⁸ = 2⁻¹⁴` | `per_query_bound_cls`, `loss_cls_at_2_64` |

Not mechanized: §3 (the forgers); (Aff) for the executable verifier's masks, on `S` and on
slices (the gate model `translateOn_gate_slice` is: any hash, any `c_mult`, labels and selection
bits as sums over the trees); Lemma P^∞, Lemma P^lin and Lemma P^dec as statements about the
one-more game (they would need `KOSPar` as a bad event at `H₂¹` in `ROM/Chains.lean`'s style, and
the extractor as a function of the log); §6.4–§6.5 (the search); for §6A: the label rows' tree
form and `AffineOn`, `TwoLabelOn` for the executable verifier's masks, Lemma P^cls and U1^cls in
the one-more game (§6A.5), and the rows of §6A.4 other than `θ = 51`.

Non-vacuity. `slice_collision_sound` takes the hypotheses of `witness_determined` (`KOSPar`:
`exists_kosPar`) and the tree form of the witness rows on `S`, which is `Claim4Hyp.tree_form`'s
shape; `claim4Hyp_slice` derives `Claim4Hyp` on a slice from it, so the certificate's hypotheses
hold for every pair of points of a slice. `translateOn_gate_slice` has no hypothesis beyond
characteristic 2 and equal label offsets on `C`. `class_or_small_dec` adds: `AffineOn` on the
slices and `TwoLabelOn` (both hold for additive rows, `affineOn_univ`, `twoLabelOn_additive`, and
for the gate model, `translateOn_gate_slice`, `twoLabel_gate`); the decoder's data (`basePts_cover`
gives the base points and their properties from generators of the blocks of `T₁`; the directions
are any subgroup of `2⁷` directions of the class); Claim 4's hypotheses on the label rows, of the
same shape as on the witness rows. The theorems are not instantiated with the executable verifier.

`scripts/pomfrit-lemmap-tight/toy.py [seed]`: four trees of widths `(3, 2, 2, 2)`, `GF(2³²)`,
a KOS check of the same shape. E1: §3.1's level sets. E2: Theorem D over all pairs. E3: `E₁^lin`.
E4: §6.1's hidden slice. Runs in seconds.

`scripts/pomfrit-lemmap-tight/slice.py [seed] [--quick] [--masks=N] [--j=J [--wrong=A]] [--cls=A]`: the
verifier's response for FAEST-EM-128f shapes (17 trees, `GF(2¹²⁸)`, 312 gates, 5 masks) with
faest-arch-opt's matrices `F`, `G`, `W_tree`, `W_gate`, `W_crt` read from
`VoleMole/Verifier/CrtData.lean`. Not modelled: the GGM trees (per-tree VOLE values are sampled),
all but 8 witness rows, QuickSilver; VOLEHash is a polynomial hash of the same shape; `H₅` is
BLAKE2b. R0: the tables' identity, an honest first message. R1: §6.1's forger and `Dec₂`. R2: the
search, wrong gates, label classes of several trees. R3: uniqueness of the gate bits. R4: `Dec₂`
with wrong gates. R5: no collisions off the slice. R6: `E₁^cls` against 9 label vectors, and
`Dec^cls` between two classes of width 56 with a 17th tree (one wrong gate; `--cls=6`: §6A's
decoder with 6 wrong gates, 45 s). R7: single-tree rigidity; other slopes on level sets of
codimension 4 and 6. About 25 s; `--j=10` adds 30 s.

## 10. Open

1. Below `2⁻⁸⁵` (§6A.6): a decoder with proof for a second class when three or more trees are
   left over, and for third classes. It needs a bound on the candidate sets for labels chosen
   after the `H₅` table is seen, and a treatment of level sets whose slopes are not the trees'.
   Or a forger that defeats the search at a cost below the search's.
2. Mechanize Lemma P^cls and U1^cls in the one-more game (§6A.5): the label rows' tree form and
   `AffineOn`, `TwoLabelOn` for `Verifier`'s masks; `E₁^cls` on the log with its `H₅` evaluations
   as queries; `KOSPar` as a bad event at `H₂¹`; a `pomEps` with `2⁵⁰`. The per-chain core is
   `class_or_small_dec`.
3. The committed-shift variant of A-OMPR⊕17 (§7): is it implied by OMPR?
4. (iii′) of §8: the size and the consistency analysis of a FAEST-style check with affine masks.
