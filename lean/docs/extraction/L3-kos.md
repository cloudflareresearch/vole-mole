# L3: KOS consistency (the sketch's Claim 2)

Status: **[paper]** (this file) and **[Lean]** for everything except the random-oracle step
(`lean/VoleMole/Seed/KOS.lean`, see §7).

The proof is the FAEST v3 spec's Lemma 10.26 / Corollary 10.27 (§10.6), re-derived for the code
and the committed data of L1. The argument uses no structure of the responses: it does not need
per-tree affinity, the CRT lift, or the shape of the mask computation. That matters because the
mask rows are *not* affine per tree (§2.3).

Line numbers refer to branch `voleith-label-rows` (commit `d5def9c`), with faest-arch-opt patches
0001–0005 applied. Patch 0005 (`CRT_DEDICATED_LABEL_ROWS`, set by all five relations) adds λ
corrected "label rows" after the witness, so the KOS check hashes λ more rows than before. That
changes `L`, and `ε_KOS` by at most 0.06 bits (§6); the argument is unchanged, because
the label rows are just more rows of the response function. For the unpatched layout (`main`),
read `L = ℓ + d − 1` throughout (§6.3).

## 1. Statement

Notation as in `README.md`: λ = 128, `F = F_{2^128}`, a challenge is `Δ' ∈ F₂^{120}`,
`e(Δ') = W_crt·Δ' ∈ F` is the CRT lift (injective), ℓ = WITNESS_BITS, `d` = QS_DEGREE. Put

    L := ℓ + λ + d − 1      (rows hashed by VOLEHash: VOLE_CORRECTION_ROWS = ℓ + λ, plus d − 1 masks)
    n_mask := d − 1 + 4     (CRT masks: d − 1 for QuickSilver, 4 direct masks for the KOS check)

**Lemma L3.** Fix a fresh H₂¹ query of `P*` with input `x` (which fixes `com`, `c_1..c_{τ−1}`,
`c_mult`, `iv_pre`, μ, hence `iv`) and the committed data of L1 relative to that query. Let
`S ⊆ F₂^{120}` be the challenges with `Δ_i = j_i` for every tree `i` with a dead leaf `j_i`
(`S = ∅` if some tree has two dead leaves). Let `r(Δ') = (Q(Δ'), D(Δ')) ∈ F^L × F^4` be the
verifier's KOS input at `Δ'` computed from the committed data (§2.2). Then, except with
probability

    ε_KOS := C(|S|, 3) · ε_v,     ε_v := 2^{−4λ} + (L − 1)^5 · 2^{−(4λ+64)},

over `chall₁ = H₂¹(x)`, the following holds **for every** `(ũ, h_V) ∈ F^4 × F^4` (chosen after
`chall₁`) and every `A ⊆ S` on which the KOS check passes with `(ũ, h_V)`: there are
`u* ∈ F^L`, `V* ∈ F^L`, `u*_D, V*_D ∈ F^4` with

    Q[j](Δ') = V*[j] + u*[j]·e(Δ')        for all Δ' ∈ A, all j < L,
    D[k](Δ') = V*_D[k] + u*_D[k]·e(Δ')    for all Δ' ∈ A, all k < 4.

Rows `j < ℓ` are the witness rows, rows `ℓ ≤ j < ℓ + λ` are the dedicated gate-label rows
(corrected across trees like the witness rows, but with no `d`), and rows `ℓ + λ ≤ j < L` are the
QuickSilver masks `q̄_0..q̄_{d−2}`, which are exactly the masks QuickSilver uses (`quicksilver.hpp`,
`verify(q_mask,…)` reads `q_mask[0..d−2]`). The lemma also gives a line through the label rows,
which nothing downstream uses. So the README's statement holds as written, with all `n_mask` masks
included, and with `|S| ≤ 2^{120}`:

    ε_KOS ≤ C(2^{120}, 3) · ε_v < 2^{357.42} · ε_v.

The accepting set `A` of the README (dead leaves hidden, KOS and ZK checks pass with the chain's
messages, opening succeeds, zero grinding bits) is such an `A` for the chain's `(ũ, h_V)`. So per
witness row `j` we get `Q[j](Δ') = v_j + u*[j]·e(Δ')` on `A`, which is `Claim4Hyp.consistent`.

`u*[j]` is a field element, not a bit, and need not equal any tree's `u^{(i)}[j]`; §6.1 shows that
nothing more can be expected from the KOS check. Bits come from L4's bit constraints.

## 2. The check in the code

### 2.1 VOLEHash and the check

Prover (`voleith.hpp:240-243`) and verifier (`voleith.hpp:457-459`) call
`kos_vole_check_both` (`kos_vole_check.hpp:197, 214`) with `n_hash = VOLE_CORRECTION_ROWS` and
`n_hash_extra = QS_DEGREE − 1`. With CRT masks and `CRT_DEDICATED_LABEL_ROWS`,
`VOLE_CORRECTION_ROWS = QUICKSILVER_ROWS + CRT_LABEL_ROWS = ℓ + λ` (`constants.hpp:430-436`, with
`CRT_LABEL_ROWS = λ` and `CRT_LABEL_ROW_OFFSET = QUICKSILVER_ROWS = ℓ` at `:410-414`; `QUICKSILVER_ROWS
= WITNESS_BITS` at `:363-369`), so `L = n_hash + n_hash_extra = ℓ + λ + d − 1`. The prover hashes
`u` on all `ℓ + λ` corrected rows, including the label offset `u₀[ℓ..ℓ+λ)`. The verifier runs the
check **before** applying `d` (`voleith.hpp:469-476`, which touches only the `ℓ` witness rows), so
`Q` is the uncorrected key.

`chall₁` has `8·16 + 8 = 136` bytes, parsed as `matrix[0..4) = r_0..r_3 ∈ F`,
`keys[0..4) = s_0..s_3 ∈ F` and `key_4 = t`, a 64-bit polynomial, i.e. `t ∈ T := {a ∈ F : deg a < 64}`,
`|T| = 2^64`. All components are independent and uniform.

For an input `x ∈ F^L`:
- `uhasher_gfsecpar` with key `s` computes `Σ_k x_k s^{L−1−k}` (`init` sets `pow = (L+7) mod 8`;
  the first input is multiplied by `s^{pow}`, and the state by `s^8` every 8 inputs; the last input
  gets `s^0`). `uhasher_gfsecpar_64` is Horner's rule with key `t`, giving the same sum. So with
  `P_x(X) := Σ_k x_k X^{L−1−k}`, the five hashes are `y_j = P_x(s_j)` for `j < 4` and
  `y_4 = P_x(t)`. The bit rows enter as `0, 1 ∈ F` (`update(poly1)`), the key rows as field
  elements.
- `combine_hashes`: `h_i = D_i + y_{i+1} + r_i·y_0` for `i < 4`, where `D_i` is mask row
  `n_hash_extra + i` (a *direct* mask, added and not hashed).

This is the spec's VOLEHash (Fig. 4.4), so the audit's description, four λ-bit hashes plus one 64-bit
hash mixed via `y0·matrix[i]`, is right. Write `H_c : F^L → F^4` for `x ↦ (r_i·P_x(s_0) + y_{i+1}(x))_i`.
`H_c` is F-linear.

The prover sends `ũ = H_c(u-rows) + u_mask[d−1..d+3)`. The verifier computes

    K_c(Δ') := H_c(Q(Δ')) + D(Δ') + e(Δ')·ũ ∈ F^4

and hashes `chall₁ ‖ ũ ‖ K_c(Δ') ‖ …` into H₂². There is no explicit comparison: the check
"passes" on a chain iff `K_c(Δ') = h_V`, where `h_V` is the value in the chain's H₂² query.
Otherwise the verifier's chall₂ belongs to a different H₂² input, hence to a different chain.

### 2.2 The response function

For `Δ' ∈ S`, define `r(Δ') = (Q(Δ'), D(Δ'))` by running the verifier's `crt_vole_reconstruct` on
the committed data: the seeds of all leaves `(i, j)` with `j ≠ Δ_i` (alive by the definition of `S`,
hence unique by L1), `c_1..c_{τ−1}`, `c_mult`, `iv`, and the oracles E (ConvertToVOLE) and H₅
(gate hashes). This determines:
- the witness and label rows `j < ℓ + λ`: `Q[j] = W_crt-lift of the per-tree columns`, i.e.
  `Q[j](Δ') = W_crt(V[j]) + Σ_i u^{(i)}[j]·e_i(Δ_i)` (`crt_lift_q` over the first
  `VOLE_CORRECTION_BYTES`, `vole_commit.inc:675`), with a constant contribution on `S` from trees
  with a dead leaf;
- the masks: `q̄_m(Δ') = W_tree(r̃_q[m](Δ')) + W_gate(g_m(Δ'))` (`compute_q_mask`,
  `compute_r_tilde`, `compute_q_gate`), where `g_m(Δ')[e] = bit_m(H₅(iv, e, L0_q[e](Δ'))) ⊕
  γ_e(Δ')·c_mult[m][e]`, `L0_q = G·(q columns)[ℓ..ℓ+λ)` (the label rows, `crt_labels`,
  `vole_commit.inc:351-372`, called at `:403`) and `γ = G·Δ'`. The verifier computes `L0_q` in
  `lift_and_hash_vq<P, true>` (`:672`) after `vole_reconstruct_impl` has applied the corrections
  `c_i` to all `ℓ + λ` corrected rows (`:173-175`), and before the CRT lift.

`r` is a function on `S`: a *graph*, so the spec's "bad event 1" (two responses for one Δ) cannot
occur. It is determined by `x`, `P*`'s queries before the H₂¹ query (which define alive leaves),
and the oracles E, H₄, H₅. None of these depends on `H₂¹(x)`, which is fresh (the first query of
`x`) and independent of the other oracles (L0: domain separation; E is a separate oracle). So,
conditioned on everything that determines `r`, `chall₁` is uniform.

### 2.3 What does not matter, and why

- **No per-tree structure is used.** The mask rows are not affine per tree: `g_m` contains H₅ of a
  Δ'-dependent input, and `L0_q[e](Δ') = L0_v[e] + Σ_c G[c][e]·Δ'_c·u^{(tree(c))}[ℓ..ℓ+λ)` is the
  honest `γ_e·u_prefix` (with `u_prefix = u₀[ℓ..ℓ+λ)`, `crt_label_offset`, `vole_commit.inc:341-348`)
  only if all trees agree on the label rows. A proof that tracked per-tree
  `u^{(i)}` (like Claim 4) would therefore fail for the masks. The triple argument treats `r` as an
  arbitrary function.
- **Mask high bits.** `u_hi` comes from `PRG(root seed, iv, 2^{31}−1)` (`gen_u_hi`) and enters only
  the prover's `u_mask` and, through `F(u_mask)`, `c_mult`. The verifier never uses it, so `r`
  does not depend on it. A cheating prover's choice is absorbed into `c_mult` (committed in H₂¹)
  and, in the conclusion, into the slopes `u*[ℓ..L)`, `u*_D`, which are arbitrary field elements.
- **Mask low bits and the row shift.** The masks sit after the `VOLE_CORRECTION_ROWS = ℓ + λ`
  corrected rows, so patch 0005 moved them down by λ. Everything that locates them is relative to
  `VOLE_CORRECTION_ROWS`: the verifier's `compute_r_tilde` reads `vq + VOLE_CORRECTION_ROWS`
  (`vole_commit.inc:295`); the prover's `extract_u_low` reads tree 0's `u` from
  `VOLE_CORRECTION_BYTES` (`:208`) and the other trees' raw, uncorrected `u_i` from `u_extra`, the
  bytes after `VOLE_CORRECTION_BYTES` of each `vole_sender` output (`:114-120`; `small_vole.hpp:29-30`).
  These rows get no correction: the verifier's keys on them (per tree, `q = v + u_i·Δ_i`,
  `small_vole.hpp:57`) are computed from the alive seeds and Δ' alone. So `q̄_m(Δ')` is still a function of committed data fixed before `chall₁`, and
  the prover's low bits, like its high bits, are absorbed into `c_mult` and the slopes.
- **CRT lift.** Only the injectivity of `e` on `S` is used (distinct Δ' give distinct `e(Δ')`).
- **Dead-leaf trees.** On `S`, their block is constant and their columns come from alive seeds, so
  they are part of the fixed function `r`, as constants.
- **ũ and h_V after chall₁.** The bad event below quantifies over all `(ũ, h_V)`.

## 3. VOLEHash is almost uniform

**Lemma A** (spec Lemma 4.6, without its length restriction). For `x ∈ F^L∖{0}` and any
`v ∈ F^4`, `Pr_c[H_c(x) = v] ≤ ε_v = 2^{−4λ} + (L−1)^5·2^{−(4λ+64)}`.

*Proof.* `x ↦ P_x` is injective (`coeff_{L−1−k} P_x = x_k`), so `P := P_x ≠ 0`, and `deg P ≤ L−1`.
- If `y_0 = P(s_0) ≠ 0`: for fixed `(s, t)`, each equation `r_i·y_0 + y_{i+1} = v_i` has exactly one
  solution `r_i`. Probability `≤ 2^{−4λ}`.
- If `P(s_0) = 0`: then `P` is not constant (a nonzero constant has no root), so `P − v_i ≠ 0` has at
  most `L−1` roots for every `v_i`. The output is `(P(s_1), P(s_2), P(s_3), P(t))`, so we need
  `P(s_0) = 0`, `P(s_1) = v_0`, `P(s_2) = v_1`, `P(s_3) = v_2`, `P(t) = v_3`. Each `s_j` is uniform
  in `F` and `t` is uniform in `T`, all independent, so the probability is
  `≤ ((L−1)/2^λ)^4 · (L−1)/2^{64}`. ∎

For `L − 1 ≤ 2^{12}` this gives the spec's `2^{−4λ}(1 + 2^{−4})`. **Ratatouille spend has
`L = 6912 > 2^{12}+1`**, outside the spec's stated condition, but Lemma A holds for every `L`: there
`ε_v = 2^{−512}(1 + 6911^5/2^{64}) ≈ 1.85·2^{−512}` (unpatched: `L = 6784`, `≈ 1.78·2^{−512}`).

The direct masks make the full check map `(x, y) ↦ H_c(x) + y` almost universal on `F^{L+4}`:
if `x = 0` then `H_c(x) + y = y`, which is 0 only for `y = 0`; if `x ≠ 0`, apply Lemma A with
`v = −y`.

## 4. The deterministic step

For three challenges define the collinearity defect (a vector in `F^{L+4}`):

    δ(Δ_0, Δ_1, Δ_2) := (e_2 − e_0)·(r_1 − r_0) − (e_1 − e_0)·(r_2 − r_0),   e_k := e(Δ_k), r_k := r(Δ_k).

For distinct `e_k`, `δ = 0` iff the points `(e_k, r_k) ∈ F^{1+L+4}` are collinear.

**Lemma B.** Suppose that for all `Δ_0, Δ_1, Δ_2 ∈ S` with `Δ_0 ∉ {Δ_1, Δ_2}`:
`K(δ) = 0 ⇒ δ = 0`, where `K(x, y) = H_c(x) + y`. Then for all `(ũ, h_V)` and all `A ⊆ S` with
`K(r(Δ')) + e(Δ')·ũ = h_V` on `A`, there are `u*, V* ∈ F^{L+4}` with `r(Δ') = V* + e(Δ')·u*` on `A`.

*Proof.* If `|A| ≤ 1`, take `u* = 0` and `V* = r(Δ_0)` (or anything if `A = ∅`). Otherwise fix
`Δ_0 ≠ Δ_1` in `A`. Then `e_1 ≠ e_0` by injectivity. Put `u* := (r_1 − r_0)/(e_1 − e_0)` and
`V* := r_0 − e_0·u*`. Let `Δ ∈ A∖{Δ_0}`. Subtracting the check at `Δ_0` from the checks at `Δ_1` and
`Δ` gives `K(r_1 − r_0) = −(e_1 − e_0)ũ` and `K(r_Δ − r_0) = −(e_Δ − e_0)ũ`. So, by linearity,
`K(δ(Δ_0, Δ_1, Δ)) = −(e_Δ − e_0)(e_1 − e_0)ũ + (e_1 − e_0)(e_Δ − e_0)ũ = 0`. By hypothesis
`δ = 0`, i.e. `(e_1 − e_0)(r_Δ − r_0) = (e_Δ − e_0)(r_1 − r_0)`, so `r_Δ = r_0 + (e_Δ − e_0)u* =
V* + e_Δ·u*`. For `Δ = Δ_0` this holds by definition of `V*`. ∎

`ũ` and `h_V` drop out: the conclusion is uniform in them, so the prover's choice after
`chall₁` cannot help.

## 5. Proof of Lemma L3

Call `chall₁ = c` *bad* if the hypothesis of Lemma B fails, i.e. some triple in `S` (with
`Δ_0, Δ_1, Δ_2` pairwise distinct, since if `Δ_1 = Δ_2` then `δ = 0`) has
`δ = (δ_Q, δ_D) ≠ 0` and `H_c(δ_Q) = −δ_D`. If `δ_Q = 0` this forces `δ_D = 0`, so a bad triple has
`δ_Q ≠ 0`. Since `r` is fixed before `c` (§2.2), each triple is bad with probability `≤ ε_v`
(Lemma A). Expanding, `δ = (e_0 r_2 − e_2 r_0) + (e_1 r_0 − e_0 r_1) + (e_2 r_1 − e_1 r_2)`, which
is alternating in `(Δ_0, Δ_1, Δ_2)`. So permuting a triple only changes the sign of `δ`, and
badness is a property of the unordered triple. It therefore suffices to union-bound over unordered triples:
`Pr[c bad] ≤ C(|S|, 3)·ε_v`. If `c` is not bad, Lemma B gives the conclusion for all `(ũ, h_V)` and
all `A ⊆ S`. ∎

(The spec additionally pays `C(|S|,2)·ε` for its bad event 1, which cannot occur here because `r`
is a function. The Lean version union-bounds over all `|S|^3` ordered triples, a factor 6 looser.)

### Accounting in the assembly

The bad event is a property of the H₂¹ query, which `P*` can repeat: it can grind `chall₁` by
varying `c_mult` or `iv_pre` at the cost of H₂¹ queries alone. So the union bound in the assembly
must run over the `q₁ ≤ q` H₂¹ queries (each fresh query is bad with probability `≤ ε_KOS`), giving
`q₁·ε_KOS`, not `Q·ε_KOS` with `Q` the number of H₂³ queries as in the README's `ε_ext`. The same
remark applies to `ε_QS` and H₂² queries. Numerically this is irrelevant (`q·2^{−153}`), but the
formula in the README should read `q·ε_KOS` (or `q₁·ε_KOS`).

## 6. Numbers

`ε_KOS ≤ C(2^{120}, 3)·ε_v`:

`log₂ C(2^{120}, 3) = 357.415`. With λ = 128 label rows:

| relation | ℓ (WITNESS_BITS) | d | n_mask | L = ℓ+λ+d−1 | log₂ ε_v | log₂ ε_KOS |
| --- | ---: | ---: | ---: | ---: | ---: | ---: |
| PomFRIT redeem (`src/pomfrit/redeem.hpp`) | 1312 | 2 | 5 | 1441 | −512.000 | −154.58 |
| Moussaka issue (`src/moussaka/issue.hpp`) | 2048 | 9 | 12 | 2184 | −511.996 | −154.58 |
| Moussaka redeem (`src/moussaka/redeem.hpp`) | 2744 | 9 | 12 | 2880 | −511.985 | −154.57 |
| Ratatouille issue (`src/ratatouille/issue.hpp`) | 1920 | 9 | 12 | 2056 | −511.997 | −154.58 |
| Ratatouille spend (`src/ratatouille/spend.hpp`) | 6776 | 9 | 12 | 6912 | −511.109 | −153.69 |

Derivation of ℓ (bytes × 8), with uov `M = 45`, `N = 119`, Keccak-p[800] state 100 bytes, two
committed states (`COMMITTED_STATES_BYTES = 200`), `R_BYTES = CTX_BYTES = 16`, `NF_BYTES = 24`,
`CREDIT_BYTES = 8`, `COMMITMENT_BYTES = 32`, `SELECTOR_BYTES = 64/8 = 8`:
- PomFRIT redeem: r ‖ s = 45 + 119 = 164 bytes.
- Moussaka issue: r ‖ ctx_red ‖ nf ‖ states = 16 + 16 + 24 + 200 = 256.
- Moussaka redeem: r ‖ s ‖ states ‖ b = 16 + 119 + 200 + 8 = 343.
- Ratatouille issue: r ‖ nf ‖ states = 16 + 24 + 200 = 240.
- Ratatouille spend: r, t, x, c, nf', t', r', s, k1, k2, 3×states
  = 16+8+8+32+24+8+16+119+8+8+600 = 847.

Degrees: Keccak `QS_DEGREE = max(2^3, max over segments {3,2},{2,2} of max(2^f, 3^b)) = 9`;
Moussaka redeem uses `max(9, 3) = 9`; PomFRIT uses 2.

Alternatively, using only `|S| ≤ 2^{120}` and `ε_v ≤ 2^{−511}` for all five relations:
`ε_KOS ≤ 2^{−153.5}`.

### 6.1 Why the conclusion is per row, with `u*[j] ∈ F`

The KOS check cannot produce bits or single out a tree. Example: let tree 0 have `u^{(0)}[j] = 1`
and every other tree `u^{(i)}[j] = 0` on some row `j`, and let the trees agree on all other rows.
Take any witness row `j < ℓ`; the gate inputs `L0` come from the separate label rows
`[ℓ, ℓ+λ)`, so they are unaffected and the masks can be honest. (In the unpatched layout, where the
labels come from rows `[0, λ)`, take `j ≥ λ`.) Then
`Q[j](Δ') = V[j] + e_0(Δ_0)`, and every other hashed row and mask is `V* + u*·e(Δ')` with the common
`u*`. For `α ∈ F` let
`A_α := {Δ' : e_0(Δ_0) = α·e(Δ')}`, an F₂-subspace (the kernel of an F₂-linear map
`F₂^{120} → F`). On `A_α`, `Q[j] = V[j] + α·e(Δ')`, an affine function with slope `u*[j] = α`. With
`u*[j] := α` and `ũ := H_c(u*_Q) + u*_D`, `h_V := H_c(V*_Q) + V*_D`, the check passes on all of
`A_α`. A heuristic count over pairs suggests about `2^{240}·2^{−128} = 2^{112}` values of `α` with
`dim A_α ≥ 2`, so non-bit slopes on sets of size ≥ 4 should occur. This is consistent with L3, whose conclusion only says `u*[j] ∈ F`. The bit constraints in
QuickSilver (L4) make `|A_α| ≤ d` unless `α ∈ {0,1}`, and Claim 4 then uses `u*[j] ∈ {0, 1}`.
Across rows there is no cancellation issue for L3: the lemma is about one line in `F^{1+L+4}`
through all accepted points. The cross-tree cancellation that motivated Claim 4 concerns
*identifying* `u*` with some tree's `u^{(i)}`, which L3 does not claim.

### 6.2 Patch 0002 (up to 32 masks)

The patch widens the per-gate H₅ output used in the mask computation from 16 to 32 bits (`uint16_t
→ uint32_t`, `transpose_16Nx16 → transpose_16Nx32`, `static_assert(N_MASK <= 32)`). It changes
only how `q̄_m(Δ')` is computed from the committed data and H₅. L3 treats `q̄_m` as an arbitrary
function fixed before `chall₁` (H₅ is independent of H₂¹), so **the patch does not affect L3**.
`n_mask` does not enter `ε_KOS`: only the `d − 1` hashed masks enter, through `L`. Side note: the
patch's description says vole-mole's issuance proof uses degree 16 (19 masks). With the current
segments the Keccak degree is 9 (12 masks), so that comment is stale. It is still true that
`d − 1 + 4 ≤ 32` is required, and this is asserted in every relation header.

### 6.3 The unpatched layout (`main`)

Without `CRT_DEDICATED_LABEL_ROWS` (as on `main`, and for FAEST's own parameter sets),
`VOLE_CORRECTION_ROWS = QUICKSILVER_ROWS = ℓ`, the gate labels come from the first λ witness rows,
and `L = ℓ + d − 1`. The proof is the same with that `L`; the numbers were:

| relation | L = ℓ+d−1 | log₂ ε_v | log₂ ε_KOS |
| --- | ---: | ---: | ---: |
| PomFRIT redeem | 1313 | −512.000 | −154.58 |
| Moussaka issue | 2056 | −511.997 | −154.58 |
| Moussaka redeem | 2752 | −511.988 | −154.57 |
| Ratatouille issue | 1928 | −511.998 | −154.58 |
| Ratatouille spend | 6784 | −511.169 | −153.75 |

The λ extra hashed rows cost at most 0.06 bits (Ratatouille spend), and `ε_KOS ≤ 2^{−153.5}` holds
for both layouts.

## 7. Lean

`lean/VoleMole/Seed/KOS.lean` (namespace `VoleMole.Seed`). No `sorry`, no axioms beyond
`propext`, `Classical.choice`, `Quot.sound`.

| Paper | Lean |
| --- | --- |
| collinearity defect δ | `cross` |
| Lemma B (generic: any linear `K`, any module of responses) | `affine_of_good` |
| `K(δ) = 0` from three accepted points | `map_cross_eq_zero` |
| `P_x`, `x ≠ 0 ⇒ P_x ≠ 0`, `deg P_x ≤ L−1`, evaluation formula | `hornerPoly`, `hornerPoly_ne_zero`, `natDegree_hornerPoly_le`, `eval_hornerPoly` |
| VOLEHash as in `combine_hashes`; linearity | `voleHashP`, `voleHash`, `voleHashL` |
| Lemma A, counting form: `#{c : H_c(P) = v} ≤ |F|⁴|T| + n⁵|F|⁴` out of `|F|⁸|T|` | `card_voleHashP_eq_le` |
| the check value `K_c(Δ')` | `kosValue` |
| "c is good for all (ũ, h_V, A)" | `KOSGood` |
| no bad triple ⇒ good | `kosGood_of_no_bad_triple` |
| **Lemma L3, counting form**: `#{c bad} ≤ |S|³(|F|⁴|T| + (L−1)⁵|F|⁴)` | `card_not_kosGood_le` |
| conclusion in the shape of `Claim4Hyp.consistent` (generic in `ℓ ≤ L` with the witness rows first, so the λ label rows between the witness rows and the masks need no change) | `consistent_of_kosGood` |
| chaining: builds `Claim4Hyp` from KOS + the other three fields | `claim4Hyp_of_kosGood` |

Not formalized: §2.2 (that `r` is a function of data fixed before the H₂¹ query and that `chall₁`
is uniform given it), the identification of `voleHashP` with the C++ (§2.1, by inspection), and the
`q₁` union bound over H₂¹ queries.
