# Q1: online-extractable leaf commitments in the quantum ideal-cipher model

Status: **[paper]**, with **[Lean]** for the database bound (§2,
`lean/VoleMole/Seed/QuantumCipher.lean`). Part of README §L9. This is the primary route for the
repo's `aes_ctr` leaf commitments.

**Summary.**
- §1–§3 set up a key-level compressed oracle for the ideal cipher, with no permutation-level
  recording, and an online extraction measurement.
- §4 proves the extraction properties with exact constants:
  - commutator `δ = 8√(2p)` per cipher query;
  - dead-leaf, uniqueness and persistence bounds `2(2q₂+1)²p`.
- §5 bounds the "two keys match" event:
  - it holds at all `q` only as `O(q³)·2^{−128}`;
  - with `iv = H₄(…)`, it improves to `O(q⁵)·2^{−256}`, valid for `q ≲ 2^{37}`.

  This is the one real weakness (§9), and it is intrinsic to key-level reasoning.
- §6 states exactly what an efficient simulator must provide. All results hold for any simulator
  that is perfectly, or `ε`-, indistinguishable from `S^IC` as a three-interface oracle.
- §8 is the interface for Q2.

## 0. Setting and notation

`X = K = {0,1}^128`, `N := 2^128`. The ideal cipher is a uniform `π : K → Sym(X)`, written
`σ_k := π(k)`. The adversary has quantum access
- forward: `|k,x,y⟩ ↦ |k,x,y ⊕ σ_k(x)⟩`;
- inverse: `|k,y,x⟩ ↦ |k,y,x ⊕ σ_k⁻¹(y)⟩`.

**The leaf commitment as implemented** (read in `subprojects/faest-arch-opt`):
- `prg_leaf_hash<aes_ctr_prg>::hash` (`vector_com.inc:1071-1085`) runs `expand_chunk<…, 2, PRG>`
  from counter 0. It sets `hashes_out = 2 blocks` and `keys_out = keys_in`. So
  `com = E_k(x₀) ‖ E_k(x₁)` and `sd = k`.
- `aes_ctr_prg::build_ecb_input` sets `x_c = iv.add32(set_low_high32(c, twk))`, which is lane-wise
  addition mod 2³². Hence `x₁ = x₀ ⊞ e₀` with `e₀ = (1,0,0,0)`, and `x₀ ≠ x₁` always.
- The leaf tweak (`expand_tree → write_leaves`) is `(tree_depth+1)·τ + tree_i`. Only "fixed per
  tree" is used below; `T` denotes the set of leaf tweaks, `|T| = τ = 17`.
- The leaf `iv` is `iv = H₄(iv_pre ‖ mu)` from `voleith.hpp`.

Write `ι = (iv, twk)`, `x_c(ι) := iv ⊞ (c,0,0,twk)`, and `f_ι(σ) := σ(x₀(ι)) ‖ σ(x₁(ι))`.

**Counting facts.**
- (F1) For `t = (a,b)` with `a ≠ b`, `|{σ : f_ι(σ) = t}|/N! = p := 1/(N(N−1))`. For `a = b` it is 0.
  The reason is that a uniform permutation sends two distinct points to a uniform pair of distinct
  values. Numerically `√(2p) ≈ 1.414·2^{−128}`.
- (F2) For any `σ'`, `Pr_σ[∃z : σ, σ' agree on {z, z⊞e₀}] ≤ N·p = 1/(N−1)`.

## 1. Purified ideal cipher

The oracle registers are `D = (D_k)_{k∈K}`, where `D_k` has basis `{|σ⟩ : σ ∈ Sym(X)}`. The initial
state is `|u⟩^{⊗K}`, with `|u⟩ := (N!)^{−1/2} Σ_σ |σ⟩`. The queries are

    O^fw  = Σ_k |k⟩⟨k| ⊗ O^fw_k,   O^fw_k  |σ⟩|x,y⟩ = |σ⟩|x, y ⊕ σ(x)⟩,
    O^inv = Σ_k |k⟩⟨k| ⊗ O^inv_k,  O^inv_k |σ⟩|y,x⟩ = |σ⟩|y, x ⊕ σ⁻¹(y)⟩.

Each `O_k` is controlled by the computational basis of `D_k` and touches no other `D_{k'}`.
Measuring `D` commutes with every query, and the measurement yields a uniform cipher. So this
purification is perfectly indistinguishable from the QICM. This is the standard argument (Zhandry,
CRYPTO 2019, §3).

## 2. Key-level compressed oracle; the database bound

**Lemma 2.1 (database bound) [Lean].** Let `P_k := |u⟩⟨u|_{D_k}`, `Q_k := 1 − P_k`, and
`Π_S := ⊗_{k∈S} Q_k ⊗ ⊗_{k∉S} P_k`. After `q` queries (forward or inverse, interleaved with
arbitrary unitaries on the other registers), the state lies in `⊕_{|S|≤q} Im Π_S`.

*Proof.* Write states as `ψ : (K → Sym(X)) → E`.
1. `⊕_{|S|≤m} Im Π_S` is the span `J_m` of functions that depend on at most `m` coordinates. A
   function of the coordinates in `S` lies in `Im avg_{K∖S} = ⊕_{T⊆S} Im Π_T`, and `Im Π_T`
   consists of functions of `T`.
2. The initial state is constant, so it lies in `J_0`.
3. Local unitaries act pointwise, so they preserve `J_m`.
4. A query `(Oψ)(H) = Σ_k B_k(H(k))(ψ(H))` maps `J_m` into `J_{m+1}`.

This is `run_mem_junta` in `QuantumCipher.lean` (any alphabet, any field, any blocks, no `sorry`, no
axioms). ∎

Lemma 2.1 uses only "controlled on the key, acting on one register", so it covers forward and inverse
evaluation queries. It does not care that a query reveals one value rather than all of `σ_k`.

**Compressed form.** Extend each `D_k` by `|⊥⟩`. Let `F_k` swap `|⊥⟩ ↔ |u⟩` and fix `u^⊥`. Extend
`O_k` by the identity on `|⊥⟩`, and set `cO_k := F_k O_k F_k`. Since `F_{k'}` commutes with `O_k` for
`k' ≠ k`, `cO = F^{⊗K} O F^{⊗K}`. Starting from `|⊥⟩^{⊗K}`, the compressed state is
`F^{⊗K}·(purified state)`, which is perfectly indistinguishable.

The *key database* is `{k : D_k ≠ ⊥}`, and it has at most `q` keys by Lemma 2.1. Measurements that
are diagonal in the `D` basis (all `Ext` below) do not enlarge the support, so the bound survives
them. `F` is DFMS's `F` (Don–Fehr–Majenz–Schaffner, EUROCRYPT 2022, §2.2): it swaps `⊥` with the
uniform vector and fixes the rest, so the definition is basis-free and needs no group structure.

**Full-value reduction** (used only in §5). Encode `Sym(X)` as the abelian group `ℤ_{N!}`. One
evaluation query is exactly two full-value (additive) queries to the random function `K → ℤ_{N!}`
(fetch `σ_k`, evaluate, un-fetch), and the compressed operators coincide. So the framework of
Chung–Fehr–Huang–Liao (EUROCRYPT 2021, arXiv 2010.11658), stated for arbitrary finite abelian
ranges, applies with `2q` queries.

## 3. The extraction measurement and the simulator `S^IC`

For classical `ι` and `t = (a,b)`:
- if `a = b`, `Ext` returns `∅`, since nothing opens such a `t`;
- otherwise let

      Π^k := Π^k_{ι,t} := Σ_{σ : f_ι(σ) = t} |σ⟩⟨σ|_{D_k}   (Π^k|⊥⟩ = 0),   Π̄^k := 1 − Π^k.

**`Ext_ι(t)`** is the projective measurement with outcomes `∅`, `k ∈ K` and `multi`:

    Σ^∅ := ⊗_k Π̄^k,   Σ^k := Π^k ⊗ ⊗_{k'≠k} Π̄^{k'},   Σ^multi := 1 − Σ^∅ − Σ_k Σ^k.

Outcome `k` means: `k` is in the database and is the only database key with `σ_k(x₀) ‖ σ_k(x₁) = t`
as cipher values.

**`S^IC`** has three interfaces:
- `Enc` and `Dec` apply `cO^fw` and `cO^inv`;
- `Ext` applies the measurement above.

For analysis, `Ext` is purified as `M = Σ_o Σ^o ⊗ X^o` (DFMS eq. (12)).

**Relation to "alive" in `L0-L2-commitments.md`.**
- Classical Definition B there: some key `k` has one block `(k, x_c, t_c)` recorded before Θ, and
  `E_k(x_{1−c}) = t_{1−c}` as a value.
- The key-level analogue is outcome `Ext ∈ K`: `k` was touched (some record under `k`, at any
  point), and both blocks match as values.

These agree up to the event "a touched key matches both blocks as values with neither block
recorded". Classically that event has probability `≤ q_E·(N−q_E)^{−2}` per commitment (unrecorded
values are uniform). Quantumly, "recorded block" is not defined at key level, and **the quantum
definition is: leaf `(i,j)` of Θ is alive iff `Ext_{ι_Θ,i}(com^Θ_{i,j}) ∈ K` when applied at Θ's
time.**

Definition B's extractor "finds one matching block, then evaluates the other block itself". Here the
corresponding step is inside `Ext` (it tests both values), together with P2 below: an extracted key
passes the extractor's own evaluation with probability `≥ 1 − 2p`. Dead-leaf bounds are proved for
this notion (Thm 4.2(a)). It is at least as inclusive as Definition B, so `Ext`-dead implies B-dead.

**Lemma 3.1 (local commutators).** `‖[F_k, Π^k]‖ = √(2p − p²) ≤ √(2p)`, and
`‖[cO_k, Π^k]‖ ≤ 2√(2p)`, for forward and inverse queries alike. The same holds with `Π̄^k`.

*Proof.* Write `F = 1 − 2|w⟩⟨w|`, `w = (|⊥⟩ − |u⟩)/√2`, and `a := Πw = −Πu/√2`. Then
`‖a‖² = ⟨u|Π|u⟩/2 = p/2` and `⟨w|a⟩ = p/2`. So `[F,Π] = −2(|w⟩⟨a| − |a⟩⟨w|)`, which has norm
`2(‖a‖² − ⟨w|a⟩²)^{1/2}`. Next, `[O_k, Π^k] = 0` because both are diagonal in `D_k`'s basis. Hence
`[FOF, Π] = [F,Π]OF + FO[F,Π]`. ∎

This is DFMS Lemma 3.3 with `2^{−n}Γ` replaced by `p`.

**Lemma 3.2 (global commutator).** `‖[cO, M]‖ ≤ δ := 8√(2p) ≈ 11.31·2^{−128}`, for `cO = cO^fw` or
`cO^inv`.

*Proof.* `cO = Σ_k |k⟩⟨k| ⊗ cO_k`, and `M` does not act on the key register, so it suffices to
bound `‖[cO_k, M]‖` (DFMS Cor. 2.2). Let `c := ‖[cO_k, Π^k]‖`.
- `[cO_k, Σ^∅]` and `[cO_k, Σ^k]` have norm `≤ c`, by the tensor structure and DFMS eq. (4).
- For `k' ≠ k`, `[cO_k, Σ^{k'}] = A_{k'} ⊗ C` with `C := [cO_k, Π̄^k]` and
  `A_{k'} := Π^{k'} ⊗ ⊗_{k''∉{k,k'}} Π̄^{k''}`. These are pairwise orthogonal projectors on registers
  other than `D_k`. Then `N := Σ_{k'} A_{k'} ⊗ C ⊗ X^{k'}` satisfies `N†N = Σ A_{k'} ⊗ C†C`, so
  `‖N‖ ≤ c`.
- `1 − Σ^multi = 1 ⊗ B_∅ + Π̄^k ⊗ B_1`, with `B_∅ := ⊗_{k'≠k} Π̄^{k'}` and `B_1 := Σ_{k'≠k} A_{k'}`.
  The first term commutes with `cO_k`, so `‖[cO_k, Σ^multi]‖ ≤ c`.

In total `4c ≤ 8√(2p)`. ∎

`Ext` commutes **exactly** with every other `Ext` (any `ι'`, `t'`; all are diagonal in the `D`
basis). It also commutes exactly with all random-oracle queries (including DFMS's extractable H₁
simulator and DFM20 reprogramming of H₂ʲ) and with all adversary unitaries, since these act on
other registers.

## 4. Properties (analogue of DFMS Theorem 4.3, plus squared bounds)

A *check* of `(k, ι, t)` means classical `Enc` queries at `(k, x₀(ι))` and `(k, x₁(ι))`, comparing
the answers with `t`. It equals `F_k · (measure f_ι(σ_k)) · F_k`, because `F_k F_k = 1`. The value
`⊥` answers `(0,0) ≠ t`.

**Theorem 4.1 (basic properties).**
- **P0.** Without `Ext`, `S^IC` is perfectly indistinguishable from the QICM.
- **P1.**
  - Independent `Enc`/`Dec` queries commute, since `FOF·FO'F = FOO'F` with `O, O'` both
    `D`-controlled.
  - `Ext` queries commute with each other.
  - `Ext` and an `Enc`/`Dec` query `δ`-almost-commute in trace distance (Lemma 3.2 and DFMS
    Cor. 3.2).
  - Moving an `Ext` query across `n` cipher queries changes the joint output by at most `nδ`.
- **P2 (an extracted key opens).** If `Ext_ι(t) = k̂ ∈ K` and `(k̂, ι, t)` is then checked, the check
  fails with probability `≤ ‖Π̄FΠ‖² = ‖Π̄[F,Π]‖² ≤ 2p`.
- **P3 (completeness).** Suppose no earlier `Ext` was applied, the adversary checks `(k, ι)` and
  gets `h`, and then `Ext_ι(h)` is run. Then `Pr[∅] ≤ 2p`.

  *Proof.* The post-check purified `D_k` is a unit vector `φ ∈ Im Π`. Its compressed form is `Fφ`,
  and `ΠFφ = φ − ⟨u|φ⟩Πu`, so `‖ΠFφ‖ ≥ 1 − p`. Outcome `∅` needs `Π̄^k`.
- **P4 (Lemma-5 analogue).** Let `A` output `(k, ι, t, z)` and let `R` be any relation. Then

      √Pr_QICM[f_ι(σ_k) = t ∧ R]  ≤  √Pr_{S^IC, D measured at end}[D_k ≠ ⊥ ∧ f_ι(D_k) = t ∧ R] + √(2p).

  *Proof.* Realise the left side in `S^IC` by a check, which is controlled on `k`. On the final
  state `φ`, `‖ΠFφ‖ ≤ ‖ΠFΠφ‖ + ‖ΠFΠ̄φ‖ ≤ ‖Πφ‖ + √(2p)`. `R` acts on output registers. ∎

Now the per-commitment statements. `Ext_ι(t)` is applied once `ι` and `t` are classically fixed,
with outcome `ô`.
- `q₁` is the number of cipher queries before `Ext`.
- `q₂` is the number after `Ext`, including the verifier's (GGM co-path, ConvertToVOLE) and the
  extractor's, excluding the final 2-query check.
- `k` is any key produced later (an opened seed, possibly derived by the verifier from an opened
  inner node; or `ô` itself), chosen adaptively, in superposition, or via inverse queries.

**Theorem 4.2 (dead leaves, uniqueness after extraction, persistence).**

    (a) Pr[ô = ∅        ∧ check(k, ι, t) passes]       ≤ 2(2q₂+1)²·p
    (b) Pr[ô = k̂ ∈ K    ∧ k ≠ k̂ ∧ check(k, ι, t) passes] ≤ 2(2q₂+1)²·p
    (c) Pr[ô = k̂ ∈ K    ∧ check(k̂, ι, t) at the end fails] ≤ 2(2q₂+1)²·p

Numerically `2(2q₂+1)²p ≈ 8q₂²·2^{−256}`.

*Proof of (a).* Let `Ψ ∈ Im Σ^∅` be the unnormalised post-outcome state. Let `V` be the evolution
up to the check, with `q₂` cipher queries; other `Ext` measurements are diagonal and commute with
`Σ^∅`. Let `C = Σ_k |k⟩⟨k| ⊗ F_k Ô_k F_k` be the coherent check and `Γ_t` the projector "answer = t".
Then

    ‖Γ_t C V Ψ‖ ≤ ‖Γ_t C Σ^∅‖·‖Ψ‖ + ‖(1 − Σ^∅) V Σ^∅ Ψ‖.

- First term: `Γ_t Ô_k = Ô_k Π^k` on a fresh answer register, so the factor is
  `≤ max_k ‖Π^k F Π̄^k‖ = max_k ‖[Π^k, F]Π̄^k‖ ≤ √(2p)`.
- Second term: at most `Σ_queries ‖[cO, Σ^∅]‖·‖Ψ‖ ≤ q₂·2√(2p)·‖Ψ‖`. Here `Σ^∅` is a single
  projector, so each commutator is `≤ c`, not `4c`.

Hence `√Pr ≤ (2q₂+1)√(2p)`.

(b) is the same argument with `⊗_{k'≠k̂} Π̄^{k'}` and the check restricted to `k ≠ k̂`.

(c) is the same argument with `Π^{k̂}` and `Π̄^{k̂}` swapped, using `‖Π̄FΠ‖ ≤ √(2p)`. ∎

These bounds are squared: `O(q²p)`, not DFMS Cor. 4.7's `O(q√p)`. The reason is that each uses one
projector's commutator, starting from a post-measurement state.

## 5. Two keys match: the `multi` outcome

Theorem 4.2 handles everything except `ô = multi`, meaning at least two database keys open `t`.
This is the quantum ideal-cipher part of `ε_bind` (L1).

**Theorem 5.1 (free iv).** Let `Q := 2q₁`. Then

    Pr[ô = multi] ≤ ε_multi^free(q₁) := (40/9)·Q³/(N−1) = (320/9)·q₁³/(N−1) ≈ 35.6·q₁³·2^{−128}.

This holds simultaneously for all commitments and all `ι`.

*Proof.* `multi` implies the diagonal event `Z(D) ≠ ∅`, where

    Z(D) := {z : ∃ k ≠ k' in the database with σ_k, σ_{k'} agreeing on {z, z⊞e₀}}.

Use the full-value reduction with `Q` queries and CFHL's framework.
- Take `P' = {Z ≠ ∅}`. The transition `¬P' → P'` is strongly recognized by the 1-local property
  "the new value at `x` agrees with some other entry on some adjacent pair". This property is
  constant-true if `Z` is already non-empty outside `x`.
- By (F2), `P[U ∈ L] ≤ s/(N−1)` for databases of size `s`.
- CFHL Theorem 5.17 gives `⟦SZ≤s ∖ P' → P'⟧ ≤ √(10 s/(N−1))`.
- By Lemma 5.6, `‖P'ψ_Q‖ ≤ Σ_{s<Q} √(10s/(N−1)) ≤ (2/3)√10·Q^{3/2}/√(N−1)`. Diagonal measurements
  in between do not increase this.
- Since `Σ^multi ≤ P'` as diagonal projectors, `Pr[multi] ≤ ‖P'ψ‖²`. ∎

**Theorem 5.2 (using `iv = H₄(iv_pre ‖ mu)`).** Model H₄ as a random oracle. Let the extractor obtain
`iv` by a classical H₄ query on `(iv_pre ‖ mu)` from Θ's input right before `Ext`. Let
`q := 2q₁ + q₄ + 1`, with `q₄` the adversary's H₄ queries, and

    θ := 2e√30 · q^{3/2}/√N ≈ 29.78 · q^{3/2} · 2^{−64}.

If `θ ≤ 1/2` (roughly `q₁, q₄ ≤ 2^{37}`), then

    Pr[ô = multi] ≤ ε_multi^H₄ := ( e q² √(10|T|p) + 4e q √(10|T|/N)·θ + q θ^{2^31} )² + 2·2^{−128}
                               ≈ 1.8·10⁷ · q⁵ · 2^{−256} + 2^{−127}.

The last term in the parentheses is negligible.

*Proof.* Treat (Π, H₄) as one random oracle on `K ⊔ W` with range `ℤ_{N!} × {0,1}^128`, each part
using its own coordinate. Let

    Bad := ∃ (w, iv) in the H₄ database, twk ∈ T: x₀(iv, twk) ∈ Z(D_Π).

1. **From `multi` to `Bad`.** After the extractor's classical H₄ query with answer `iv`, the
   register `D_4(w)` is `F|iv⟩`. Measuring it gives `iv` except with probability `2·2^{−128}`
   (DFMS eq. (8)). Then `multi ⇒ Bad`, since both events are diagonal.
2. **Agreement levels.** Let `A_{≥j}` be the projector onto `|Z(D_Π)| ≥ j`, and
   `α_j(s) := ‖A_{≥j} ψ_s‖` after `s` queries.
   - An H₄ query does not change `Z`.
   - A Π query at `x` moves `|Z|` from `i` to `≥ i+m` only if the new value creates `≥ m` new
     agreement points.
   - Consider `m' := min(m, 2^31)` such points. They form runs under `⊞e₀` with `r ≥ 1` runs, which
     impose `m' + r` distinct values. Counting configurations (`≤ N^r·C(m'−1, r−1)` positions and
     `s^{m'}` keys) gives `P[U ∈ L] ≤ (3s/N)^{m'}`.
   - CFHL Theorem 5.23 (weak recognizability, 1-local, `k = 1`) gives
     `‖A_{≥i+m} cO A_{=i}‖ ≤ e√(10(3s/N)^{m'})`.
   - Hence `α_j(s+1) ≤ α_j(s) + e√10 Σ_{m=1}^{j} (3s/N)^{m/2} α_{j−m}(s)`, with `α_0 ≤ 1`.
   - Induction with `C = 2e√10` gives `α_j(q) ≤ θ^j` for all `j ≤ 2^31`. Write `ρ = √(3q/N)`. The
     `m = 1` term contributes `≤ (1/2)(Cρq)^j`, and the `m ≥ 2` terms contribute
     `≤ (Cρq)^j · c₀/(C²(1 − 1/C)) ≤ 0.031·(Cρq)^j`.
3. **Transitions into `Bad`** from `¬Bad ∩ A_{=i}` (weak recognizability):
   - an H₄ query hits `Z` with probability `≤ |T|·i/N`;
   - a Π query creates an agreement at one of the `≤ s|T|` points `x₀(iv,twk)` with probability
     `≤ s²|T|p`.

   So `‖Bad·ψ_q‖ ≤ Σ_{s<q} [ e√(10 s²|T|p) + Σ_{1≤i<2^31} e√(10|T|i/N)·α_i(s) + α_{2^31}(s) ]`. Use
   `Σ_i √i θ^i ≤ θ/(1−θ)² ≤ 4θ`. ∎

| `q₁ = q₄` | free-iv bound | H₄ bound |
|---|---|---|
| `2^30` | `2^{−32.8}` | `2^{−74}` |
| `≳ 2^37` | `≳ 2^{−12}` | not applicable (`θ > 1/2`) |

**`ε_multi := min(ε_multi^free, ε_multi^H₄)`.** For `q ≳ 2^{40}` neither bound is meaningful; see §9.

**Corollary 5.3 (ε_OE).** For one commitment,

    Pr[check(k, ι, t) passes ∧ k ≠ ô]  ≤  2(2q₂+1)²·p + ε_multi.

For `L = 2304` leaves the bound is `L·2(2q₂+1)²·p + ε_multi`. The `ε_multi` term is one event for
all leaves.

**iv and inverse queries.**
- *Inverse queries before `Ext`.* Inverse (and forward) queries under `k` put `k` into the database.
  So "pick `com`, then find `k` via `E_k⁻¹`, then pick `iv`", done before Θ, is not an attack: `k` is
  extracted, and P2 says it opens.
- *Inverse queries after `Ext`.* These are covered by Theorem 4.2, through Lemma 3.1.
- *`iv` after `Ext`.* `iv` is fixed at `Ext` time (it is in Θ's input), so freedom after `Ext` is
  Q2's H₂¹/H₁ binding, not Q1's business.
- *`iv` before `Ext`.* The adversary's freedom here matters only for `multi`. Theorem 5.1 needs no
  property of H₄; Theorem 5.2 uses that `iv` must be an H₄ output.

## 6. Efficiency: what the extractor needs from a simulator

`S^IC` is information-theoretic: a non-`⊥` register holds a superposition over `Sym(X)`. DFMS's
sparse representation (their App. B) covers the key level (`≤ q` keys, efficiently listable) but not
the permutation inside each register. The efficient simulation is being handled separately (qPRP-based
versus compressed permutation oracles). The results here are stated so that they transfer.

**Requirement on a simulator `Sim`.** `Sim` must be an efficient stateful oracle with interfaces
`Enc`, `Dec`, `Ext_ι(t)` (classical `ι`, `t`; outcomes `∅ / k / multi`). For every adversary making
`q` cipher queries and `ℓ` classical `Ext` queries, interleaved arbitrarily, `Sim` must be
`ε_Sim(q, ℓ)`-indistinguishable from `S^IC` as a three-interface oracle. Indistinguishability is
measured in trace distance of the adversary's final state together with all `Ext` outcomes.

Then every probability bound in §4–§5 holds for `Sim` up to an additive `ε_Sim`. Each of them
(P2–P4, Theorems 4.2, 5.1, 5.2) is a bound on an event of the joint classical output: `Ext`
outcomes, adversary outputs, and checks done through `Enc`. The commutation properties P1 also
transfer: the trace distance between the two orders is at most `δ + 2ε_Sim`.

The analyses' own extra devices (the full-value reduction, the H₄ database) are proof-only. The
extractor never needs them.

Remarks for the simulation worker:
- **Definition B is enough on the simulator side.** Suppose `Sim` keeps point-level records. Then
  `Ext` may be implemented as Definition B: find a database key with one matching recorded block,
  evaluate the other block (`Ext` may evaluate the cipher internally), and return `multi` if two
  keys pass. This is acceptable provided the resulting interface is `ε`-close to `S^IC`'s. The gap
  is the "touched key, both values match, no matching record" event of §3. Proving this closeness
  is part of `ε_Sim`.
- **Option E1 (computational).** Set `E_k := P_{g(k)}` with `g` a compressed RO,
  `P_{(s',α,β)}(x) = Q_{s'}(αx + β)`, and `Q` a strong qPRP (Zhandry, eprint 2016/1076).
  - The affine pre-whitening makes (F1) hold *exactly* for every `Q`.
  - DFMS's simulator for `g`, with commitment function `F_ι(k,s) = P_s(x₀) ‖ P_s(x₁)`, then has
    `Γ/|Seed| = Γ'/|Seed| = p`. So §4's proofs go through verbatim. `δ` at most doubles if one
    does not use diagonality.
  - The residual is the distance from an ideal cipher: a multi-key strong-qPRP step, plausibly
    `O(q²)·Adv^{sqprp}` via the keyed-oracle lifting of Bhaumik–Huang (eprint 2026/2324; abstract
    only).
  - Note that in E1, `S^sim` is not `ε`-close to `S^IC` as a three-interface oracle; it is a different
    oracle with its own exact properties. The real-world transfer is then via `ε_sim` on
    efficiently testable events, as in DFMS-style PoK statements.
- **Option E2 (statistical).** Use compressed permutation oracles with inverse access: Carolan,
  arXiv 2509.18586, soundness `O(q³/N^{1/4})` (Thm 5.19); Carolan–Majenz, arXiv 2609.28469, with
  tight `Ω(√N)` soundness (abstract). Such an oracle might also give binding at the point level
  (§9.2).

## 7. Literature: what is cited and what is new

**Cited:**
- Zhandry 2019 (compressed oracle; Lemma 5);
- CFHL EUROCRYPT 2021 (abelian-range framework; Lemma 5.6; Theorems 5.17, 5.23; Example 5.28);
- DFMS EUROCRYPT 2022, eprint 2021/280 (Lemmas 2.1, 3.3, 3.4; Thm 3.1; Thm 4.3; Cor. 4.7/4.8;
  App. B, D).

**Related:**
- Majenz–Malavolta–Walter, eprint 2024/1140: permutation superposition oracles with inverse
  access, not list-of-pairs.
- Carolan 2025, Carolan–Majenz 2026: compressed permutation oracles, including inverse access.
- Bhaumik–Huang, eprint 2026/2324: lifting for keyed oracles; an efficiently implementable
  compressed ideal cipher built on Carolan's oracle (abstract only; the PDF was not reachable).
- Hosoyamada–Yasuda, ASIACRYPT 2018: QICM, Davies–Meyer one-wayness.
- Hosoyamada–Iwata 2019: 4-round Luby–Rackoff qPRP claim; a bug was found by Bhaumik et al. 2024,
  per Carolan.
- Alagic–Bai–Katz–Majenz et al. (post-quantum Even–Mansour): not checked in detail here; to my
  knowledge they give no key-extraction interface.

**New here, as far as I found:**
1. Key-level recording for the ideal cipher, with the full DFMS online-extraction toolkit, for
   predicates on a key's values at fixed points. This needs no permutation-level recording, and
   `Γ/2^n ↦ p` is exact. It works because DFMS's proofs use only "controlled on `D_x`", which
   evaluation queries satisfy.
2. The `{∅, k, multi}` measurement with commutator `8√(2p)`, and the squared `O(q²p)` dead-leaf,
   uniqueness and persistence bounds.
3. The agreement-level analysis (Theorem 5.2) for the `multi` event using H₄.
4. Affine pre-whitening for an exact `Γ` in qPRP-based simulators.

Bhaumik–Huang's compressed ideal cipher may overlap with point 1 in spirit, but it is
permutation-level.

## 8. Interface for Q2

Q2 may assume a simulator `S` (`S^IC`, or any `Sim` meeting §6 with error `ε_Sim`), with
`N = 2^128`, `p = 1/(N(N−1))`, and:

- **(I0)** Without `Ext`, `S` is perfectly (or `ε_Sim`-) indistinguishable from the QICM.
- **(I1) Commutation.**
  - `Ext` commutes exactly with RO queries (H₁…H₅, DFMS's H₁ simulator, DFM20 reprogramming), with
    adversary unitaries, and with other `Ext`.
  - With each `Enc`/`Dec` query, `Ext` `δ`-almost-commutes, `δ = 8√(2p) ≤ 11.32·2^{−128}`.
  - Moving one `Ext` across `n` cipher queries costs `nδ` in trace distance.
- **(I2) Alive / dead.** Leaf `(i,j)` of chain Θ is *alive* iff `Ext_{(iv_Θ, twk_i)}(com^Θ_{i,j}) ∈ K`
  when applied at Θ's time, after the extractor's classical H₄ query for `iv_Θ`. Its committed seed
  is that key.
- **(I3) Correctness, ε_OE.** If `k` is the key eventually used or opened for the leaf, then
  `Pr[check(k) passes ∧ k ≠ ô] ≤ 2(2q₂+1)²p + ε_multi`. This includes:
  - (I3a) dead leaves: `Pr[ô = ∅ ∧ the leaf is later validly opened] ≤ 2(2q₂+1)²p`;
  - (I3b) a different key: `Pr[ô = k̂ ∈ K ∧ another key opens] ≤ 2(2q₂+1)²p`.

  Over `L = 2304` leaves the bound is `L·2(2q₂+1)²p + ε_multi`.
- **(I4) Validity.** `ô ∈ K` passes the extractor's own evaluation with probability `≥ 1 − 2p` at
  `Ext` time (P2), and `≥ 1 − 2(2q₂+1)²p` at the end (Thm 4.2(c)).
- **(I5) `multi`.** `Pr[ô = multi] ≤ ε_multi = min(ε_multi^free, ε_multi^H₄)` (Thms 5.1, 5.2), with
  - `ε_multi^free = (320/9)·q₁³/(N−1)`;
  - `ε_multi^H₄ ≈ 1.8·10⁷·(2q₁+q₄+1)⁵·2^{−256} + 2^{−127}`, valid while `θ ≤ 1/2`.
- **(I6) Lemma 5 (P4).** `√P_real ≤ √P_db + √(2p)`.
- **(I7)** The database has at most `q` keys at all times.

Here `q₁` and `q₂` are the cipher queries before and after `Ext` (verifier's and extractor's
included in `q₂`).

**Not provided:**
- binding of `iv`, `com` and the leaf commitments to Θ (H₂¹/H₁; L1, Q2);
- uniqueness of GGM inner-node seeds. Opened inner nodes enter only through the leaf keys the
  verifier derives, which (I3) covers.

## 9. What fails or is loose, and fallbacks

1. **Efficiency** is not solved here. It is delegated, with the precise requirement in §6.
2. **`multi` (two keys open the same leaf commitment) is only bounded for moderate `q`.**
   - Without H₄ the bound is `35.6·q³·2^{−128}`. With H₄ it is `≈ 1.8·10⁷·q⁵·2^{−256}`, but only for
     `q ≲ 2^{37}`. Both are vacuous by `q ≈ 2^{40}`.
   - This is intrinsic to key-level reasoning, and not only a proof artefact. The key database
     "knows" each touched key's whole permutation. Among `q` touched keys, pairs agreeing on some
     adjacent pair `(z, z⊞e₀)` exist with probability `≈ q²/N` classically, and can be created
     with probability `≈ q³/N` by BHT-style quantum search in the full-value view. A Grover search
     over `iv_pre` then hits such a `z`.
   - A real attacker must instead find a 256-bit collision `E_k(x_c) = E_{k'}(x_c)`, `c = 0, 1`,
     under the same `iv`, which costs about `2^{85}` quantum queries.
   - **Fallback:** bound `multi` at the point level. The needed statement is a collision-type
     database bound in a compressed ideal cipher (E2 or Bhaumik–Huang): "two database keys with both
     blocks recorded and equal under one iv in the H₄ database", which should be `O(q³/N²)` plus the
     oracle's soundness error. Alternatively, a simulator whose `Ext` has Definition-B semantics
     returns `multi` only on that recorded-collision event.

     `multi` is the only Q1 quantity that needs this. Theorem 4.2 is fine at all `q`
     (`≈ 2^{−113.8}` for `L = 2304`, `q₂ = 2^{64}`).
3. **`ε_multi^H₄` has a constant `2^{−127}`.** It comes from DFMS eq. (8), for reading `iv` back from
   the compressed H₄ database. This is harmless.
4. **No power-of-two assumption is needed.** Every constant is either re-derived (Lemmas 3.1 and 3.2,
   P2–P4, Theorem 4.2) or obtained from CFHL, which is stated for abelian ranges (§5).
