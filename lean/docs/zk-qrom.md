# Zero knowledge of vole-mole's VOLEitH proofs against quantum distinguishers (QROM)

This note lifts `lean/docs/zk.md` (classical, programmable ROM) to quantum distinguishers in the quantum
random oracle model. It assumes the dedicated-label-rows fix (branch `voleith-label-rows`, faest
patch 0005). With the fix, lean/docs/zk.md's condition (PU) is gone: zero knowledge holds for every witness.

Notation follows lean/docs/zk.md: λ = 128, τ = 17, w_grind = 8, `n_mult ≤ 312` gates, `n_mask = d + 3`
masks, ℓ witness bits. Code citations of the form `voleith.hpp:N` are to `src/voleith.hpp` **on
branch `origin/voleith-label-rows`** (commit d5def9c). Its lines are 17 higher than on `main` from
line 20 on. `faest/<file>:N` is faest-arch-opt v3.0.0 as patched in this repository, and
"patch 0005" is
`subprojects/packagefiles/faest-arch-opt/0005-Optionally-derive-CRT-VOLE-gate-labels-from-dedicated-rows.patch`
on that branch. "Spec" is the FAEST v3.0 specification. "GHHM" is Grilo, Hövelmanns, Hülsing and
Majenz, *Tight adaptive reprogramming in the QROM*, ASIACRYPT 2021 (arXiv:2010.15103v2; the
theorem numbers below were checked against that version).

---

## 0. Summary

**Theorem (informal).** Assume the fix (§1), quantum random oracles for H₂⁰…H₂⁴, H₃, H₄, H₅ and
the XOFs, AES-128 secure as a PRP against quantum adversaries that query it *classically*, and
fresh uniform 128-bit `rho` per proof. Then the proof system is adaptive multi-proof NIZK against
quantum distinguishers that choose `(x, w)` themselves and query all oracles in superposition.
In the non-delayed experiment, and in the delayed experiment where the distinguisher sees π₁ only
through a random-oracle hash that contains chal1 (as in PomFRIT), the bound is

```
ε_ZK^Q ≤ ε_rho + ε_RP + 2·ε_hide + ε_lab + 2·ε_iv + ε_neg

ε_rho  = 4·q₃²·Q_P·2⁻¹²⁸ + Q_P²·2⁻¹²⁹          H₃ replaced by fresh coins       (Lemma R)
ε_RP   = Q_P·( √(q₂₁*·2⁻¹²⁸) + q₂₁*·2⁻¹²⁹ )     chal1 made fresh, entropy from iv_pre  (Lemma C)
ε_hide = spec Lemma 10.51's PRG terms (classical-access PRP, quantum adversary)  (H4, H8)
ε_lab  = 4·(q₅*)²·K·2⁻¹²⁸,  K = 2               H₅ sibling labels, Θ hidden   (Lemma R)
ε_iv   = C(Q_P,3)·λ²·2⁻²⁵⁶ + 2⁻λ                no iv value occurs 3 times    (spec Cor. 10.18)
ε_neg  = reprogramming at points with ≥ 256 bits of fresh entropy (H₂², H₂³ slices, H₅ before
         the proof, reverse hops): below 2⁻⁹⁰ for q ≤ 2⁶⁴                  (Lemma C)
ε_abort = 0
```

Here `q_o` counts the distinguisher's queries to oracle `o`. Starred counts add the challenger's
own classical queries: `q₂₁* = q₂₁ + Q_P + Q_V` and `q₅* = q₅ + n_mult·(Q_P + Q_V)`. In lean/docs/zk.md's full
delayed experiment, where the distinguisher sees π₁ before it picks the instance, add the
computational term `ε_dly = Σ_j (√p_j + p_j/2)` of §6, Q2b.

**Numbers** (λ = 128, `Q_P = 2³⁰`, every per-oracle count = q; Lean `VoleMole/ZK/QROM.lean`):

| term | q = 2³⁰ | q = 2⁵⁰ | q = 2⁶⁴ | matching attack? |
|---|---|---|---|---|
| ε_rho | 2⁻³⁶ | 2⁴ (vacuous) | vacuous | **yes**: multi-target Grover on `rho` when the distinguisher repeats `(w, x)` (§7.4) |
| ε_RP | 2⁻¹⁹ | 2⁻⁹ | 2⁻² | none known (proof artifact) |
| ε_lab | 2⁻⁴⁶ (challenger's queries dominate) | 2⁻²⁵ | 2³ (vacuous) | yes, up to `n_mult²·32` (Grover over Θ, §7.3) |
| 2·ε_hide, single-key PRP + union bound | 2⁻²⁹ | 2¹¹ (vacuous) | vacuous | union bound only |
| 2·ε_hide, multi-user heuristic `t²·2⁻¹²⁸` | 2⁻⁶⁷ | 2⁻²⁷ | 2¹ (vacuous) | yes: Grover on one AES key |
| ε_iv, ε_neg | ≤ 2⁻⁹⁰ | ≤ 2⁻⁹⁰ | ≤ 2⁻⁹⁰ | |
| **total** (union-bound hiding) | **≈ 2⁻¹⁹** | vacuous | vacuous | |
| **total** (with 256-bit `rho` and multi-user AES) | **≈ 2⁻¹⁹** | **≈ 2⁻⁹** | vacuous | |

**Dominant term.** For q up to about 2⁴⁰ it is ε_RP ≈ Q_P·√(q/2¹²⁸). It arises because the only
*statistically* fresh input to the first reprogrammed oracle is the 128-bit `iv_pre`. I know no
attack that matches it. Around q = 2⁵⁰, the 128-bit secrets exposed to multi-target search
dominate: `rho` (a real attack) and the AES keys of the hidden GGM nodes (a union-bound loss). At
q = 2⁶⁴ the bound is vacuous, and that is inherent for λ = 128: Grover recovers a hidden AES-128
key with about 2⁶⁴ evaluations.

**Comparison with FAEST v3.** The spec makes **no standalone QROM ZK claim**. Its QROM EUF-CMA
bound (Thm 10.53, Cor 10.54) contains the simulation steps. Its chall₁ step costs
`2·Q_sig·3·√(… + 3√(Q₁·2⁻λ) + …)`, which is about `Q_sig·(Q₁/2¹²⁸)^{1/4}` and is already
vacuous at `Q_sig = 2³⁰` (2^8.9 at `Q₁ = 2³⁰`). Our ε_RP is the counterpart of that step, and it
is 2⁻¹⁹ at the same counts. The spec's QROM proof also needs no q²-type label term. An EUF-CMA
reduction can leave H₅ programmed forever, while a ZK simulator against a distinguisher that knows
`w` cannot (§7.3).

**Findings beyond the proof.**
1. **`rho` should be 256 bits.** With 128-bit `rho` (`voleith.hpp:91`) and `Q_P` proofs of the
   same `(w, x)`, a quantum distinguisher finds some `rho_j` after about `√(2¹²⁸/Q_P)`
   evaluations of H₃. That is 2⁴⁹ at `Q_P = 2³⁰`, and it breaks ZK for that proof. The attack
   needs `w_pre`, so in the protocols it matters only where the adversary knows the witness
   prefix (§10).
2. **The fix is what makes a quantum proof possible.** The sibling labels are `forced ⊕ Θ`, with Θ
   uniform and independent of the view. Lemma R (§3.2, new) then gives a q²-type bound. Without
   the fix, `Θ = d ⊕ w[0..λ)`, and Prop. 4.1 of lean/docs/zk.md applies.
3. **lean/docs/zk.md's H2 has a gap in the delayed mode.** Its "chal2 is fresh" needs `z = (chal1 ‖ ũ ‖
   h_V ‖ … ‖ d)` to be unpredictable given π₁. That is only computational (§6, Q2b). It is easy
   to fix classically, but costly in the QROM.
4. **Only standard post-quantum PRP security of AES (classical queries) is needed**, not qPRP or
   Zhandry's quantum GGM: the hidden keys are only ever used by the challenger, on classical
   inputs (§3.4).

---

## 1. The fix: properties used, and the branch

The proof uses exactly these properties.

- **(F1) Dedicated label rows.** The gate labels are `L⁰_e = G[e]·V[R_Θ]` and `L¹_e = L⁰_e ⊕ Θ`.
  Here `R_Θ` is a set of λ VOLE rows disjoint from the witness rows and from the mask rows, and
  `Θ := u₀[R_Θ]` is tree 0's VOLE input on them.
- **(F2) Corrections, but no d.** Each tree `i ≥ 1` publishes `c_i[R_Θ] = u₀[R_Θ] ⊕ u_i[R_Θ]`.
  Neither prover nor verifier applies a witness correction on `R_Θ`. So the verifier's corrected
  keys satisfy `Q[R_Θ] = V[R_Θ] + Δ·Θ`, and its label is `L^{γ_e} = G[e]·Q[R_Θ]` with
  `γ_e = G[e]·Δ`. Hence **sibling label = forced label ⊕ Θ**.
- **(F3) Θ enters nothing else in the clear.** The witness, the constraints and QuickSilver do not
  touch `R_Θ`. The KOS hash may cover `R_Θ`; it does on the branch. Its response stays masked by
  the four KOS masks, so the H6/H7 bijections are unchanged.
- **(F4) Fresh per proof.** `R_Θ` belongs to the proof's own VOLE, which comes from the fresh
  seed. So after H4, Θ comes from tree 0's hidden leaf and is padded in each `c_i` by tree `i`'s
  hidden leaf.
- **(F5)** The H₅ input format `(iv, e, L)` is unchanged.

Consequence (used in H5): after puncturing, `(Θ, c_1[R_Θ], …, c_{τ−1}[R_Θ])` is uniform, because
`(u₀, u_i) ↦ (u₀, u₀ ⊕ u_i)` is a bijection (Lean `correctionsEquiv` with `w = 0`). Θ is then
independent of the opened data, the corrections, `d`, the masks and `Q`.

**The branch matches.** I read commit d5def9c (`git show origin/voleith-label-rows`), patch 0005
and the `voleith.hpp` diff.
- (F1): `CRT_LABEL_ROW_OFFSET = QUICKSILVER_ROWS = WITNESS_BITS` and `CRT_LABEL_ROWS = λ`. The
  prover's offset is `crt_label_offset` (u at that offset). Both sides compute labels with
  `crt_labels`, from the label rows of V or Q. Both are called from `lift_and_hash_vq`.
- (F2): `VOLE_CORRECTION_ROWS = QUICKSILVER_ROWS + CRT_LABEL_ROWS`, so the label rows get `c_i`.
  The verifier applies `d` only for `i < WITNESS_BITS` (`voleith.hpp:470-477`). The prover's
  correction array has exactly `WITNESS_BYTES` (`voleith.hpp:293-299`).
- (F3): QuickSilver reads the witness rows only (`QUICKSILVER_ROWS = WITNESS_BITS`,
  `faest/constants.hpp:353-359`; `voleith.hpp:306-312`). KOS covers `VOLE_CORRECTION_ROWS`
  (`voleith.hpp:240-243`), so it covers the label rows.
- The mask rows start at `VOLE_CORRECTION_ROWS` (`faest/vole_commit.inc:196-210, 295`), so they
  are disjoint from the label rows.
- The flag is on for all five relations, with static_asserts in the relation headers.

I found no deviation.

---

## 2. Model and notion

**Oracles.** H₂⁰…H₂⁴, H₃, H₄, H₅, the PomFRIT target hash `G` and the UOV-combination XOF are
independent random functions, by domain separation. The distinguisher `D` has superposition access
to all of them. AES is a fixed public function. `D` may evaluate it on any key, in superposition,
as part of its own computation. In the standard model that is not an oracle. The quantum
ideal-cipher variant is in Remark 3.5.

**Experiment `Exp^{mode}_b`** (b = 0 real, b = 1 simulated). `D` interacts with a challenger for
`Q_P` proofs, in any order. It may trigger `Q_V` verifications.
- `mode = nd` (non-delayed). `D` submits `(x, w, b₁, b₂)` with `(x, w) ∈ R` and receives a proof.
  This is the four Keccak relations: `WITNESS_PREFIX_BYTES = WITNESS_BYTES`, with the instance
  bound at `voleith_vole_gen`.
- `mode = dly` (lean/docs/zk.md §2, with the prefix-predictability restriction removed). `D` submits
  `(w_pre, b₁, aux₀)` and receives π₁: the step-1 fields plus chal1. Then it submits
  `(x, w_suf, b₂)` with `(x, w_pre ‖ w_suf) ∈ R` and receives π₂.
- `mode = dly-G` (blind delayed). As `dly`, but between the phases `D` receives only
  `G(chal1 ‖ ũ ‖ d_pre ‖ aux₀)`, for a random oracle `G`. It receives π₁ together with π₂. This is
  PomFRIT's issuance: the Issuer sees `t = h ⊕ r` with
  `h = hash_to_target(pk, chal1, ũ, d_pre, msg)` (`src/pomfrit/pomfrit.cpp:96-111, 167-176`). A
  `D` that knows `r` thus sees exactly `G(…)`.

In the simulated experiment the challenger runs `Sim^Q` (§4), which never sees `w` and may program
oracles. `ε_ZK^Q := |Pr[Exp_0 → 1] − Pr[Exp_1 → 1]|`. This is standard adaptive multi-proof NIZK:
`D` knows `w`.

---

## 3. Tools

### 3.1 Reprogramming a set (GHHM Theorem 1, set version), "Lemma C"

Use the superposition oracle (GHHM §5.1). Register `F_x` holds the value at `x`, initially
`|φ₀⟩ = 2^{−m/2}Σ_y|y⟩`. For a set `T` of inputs, let `P_T := ⊗_{x∈T}|φ₀⟩⟨φ₀|_{F_x}` and
`ε_T := 1 − ‖P_T γ‖²` for the joint algorithm-oracle state γ. *Reprogramming H on T to fresh
independent uniform values* means resetting `F_T` to `|φ₀⟩^{⊗T}`.

**Lemma C.** Resetting `F_T` changes the joint state by `‖ρ − ρ'‖₁ ≤ 2√ε_T + ε_T`. So it changes
any later distinguishing probability by at most `E[√ε_T + ε_T/2] ≤ √(E ε_T) + E ε_T/2`. If `T` is
sampled independently of γ (with arbitrary side information given afterwards), and at most q
queries have been made, then `E ε_T ≤ q·P_T` with `P_T := max_x Pr[x ∈ T]`.

*Proof.* For |T| = 1 this is GHHM Theorem 6, eqs. (8)–(12). For a general T, replace the
projector `|φ₀⟩⟨φ₀|_{F_x}` by `P_T` in eqs. (8)–(11). Those steps use only that it is a projector
and that the reset is `Tr_{F_T}(·) ⊗ |φ₀⟩⟨φ₀|^{⊗T}`.

For the expectation, write `ε_x := ε_{{x}}`. The `P_x` commute, so `1 − P_T ≤ Σ_{x∈T}(1 − P_x)`,
and hence `ε_T ≤ Σ_{x∈T} ε_x`. GHHM Lemma 1 (from AMRS20 Lemma 2) decomposes
`γ = Σ_{|S|≤q} ψ^{(S)} ⊗ |φ₀⟩^{⊗S^c}` with `⟨φ₀|_{F_x}ψ^{(S)} = 0` for `x ∈ S`. Then
`ε_x = Σ_{S∋x}‖ψ^{(S)}‖²`, so `Σ_x ε_x = Σ_S |S|·‖ψ^{(S)}‖² ≤ q`. Therefore
`E_T ε_T ≤ Σ_x Pr[x∈T]·ε_x ≤ P_T·q`. ∎

Several reprogrammings combine by the hybrid argument of GHHM Lemma 2 / Theorem 1. The costs add.
`ε_T` is the probability that the binary measurement `{P_T, 1 − P_T}` reports "recorded". In a
compressed-oracle simulation (Zhandry, CRYPTO 2019) this is "some `x ∈ T` is in the database",
which is efficiently testable. The computational use in Q2b relies on that.

### 3.2 Hidden-set reprogramming, "Lemma R" (new)

**Lemma R.** Let Θ have distribution `p` on a finite set, independent of all other randomness.
Fix the other randomness. Let an algorithm be given by unitaries `U_0, …, U_q` on `H`, which do
not depend on Θ (the distinguisher, the challenger and deferred measurements all folded in), and q
queries.
- In world 0, query `i` applies a unitary `O^{(i)}`.
- In world 1, query `i` applies `O^{(i)}_Θ`.

Let `H = ⊕_z H_z` be the decomposition by query input, *including any classical control
registers* such as the adversary's chosen instance or the challenger's coins. Suppose both oracles
are block diagonal, `O^{(i)}_Θ = O^{(i)}` on every block `z ∉ S^{(i)}_Θ`, and
`b := max_{i,z} Pr_Θ[z ∈ S^{(i)}_Θ]`. The programmed values may depend on Θ and on the control
registers arbitrarily. Then for the final states,

```
TD( ρ₀ , E_Θ ρ₁^Θ ) ≤ 4·q²·b.
```

*Proof.* Purify Θ in a register `R_Θ` with `|u⟩ := Σ_Θ √p_Θ|Θ⟩`. World 1 is
`C_i = Σ_Θ |Θ⟩⟨Θ| ⊗ O^{(i)}_Θ = 1 ⊗ O^{(i)} + D_i`, with
`D_i = Σ_Θ |Θ⟩⟨Θ| ⊗ D_{i,Θ}` and `D_{i,Θ} = O^{(i)}_Θ − O^{(i)}`. Write the world-1 state before
query `i` as `|u⟩⊗α_i + Γ_i`, with `Γ_i ∈ u^⊥ ⊗ H`. Let ψ_i be the world-0 state, `e_i := α_i − ψ_i`,
and `α_0 = ψ_0`, `Γ_0 = 0`.

Three operator facts, from block diagonality and `‖D_{i,Θ}Π_z‖ ≤ 2`:
- (a) `Ē_i := Σ_Θ p_Θ D_{i,Θ} = Σ_z Π_z (Σ_Θ p_Θ 1[z ∈ S_Θ] D_{i,Θ}) Π_z`, so `‖Ē_i‖ ≤ 2b`.
- (b) `‖D_i(|u⟩⊗φ)‖² = ⟨φ|Σ_Θ p_Θ D†D|φ⟩ ≤ 4b‖φ‖²`, since `Σ_Θ p_Θ D†D ≤ 4Σ_z Pr[z∈S]Π_z`.
- (c) For `Γ = Σ_Θ |Θ⟩⊗Γ_Θ`, `(⟨u|⊗1)D_iΓ = Σ_Θ √p_Θ D_{i,Θ}Γ_Θ = R(Γ)`. Here
  `‖R‖² = ‖Σ_Θ p_Θ D D†‖ ≤ 4b`, so this is at most `2√b·‖Γ‖`.

Since `⟨u|(1⊗O)Γ = O⟨u|Γ = 0`, one query followed by `U` gives:
- `α_{i+1} = U[(O + Ē)α_i + ⟨u|DΓ_i]`, hence `‖e_{i+1}‖ ≤ ‖e_i‖ + 2b + 2√b·‖Γ_i‖`;
- `Γ_{i+1} = U[Π_{u^⊥}D(|u⟩α_i) + Π_{u^⊥}C Γ_i]`, hence `‖Γ_{i+1}‖ ≤ ‖Γ_i‖ + 2√b`.

Tracing out `R_Θ` kills the cross terms, because `Γ ⊥ |u⟩` in `R_Θ`. So
`ρ₁ = α_qα_q† + Tr_Θ Γ_qΓ_q†` and `ρ₀ = ψ_qψ_q†`. Then
`TD ≤ ½‖αα† − ψψ†‖₁ + ½‖Γ_q‖² ≤ ‖e_q‖ + ½‖Γ_q‖²`. The recurrences give `‖e_q‖ + ½‖Γ_q‖² ≤ 4q²b`
(Lean `lemmaR_td`, with `gamma_le` and `err_le`). Average over the other randomness. ∎

**Why not O2H.** One-way-to-hiding (Ambainis–Hamburg–Unruh, CRYPTO 2019, Thms 1–3) needs the set
fixed in advance, while our sets depend on adaptive choices. It also gives only `≈ 4q√b`. Lemma R
is adaptive, and its `q²b` matches Grover: with a verifiable hidden point, search succeeds with
probability `Θ(q²b)`. The key step is that the first-order term averages over Θ to `‖Ē‖ ≤ 2b`, not
`2√b`.

**Confidence: medium-high.** The proof is short and self-contained, the scalar part is in Lean,
and the three operator facts are elementary. It is new and has not been reviewed.

### 3.3 Efficient simulation of quantum random oracles

The PRG reductions (H4, Q2b) must run `D` efficiently. A 2q-wise independent function perfectly
simulates a q-query QRO (Zhandry, CRYPTO 2012, "Secure identity-based encryption in the quantum
random oracle model", Thm 6.1). Alternatively one can use the compressed oracle. Programmed points
and slices are overrides computed in superposition ("if x ∈ T then table(x) else f(x)"). An
H₂³ slice is overridden by a fresh 2q-wise independent function of the counter.

### 3.4 AES assumption

**ε_hide** is spec Lemma 10.51 (the QROM version of Lemma 10.24) without its H₅ term:

```
ε_hide = (γ − 1) + Q_P·Adv^{PRG_root}[1] + Q_P·τ⌈log L − 1⌉·Adv^{PRG_2λ}[1] + Q_P·τ·Adv^{leaf}[1],
γ = e^{Q_P(β_root² + 4τ⌈log L − 1⌉β² + τ·a_leaf²)/2¹²⁸},
```

with the FAEST-EM leaf variant. The advantages are those of quantum adversaries that receive the
generator outputs *classically*.

That is all the proof needs. Every hidden key (the root, the hidden-path nodes and the hidden
leaves) is used only by the challenger, on fixed classical inputs `iv ⊞ (cnt, twk)`
(`faest/prgs.hpp:204`). `D` never gets superposition access to a keyed function under a hidden
key. Its "quantum access to AES" is its own computation, and the PRG distinguisher may perform it
too. So neither qPRP/qPRF security nor Zhandry's quantum GGM theorem (FOCS 2012) is required. The
classical GGM hybrid over the co-path, with a quantum distinguisher, is enough.

For numbers I use the Grover heuristic `Adv(t) ≈ t²·2⁻¹²⁸` for a t-time quantum adversary. The
spec's union over all instances loses a factor of about `Q_P·205`. A multi-user assumption,
plausible because the plaintexts differ per key and per proof, would remove it.

**Remark 3.5 (quantum ideal cipher).** If AES is modelled as a quantum ideal cipher with forward
and inverse superposition queries, as in Q1/Q2, the hiding hop becomes Lemma R. Take Θ = the
values of the hidden keys. In world 0 the challenger uses independent permutations under them.
After a PRP/PRF switch on sibling outputs, `b ≤ Q_P·N_hid/(2¹²⁸ − β)` with `N_hid ≤ 138`
(L8 (S3)). This gives `≈ 4q_E²·138·Q_P·2⁻¹²⁸`, the same order as the union bound. I have not
written out the switch in full. Confidence: medium.

---

## 4. The simulator `Sim^Q`

`Sim^Q` is lean/docs/zk.md §5 with one change forced by the QROM: **programming never aborts**. A quantum
oracle cannot be checked for "already defined", so `Sim^Q` overwrites.
1. Sample `seed*` and `iv_pre` uniformly. Compute `mu`, `iv = H₄(iv_pre ‖ mu)` and
   `crt_vole_commit(seed*, iv)` honestly. Replace `c_mult` by a uniform value. Compute `chal1`
   honestly. Sample `ũ` and `d_pre` uniformly.
2. Sample the grinding outcome by the first-hit law: `ctr` geometric, `Δ ← A`, `Δ_c ← Aᶜ` for
   `c < ctr`, and output ⊥ with probability `(1 − p)^{2³²}`. Lean `card_isFirstHit`,
   `isFirstHit_uniform_on_A` and `card_noHit` show that this is exactly the law of the first hit of
   a uniform table.
3. Open at Δ. Recompute `Q`, the forced labels, `q̄` and `h_V` as the verifier does. Sample
   `d_suf` uniformly and compute `chal2` honestly. Sample `ã` uniformly and compute `qs_check` as
   the verifier does.
4. Set `H₂³(chal2 ‖ qs_check ‖ ã ‖ c ‖ 0x0B) := Δ_c` for `c < ctr`, and `:= Δ` for `c = ctr`.
   This overwrites. The input format is at `voleith.hpp:487-494`.

This is efficient, with at most `ctr + 1` overrides per proof (§3.3). It never uses `w` and never
programs H₅, H₂¹ or H₂².

**Punctured variant `Sim°`** (L8 §3.3) skips the hidden paths: co-path seeds are uniform and the
hidden-leaf commitments are uniform 2λ-bit strings (§11).

---

## 5. The theorem

**Theorem Q.** Assume (F1)–(F5), the oracle model of §2, the AES assumption of §3.4, a fresh
uniform secret 128-bit `rho` per proof (the callers satisfy this, lean/docs/zk.md §7.2), and satisfying
witnesses. Then for every quantum `D`:
- In `Exp^{nd}` and `Exp^{dly-G}`, `ε_ZK^Q ≤ ε_rho + ε_RP + 2ε_hide + ε_lab + 2ε_iv + ε_neg`, with
  the terms of §0.
- In `Exp^{dly}`, the same plus `ε_dly`.

`ε_neg` collects the following. For the H₂³ step, `q₂₃* := q₂₃ + Q_V + 2³²·Q_P` (the challenger's
grinding queries, worst case). For the H₂² step, `q₂₂* := q₂₂ + Q_P + Q_V`.
```
ε_neg = Q_P·[ √(q₂₂*·2⁻¹⁰⁸⁸) + √(q₂₃*·2⁻⁴⁴⁸) + √(q₅*·λ·2⁻²⁵⁶)
            + √(q₂₁*·2^{−128−n_mask·n_mult}) + √(q₂₂*·2⁻⁵¹²) + √(q₂₃*·2⁻⁴⁴⁸) ]
        (+ Q_P·√(q_G*·2⁻¹⁰⁸⁸) in Exp^{dly-G})  + (the linear halves)
```
plus the Kmax failure `2⁻λ` of spec Cor. 10.18.

---

## 6. Hybrids

All hybrids are over the whole multi-proof experiment. Proof-by-proof sub-hybrids are implicit,
and the per-proof costs add.

**Q0 = real.**

**Q1: H₃ → fresh coins** (`voleith.hpp:186-201`). This uses Lemma R with Θ = `(rho_j)_j`.

Reparametrize the real world. For each proof index `j`, pre-sample a random function `Y_j(·,·)`.
`D`'s H₃ on the slice `{(a, b, rho_j)}` is `Y_j(a, b)`, and the challenger uses
`Y_j(w_pre,j, mu_j)` as `(seed, iv_pre)`. This is the real world, unless two `rho` collide
(`Q_P²·2⁻¹²⁹`). In world 0, `D`'s H₃ is an independent random function. The challenger's coins
`Y_j(·)` do not depend on Θ, the oracles differ only on slices whose last component is some
`rho_j`, and `b ≤ Q_P·2⁻¹²⁸`.

Cost: `ε_rho = 4q₃²Q_P·2⁻¹²⁸ + Q_P²·2⁻¹²⁹`. The slice is needed because `(w_j, mu_j)` is chosen
adaptively, after the oracle must already be defined. After Q1, `seed` and `iv_pre` are fresh and
uniform.

**Q2a: chal1 fresh** (`voleith.hpp:223-233`). Apply Lemma C at phase 1 with
`T = {y₁}`, `y₁ = mu ‖ com ‖ c ‖ c_mult ‖ iv_pre ‖ b₁ ‖ 0x09`. `iv_pre` is fresh, so
`P_T ≤ 2⁻¹²⁸`. Cost: `ε_RP`.

This is the only reprogramming point in near-real hybrids with provable statistical entropy. The
seed's 128 bits reach `y₁` only through AES, which a statistical lemma cannot use (Remark 6.1).

**Q2b: chal2 fresh** (`voleith.hpp:235-243, 284-302`). Apply Lemma C to H₂² at
`T = {z}`, `z = chal1 ‖ ũ ‖ h_V ‖ [mu] ‖ b₂ ‖ d ‖ 0x0A`, at the moment the challenger forms `z`.
- **nd.** `D` has seen nothing since chal1 was sampled, so `E ε_T ≤ q₂₂*·2⁻¹⁰⁸⁸`.
- **dly-G.** First apply Lemma C to `G` at its input. That input contains the fresh chal1, so the
  cost is at most `Q_P√(q_G*·2⁻¹⁰⁸⁸)`. After this the between-phase leak is uniform and
  independent of chal1, `D`'s state between the phases is independent of chal1, and
  `E ε_T ≤ q₂₂*·2⁻¹⁰⁸⁸`.
- **dly.** `D` knows chal1, `ũ` and `d_pre`. The fresh part of `z` is `(h_V, d_suf)`, which is
  only computationally unpredictable. Here `p_j := E ε_{z_j}` is the probability that the
  H₂²-database contains `z_j` when phase 2 of proof `j` starts. An efficient `B_j` runs the
  hybrid up to that moment with compressed oracles. It needs no opening for proof `j`, because
  nothing has been opened yet, so it needs no Δ. It takes proof `j`'s leaves (all VOLE PRG outputs
  and leaf commitments, plus `u_hi`) from a challenge, and measures the database. With uniform
  leaves, `u₀` on the suffix rows is uniform given π₁, up to the ≤ 4λ bits that `ũ` can carry. So

  ```
  p_j ≤ Adv^{tree}(B_j) + q₂₂*·2^{4λ−ℓ_suf},      ε_dly = Σ_j (√p_j + p_j/2),
  ```

  where `Adv^{tree}` is the full-tree PRG advantage: root, all internal nodes and all leaves, by
  the spec's level hybrid. For PomFRIT, `ℓ_suf = 8·uov::N = 952`. The square root is intrinsic to
  reprogramming (GHHM show √ tightness). With `Adv^{tree}(t) ≈ t²·2⁻¹²⁸`, `ε_dly ≈ Q_P·t·2⁻⁶⁴`,
  which is vacuous at `Q_P = 2³⁰` already for `t ≈ 2³⁴`. That is weak, and it is the price of
  letting `D` see π₁ between the phases. The spec's G3 (quantum-list unpredictability, Lemma 10.52)
  pays the same kind of price.

**Q2c: Δ first** (lean/docs/zk.md H2; `voleith.hpp:314-333`, `faest/vector_com.inc:982-1066`). Apply
Lemma C to H₂³ on the whole *slice* `T = {P ‖ c ‖ 0x0B : c < 2³²}`, `P = chal2 ‖ qs_check ‖ ã`,
setting it to a fresh uniform table. chal2 was sampled fresh, inside the reprogramming
distribution, in Q2b. So `P_T ≤ 2⁻⁴⁴⁸`, and the cost is in `ε_neg`.

The honest prover now reads `(ctr, Δ, failed values)` off a uniform table. By the Lean first-hit
lemmas this is exactly the Sim law, and it includes the overflow abort, so `ε_abort = 0`. The table
is independent of everything before phase 2, so it may be sampled at phase 1: this is Δ first.
Reprogramming the whole slice, rather than only `c ≤ ctr`, avoids "already defined" questions.
Truncating to `c ≤ ctr` at the end costs `√(q₂₃*·2⁻⁴⁴⁸)` (in `ε_neg`).

**Q3: verifier-side recomputation.** Perfect, as in lean/docs/zk.md H3 (KOS and QuickSilver completeness
identities).

**Q4: puncture the hidden paths.** As in lean/docs/zk.md H4, now with Δ known at phase 1. This is
computational: `ε_hide`, with the reductions of §3.3/§3.4. The inputs under a key are distinct
because the tweak has its own lane, with tweaks `< 2³¹` (`faest/prgs.hpp:204`).

**Q5: decouple** (perfect). Sample `d`, `c_i` on all corrected rows, and Θ uniformly and
independently. Define `u₀ := d ⊕ w` on the witness rows, `u₀ := Θ` on `R_Θ`, and
`u_i := u₀ ⊕ c_i`. This uses Lean `correctionsEquiv` and `corrections_fiberCard`, with `w = 0` on
`R_Θ`. `Q` is a function of the opened seeds, the hidden-leaf commitments, `c`, `d` and Δ. It is
independent of Θ, because `c_i[R_Θ]` is sampled. `V := Q − Δ·u` (Lean `vole_v_unique`).

**Q6a: reprogram the sibling labels at proof time.** For proof `j` let
`S_j = {(iv_j, e, A_{j,e} ⊕ Θ_j)}_e`, where `A_{j,e} = G[e]·Q_j[R_Θ]` is the forced label (Lean
`label_q_eq`). Apply Lemma C to H₅ on `S_j` at phase 1. Then sample `c_mult` uniformly and set the
fresh values to `y_{j,e} := c_mult[·,e] ⊕ h^{γ}_{j,e} ⊕ F[e]·ū_j` (bijection, Lean `cmultEquiv`).

For a fixed `x = (iv*, e*, L*)`, `Pr[x ∈ S_j] ≤ Pr[iv_j = iv*]·2⁻¹²⁸ ≤ λ·2⁻²⁵⁶`: `iv_pre` is fresh,
H₄ is λ-preimage-bounded (spec Lemma 10.17, Cor. 10.18), and Θ is uniform. Cost:
`Q_P(√(q₅*·λ·2⁻²⁵⁶) + …)`, in `ε_neg`. This step handles queries made *before* the proof.

**Q6b: reparametrize the responses** (perfect). Sample `ũ` and `ã` uniformly and *define*
`ū := bij⁻¹(ũ, ã)`, the inverse of the KOS-plus-QuickSilver map for the given `w`, coefficients,
`q̄` and Δ (Lean `kosQsEquiv`, `qsResponse_bijective`). `ū` now depends on Θ, because the KOS hash
covers `R_Θ`, but it is used only inside the programmed values `y_{j,e}`.

**Q6c: stop programming H₅.** Lemma R. World 1 is Q6b. World 0 is Q6b without the H₅ programming.
All messages (`c_mult`, `ũ`, `ã`, `d`, `c`, openings, challenges) are sampled independently of Θ.
Θ occurs only in the set `∪_j S_j` and in the programmed values. The challenger's forced-label
queries and the verifications are classical queries, counted in `q₅*`.

To get `b ≤ K·2⁻¹²⁸` with `K = 2`, cap in both worlds: if `iv_j` already occurred twice, do not
program. The cap triggers with probability at most `ε_iv`, in either world, because `iv_pre` is
fresh; this costs `2ε_iv`. A query names one `iv` and one `e`, so it meets at most `K` proofs and
one gate of each. Cost: `ε_lab = 4(q₅*)²·2·2⁻¹²⁸`.

**Q7.** The state is lean/docs/zk.md H7: `c_mult`, `ũ`, `ã`, `d` and `c` are uniform, and H₅ is
unprogrammed.

**Q8: un-puncture.** Generate the tree honestly from `seed*` (`ε_hide`), and undo Q5 (perfect).

**Q9: undo Q2a/Q2b and truncate the Q2c slice.** In this hybrid `y₁` contains a uniform `c_mult`
(`n_mask·n_mult ≥ 1550` bits), and `z` contains a uniform `ũ` (512 bits). The costs are in
`ε_neg`. In `Exp^{dly}`, the H₂² undo uses `d_suf` (uniform, ℓ_suf bits) instead. **Q9 = Sim^Q.**

**Remark 6.1 (why ε_RP and not better).** Δ must be known at commit time for Q4. In near-real
hybrids, the only statistically fresh input on the path to Δ is `iv_pre`. The real distance
between Q0 and Sim^Q need not contain `√(q·2⁻¹²⁸)`: `Sim^Q` programs H₂³ only at points with
≥ 448 fresh bits. I conjecture ε_RP is an artifact. Removing it would need a reprogramming lemma
for computationally unpredictable points without the √ loss, or a puncturing argument that works
for an adaptively chosen hidden set. A fresh 256-bit salt in the chal1 input would make it
negligible at the cost of 32 proof bytes. The same salt in the chal2 input would remove ε_dly.

**Remark 6.2 (min-entropy of the programmed H₂³ input).** At Q2c the slice prefix
`P = chal2 ‖ qs_check ‖ ã` has `H∞ ≥ 448` statistical bits, from chal2. `ã` (`(d−1)·128` bits)
and the KOS response are only pseudorandom at that point, since their masks come from AES. In the
simulated world `ã` is uniform, so `H∞(P) ≥ 448 + 128(d−1)`. Through chal2, the H₂² input carries
`ũ` (512 bits) and `d_suf`. Grinding adds up to `2³²` points per proof, but they all share `P`.
The slice formulation charges the proof once, with `P_T ≤ 2⁻⁴⁴⁸`.

---

## 7. The labels in detail (ε_lab)

### 7.1 Why the fix is necessary and sufficient

Without the fix, `Θ = u[0..λ) = d ⊕ w[0..λ)`. Since `d` is public, Θ is a function of `D`'s view
and `w`. Lemma R does not apply, and lean/docs/zk.md Prop. 4.1 is an attack with advantage ≈ 1 using
`n_mult` classical queries.

With the fix, Θ is uniform and independent of everything `D` sees in Q6c's world 0, where `c_mult`
is a one-time pad and `ũ`, `ã` are uniform. Each sibling point is `forced ⊕ Θ_j`, so a fixed
query input hits it with probability at most `2⁻¹²⁸` per proof sharing its `iv`.

### 7.2 Query counting

`q₅* = q₅ + n_mult(Q_P + Q_V)` counts every H₅ evaluation in the run: `D`'s, the challenger's
forced labels, and the verifications `D` triggers. At `q = 2³⁰`, the challenger's
`n_mult·2·2³⁰ ≈ 2³⁹·³` dominates, giving `ε_lab ≈ 2⁻⁴⁶`.

### 7.3 Tightness: Grover over Θ

`D` knows `w`. For a candidate Θ', it computes `y_m = c_mult[m] ⊕ h^γ ⊕ H₅(forced ⊕ Θ')` and
tests `y_m ∈ im(F)` for all `m`. In a real proof the test passes for Θ' = Θ. For Θ' ≠ Θ it passes
with probability at most `2^{−(n_mult−λ)·n_mask}`.

Grover over Θ' with `q/n_mult` iterations finds Θ with probability `≈ (q/n_mult)²·2⁻¹²⁸`. It then
recovers `F·ū`, hence `ū`, and checks `ũ` and `ã` against `w`. A simulator that does not know `w`
fails one of the two tests:
- with a uniform `c_mult`, no Θ' passes;
- with an honest `c_mult` for its own Θ*, the recovered `ū*` does not match `ũ`, `ã`, `w`.

So every simulator is at distance `Ω((q/n_mult)²·2⁻¹²⁸)` from the real world (Lean
`lab_attack_at_2_64`: ≥ 2⁻¹⁸ at q = 2⁶⁴). This also explains why the spec's EUF-CMA reduction
escapes this term. It keeps H₅ programmed at the sibling points forever, which is consistent
because its adversary does not know the key.

### 7.4 The analogous attack on `rho`

If `D` asks for `Q_P` proofs of the same `(w, x)`, then `f(ρ') = [H₃(w_pre ‖ mu ‖ ρ').iv_pre ∈
{iv_pre,j}]` has `Q_P` marked points, and each candidate costs one H₃ query. Grover succeeds with
probability `≈ q²·Q_P·2⁻¹²⁸`, matching ε_rho, and the recovered `rho_j` lets `D` recompute proof `j`
exactly. With a 256-bit `rho`, `ε_rho = q²·Q_P·2⁻²⁵⁴` (Lean `rho256_at_2_64`: 2⁻⁹⁶ at q = 2⁶⁴).

---

## 8. Grinding under reprogramming

lean/docs/zk.md §7.3 shows that the counter depends only on Δ and the opening-size test, that the first hit
is returned even with 4-way batching, and that the verifier checks only the top bits. Q2c programs
the **whole slice** with a fresh uniform table, so the prover's output is a deterministic function
of a uniform table. Lean `card_isFirstHit`, `isFirstHit_uniform_on_A`, `isFirstHit_unique` and
`card_noHit` give its law, including the abort probability `(1 − p)^{2³²}`. That law is what
`Sim^Q` samples.

Three points that differ from the classical proof:
- There is no "already defined" abort: Lemma C charges the slice once per proof.
- The challenger's own grinding queries (at most `2³²` per proof) are counted in `q₂₃*`. They are
  harmless because `P_T ≤ 2⁻⁴⁴⁸`.
- A quantum `D` can grind too (Grover over the counter), but that concerns soundness (Q2 §8), not
  ZK.

---

## 9. Numbers

Assume λ = 128, `Q_P = Q_V = 2³⁰`, `n_mult = 312`, every per-oracle count q, and `t = q` in the AES
heuristic. The Lean theorems are in `VoleMole/ZK/QROM.lean`.

| term | formula | 2³⁰ | 2⁵⁰ | 2⁶⁴ | Lean |
|---|---|---|---|---|---|
| ε_rho | `q²·2⁻⁹⁶` | 2⁻³⁶ | 2⁴ | 2³² | `rho_at_2_30`, `rho_at_2_50` |
| ε_RP | `2³⁰·√(q·2⁻¹²⁸)` | 2⁻¹⁹ | 2⁻⁹ | 2⁻² | `rp_at_2_30/50/64` |
| ε_lab | `(q₅*)²·2⁻¹²⁵` | 2⁻⁴⁶·⁴ | 2⁻²⁵ | 2³ | `lab_at_2_50/64` |
| 2ε_hide (union) | `2·2⁸·2³⁰·q²·2⁻¹²⁸` | 2⁻²⁹ | ≥ 1 | ≥ 1 | `hide_union_at_2_30/50` |
| 2ε_hide (multi-user) | `2q²·2⁻¹²⁸` | 2⁻⁶⁷ | 2⁻²⁷ | 2 | `hide_mu_at_2_30/50` |
| 2ε_iv | | ≈ 2⁻¹²⁷ | ≈ 2⁻¹²⁷ | ≈ 2⁻¹²⁷ | `iv_triple` |
| ε_neg | | < 2⁻⁹⁰ | < 2⁻⁹⁰ | < 2⁻⁹⁰ | `h5_pre_sq_at_2_64` |
| ε_dly (dly only) | `≈ 2³⁰·q·2⁻⁶⁴` | 2⁻⁴ | ≥ 1 | ≥ 1 | |

ε_neg's largest part is the H₂³-slice term at the worst-case grinding count
`q₂₃* ≈ 2⁶⁴ + 2⁶²`, which is about `2³⁰·2⁻¹⁹²`.

**Totals.** In `Exp^{nd}`/`Exp^{dly-G}`, ε_ZK^Q ≈ **2⁻¹⁹** at q = 2³⁰, dominated by ε_RP. The bound
is vacuous at q = 2⁵⁰ unless `rho` is 256 bits *and* a multi-user AES assumption is made; then it
is **≈ 2⁻⁹**, still dominated by ε_RP. It is vacuous at q = 2⁶⁴ in every variant. For λ = 128
that last point is inherent: AES-128 key search, and up to `n_mult²·32` also the Θ search.

---

## 10. Per-relation conclusions

- **PomFRIT redeem (blindness against the Issuer, proof-system level).** The Issuer sees
  `t = h ⊕ r` between the phases, with `h = G(pk, chal1, ũ, d_pre, msg)`
  (`src/pomfrit/pomfrit.cpp:96-111, 167-176`). This is the `Exp^{dly-G}` setting, even if the
  Issuer knows `r`. With the fix, Theorem Q applies with no condition on `r`. lean/docs/zk.md's linking
  attack (§4) is gone, also against quantum Issuers, and proof-level unlinkability costs
  `ε_ZK^Q ≈ 2⁻¹⁹` at 2³⁰ queries.
  - **`rho` search.** An Issuer that suspects session `j` knows `r_j`, and `mu = H₂⁴(DST)` is
    constant. It can Grover-search `rho` against `iv_pre(σ)`, single target per pair `(σ, j)`, at
    about 2⁶⁴ quantum cost. This is the 128-bit (category-1) level. Different sessions have
    different prefixes, so there is no multi-target gain.
  - PomFRIT's own blindness proof (hash_to_target, refresher) is outside this note.
- **Moussaka issue/redeem, Ratatouille issue/spend.** These are non-delayed
  (`WITNESS_PREFIX_BYTES = WITNESS_BYTES`; `src/moussaka/issue.hpp:160`, `redeem.hpp:178`,
  `src/ratatouille/issue.hpp:147`, `spend.hpp:317`), so `Exp^{nd}` applies.
  - ZK is now statistical in `w`, up to AES. It no longer depends on Keccak one-wayness, and
    Moussaka redeem's "margin exactly 2¹²⁸" caveat from lean/docs/zk.md disappears.
  - In the protocols the adversary does not know `w`, which contains the secret opening `r`. So
    it cannot evaluate `H₃(w ‖ mu ‖ ·)`, and the `rho` attack of §7.4 does not apply to them. It
    applies only in the NIZK game.

---

## 11. Extras

**The punctured simulator `Sim°` (L8 §3.3).** Up to Q9's negligible undo steps, `Sim°`'s
distribution is hybrid Q7. So `Sim°` is quantum-ZK with **one** `ε_hide` instead of two:
`ε^Q(Sim°) = ε_rho + ε_RP + ε_hide + ε_lab + 2ε_iv + ε_neg`. L8 prefers `Sim°` because it has
(S3) with `K_s = ∅`. That carries over: `Sim°` uses no AES key that `D` could hit. It still needs
the slice programming of Q2c, which is efficient.

**QROM simulation-extractability (not proved).** Two points of interaction.
1. Lemma C bounds the joint adversary-and-oracle state (GHHM work with the purified oracle). So
   the steps Q2a–Q2c and Q6a compose with Q2's compressed-oracle extractor (Lemma T). The
   database then contains simulator-programmed H₂³ slices with fresh 448-bit prefixes, which is
   L8 (S1)/(S2).
2. Lemma R is stated with the oracle functions as classical randomness. It bounds only
   `D`'s reduced state, not the database the extractor reads. An SE proof would need Lemma R for
   a purified (compressed) H₅, H₃ and cipher. The proof idea carries over, since it uses only
   unitarity and block diagonality, but the "programmed values" become database-dependent. I have
   not checked this.

Q2 gap 3 (SE in the QROM) therefore remains open. ZK no longer blocks it, but Lemma R needs the
purified form.

---

## 12. Gaps and confidence

| step | status | confidence |
|---|---|---|
| (F1)–(F5) against the branch | read patch 0005 and the diff | high |
| Lemma C (GHHM, set version) | one-projector change to GHHM Thm 6 (proof text checked) | high |
| Lemma R | new; proof in §3.2; scalar core in Lean | medium-high |
| Q1 (H₃, Lemma R with slices) | proof given | high, given Lemma R |
| Q2a–Q2c, Q6a (statistical reprogramming) | proofs given | high |
| Q2b in `Exp^{dly}` (computational, √) | reduction sketched (spec G3 pattern) | medium; the bound is weak |
| Q4/Q8 (ε_hide) | imported from spec Lemma 10.51; classical-access PRP suffices | high |
| Q5, Q6b (bijections) | Lean (lean/docs/zk.md §10) | high |
| Q6c (ε_lab) | Lemma R, with the iv cap | medium-high |
| grinding (exact law, no abort) | Lean first-hit lemmas plus the slice formulation | high |
| numbers | Lean; AES numbers rest on the Grover heuristic | high (arithmetic) |

**Gaps.**
1. **ε_RP** (`Q_P·√(q/2¹²⁸)`) dominates and is probably an artifact (Remark 6.1). No proof
   removes it yet.
2. **`Exp^{dly}`** costs `Σ_j √(Adv^{tree})`, which is vacuous at `Q_P = 2³⁰`. lean/docs/zk.md's classical
   H2 also silently needs the computational unpredictability of `z` here. PomFRIT is not affected,
   since it is `Exp^{dly-G}`.
3. **ε_hide** uses the spec's union over `≈ 205·Q_P` PRG instances. The q = 2⁵⁰ column needs a
   multi-user AES assumption.
4. **Lemma R** is new and unreviewed. Its operator steps are not in Lean.
5. **SE** is not covered (§11).
6. Remark 3.5 (QICM) is only sketched.

**Recommendations.**
- R1: make `ProveSeed` 32 bytes (`voleith.hpp:91`). This removes the multi-target `rho` attack.
- R2 (optional): add a fresh salt to the chal1 input, and in delayed mode to the chal2 input. This
  makes ε_RP and ε_dly negligible.
- R3: raise the spec's G8→G9 gap (lean/docs/zk.md §8.3) together with its QROM counterpart. The QROM proof
  (Thm 10.53) reuses those hops "identical to Theorem 10.42".

---

## 13. Lean (`lean/VoleMole/ZK/QROM.lean`)

`#print axioms` lists only `propext`, `Classical.choice` and `Quot.sound`. There is no `sorry` and
no `axiom`. Check with `lake env lean VoleMole/ZK/QROM.lean`.

| statement | Lean |
|---|---|
| `Γ_n ≤ nβ` (escaped part, Lemma R) | `gamma_le` |
| `e_n ≤ na + β²n(n−1)/2` | `err_le` |
| `e_q + Γ_q²/2 ≤ 4q²b` for `a = 2b`, `β = 2√b` | `lemmaR_td` |
| monotonicity of `√x + x/2` (Lemma C) | `ghhm_set_mono` |
| every number in §0/§9 | `lab_*`, `rho_*`, `rp_*`, `hide_*`, `h5_pre_sq_at_2_64`, `iv_triple`, `lab_attack_at_2_64` |

lean/docs/zk.md's Lean results are reused unchanged: the bijections (`correctionsEquiv`, `cmultEquiv`,
`kosQsEquiv`, `qsResponse_bijective`, `fiberCard_shear`), the labels (`label_q_eq`, `sibling_eq`)
and the grinding law.

---

## References

- [GHHM21] A. B. Grilo, K. Hövelmanns, A. Hülsing, C. Majenz. *Tight adaptive reprogramming in
  the QROM*. ASIACRYPT 2021; arXiv:2010.15103v2. Used: Theorem 1 (adaptive reprogramming, eq. (2)),
  Theorem 6 and its proof (eqs. (8)–(12)), Lemma 1 (= AMRS20 Lemma 2), Lemma 2 (multi-instance
  hybrid). Local copy in the session scratchpad, used as reference data only.
- [AMRS20] G. Alagic, C. Majenz, A. Russell, F. Song. *Quantum-access-secure message
  authentication via blind-unforgeability*. EUROCRYPT 2020. Lemma 2, via GHHM Lemma 1.
- [AHU19] A. Ambainis, M. Hamburg, D. Unruh. *Quantum security proofs using semi-classical
  oracles*. CRYPTO 2019. Discussed, not used (§3.2).
- [Zha12a] M. Zhandry. *Secure identity-based encryption in the quantum random oracle model*.
  CRYPTO 2012. 2q-wise independent simulation of QROs (§3.3). Theorem number from memory, not
  re-checked.
- [Zha12b] M. Zhandry. *How to construct quantum random functions*. FOCS 2012. Quantum GGM; shown
  not to be needed (§3.4).
- [Zha19] M. Zhandry. *How to record quantum queries*. CRYPTO 2019. Compressed oracle.
- FAEST v3.0 specification: Lemma 10.1, Thm 10.3 (ABKM22 special case), Lemmas 10.16–10.17,
  Cor. 10.18, Lemma 10.24, §10.11.3, Def. 10.47, Lemmas 10.51–10.52, Thm 10.53, Cor. 10.54.
  Local copy (`scratchpad/spec/`), reference only.
- Repo: `lean/docs/zk.md`; `lean/docs/extraction/Q1-quantum-ideal-cipher.md`, `Q2-qrom-fiat-shamir.md`,
  `L8-simulation-extractability.md`; `lean/VoleMole/ZK/{Masking,Grinding,Labels}.lean`.
