import VoleMole.ZK.Main
import VoleMole.Arith.Moussaka
import VoleMole.Arith.Ratatouille
import VoleMole.Arith.PomFRIT
import VoleMole.Spec.Moussaka
import VoleMole.Spec.PomFRIT

/-!
# Zero knowledge on `main`, per relation: what `w[0..16)` is (`lean/docs/zk.md` §4, §7.1)

On `main` the label offset is `Θ = d[0..λ) + w[0..λ)` (`Main.lean`), so ZK needs (PU): the first
λ = 128 witness bits must be unpredictable to the verifier. This file identifies those bits in each
relation, from the witness layouts already modelled in `Arith/` and `Spec/`, and instantiates the
bound of `Main.lean`.

**Labels and witness bytes.** `Label = F₂^128`. A witness is a bit vector `w : ℕ → Bool` (bit `i`
is bit `i % 8` of witness byte `i / 8`, `Arith.Keccak.witByte`), embedded in `F₂^ℓ` by `witBits`;
`prefixHom` projects to the first 128 rows, giving `labelPrefix w` (`prefixHom_witBits`).
`labelPrefix_eq` writes it as `labelOfBytes` of the witness bytes `[0, 16)`, and `bytesOfLabel`
inverts this on 16 bytes (`bytesOfLabel_labelOfBytes`, `labelOfBytes_bytesOfLabel`).

**Moussaka and Ratatouille: `w[0..16) = r`, the commitment opening.**
* `moussakaIssue_labelPrefix`, `moussakaRedeem_labelPrefix`, `ratatouilleIssue_labelPrefix`,
  `ratatouilleSpend_labelPrefix`: the label prefix is `labelOfBytes` of the opening that the
  constraint systems read (`Arith.Moussaka.issueR`, `redeemR`, `Arith.Ratatouille.bytesAt w 0`), the
  `r` of `t = Com(nf, ctx_iss, ctx_red, r)` resp. `c = Com(nf, ctx, t, r)` in `issue_sound`,
  `redeem_sound`, `Ratatouille.issue_sound`, `spend_sound` (C++: `moussaka/issue.hpp:58, 95`,
  `moussaka/redeem.hpp:74-75, 114`, `ratatouille/issue.hpp:55, 89`, `ratatouille/spend.hpp:92,
  240`). `encodeIssueWitness_take`, `encodeRedeemWitness_take`: the honest encodings of
  `Spec/Moussaka.lean` start with `r`.
* `MainLayout.prU_exists_hit_le_opening`: for any layout whose label prefixes are the opening
  `opening s`, the bad event is at most `q·ε_PU`, where (PU) is stated for the explicit predictors
  as predicting the 16 opening bytes from the auxiliary information (for a colluding Anchor or the
  Issuer, the commitment: this is one-wayness of Keccak-p[800] in `r`, `security/moussaka.md`
  §3.2, an assumption, not proved).
* `moussaka_main_zk`, `ratatouille_main_zk`: the issuance proof and the redemption (spend) proof
  of the same token jointly (`MainLayout.prod`; both have `r` first), with the responses.
* `moussakaRedeem_main_zk_uniform`: towards a verifier whose information does not depend on `r`
  (the Moderator, not colluding with the issuing Anchor), (PU) holds for every adversary with
  `ε_PU = 2^{-128}` exactly: the bad event is at most `q·2^{-128}`, with no assumption.

**PomFRIT: (PU) fails.** `w[0..45) = r` (`Arith.PomFRIT.witOffR = 0`) and the Issuer receives
`t = h ⊕ r`, with `h` recomputable from the signature.
* `issuerGuess_eq`: in every honest run, the Issuer's guess `t ⊕ h(σ)` is `r`, deterministically.
* `pomfrit_issuer_hits`: so the Issuer's query `π d − labelOfBytes(guess)` is `Θ` on every tape:
  its predictor succeeds with probability 1 (`pomfrit_issuer_prU_hit`), and the attack test of
  `lean/docs/zk.md` Proposition 4.1 accepts every real proof (`pomfrit_attack_test`), while a
  uniform `c_mult` passes for only a `#S/|B|` fraction (`card_attack_test_ideal`).
-/

open Finset VoleMole.Prob ENNReal

namespace VoleMole.ZK

open VoleMole.Arith.Keccak (witByte)

/-! ## Labels and witness bits -/

/-- The label space on `main`: the first λ = 128 witness rows, over `F₂`. -/
abbrev Label := Fin 128 → ZMod 2

theorem label_add_self (x : Label) : x + x = 0 :=
  funext fun j => CharTwo.add_self_eq_zero (x j)

/-- A bit as an element of `F₂`. -/
def bitZ (b : Bool) : ZMod 2 := if b then 1 else 0

theorem bitZ_eq_one_iff (b : Bool) : bitZ b = 1 ↔ b = true := by
  cases b <;> simp [bitZ]

/-- The witness bit vector as an element of `F₂^ℓ` (the prover's `w` on the `ℓ` witness rows). -/
def witBits (ℓ : ℕ) (w : ℕ → Bool) : Fin ℓ → ZMod 2 := fun i => bitZ (w i)

/-- The projection `π` to the first 128 rows: the label rows on `main`. -/
def prefixHom {ℓ : ℕ} (h : 128 ≤ ℓ) : (Fin ℓ → ZMod 2) →+ Label where
  toFun v j := v (Fin.castLE h j)
  map_zero' := rfl
  map_add' _ _ := rfl

/-- `w[0..λ)`, the label prefix of a witness. -/
def labelPrefix (w : ℕ → Bool) : Label := fun j => bitZ (w j)

theorem prefixHom_witBits {ℓ : ℕ} (h : 128 ≤ ℓ) (w : ℕ → Bool) :
    prefixHom h (witBits ℓ w) = labelPrefix w := rfl

/-- The 128 bits of 16 bytes, least significant bit first. -/
def labelOfBytes (b : ℕ → UInt8) : Label := fun j => bitZ ((b (j / 8)).toBitVec.getLsbD (j % 8))

/-- 16 bytes from 128 bits (the inverse of `labelOfBytes` on bytes `[0, 16)`). -/
def bytesOfLabel (x : Label) : ℕ → UInt8 :=
  witByte fun j => if h : j < 128 then decide (x ⟨j, h⟩ = 1) else false

/-- **The label prefix is the first 16 witness bytes.** -/
theorem labelPrefix_eq (w : ℕ → Bool) (b : ℕ → UInt8) (hb : ∀ i < 16, witByte w i = b i) :
    labelPrefix w = labelOfBytes b := by
  funext j
  have hj := j.isLt
  simp only [labelPrefix, labelOfBytes]
  rw [← hb _ (by omega), Arith.Ratatouille.witByte_bit _ _ _ (Nat.mod_lt _ (by norm_num)),
    Nat.div_add_mod]

theorem labelOfBytes_congr {b b' : ℕ → UInt8} (h : ∀ i < 16, b i = b' i) :
    labelOfBytes b = labelOfBytes b' := by
  funext j
  simp only [labelOfBytes, h _ (by omega : j.1 / 8 < 16)]

theorem bytesOfLabel_labelOfBytes (b : ℕ → UInt8) (i : ℕ) (hi : i < 16) :
    bytesOfLabel (labelOfBytes b) i = b i := by
  refine Arith.Ratatouille.uint8_ext fun j hj => ?_
  rw [bytesOfLabel, Arith.Ratatouille.witByte_bit _ _ _ hj]
  simp only [show 8 * i + j < 128 by omega, ↓reduceDIte, labelOfBytes, bitZ_eq_one_iff,
    show (8 * i + j) / 8 = i by omega, show (8 * i + j) % 8 = j by omega, Bool.decide_eq_true]

theorem labelOfBytes_bytesOfLabel (x : Label) : labelOfBytes (bytesOfLabel x) = x := by
  funext j
  have hj := j.isLt
  simp only [labelOfBytes, bytesOfLabel]
  rw [Arith.Ratatouille.witByte_bit _ _ _ (Nat.mod_lt _ (by norm_num)), Nat.div_add_mod]
  simp only [hj, ↓reduceDIte]
  have : ∀ z : ZMod 2, bitZ (decide (z = 1)) = z := by decide
  exact this _

/-! ## Moussaka and Ratatouille: the label prefix is the commitment opening -/

/-- Moussaka issuance: `w[0..16) = r` (`issue.hpp:58, 95`; `Arith.Moussaka.issueR`). -/
theorem moussakaIssue_labelPrefix (w : ℕ → Bool) :
    labelPrefix w = labelOfBytes (Arith.Moussaka.issueR w) :=
  labelPrefix_eq w _ fun i _ => by simp [Arith.Moussaka.issueR, Arith.Moussaka.issueOffR]

/-- Moussaka redemption: `w[0..16) = r` (`redeem.hpp:74-75, 114`; `Arith.Moussaka.redeemR`). -/
theorem moussakaRedeem_labelPrefix (w : ℕ → Bool) :
    labelPrefix w = labelOfBytes (Arith.Moussaka.redeemR w) :=
  labelPrefix_eq w _ fun i _ => by simp [Arith.Moussaka.redeemR, Arith.Moussaka.redeemOffR]

/-- Ratatouille issuance: `w[0..16) = r` (`issue.hpp:55, 89`; `issueComMap` reads `r` at 0). -/
theorem ratatouilleIssue_labelPrefix (w : ℕ → Bool) :
    labelPrefix w = labelOfBytes (Arith.Ratatouille.bytesAt w 0) :=
  labelPrefix_eq w _ fun i _ => by simp [Arith.Ratatouille.bytesAt]

/-- Ratatouille spend: `w[0..16) = r`, the opening of the spent state (`spend.hpp:92, 240`;
`spendComMap` reads `r` at 0). The same decoding as issuance. -/
theorem ratatouilleSpend_labelPrefix (w : ℕ → Bool) :
    labelPrefix w = labelOfBytes (Arith.Ratatouille.bytesAt w 0) :=
  ratatouilleIssue_labelPrefix w

/-- The honest Moussaka issuance witness `r ‖ ctx_red ‖ nf ‖ s5 ‖ s9` starts with `r`. -/
theorem encodeIssueWitness_take (nf ctxIss ctxRed r : Spec.Bytes) (hr : r.length = 16) :
    (Spec.Moussaka.encodeIssueWitness nf ctxIss ctxRed r).take 16 = r := by
  simp [Spec.Moussaka.encodeIssueWitness, List.append_assoc, ← hr]

/-- The honest Moussaka redemption witness `r ‖ s ‖ s5 ‖ s9 ‖ b` starts with `r`. -/
theorem encodeRedeemWitness_take (nf ctxIss ctxRed r s : Spec.Bytes) (i : ℕ) (hr : r.length = 16) :
    (Spec.Moussaka.encodeRedeemWitness nf ctxIss ctxRed r s i).take 16 = r := by
  simp [Spec.Moussaka.encodeRedeemWitness, List.append_assoc, ← hr]

/-- A bit vector that encodes a byte string starting with `r` has label prefix `r`. -/
theorem labelPrefix_of_encodes (w : ℕ → Bool) (b r : Spec.Bytes)
    (hb : ∀ i < 16, witByte w i = b.getD i 0) (hr : b.take 16 = r) :
    labelPrefix w = labelOfBytes fun i => r.getD i 0 := by
  rw [labelPrefix_eq w _ hb]
  refine labelOfBytes_congr fun i hi => ?_
  rw [← hr, List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_take_of_lt hi]

/-! ## The bound for layouts whose label prefix is an opening -/

section Opening

variable {S R V J X Ω : Type*} [Fintype S] [Nonempty S] [Fintype R] [Nonempty R] [Fintype Ω]
  [Nonempty Ω]

omit [Fintype S] [Nonempty S] [Fintype R] [Nonempty R] [Fintype Ω] [Nonempty Ω] in
/-- A predictor of the label prefix is a predictor of the opening. -/
theorem MainLayout.opening_of_predicts (L : MainLayout S R V J Label)
    (opening : S → ℕ → UInt8) (hpre : ∀ j s, L.pre j s = labelOfBytes (opening s)) (g : J × Label)
    (s : S) (h : L.Predicts g s) : ∀ i < 16, bytesOfLabel g.2 i = opening s i := fun i hi => by
  rw [MainLayout.Predicts, hpre] at h
  rw [h, bytesOfLabel_labelOfBytes _ _ hi]

/-- **(PU) as predicting the opening.** If every label prefix is `labelOfBytes (opening s)`, and
each of the `q` explicit predictors outputs the 16 opening bytes with probability at most `ε_PU`,
the sibling-label bad event is at most `q·ε_PU`. -/
theorem MainLayout.prU_exists_hit_le_opening (L : MainLayout S R V J Label)
    (opening : S → ℕ → UInt8) (hpre : ∀ j s, L.pre j s = labelOfBytes (opening s)) (aux : S → X)
    {q : ℕ} (Q : Fin q → X → V → Ω → J × Label) {ε : ℝ≥0∞}
    (hPU : ∀ k, prU (S × R × Ω) (fun p => ∀ i < 16,
      bytesOfLabel (L.predictor (Q k) (aux p.1) p.2.1 p.2.2).2 i = opening p.1 i) ≤ ε) :
    prU (S × R × Ω) (fun p => ∃ k, L.Hit (Q k (aux p.1) (L.view p.1 p.2.1) p.2.2) p.2.1) ≤
      q * ε :=
  L.prU_exists_hit_le aux Q fun k =>
    (prU_mono fun (p : S × R × Ω) => L.opening_of_predicts opening hpre _ p.1).trans (hPU k)

end Opening

/-! ## Moussaka and Ratatouille: issuance and redemption of one token, jointly -/

section Instances

/-- The witness rows `F₂^ℓ`. -/
abbrev WitRows (ℓ : ℕ) := Fin ℓ → ZMod 2

/-- The type of `mainView` on `ℓ` witness rows. -/
abbrev MainViewT (ℓ τ : ℕ) (Lab : Type*) := WitRows ℓ × (Fin τ → WitRows ℓ) × Lab

/-- The tapes of a Moussaka token's two proofs. -/
abbrev MoussakaTape (τ : ℕ) :=
  MainTape (WitRows Arith.Moussaka.issueWitnessBits) τ ×
    MainTape (WitRows Arith.Moussaka.redeemWitnessBits) τ

/-- The views of a Moussaka token's two proofs. -/
abbrev MoussakaView (τ : ℕ) (Lab₁ Lab₂ : Type*) :=
  MainViewT Arith.Moussaka.issueWitnessBits τ Lab₁ ×
    MainViewT Arith.Moussaka.redeemWitnessBits τ Lab₂

/-- The tapes of a Ratatouille state's issuance and spend proofs. -/
abbrev RatatouilleTape (τ : ℕ) :=
  MainTape (WitRows (8 * Arith.Ratatouille.issueWitnessBytes)) τ ×
    MainTape (WitRows (8 * Arith.Ratatouille.spendWitnessBytes)) τ

/-- The views of a Ratatouille state's issuance and spend proofs. -/
abbrev RatatouilleView (τ : ℕ) (Lab₁ Lab₂ : Type*) :=
  MainViewT (8 * Arith.Ratatouille.issueWitnessBytes) τ Lab₁ ×
    MainViewT (8 * Arith.Ratatouille.spendWitnessBytes) τ Lab₂

variable {S Lab₁ Lab₂ X Ω M M' : Type*} {τ : ℕ} [Fintype S] [Nonempty S] [Fintype Ω] [Nonempty Ω]
  [Fintype M] [Nonempty M] [Fintype M'] [Nonempty M']

/-- The two proofs of one Moussaka token on `main`: issuance (`2048` witness bits) and redemption
(`8·343`), each with its own tape and forced labels, sharing the opening. -/
def moussakaLayout (witIss witRed : S → ℕ → Bool)
    (forcedIss : (Fin Arith.Moussaka.issueWitnessBits → ZMod 2) →
      (Fin τ → Fin Arith.Moussaka.issueWitnessBits → ZMod 2) → Lab₁)
    (forcedRed : (Fin Arith.Moussaka.redeemWitnessBits → ZMod 2) →
      (Fin τ → Fin Arith.Moussaka.redeemWitnessBits → ZMod 2) → Lab₂) :=
  (mainLayout (prefixHom (by decide)) (fun s => witBits _ (witIss s)) forcedIss).prod
    (mainLayout (prefixHom (by decide)) (fun s => witBits _ (witRed s)) forcedRed)

/-- **Moussaka on `main`: ZK under (PU).** Let the issuance and redemption witnesses of a token
both decode (`Arith.Moussaka.issueR`, `redeemR`) to the opening `opening s`. For `q` queries that
see auxiliary information `aux s` (for a colluding Anchor, `t = Com(nf, ctx_iss, ctx_red, r)`), both
views, both proofs' responses (any bijection `φ` of uniform masks) and independent coins, the
probability that some query hits a sibling label of either proof is at most `q·ε_PU`, provided each
derived predictor inverts the opening with probability at most `ε_PU`. -/
theorem moussaka_main_zk [DecidableEq Lab₁] [DecidableEq Lab₂] (witIss witRed : S → ℕ → Bool)
    (opening : S → ℕ → UInt8)
    (hIss : ∀ s, ∀ i < 16, Arith.Moussaka.issueR (witIss s) i = opening s i)
    (hRed : ∀ s, ∀ i < 16, Arith.Moussaka.redeemR (witRed s) i = opening s i)
    (forcedIss : (Fin Arith.Moussaka.issueWitnessBits → ZMod 2) →
      (Fin τ → Fin Arith.Moussaka.issueWitnessBits → ZMod 2) → Lab₁)
    (forcedRed : (Fin Arith.Moussaka.redeemWitnessBits → ZMod 2) →
      (Fin τ → Fin Arith.Moussaka.redeemWitnessBits → ZMod 2) → Lab₂)
    (aux : S → X) (φ : S × MoussakaTape τ → M ≃ M') {q : ℕ}
    (Q : Fin q → X → MoussakaView τ Lab₁ Lab₂ × M' → Ω → (Unit ⊕ Unit) × Label) {ε : ℝ≥0∞}
    (hPU : ∀ k, prU (S × MoussakaTape τ × (M' × Ω)) (fun p => ∀ i < 16, bytesOfLabel
      ((moussakaLayout witIss witRed forcedIss forcedRed).predictor
        (fun x v (mω : M' × Ω) => Q k x (v, mω.1) mω.2) (aux p.1) p.2.1 p.2.2).2 i =
          opening p.1 i) ≤ ε) :
    prU ((S × MoussakaTape τ) × (M × Ω)) (fun p => ∃ k, (moussakaLayout witIss witRed forcedIss forcedRed).Hit
      (Q k (aux p.1.1) ((moussakaLayout witIss witRed forcedIss forcedRed).view p.1.1 p.1.2,
        φ p.1 p.2.1) p.2.2) p.1.2) ≤ q * ε := by
  have hpre : ∀ j s, (moussakaLayout witIss witRed forcedIss forcedRed).pre j s =
      labelOfBytes (opening s) := by
    rintro (_ | _) s
    · exact (moussakaIssue_labelPrefix _).trans (labelOfBytes_congr (hIss s))
    · exact (moussakaRedeem_labelPrefix _).trans (labelOfBytes_congr (hRed s))
  exact (moussakaLayout witIss witRed forcedIss forcedRed).prU_exists_hit_responses_le aux φ Q
    fun k => (prU_mono fun (p : S × MoussakaTape τ × (M' × Ω)) =>
      (moussakaLayout witIss witRed forcedIss forcedRed).opening_of_predicts opening hpre _
        p.1).trans (hPU k)

/-- The two proofs of one Ratatouille state on `main`: issuance (`8·240` witness bits) and its
first spend (`8·847`), sharing the opening. -/
def ratatouilleLayout (witIss witSpend : S → ℕ → Bool)
    (forcedIss : (Fin (8 * Arith.Ratatouille.issueWitnessBytes) → ZMod 2) →
      (Fin τ → Fin (8 * Arith.Ratatouille.issueWitnessBytes) → ZMod 2) → Lab₁)
    (forcedSpend : (Fin (8 * Arith.Ratatouille.spendWitnessBytes) → ZMod 2) →
      (Fin τ → Fin (8 * Arith.Ratatouille.spendWitnessBytes) → ZMod 2) → Lab₂) :=
  (mainLayout (prefixHom (by decide)) (fun s => witBits _ (witIss s)) forcedIss).prod
    (mainLayout (prefixHom (by decide)) (fun s => witBits _ (witSpend s)) forcedSpend)

/-- **Ratatouille on `main`: ZK under (PU).** As `moussaka_main_zk`, for an issuance and a spend
witness that both decode (`Arith.Ratatouille.bytesAt w 0`) to the opening (for the Issuer, `aux`
contains `c = Com(nf, ctx, t, r)`). A later spend's opening `r'` sits at offset 96 of the previous
spend's witness, but only that later spend has it as its label prefix. -/
theorem ratatouille_main_zk [DecidableEq Lab₁] [DecidableEq Lab₂] (witIss witSpend : S → ℕ → Bool)
    (opening : S → ℕ → UInt8)
    (hIss : ∀ s, ∀ i < 16, Arith.Ratatouille.bytesAt (witIss s) 0 i = opening s i)
    (hSpend : ∀ s, ∀ i < 16, Arith.Ratatouille.bytesAt (witSpend s) 0 i = opening s i)
    (forcedIss : (Fin (8 * Arith.Ratatouille.issueWitnessBytes) → ZMod 2) →
      (Fin τ → Fin (8 * Arith.Ratatouille.issueWitnessBytes) → ZMod 2) → Lab₁)
    (forcedSpend : (Fin (8 * Arith.Ratatouille.spendWitnessBytes) → ZMod 2) →
      (Fin τ → Fin (8 * Arith.Ratatouille.spendWitnessBytes) → ZMod 2) → Lab₂)
    (aux : S → X) (φ : S × RatatouilleTape τ → M ≃ M') {q : ℕ}
    (Q : Fin q → X → RatatouilleView τ Lab₁ Lab₂ × M' → Ω → (Unit ⊕ Unit) × Label) {ε : ℝ≥0∞}
    (hPU : ∀ k, prU (S × RatatouilleTape τ × (M' × Ω)) (fun p => ∀ i < 16, bytesOfLabel
      ((ratatouilleLayout witIss witSpend forcedIss forcedSpend).predictor
        (fun x v (mω : M' × Ω) => Q k x (v, mω.1) mω.2) (aux p.1) p.2.1 p.2.2).2 i =
          opening p.1 i) ≤ ε) :
    prU ((S × RatatouilleTape τ) × (M × Ω)) (fun p => ∃ k,
      (ratatouilleLayout witIss witSpend forcedIss forcedSpend).Hit
        (Q k (aux p.1.1) ((ratatouilleLayout witIss witSpend forcedIss forcedSpend).view p.1.1 p.1.2,
          φ p.1 p.2.1) p.2.2) p.1.2) ≤ q * ε := by
  have hpre : ∀ j s, (ratatouilleLayout witIss witSpend forcedIss forcedSpend).pre j s =
      labelOfBytes (opening s) := by
    rintro (_ | _) s
    · exact (ratatouilleIssue_labelPrefix _).trans (labelOfBytes_congr (hIss s))
    · exact (ratatouilleSpend_labelPrefix _).trans (labelOfBytes_congr (hSpend s))
  exact (ratatouilleLayout witIss witSpend forcedIss forcedSpend).prU_exists_hit_responses_le aux φ Q
    fun k => (prU_mono fun (p : S × RatatouilleTape τ × (M' × Ω)) =>
      (ratatouilleLayout witIss witSpend forcedIss forcedSpend).opening_of_predicts opening hpre _
        p.1).trans (hPU k)

/-- **Moussaka redemption towards a verifier that has no information on `r`: `q·2^{-128}`.** The
opening is uniform (`S = Label`, the 128 bits of `r`); the redemption witness decodes to it; the
adversary's auxiliary information is constant (the Moderator sees `nf`, the contexts and the
Anchor Set, which do not depend on `r`, and not `t`). Then every adversary, unbounded, hits a
sibling label with probability at most `q/2^{128}`: (PU) holds with `ε_PU = 2^{-128}` exactly, the
same as the patched layout's per-query term. -/
theorem moussakaRedeem_main_zk_uniform [DecidableEq Lab₂] (witRed : Label → ℕ → Bool)
    (hRed : ∀ s, ∀ i < 16, Arith.Moussaka.redeemR (witRed s) i = bytesOfLabel s i)
    (forcedRed : (Fin Arith.Moussaka.redeemWitnessBits → ZMod 2) →
      (Fin τ → Fin Arith.Moussaka.redeemWitnessBits → ZMod 2) → Lab₂)
    (x₀ : X) {q : ℕ} (Q : Fin q → X → MainViewT Arith.Moussaka.redeemWitnessBits τ Lab₂ → Ω → Unit × Label) :
    prU (Label × MainTape (Fin Arith.Moussaka.redeemWitnessBits → ZMod 2) τ × Ω) (fun p => ∃ k,
      (mainLayout (prefixHom (by decide)) (fun s => witBits _ (witRed s)) forcedRed).Hit
        (Q k x₀ ((mainLayout (prefixHom (by decide)) (fun s => witBits _ (witRed s))
          forcedRed).view p.1 p.2.1) p.2.2) p.2.1) ≤ q * (2 ^ 128 : ℝ≥0∞)⁻¹ := by
  have hpre : ∀ (j : Unit) (s : Label),
      (mainLayout (τ := τ) (prefixHom (by decide)) (fun s => witBits _ (witRed s)) forcedRed).pre
        j s = s := fun _ s =>
    (moussakaRedeem_labelPrefix _).trans
      ((labelOfBytes_congr (hRed s)).trans (labelOfBytes_bytesOfLabel s))
  have hone : ∀ (j : Unit) (u : Label), #{s | (mainLayout (τ := τ) (prefixHom (by decide))
      (fun s => witBits _ (witRed s)) forcedRed).pre j s = u} * Fintype.card Label ≤
        Fintype.card Label := by
    intro j u
    have h1 : #{s | (mainLayout (τ := τ) (prefixHom (by decide))
        (fun s => witBits _ (witRed s)) forcedRed).pre j s = u} = 1 := by
      rw [Finset.card_eq_one]
      exact ⟨u, by ext s; simp only [mem_filter, mem_univ, true_and, mem_singleton, hpre]⟩
    -- (Closing `|Label| ≤ |Label|` by `rfl`/`simp` would unfold `Fintype.card Label`: out of memory.)
    rw [h1]
    exact Nat.le_of_eq (Nat.one_mul _)
  have hcard : Fintype.card Label = 2 ^ 128 := by
    rw [Fintype.card_fun, ZMod.card, Fintype.card_fin]
  have := (mainLayout (τ := τ) (prefixHom (by decide)) (fun s => witBits _ (witRed s))
    forcedRed).prU_exists_hit_le_of_uniform hone x₀ Q
  rwa [hcard, Nat.cast_pow, Nat.cast_ofNat] at this

end Instances

/-! ## PomFRIT: the Issuer predicts `w[0..16)` with certainty -/

section PomFRIT

open Spec Spec.PomFRIT

theorem xorBytes_comm (a b : Bytes) : xorBytes a b = xorBytes b a := by
  unfold xorBytes
  rw [List.zipWith_comm]
  congr 1
  funext x y
  exact UInt8.xor_comm y x

/-- The Issuer's guess of `r`: `t ⊕ h`, with `h = hash_to_target(pk, σ, chal1, msg)` recomputed
from the final signature exactly as `verify` does (`pomfrit.cpp:96-111, 234`). -/
def issuerGuess (V : Verifier) (pk : UOVKey) (msg t sig : Bytes) : Bytes :=
  match V.reconstruct (sigProof sig) (sigRefresherCom sig) with
  | some chal1 => xorBytes t (hashToTarget pk.digest chal1 sig msg)
  | none => []

/-- **The Issuer recovers `r`.** In every honest run (correct proof system and signer), the final
signature `σ` verifies and the Issuer's guess from its log entry `t` and `σ` is the Client's mask
`r`, the witness prefix: deterministically, for every seed. -/
theorem issuerGuess_eq {St : Type} (P : Prover St) (V : Verifier) (hPV : Correct P V)
    (pk : UOVKey) (sk : Signer) (hsk : sk.Correct pk) (msg seed : Bytes) (s : Bytes)
    (hs : issueResponse sk (issueRequest P pk msg seed).2 = .ok s) :
    ∃ sig, finalizeIssue P pk (issueRequest P pk msg seed).1 s = .ok (some sig) ∧
      verify V pk msg sig = true ∧
      issuerGuess V pk msg (issueRequest P pk msg seed).2 sig =
        (expandSeed pk.digest msg seed).2.2 := by
  obtain ⟨sig, hsig, hver⟩ := honest_run_verifies P V hPV pk sk hsk msg seed s hs
  refine ⟨sig, hsig, hver, ?_⟩
  obtain ⟨hl1, hl2, hl3⟩ := length_expandSeed pk.digest msg seed
  set e := expandSeed pk.digest msg seed with he
  obtain ⟨rho, refresher, r⟩ := e
  simp only at hl1 hl2 hl3 ⊢
  set g := P.voleGen r rho (commitRefresher refresher) with hg
  obtain ⟨proof, chal1, st⟩ := g
  have hpl : proof.length = proofBytes := by
    have := hPV.voleGen_length r rho (commitRefresher refresher); rw [← hg] at this; exact this
  have hrc := length_commitRefresher refresher
  obtain ⟨f1, f2, f3, f4, f5, -⟩ := sig_fields hpl hrc hl2
  set h := hashToTarget pk.digest chal1 (proof ++ commitRefresher refresher ++ refresher) msg with hh
  have hhl : h.length = uovM := length_hashToTarget _ _ _ _
  have hreq : issueRequest P pk msg seed =
      (⟨pk.digest, xorBytes h r, h, proof ++ commitRefresher refresher ++ refresher, st⟩,
        xorBytes h r) := by
    simp only [issueRequest, ← he, ← hg, hh]
  rw [hreq] at hsig hs ⊢
  have htl : (xorBytes h r).length = uovM := by simp [length_xorBytes, hhl, hl3]
  simp only [issueResponse, htl, ne_eq, not_true_eq_false, ↓reduceIte] at hs
  split at hs
  case h_2 => cases hs
  rename_i s' hd
  cases hs
  obtain ⟨hsl, hev⟩ := hsk _ _ htl hd
  simp only [finalizeIssue, hsl, ne_eq, not_true_eq_false, ↓reduceIte, hev, Except.ok.injEq,
    Option.some.injEq, f1, f2, f3] at hsig
  subst hsig
  set proof2 := P.proveCommit proof pk h s (refresher) st with hp2
  have hp2l : proof2.length = proofBytes := hPV.proveCommit_length _ _ _ _ _ _
  obtain ⟨g1, g2, -, g4, g5, -⟩ := sig_fields hp2l hrc hl2
  have hrec : V.reconstruct proof2 (commitRefresher refresher) = some chal1 := by
    have := hPV.reconstruct_eq r rho (commitRefresher refresher) pk h s refresher
    rw [← hg] at this; exact this
  have hH : hashToTarget pk.digest chal1 (proof2 ++ commitRefresher refresher ++ refresher) msg =
      h := by
    rw [hh, hashToTarget, hashToTarget, g4, g5, f4, f5, hp2, hPV.keeps_uTilde, hPV.keeps_prefix]
  simp only [issuerGuess, g1, g2, hrec, hH]
  rw [xorBytes_comm h r]
  exact xorBytes_xorBytes_right (by rw [hl3, hhl])

/-- **PomFRIT on `main`: the Issuer's sibling query hits on every tape.** Let the witness bit
vector put `r` at `WIT_OFF_R = 0` (`Arith.PomFRIT.witOffR`, `redeem.hpp:42`). In every honest run,
for every tape, the label offset is the public `π d` minus `labelOfBytes` of the Issuer's guess:
the Issuer computes `Θ`, both labels, and (with `attack_recovers`) the masks. -/
theorem pomfrit_issuer_hits {St : Type} (P : Prover St) (V : Verifier) (hPV : Correct P V)
    (pk : UOVKey) (sk : Signer) (hsk : sk.Correct pk) (msg seed : Bytes) (s : Bytes)
    (hs : issueResponse sk (issueRequest P pk msg seed).2 = .ok s) (w : ℕ → Bool)
    (hw : ∀ k < 16, witByte w (Arith.PomFRIT.witOffR + k) =
      (expandSeed pk.digest msg seed).2.2.getD k 0)
    {ℓ τ : ℕ} {Lab : Type*} (hℓ : 128 ≤ ℓ) (forcedOf : (Fin ℓ → ZMod 2) → (Fin τ → Fin ℓ → ZMod 2) → Lab) :
    ∃ sig, finalizeIssue P pk (issueRequest P pk msg seed).1 s = .ok (some sig) ∧
      verify V pk msg sig = true ∧
      labelPrefix w = labelOfBytes (fun i =>
        (issuerGuess V pk msg (issueRequest P pk msg seed).2 sig).getD i 0) ∧
      ∀ rt : MainTape (Fin ℓ → ZMod 2) τ, prefixHom hℓ rt.1 =
        prefixHom hℓ (mainView (witBits ℓ w) forcedOf rt).1 -
          labelOfBytes (fun i => (issuerGuess V pk msg (issueRequest P pk msg seed).2 sig).getD i 0) := by
  obtain ⟨sig, hsig, hver, hg⟩ := issuerGuess_eq P V hPV pk sk hsk msg seed s hs
  have hpre : labelPrefix w = labelOfBytes (fun i =>
      (issuerGuess V pk msg (issueRequest P pk msg seed).2 sig).getD i 0) := by
    rw [hg]
    exact labelPrefix_eq w _ fun i hi => by simpa [Arith.PomFRIT.witOffR] using hw i hi
  refine ⟨sig, hsig, hver, hpre, fun rt => ?_⟩
  rw [mainView_theta (prefixHom hℓ) (witBits ℓ w) forcedOf rt, prefixHom_witBits, hpre]

/-- The Issuer's query succeeds with probability 1 over the tape and the other coins: (PU) fails
(its `ε_PU` is 1). -/
theorem pomfrit_issuer_prU_hit {St : Type} (P : Prover St) (V : Verifier) (hPV : Correct P V)
    (pk : UOVKey) (sk : Signer) (hsk : sk.Correct pk) (msg seed : Bytes) (s : Bytes)
    (hs : issueResponse sk (issueRequest P pk msg seed).2 = .ok s) (w : ℕ → Bool)
    (hw : ∀ k < 16, witByte w (Arith.PomFRIT.witOffR + k) =
      (expandSeed pk.digest msg seed).2.2.getD k 0)
    {ℓ τ : ℕ} {Lab Ω : Type*} [Fintype Ω] [Nonempty Ω] (hℓ : 128 ≤ ℓ)
    (forcedOf : (Fin ℓ → ZMod 2) → (Fin τ → Fin ℓ → ZMod 2) → Lab) :
    ∃ sig, finalizeIssue P pk (issueRequest P pk msg seed).1 s = .ok (some sig) ∧
      prU (MainTape (Fin ℓ → ZMod 2) τ × Ω) (fun p => prefixHom hℓ p.1.1 =
        prefixHom hℓ (mainView (witBits ℓ w) forcedOf p.1).1 -
          labelOfBytes (fun i =>
            (issuerGuess V pk msg (issueRequest P pk msg seed).2 sig).getD i 0)) = 1 := by
  obtain ⟨sig, hsig, -, -, hhit⟩ := pomfrit_issuer_hits P V hPV pk sk hsk msg seed s hs w hw hℓ forcedOf
  refine ⟨sig, hsig, ?_⟩
  classical
  rw [prU_eq_card, Finset.filter_true_of_mem fun p _ => hhit p.1, card_univ]
  exact ENNReal.div_self (by exact_mod_cast Fintype.card_ne_zero) (ENNReal.natCast_ne_top _)

/-- **PomFRIT on `main`: blindness fails.** With the Issuer's guess, the test of
`lean/docs/zk.md` Proposition 4.1 accepts every real `c_mult` column `H(L⁰) + H(L⁰ + Θ) + F·ū`
(`F·ū ∈ S`, the image of the CRT matrix), for every hash function `H` and every tape, whereas a
uniform column passes for only `#S` of the `|B|` values (`card_attack_test_ideal`). -/
theorem pomfrit_attack_test {St : Type} (P : Prover St) (V : Verifier) (hPV : Correct P V)
    (pk : UOVKey) (sk : Signer) (hsk : sk.Correct pk) (msg seed : Bytes) (s : Bytes)
    (hs : issueResponse sk (issueRequest P pk msg seed).2 = .ok s) (w : ℕ → Bool)
    (hw : ∀ k < 16, witByte w (Arith.PomFRIT.witOffR + k) =
      (expandSeed pk.digest msg seed).2.2.getD k 0)
    {ℓ τ : ℕ} {Lab B : Type*} [AddCommGroup B] [DecidableEq B] (h2B : ∀ x : B, x + x = 0)
    (hℓ : 128 ≤ ℓ) (forcedOf : (Fin ℓ → ZMod 2) → (Fin τ → Fin ℓ → ZMod 2) → Lab)
    (H : Label → B) (Sset : Finset B) (L0 : Label) (f : B) (hf : f ∈ Sset) (γ : Bool) :
    ∃ sig, finalizeIssue P pk (issueRequest P pk msg seed).1 s = .ok (some sig) ∧
      ∀ rt : MainTape (Fin ℓ → ZMod 2) τ,
        attackTest H Sset (forced L0 (prefixHom hℓ rt.1) γ)
          (prefixHom hℓ (mainView (witBits ℓ w) forcedOf rt).1)
          (labelOfBytes fun i => (issuerGuess V pk msg (issueRequest P pk msg seed).2 sig).getD i 0)
          (H L0 + H (L0 + prefixHom hℓ rt.1) + f) := by
  obtain ⟨sig, hsig, -, hpre, -⟩ := pomfrit_issuer_hits P V hPV pk sk hsk msg seed s hs w hw hℓ forcedOf
  refine ⟨sig, hsig, fun rt => ?_⟩
  have hd : prefixHom hℓ (mainView (witBits ℓ w) forcedOf rt).1 =
      prefixHom hℓ rt.1 + labelPrefix w := by
    simp only [mainView, map_add, prefixHom_witBits]
  rw [hd, ← hpre]
  exact attack_test_real label_add_self h2B H Sset L0 _ _ f hf γ

end PomFRIT

end VoleMole.ZK
