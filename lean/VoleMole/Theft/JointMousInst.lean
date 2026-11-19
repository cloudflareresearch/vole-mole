import VoleMole.Theft.JointMousBad
import VoleMole.Theft.JointTheft

/-!
# The Moussaka redirect game as a game of Lean proofs with point charges, and its joint step

The Moussaka counterpart of `Theft/JointInst.lean` and `Theft/JointTheft.lean`. The redirect game
NM^{U,M} (`Theft/MoussakaMany.lean`, with the Lean provers on the tables, `leanPIX hbX`,
`leanPRX hbX`) is the joint game `gP proveJ (xJ A) (wJ A)` of one proof system:

* **`TRd.toI`, `Conf.toI`, `ZKExp.toI`**: the redemption system runs at the parameters `pR` on
  the tables of `pI` (`Sh pR` is `Sh pI` by definition); readers, confinements (`gate5_params`)
  and `ZKExp` (the charge by `chPt_params`) at `pR` are ones at `pI`;
* the instance of slot `j` is `(j, xN …)` (`xJ`): its index and its statement (none if the
  Client refused: the token did not finalize, or no key of the set verifies it);
* the output maps `φI`, `φR` are the spec's (`toL` of the proof, the empty proof on an error);
  the `iv` of an entry with a nonempty proof is `H₄(iv_pre ‖ μ₁ ‖ 4)` of that proof (`ivA`; an
  empty proof has none: `ivA_φI`, `ivA_φR`);
* **`PN_eq`, `SmP_eq`, `pgP_eq`**: the redirect game's real slot, simulated slot and
  programming are `gP`, `gS`, `gPg` of `proveJ`, `simJ`, `progJ`, the `osum` of the two Lean
  systems with "no proof";
* **`zkExpJ`**: `ZKExp` of the joint system at the point charge for active slots and `0` for the
  others (`lean_zkExpD`, `ZKExp.osum`);
* **`progRdJ_conf`, `proveRdJ_conf`**: the programmings and the real proofs are point readers
  confined to their `iv`s.

**`redirect_joint_le`**: with the event `BadN` with `ROM/`'s extractor read by `badGRd`
(`Theft/JointMousBad.lean`), `real_sim_leN_leanA` gives

    |Pr_real[BadN] − Pr_sim[BadN]| ≤ (Σ_i (εZK/(1 − βZK) + (1 + B)·Pr[deltaNM i]) + J) / (1 − N·B),

for every `J` that bounds the summed charges of the active slots in the simulated game, with the
game reader's budgets `a₃ = q h3`, `a₅ = N·312 + q h5 + 312`, `a_E = 2·(N·cells(pR) + q_E) + 9215`
and the honest readers' `(624, 4607)`.
-/

open Finset

set_option synthInstance.maxSize 1024

namespace VoleMole.Theft

open VoleMole.Privacy VoleMole.ZK.Sim VoleMole.ZK VoleMole.Verifier VoleMole.Verifier.Bridge
open VoleMole.ROM VoleMole.ROM.IC VoleMole.ROM.Reads

namespace Moussaka

open VoleMole.Spec VoleMole.Spec.Moussaka VoleMole.Privacy.Moussaka
open VoleMole.Theft.Ratatouille (a5R)

-- `Com` evaluates Keccak-p[800]; nothing below needs to unfold it.
attribute [local irreducible] com UOVKey.eval

/-! ## The redemption system's parameters on the issuance system's tables -/

section Params

variable {Y : Type*}

/-- **A table reader at `pR` is one at `pI`.** -/
def TRd.toI {F : Tab3 → Sh pR → Y} (R : TRd (p := pR) F) :
    TRd (p := pI) (fun g (s : Sh pI) => F g s) :=
  ⟨R.Q3, R.Q5, R.QE, R.cons⟩

/-- A table reader at `pI` is one at `pR`. -/
def TRd.toR {F : Tab3 → Sh pI → Y} (R : TRd (p := pI) F) :
    TRd (p := pR) (fun g (s : Sh pR) => F g s) :=
  ⟨R.Q3, R.Q5, R.QE, R.cons⟩

lemma TRd.bnd_toR {F : Tab3 → Sh pI → Y} {R : TRd (p := pI) F} {q3 q5 qE : ℕ}
    (h : R.Bnd q3 q5 qE) : (TRd.toR R).Bnd q3 q5 qE :=
  ⟨h.h3, h.h5, h.hE⟩

/-- **A confinement at `pR` is one at `pI`** (`gate5_params`). -/
theorem Conf.toI {F : Tab3 → Sh pR → Y} {R : TRd (p := pR) F} {iv : Sh pR → Option ByteArray}
    {a5 aE : ℕ} (h : Conf R iv a5 aE) : Conf (TRd.toI R) (fun s : Sh pI => iv s) a5 aE :=
  ⟨h.h3, h.h5, h.hE, fun g s v hv k hk => gate5_params (h.in5 g s v hv k hk), h.inE⟩

/-- **`ZKExp` at `pR` is `ZKExp` at `pI`**, for the same functions on the tables. -/
theorem ZKExp.toI {I W ρ C O : Type*} [Fintype ρ] [Fintype C] {Rel : I → W → Prop}
    {prove : I → W → ρ → Tab3 → Sh pI → O} {sim : I → C → O} {prog : I → C → Sh pI → Sh pI}
    {q3 q5 qE : ℕ} {ε : ℝ}
    {ch : I → O → Finset (ZK.Sim.Bytes 16) → Finset (ZK.Sim.Bytes 37) → Finset (Blk × Blk) → ℝ}
    (h : ZKExp (p := pR) Rel prove sim prog q3 q5 qE ε ch) :
    ZKExp (p := pI) Rel prove sim prog q3 q5 qE ε ch := by
  intro x w hxw D R hR
  exact h x w hxw D (fun o => TRd.toR (R o)) (fun o => TRd.bnd_toR (hR o))

end Params

/-! ## The joint system -/

section Joint

variable {L : ℕ}

/-- The extra table of the Moussaka games. -/
abbrev XM (L : ℕ) := XTab L Arith.Moussaka.M

/-- The log entry type of the redirect game. -/
abbrev EntM := Option (MI × Bytes)

/-- **The instance of a slot**: its index and its statement (none: the Client refused). -/
abbrev JI := ℕ × Option MI

/-- Whether a slot makes a proof. -/
def actJ (xI : JI) : Prop := xI.2.isSome = true

instance : DecidablePred actJ := fun xI => inferInstanceAs (Decidable (xI.2.isSome = true))

/-- The proof bytes of a prover's output, as the spec has them (the empty proof on an error). -/
def pfOf (e : Except String ByteArray) : Bytes := toL (e.toOption.getD .empty)

/-- The output map of the issuance system: the log entry. -/
def φI (x : IssueInstance) (e : Except String ByteArray) : EntM := some (.inl x, pfOf e)

/-- The output map of the redemption system: the log entry. -/
def φR (x : RedeemInstance) (e : Except String ByteArray) : EntM := some (.inr x, pfOf e)

/-- **The `iv` of an active slot's log entry**: `H₄(iv_pre ‖ μ₁ ‖ 4)` of its proof, none for the
empty proof. -/
noncomputable def ivA (x : XM L) : MI → EntM → Option ByteArray
  | .inl xI, some (_, π) => if π = [] then none else
      some (ivOf (hbX x) ⟨pI, toBA π⟩ ((Privacy.Moussaka.stI xI).mu1 (hbX x)))
  | .inr xR, some (_, π) => if π = [] then none else
      some (ivOf (hbX x) ⟨pR, toBA π⟩ ((Privacy.Moussaka.stR xR).mu1 (hbX x)))
  | _, none => none

/-- **The `iv` decoder of the joint system**: `ivA` for an active slot, `ivN x j` (to be chosen)
for a refused slot `j`. -/
noncomputable def ivJ (ivN : XM L → ℕ → Option ByteArray) (x : XM L) : JI → EntM → Option ByteArray
  | (_, some xI), o => ivA x xI o
  | (j, none), _ => ivN x j

lemma pfOf_ne_nil {e : Except String ByteArray} (h : pfOf e ≠ []) :
    ∃ b, e = .ok b ∧ toBA (pfOf e) = b := by
  rcases e with er | b
  · exact absurd (show pfOf (.error er) = [] by simp [pfOf, toL, Except.toOption]) h
  · exact ⟨b, rfl, toBA_toL' b⟩

lemma ivA_φI (x : XM L) (xI : IssueInstance) (e : Except String ByteArray) (v : ByteArray)
    (h : ivA x (.inl xI) (φI xI e) = some v) :
    ivV (hbX x) (Privacy.Moussaka.stI xI) e = some v := by
  simp only [φI, ivA] at h
  split_ifs at h with h0
  obtain ⟨b, rfl, hb⟩ := pfOf_ne_nil h0
  rw [hb] at h
  exact h

lemma ivA_φR (x : XM L) (xR : RedeemInstance) (e : Except String ByteArray) (v : ByteArray)
    (h : ivA x (.inr xR) (φR xR e) = some v) :
    ivV (hbX x) (Privacy.Moussaka.stR xR) e = some v := by
  simp only [φR, ivA] at h
  split_ifs at h with h0
  obtain ⟨b, rfl, hb⟩ := pfOf_ne_nil h0
  rw [hb] at h
  exact h

/-- The issuance prover with the base record of the extra table. -/
noncomputable def proveI (x : XM L) (xI : IssueInstance) (w : Bytes) (r : ZK.Sim.Bytes 16)
    (g : Tab3) (s : Sh pI) : EntM :=
  φI xI (realRO pI (hbX x) (Privacy.Moussaka.stI xI) (toBA w) r g s)

/-- The redemption prover (parameters `pR`) on the tables of `pI`. -/
noncomputable def proveR (x : XM L) (xR : RedeemInstance) (w : Bytes) (r : ZK.Sim.Bytes 16)
    (g : Tab3) (s : Sh pI) : EntM :=
  φR xR (realRO pR (hbX x) (Privacy.Moussaka.stR xR) (toBA w) r g s)

def simI (xI : IssueInstance) (c : SimCoins pI) : EntM := φI xI (simulate pI c)
def simR (xR : RedeemInstance) (c : SimCoins pR) : EntM := φR xR (simulate pR c)

noncomputable def progI (x : XM L) (xI : IssueInstance) (c : SimCoins pI) (s : Sh pI) : Sh pI :=
  progRO pI (hbX x) (Privacy.Moussaka.stI xI) c s
noncomputable def progR (x : XM L) (xR : RedeemInstance) (c : SimCoins pR) (s : Sh pI) : Sh pI :=
  progRO pR (hbX x) (Privacy.Moussaka.stR xR) c s

/-- **The joint prover**: the two Lean provers, and no proof when the Client refused. -/
noncomputable def proveJ (x : XM L) (xI : JI) : Bytes × Bytes → ZK.Sim.Bytes 16 → Tab3 → Sh pI →
    EntM :=
  osumProve (proveI x) (proveR x) none xI.2

/-- **The joint simulator.** -/
def simJ (xI : JI) : SimCoins pI × SimCoins pR → EntM :=
  osumSim simI simR none xI.2

/-- **The joint programming.** -/
noncomputable def progJ (x : XM L) (xI : JI) : SimCoins pI × SimCoins pR → Sh pI → Sh pI :=
  osumProg (progI x) (progR x) xI.2

/-- The joint relation. -/
def RelJ (xI : JI) (w : Bytes × Bytes) : Prop := osumRel IssueRelW RedeemRelW xI.2 w

variable {U M : ℕ} (A : ThiefN U M Tab3 (TabM L))

/-- **The instance of the next slot**: its index and `xN`. -/
def xJ (ω : SecN U) (l : Log) : JI := (l.length, xN A (pubOf A ω) l)

/-- **The witness of the next slot**, for either relation. -/
def wJ (ω : SecN U) (l : Log) : Bytes × Bytes :=
  match xwN A ω l with
  | some (_, w) => (w, w)
  | none => ([], [])

/-- **The witness is a witness.** -/
theorem relJ_xJ (ω : SecN U) (l : Log) : RelJ (xJ A ω l) (wJ A ω l) := by
  have hf := xwN_fst A ω l
  unfold RelJ xJ wJ
  cases hx : xwN A ω l with
  | none =>
    rw [hx] at hf
    simp only [Option.map_none] at hf
    rw [← hf]; trivial
  | some xw =>
    obtain ⟨x, w⟩ := xw
    rw [hx] at hf
    simp only [Option.map_some] at hf
    rw [← hf]
    by_cases hl : l.length < U
    · have := xwN_relI A ω l hl x w hx
      rcases x with x | x
      · exact this
      · exact this.elim
    · have := xwN_relR A ω l hl x w hx
      rcases x with x | x
      · exact this.elim
      · exact this

/-! ## The redirect game is the joint game -/

/-- **The redirect game's real slot is the joint prover's.** -/
theorem PN_eq : PN A (leanPIX hbX) (leanPRX hbX) = gP proveJ (xJ A) (wJ A) := by
  funext ω l ρ g t
  have hf := xwN_fst A ω l
  unfold PN gP proveJ xJ wJ
  cases hx : xwN A ω l with
  | none =>
    rw [hx] at hf
    simp only [Option.map_none] at hf
    simp only [← hf, pairO, proveO, osumProve]
  | some xw =>
    obtain ⟨x, w⟩ := xw
    rw [hx] at hf
    simp only [Option.map_some] at hf
    simp only [← hf, proveO]
    rcases x with x | x
    · simp only [PM, sumProve, pairO, leanPIX, leanPIH, osumProve, proveI, φI, pfOf, realRO,
        toBA_ofFn]
    · simp only [PM, sumProve, pairO, leanPRX, leanPRH, osumProve, proveR, φR, pfOf, realRO,
        toBA_ofFn]

/-- **The redirect game's simulated slot is the joint simulator's.** -/
theorem SmP_eq : (fun ω => SmP A (leanSim pI) (leanSim pR) (pubOf A ω)) = gS simJ (xJ A) := by
  funext ω l c
  unfold SmP gS simJ xJ
  cases xN A (pubOf A ω) l with
  | none => rfl
  | some x => rcases x with x | x <;> rfl

/-- **The redirect game's programming is the joint programming's.** -/
theorem pgP_eq : (fun ω => pgP A (leanProgIX hbX) (leanProgRX hbX) (pubOf A ω)) =
    gPg progJ (xJ A) := by
  funext ω l c t
  unfold pgP gPg progJ xJ
  cases xN A (pubOf A ω) l with
  | none => rfl
  | some x => rcases x with x | x <;> rfl

/-! ## `ZKExp` of the joint system -/

/-- **The joint system is `ZKExp`** at the point charge of `ivJ` for the active slots and `0` for
the refused ones. -/
theorem zkExpJ (ivN : XM L → ℕ → Option ByteArray) (x : XM L) {q3 q5 qE : ℕ}
    (h3 : (q3 : ℝ) < 2 ^ 128) (hE : 221 * ((qE + 4607 : ℕ) : ℝ) < 2 ^ 128) (hβ : βZK q5 qE < 1) :
    ZKExp RelJ (proveJ x) simJ (progJ x) q3 q5 qE (εZK qE / (1 - βZK q5 qE))
      (fun xI o Q3 Q5 QE => if actJ xI then
        chPt pI CrtGen.tables q3 qE (ivJ ivN x xI o) Q3 Q5 QE / (1 - βZK q5 qE) else 0) := by
  have h₁ := lean_zkExpD pI (hbX x) Privacy.Moussaka.stI (fun _ => rfl) rfl (fun _ w => toBA w)
    IssueRelW csI zkHypI (hbX_wf x) (smallParams_of_le (by decide) (by decide)) φI
    (fun xI o => ivA x (.inl xI) o) (ivA_φI x) h3 hE hβ
  have h₂ := lean_zkExpD pR (hbX x) Privacy.Moussaka.stR (fun _ => rfl) rfl (fun _ w => toBA w)
    RedeemRelW csR zkHypR (hbX_wf x) (smallParams_of_le (by decide) (by decide)) φR
    (fun xR o => ivA x (.inr xR) o) (ivA_φR x) h3 hE hβ
  have e₂ : (fun xR o Q3 Q5 QE => chPt pR CrtGen.tables q3 qE (ivA x (.inr xR) o) Q3 Q5 QE /
      (1 - βZK q5 qE)) = (fun xR o Q3 Q5 QE => chPt pI CrtGen.tables q3 qE
        (ivA x (.inr xR) o) Q3 Q5 QE / (1 - βZK q5 qE)) := by
    funext xR o Q3 Q5 QE
    rw [chPt_params pR pI]
  rw [e₂] at h₂
  have h₂' := ZKExp.toI h₂
  have hden : 0 < 1 - βZK q5 qE := by linarith
  have hε : 0 ≤ εZK qE / (1 - βZK q5 qE) :=
    div_nonneg (add_nonneg (add_nonneg (pr_nonneg _)
      (div_nonneg (by norm_num) (dEZK_pos hE).le)) (by norm_num)) hden.le
  have hs := ZKExp.osum (ch := fun xI o Q3 Q5 QE => match xI with
      | none => 0
      | some y => chPt pI CrtGen.tables q3 qE (ivA x y o) Q3 Q5 QE / (1 - βZK q5 qE))
    (p₁ := proveI x) (p₂ := proveR x) (s₁ := simI) (s₂ := simR) (g₁ := progI x) (g₂ := progR x)
    h₁ h₂' hε (fun _ _ _ _ => le_rfl) none
  refine ZKExp.of_ch (ZKExp.comap (fun xI : JI => xI.2) hs) fun xI o Q3 Q5 QE => ?_
  obtain ⟨j, _ | y⟩ := xI
  · simp [actJ]
  · simp [actJ, ivJ]

/-! ## The honest readers -/

lemma ivJ_some (ivN : XM L → ℕ → Option ByteArray) (x : XM L) (j : ℕ) (y : MI) (o : EntM) :
    ivJ ivN x (j, some y) o = ivA x y o := rfl

lemma simJ_inl (j : ℕ) (xI : IssueInstance) (c : SimCoins pI × SimCoins pR) :
    simJ (j, some (.inl xI)) c = simI xI c.1 := by
  simp only [simJ, osumSim]

lemma simJ_inr (j : ℕ) (xR : RedeemInstance) (c : SimCoins pI × SimCoins pR) :
    simJ (j, some (.inr xR)) c = simR xR c.2 := by
  simp only [simJ, osumSim]

lemma proveJ_inl (x : XM L) (j : ℕ) (xI : IssueInstance) (w : Bytes × Bytes)
    (r : ZK.Sim.Bytes 16) (g' : Tab3) (s : Sh pI) :
    proveJ x (j, some (.inl xI)) w r g' s = proveI x xI w.1 r g' s := by
  simp only [proveJ, osumProve]

lemma proveJ_inr (x : XM L) (j : ℕ) (xR : RedeemInstance) (w : Bytes × Bytes)
    (r : ZK.Sim.Bytes 16) (g' : Tab3) (s : Sh pI) :
    proveJ x (j, some (.inr xR)) w r g' s = proveR x xR w.2 r g' s := by
  simp only [proveJ, osumProve]

/-- **The joint programmings as point readers.** -/
noncomputable def progRdJ (x : XM L) :
    (xI : JI) → (c : SimCoins pI × SimCoins pR) →
      TRd (fun (_ : Tab3) (s : Sh pI) => (progJ x xI c s).1)
  | (_, none), _ => h23Rd
  | (_, some (.inl xI)), c => (progPtRd (p := pI) (hbX x) (Privacy.Moussaka.stI xI) c.1 :
      TRd (fun (_ : Tab3) (s : Sh pI) => (progI x xI c.1 s).1))
  | (_, some (.inr xR)), c =>
      (TRd.toI (progPtRd (p := pR) (hbX x) (Privacy.Moussaka.stR xR) c.2) :
        TRd (fun (_ : Tab3) (s : Sh pI) => (progR x xR c.2 s).1))

/-- **The joint programmings are confined to the simulated proofs' `iv`s**, within
`(312, 4607)`. -/
theorem progRdJ_conf (ivN : XM L → ℕ → Option ByteArray) (x : XM L) (xI : JI)
    (c : SimCoins pI × SimCoins pR) :
    Conf (progRdJ x xI c) (fun _ => ivJ ivN x xI (simJ xI c)) 312 4607 := by
  obtain ⟨j, _ | xI | xR⟩ := xI
  · exact ⟨fun _ _ => rfl, fun _ _ => by simp [progRdJ, h23Rd], fun _ _ => by simp [progRdJ, h23Rd],
      fun _ _ _ _ k hk => by simp [progRdJ, h23Rd] at hk,
      fun _ _ _ _ kz hkz => by simp [progRdJ, h23Rd] at hkz⟩
  · refine (progPtRd_conf (p := pI) (hbX_wf x) rfl c.1).of_iv fun _ v h => ?_
    rw [ivJ_some, simJ_inl] at h
    exact ivA_φI x xI (simulate pI c.1) v h
  · refine Conf.toI ((progPtRd_conf (p := pR) (hbX_wf x) rfl c.2).of_iv fun _ v h => ?_)
    rw [ivJ_some, simJ_inr] at h
    exact ivA_φR x xR (simulate pR c.2) v h

/-- The issuance prover as a point reader. -/
noncomputable def proveRdI (x : XM L) (xI : IssueInstance) (w : Bytes) (r : ZK.Sim.Bytes 16)
    (g' : Tab3) : TRd (fun (_ : Tab3) (s : Sh pI) => proveI x xI w r g' s) :=
  (realPtRdP (p := pI) (hbX x) (Privacy.Moussaka.stI xI) (toBA w) rfl (hbX_wf x) r g').map (φI xI)

/-- The redemption prover as a point reader (on the tables of `pI`). -/
noncomputable def proveRdR (x : XM L) (xR : RedeemInstance) (w : Bytes) (r : ZK.Sim.Bytes 16)
    (g' : Tab3) : TRd (fun (_ : Tab3) (s : Sh pI) => proveR x xR w r g' s) :=
  TRd.toI ((realPtRdP (p := pR) (hbX x) (Privacy.Moussaka.stR xR) (toBA w) rfl (hbX_wf x) r
    g').map (φR xR))

/-- **The joint real provers as point readers.** -/
noncomputable def proveRdJ (x : XM L) :
    (xI : JI) → (w : Bytes × Bytes) → (r : ZK.Sim.Bytes 16) → (g' : Tab3) →
      TRd (fun (_ : Tab3) (s : Sh pI) => proveJ x xI w r g' s)
  | (_, none), _, _, _ => TRd.const none
  | (j, some (.inl xI)), w, r, g' =>
      (proveRdI x xI w.1 r g').congr fun _ s => proveJ_inl x j xI w r g' s
  | (j, some (.inr xR)), w, r, g' =>
      (proveRdR x xR w.2 r g').congr fun _ s => proveJ_inr x j xR w r g' s

/-- **The joint real provers are confined to their proofs' `iv`s**, within `(624, 4607)`. -/
theorem proveRdJ_conf (ivN : XM L → ℕ → Option ByteArray) (x : XM L) (xI : JI)
    (w : Bytes × Bytes) (r : ZK.Sim.Bytes 16) (g' : Tab3) (hw : RelJ xI w) :
    Conf (proveRdJ x xI w r g') (fun s => ivJ ivN x xI (proveJ x xI w r g' s)) 624 4607 := by
  obtain ⟨j, _ | xI | xR⟩ := xI
  · exact ⟨fun _ _ => rfl, fun _ _ => by simp [proveRdJ, TRd.const],
      fun _ _ => by simp [proveRdJ, TRd.const],
      fun _ _ _ _ k hk => by simp [proveRdJ, TRd.const] at hk,
      fun _ _ _ _ kz hkz => by simp [proveRdJ, TRd.const] at hkz⟩
  · refine (((realPtRdP_conf (p := pI) (zkHypI xI w.1 hw) (hbX_wf x) rfl rfl r g').map
      (φI xI)).of_iv fun s v h => ?_).congr fun _ s => proveJ_inl x j xI w r g' s
    rw [ivJ_some, proveJ_inl] at h
    exact ivA_φI x xI _ v h
  · refine (Conf.toI (((realPtRdP_conf (p := pR) (zkHypR xR w.2 hw) (hbX_wf x) rfl rfl r g').map
      (φR xR)).of_iv fun s v h => ?_)).congr fun _ s => proveJ_inr x j xR w r g' s
    rw [ivJ_some] at h
    simp only [proveJ, osumProve, proveR] at h
    exact ivA_φR x xR _ v h

end Joint

/-! ## The joint step for the redirect game -/

section Redirect

variable {U M L : ℕ}

/-- The game reader's cipher budget (keys and classes). -/
def aEM (N qE : ℕ) : ℕ := 2 * (N * verifyCellBound pR + qE) + 9215

variable (A : ThiefN U M Tab3 (TabM L)) {q : Kind → ℕ} {qE nG : ℕ}
  (hA : ∀ reqs reds, AdmLN (QBudT q qE nG) ansPN (A.out reqs reds))

/-- The redirect game's real slot, simulated slot and programming, as the joint game's. -/
lemma nmRealN_eq :
    nmRealN A (leanPIX hbX) (leanPRX hbX) (verILX hbX) (verRLX hbX) (extRomMN q qE nG) =
      realGN (C := SimCoins pI × SimCoins pR) (gP proveJ (xJ A) (wJ A))
        (BadN A (verILX hbX) (verRLX hbX) (extRomMN q qE nG)) := by
  unfold nmRealN
  rw [PN_eq]

lemma nmSimN_eq :
    nmSimN A (leanSim pI) (leanProgIX hbX) (leanSim pR) (leanProgRX hbX)
        (BadN A (verILX hbX) (verRLX hbX) (extRomMN q qE nG)) =
      simGN (ρ := ZK.Sim.Bytes 16) (gS simJ (xJ A)) (gPg (progJ (L := L)) (xJ A))
        (BadN A (verILX hbX) (verRLX hbX) (extRomMN q qE nG)) := by
  unfold nmSimN
  rw [SmP_eq, pgP_eq]

lemma deltaNM_eq (i : Fin (U + M)) :
    deltaNM A (leanPIX hbX) (leanPRX hbX) (leanSim pI) (leanProgIX hbX) (leanSim pR)
        (leanProgRX hbX) i =
      deltaN (gP proveJ (xJ A) (wJ A)) (gS simJ (xJ A)) (gPg (progJ (L := L)) (xJ A)) i := by
  unfold deltaNM
  rw [PN_eq, SmP_eq, pgP_eq]

include hA in
set_option maxHeartbeats 1000000 in
/-- **The joint step for Moussaka's redirect game.** For an adversary whose last stage is the run
of an oracle computation within `QBudT q q_E n_G` (`hA`), `ROM/`'s extractor, any `iv` for the
refused slots (`ivN`), and any `J` bounding the summed charges of the active slots in the
simulated game:

    |Pr_real[BadN] − Pr_sim[BadN]| ≤ (Σ_i (εZK/(1 − βZK) + (1 + B)·Pr[deltaNM i]) + J)/(1 − N·B),

`N = U + M`, budgets `(a₃, a₅, a_E) = (q h3, N·312 + q h5 + 312, 2·(N·cells(pR) + q_E) + 9215)`,
honest readers `(624, 4607)`. -/
theorem redirect_joint_le (ivN : XM L → ℕ → Option ByteArray)
    (h3 : (q .h3 : ℝ) < 2 ^ 128)
    (hE : 221 * ((aEM (U + M) qE + (U + M) * max 4607 4607 + 4607 : ℕ) : ℝ) < 2 ^ 128)
    (hβ : βZK (a5R (U + M) q + (U + M) * max 312 624)
      (aEM (U + M) qE + (U + M) * max 4607 4607) < 1)
    {J : ℝ}
    (hJ : ∑ i ∈ range (U + M), ∑ k, wZK (q .h3) (a5R (U + M) q + (U + M) * max 312 624)
        (aEM (U + M) qE + (U + M) * max 4607 4607) k *
      exU _ (fun z => (nZKA actJ (ivJ ivN) (xJ A) (badGRd A hA) (max 312 624) (max 4607 4607) i k
        (viewN (C := SimCoins pI × SimCoins pR) (ρ := ZK.Sim.Bytes 16)
          (gP proveJ (xJ A) (wJ A)) (gS simJ (xJ A)) (gPg (progJ (L := L)) (xJ A)) (U + M) z) : ℝ))
        ≤ J)
    (hNB : ((U + M : ℕ) : ℝ) * ∑ k, wZK (q .h3) (a5R (U + M) q + (U + M) * max 312 624)
        (aEM (U + M) qE + (U + M) * max 4607 4607) k *
      MZK (U + M) (q .h3) (a5R (U + M) q) (aEM (U + M) qE) (max 312 624) (max 4607 4607) k < 1) :
    |pr (TapeN U M (SimCoins pI) (SimCoins pR) Tab3 (TabM L))
        (nmRealN A (leanPIX hbX) (leanPRX hbX) (verILX hbX) (verRLX hbX) (extRomMN q qE nG)) -
      pr (TapeN U M (SimCoins pI) (SimCoins pR) Tab3 (TabM L))
        (nmSimN A (leanSim pI) (leanProgIX hbX) (leanSim pR) (leanProgRX hbX)
          (BadN A (verILX hbX) (verRLX hbX) (extRomMN q qE nG)))| ≤
      (∑ i : Fin (U + M), (εZK (aEM (U + M) qE + (U + M) * max 4607 4607) /
          (1 - βZK (a5R (U + M) q + (U + M) * max 312 624)
            (aEM (U + M) qE + (U + M) * max 4607 4607)) +
        (1 + ∑ k, wZK (q .h3) (a5R (U + M) q + (U + M) * max 312 624)
            (aEM (U + M) qE + (U + M) * max 4607 4607) k *
          MZK (U + M) (q .h3) (a5R (U + M) q) (aEM (U + M) qE) (max 312 624) (max 4607 4607) k) *
          pr (TapeN U M (SimCoins pI) (SimCoins pR) Tab3 (TabM L))
            (deltaNM A (leanPIX hbX) (leanPRX hbX) (leanSim pI) (leanProgIX hbX) (leanSim pR)
              (leanProgRX hbX) i)) + J) /
        (1 - ((U + M : ℕ) : ℝ) * ∑ k, wZK (q .h3) (a5R (U + M) q + (U + M) * max 312 624)
            (aEM (U + M) qE + (U + M) * max 4607 4607) k *
          MZK (U + M) (q .h3) (a5R (U + M) q) (aEM (U + M) qE) (max 312 624) (max 4607 4607) k) := by
  rw [nmRealN_eq, nmSimN_eq]
  simp only [deltaNM_eq]
  exact real_sim_leN_leanA proveJ simJ progJ
    (fun x xI c s => osumProg_keep (g₁ := progI x) (g₂ := progR x) (fun _ _ _ => rfl)
      (fun _ _ _ => rfl) xI.2 c s) RelJ actJ (ivJ ivN) (xJ A) (wJ A)
    (relJ_xJ A) progRdJ (progRdJ_conf ivN) proveRdJ
    (fun x xI w r g' hw => proveRdJ_conf ivN x xI w r g' hw) (badGRd A hA) (badGRd_cons A hA)
    (badGRd_bnd A hA) h3 hE hβ (fun x => zkExpJ ivN x h3 hE hβ) hJ hNB _ (badGRd_reads A hA)

end Redirect

end Moussaka

end VoleMole.Theft
