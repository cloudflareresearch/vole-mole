import VoleMole.Theft.JointUnbBad
import VoleMole.Theft.JointInst

/-!
# The unbound game as a game of Lean proofs with point charges, and its joint step

As `Theft/JointInst.lean` and `Theft/JointTheft.lean` do for Ratatouille's theft game, the unbound
game NM-U^{U,M} (`Theft/MoussakaUnboundMany.lean`, with the Lean provers on the tables,
`leanPIUX hbX`, `leanPRUX hbX`) is shown to be a game `gP prove xOf wOf` of one proof system with
`ZKExp` at the point charge, and `real_sim_leN_leanA` is applied to it:

* **`TRd.toMI`, `Conf.toMI`, `ZKExp.toMI`** (and `…MR`): the unbound issuance (`pI`) and
  redemption (`pR`) systems run on the tables of Moussaka's `pI` (`Sh` of the three is the same
  type: the `H₂³` keys have the same length); readers, confinements (`gate5_params`) and `ZKExp`
  (`chPt_params`) carry over;
* the instance of slot `j` is `(j, xN …)` (`xJ`), the witness the pair `(w, w)` of `xwN`'s
  witness (`wJ`, `relJ_xJ`);
* the output maps `φI`, `φR` are the game's log entries (`toL` of the proof, the empty proof for a
  failed run); their `iv` decoder `ivA` reads the `iv` off an entry with a proof of the right size
  (`ivA_φI`, `ivA_φR`: a failed run has the empty proof and no `iv`);
* **`PN_eq`, `SmP_eq`, `pgP_eq`**: the game's real slot, simulated slot and programming are `gP`,
  `gS`, `gPg` of `proveJ`, `simJ`, `progJ`; **`zkExpJ`**: `ZKExp` at the point charge for the
  active slots and `0` for the others; **`progRdJ_conf`**, **`proveRdJ_conf`**: the honest readers
  are confined to their `iv`s;
* **`nmU_joint_le`**: `|Pr_real[BadN] − Pr_sim[BadN]| ≤ (Σ_i (εZK/(1 − βZK) + (1 + B)·Pr[deltaNU i]) + J)/(1 − N·B)`
  with `ROM/`'s extractor, the game reader `badGRd` (`Theft/JointUnbBad.lean`) at
  `(a₃, a₅, a_E) = (q h3, N·312 + q h5 + 312, 2·(N·cells(pR) + q_E) + 9215)`, honest readers
  `(624, 4607)`, for every `J` bounding the summed charges of the active slots in the simulated
  game, and any `iv`s of the refused slots.
-/

open Finset

set_option synthInstance.maxSize 1024

namespace VoleMole.Theft

open VoleMole.Privacy VoleMole.ZK.Sim VoleMole.ZK VoleMole.Verifier VoleMole.Verifier.Bridge
open VoleMole.ROM VoleMole.ROM.IC VoleMole.ROM.Reads

namespace MoussakaUnbound

open VoleMole.Privacy.MoussakaUnbound VoleMole.Spec VoleMole.Spec.MoussakaUnbound
open VoleMole.Spec.Moussaka (AnchorSet ctxBytes proveSeedBytes nfBytes)
open VoleMole.Privacy.Moussaka (ShM leanSim)

-- `UCom`, `Derive` and `Com` evaluate Keccak-p[800]; nothing below needs to unfold them.
attribute [local irreducible] ucom derive UOVKey.eval

/-! ## The unbound systems' parameters on the tables of Moussaka's `pI` -/

section Params

variable {Y : Type*}

/-- **A table reader at the unbound `pI` is one at Moussaka's `pI`.** -/
def TRd.toMI {F : Tab3 → Sh pI → Y} (R : TRd (p := pI) F) :
    TRd (p := Privacy.Moussaka.pI) (fun g (s : Sh Privacy.Moussaka.pI) => F g s) :=
  ⟨R.Q3, R.Q5, R.QE, R.cons⟩

/-- **A table reader at `pR` is one at Moussaka's `pI`.** -/
def TRd.toMR {F : Tab3 → Sh pR → Y} (R : TRd (p := pR) F) :
    TRd (p := Privacy.Moussaka.pI) (fun g (s : Sh Privacy.Moussaka.pI) => F g s) :=
  ⟨R.Q3, R.Q5, R.QE, R.cons⟩

/-- A table reader at Moussaka's `pI` is one at the unbound `pI`. -/
def TRd.ofMI {F : Tab3 → Sh Privacy.Moussaka.pI → Y} (R : TRd (p := Privacy.Moussaka.pI) F) :
    TRd (p := pI) (fun g (s : Sh pI) => F g s) :=
  ⟨R.Q3, R.Q5, R.QE, R.cons⟩

/-- A table reader at Moussaka's `pI` is one at `pR`. -/
def TRd.ofMR {F : Tab3 → Sh Privacy.Moussaka.pI → Y} (R : TRd (p := Privacy.Moussaka.pI) F) :
    TRd (p := pR) (fun g (s : Sh pR) => F g s) :=
  ⟨R.Q3, R.Q5, R.QE, R.cons⟩

lemma TRd.bnd_ofMI {F : Tab3 → Sh Privacy.Moussaka.pI → Y} {R : TRd (p := Privacy.Moussaka.pI) F}
    {q3 q5 qE : ℕ} (h : R.Bnd q3 q5 qE) : (TRd.ofMI R).Bnd q3 q5 qE :=
  ⟨h.h3, h.h5, h.hE⟩

lemma TRd.bnd_ofMR {F : Tab3 → Sh Privacy.Moussaka.pI → Y} {R : TRd (p := Privacy.Moussaka.pI) F}
    {q3 q5 qE : ℕ} (h : R.Bnd q3 q5 qE) : (TRd.ofMR R).Bnd q3 q5 qE :=
  ⟨h.h3, h.h5, h.hE⟩

/-- **A confinement at the unbound `pI` is one at Moussaka's `pI`** (`gate5_params`). -/
theorem Conf.toMI {F : Tab3 → Sh pI → Y} {R : TRd (p := pI) F} {iv : Sh pI → Option ByteArray}
    {a5 aE : ℕ} (h : Conf R iv a5 aE) :
    Conf (TRd.toMI R) (fun s : Sh Privacy.Moussaka.pI => iv s) a5 aE :=
  ⟨h.h3, h.h5, h.hE, fun g s v hv k hk => gate5_params (h.in5 g s v hv k hk), h.inE⟩

/-- **A confinement at `pR` is one at Moussaka's `pI`** (`gate5_params`). -/
theorem Conf.toMR {F : Tab3 → Sh pR → Y} {R : TRd (p := pR) F} {iv : Sh pR → Option ByteArray}
    {a5 aE : ℕ} (h : Conf R iv a5 aE) :
    Conf (TRd.toMR R) (fun s : Sh Privacy.Moussaka.pI => iv s) a5 aE :=
  ⟨h.h3, h.h5, h.hE, fun g s v hv k hk => gate5_params (h.in5 g s v hv k hk), h.inE⟩

/-- **`ZKExp` at the unbound `pI` is `ZKExp` at Moussaka's `pI`.** -/
theorem ZKExp.toMI {I W ρ C O : Type*} [Fintype ρ] [Fintype C] {Rel : I → W → Prop}
    {prove : I → W → ρ → Tab3 → Sh Privacy.Moussaka.pI → O} {sim : I → C → O}
    {prog : I → C → Sh Privacy.Moussaka.pI → Sh Privacy.Moussaka.pI} {q3 q5 qE : ℕ} {ε : ℝ}
    {ch : I → O → Finset (ZK.Sim.Bytes 16) → Finset (ZK.Sim.Bytes 37) → Finset (Blk × Blk) → ℝ}
    (h : ZKExp (p := pI) Rel prove sim prog q3 q5 qE ε ch) :
    ZKExp (p := Privacy.Moussaka.pI) Rel prove sim prog q3 q5 qE ε ch := by
  intro x w hxw D R hR
  exact h x w hxw D (fun o => TRd.ofMI (R o)) (fun o => TRd.bnd_ofMI (hR o))

/-- **`ZKExp` at `pR` is `ZKExp` at Moussaka's `pI`.** -/
theorem ZKExp.toMR {I W ρ C O : Type*} [Fintype ρ] [Fintype C] {Rel : I → W → Prop}
    {prove : I → W → ρ → Tab3 → Sh Privacy.Moussaka.pI → O} {sim : I → C → O}
    {prog : I → C → Sh Privacy.Moussaka.pI → Sh Privacy.Moussaka.pI} {q3 q5 qE : ℕ} {ε : ℝ}
    {ch : I → O → Finset (ZK.Sim.Bytes 16) → Finset (ZK.Sim.Bytes 37) → Finset (Blk × Blk) → ℝ}
    (h : ZKExp (p := pR) Rel prove sim prog q3 q5 qE ε ch) :
    ZKExp (p := Privacy.Moussaka.pI) Rel prove sim prog q3 q5 qE ε ch := by
  intro x w hxw D R hR
  exact h x w hxw D (fun o => TRd.ofMR (R o)) (fun o => TRd.bnd_ofMR (hR o))

end Params

/-! ## The joint system -/

section Joint

variable {L : ℕ}

/-- The extra table of the Moussaka games. -/
abbrev XU (L : ℕ) := XTab L Arith.Moussaka.M

/-- The log entry of a slot. -/
abbrev EntU := Option (UI × Bytes)

/-- **The instance of a slot**: its index and its statement (none: the Client refused). -/
abbrev JI := ℕ × Option UI

/-- Whether a slot makes a proof. -/
def actJ (xI : JI) : Prop := xI.2.isSome = true

instance : DecidablePred actJ := fun xI => inferInstanceAs (Decidable (xI.2.isSome = true))

/-- The output map of the issuance system: the log entry (the empty proof for a failed run). -/
def φI (x : IssueInstance) (e : Except String ByteArray) : EntU :=
  some (.inl x, toL (e.toOption.getD .empty))

/-- The output map of the redemption system: the log entry. -/
def φR (x : RedeemInstance) (e : Except String ByteArray) : EntU :=
  some (.inr x, toL (e.toOption.getD .empty))

/-- **The `iv` of an active slot's log entry**: `H₄(iv_pre ‖ μ₁ ‖ 4)` of its proof, if the proof
has the parameters' size (none for the empty proof of a failed run). -/
noncomputable def ivA (x : XU L) : UI → EntU → Option ByteArray
  | .inl xI, some (_, π) => if π.length = pI.proofBytes then
      some (ivOf (hbX x) ⟨pI, toBA π⟩ ((Privacy.MoussakaUnbound.stI xI).mu1 (hbX x))) else none
  | .inr xR, some (_, π) => if π.length = pR.proofBytes then
      some (ivOf (hbX x) ⟨pR, toBA π⟩ ((Privacy.MoussakaUnbound.stR xR).mu1 (hbX x))) else none
  | _, none => none

/-- **The `iv` decoder of the joint system**: `ivA` for an active slot, `ivN x j` (to be chosen)
for a refused slot `j`. -/
noncomputable def ivJ (ivN : XU L → ℕ → Option ByteArray) (x : XU L) : JI → EntU → Option ByteArray
  | (_, some xI), o => ivA x xI o
  | (j, none), _ => ivN x j

lemma pI_proofBytes_pos : pI.proofBytes ≠ 0 := by decide
lemma pR_proofBytes_pos : pR.proofBytes ≠ 0 := by decide

lemma toBA_toL' (b : ByteArray) : toBA (toL b) = b := by
  rw [Privacy.toL_eq]
  cases b
  rfl

lemma ivA_φI (x : XU L) (xI : IssueInstance) (e : Except String ByteArray) (v : ByteArray)
    (h : ivA x (.inl xI) (φI xI e) = some v) :
    ivV (hbX x) (Privacy.MoussakaUnbound.stI xI) e = some v := by
  rcases e with er | b
  · simp only [φI, ivA, Except.toOption, Option.getD_none, length_toL, ByteArray.size_empty] at h
    split_ifs at h with hs
    exact absurd hs.symm pI_proofBytes_pos
  · simp only [φI, ivA, Except.toOption, Option.getD_some, length_toL, toBA_toL'] at h
    split_ifs at h with hs
    rw [← h]; rfl

lemma ivA_φR (x : XU L) (xR : RedeemInstance) (e : Except String ByteArray) (v : ByteArray)
    (h : ivA x (.inr xR) (φR xR e) = some v) :
    ivV (hbX x) (Privacy.MoussakaUnbound.stR xR) e = some v := by
  rcases e with er | b
  · simp only [φR, ivA, Except.toOption, Option.getD_none, length_toL, ByteArray.size_empty] at h
    split_ifs at h with hs
    exact absurd hs.symm pR_proofBytes_pos
  · simp only [φR, ivA, Except.toOption, Option.getD_some, length_toL, toBA_toL'] at h
    split_ifs at h with hs
    rw [← h]; rfl

/-- The unbound issuance prover on the tables of Moussaka's `pI`. -/
noncomputable def proveI (x : XU L) (xI : IssueInstance) (w : Bytes) (r : ZK.Sim.Bytes 16)
    (g : Tab3) (s : Sh Privacy.Moussaka.pI) : EntU :=
  φI xI (realRO pI (hbX x) (Privacy.MoussakaUnbound.stI xI) (toBA w) r g s)

/-- The unbound redemption prover on the tables of Moussaka's `pI`. -/
noncomputable def proveR (x : XU L) (xR : RedeemInstance) (w : Bytes) (r : ZK.Sim.Bytes 16)
    (g : Tab3) (s : Sh Privacy.Moussaka.pI) : EntU :=
  φR xR (realRO pR (hbX x) (Privacy.MoussakaUnbound.stR xR) (toBA w) r g s)

def simI (xI : IssueInstance) (c : SimCoins pI) : EntU := φI xI (simulate pI c)
def simR (xR : RedeemInstance) (c : SimCoins pR) : EntU := φR xR (simulate pR c)

noncomputable def progI (x : XU L) (xI : IssueInstance) (c : SimCoins pI)
    (s : Sh Privacy.Moussaka.pI) : Sh Privacy.Moussaka.pI :=
  progRO pI (hbX x) (Privacy.MoussakaUnbound.stI xI) c s
noncomputable def progR (x : XU L) (xR : RedeemInstance) (c : SimCoins pR)
    (s : Sh Privacy.Moussaka.pI) : Sh Privacy.Moussaka.pI :=
  progRO pR (hbX x) (Privacy.MoussakaUnbound.stR xR) c s

/-- **The joint prover**: the two Lean provers, and no proof when the Client refused. -/
noncomputable def proveJ (x : XU L) (xI : JI) : Bytes × Bytes → ZK.Sim.Bytes 16 → Tab3 →
    Sh Privacy.Moussaka.pI → EntU :=
  osumProve (proveI x) (proveR x) none xI.2

/-- **The joint simulator.** -/
def simJ (xI : JI) : SimCoins pI × SimCoins pR → EntU :=
  osumSim simI simR none xI.2

/-- **The joint programming.** -/
noncomputable def progJ (x : XU L) (xI : JI) :
    SimCoins pI × SimCoins pR → Sh Privacy.Moussaka.pI → Sh Privacy.Moussaka.pI :=
  osumProg (progI x) (progR x) xI.2

/-- The joint relation. -/
def RelJ (xI : JI) (w : Bytes × Bytes) : Prop := osumRel IssueRelW RedeemRelW xI.2 w

variable {U M : ℕ} (A : ThiefN U M Tab3 (TabU L))

/-- **The instance of the next slot**: its index and `xN`. -/
def xJ (ω : SecN U) (l : Log) : JI := (l.length, xN A (pubOf A ω) l)

/-- **The witness of the next slot**, for both systems. -/
def wJ (ω : SecN U) (l : Log) : Bytes × Bytes :=
  (((xwN A ω l).map Prod.snd).getD [], ((xwN A ω l).map Prod.snd).getD [])

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
    simp only [Option.map_some, Option.getD_some]
    by_cases hl : l.length < U
    · have := xwN_relI A ω l hl x w hx
      rcases x with x | x
      · exact this
      · exact this.elim
    · have := xwN_relR A ω l hl x w hx
      rcases x with x | x
      · exact this.elim
      · exact this

/-! ## The unbound game is the joint game -/

/-- **The game's real slot is the joint prover's.** -/
theorem PN_eq : PN A (leanPIUX hbX) (leanPRUX hbX) = gP proveJ (xJ A) (wJ A) := by
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
    simp only [← hf, proveO, Option.map_some, Option.getD_some]
    rcases x with x | x
    · simp only [PU, sumProve, pairO, osumProve, proveI, φI, leanPIUX, leanPIUH, realRO,
        toBA_ofFn]
    · simp only [PU, sumProve, pairO, osumProve, proveR, φR, leanPRUX, leanPRUH, realRO,
        toBA_ofFn]

/-- **The game's simulated slot is the joint simulator's.** -/
theorem SmP_eq : (fun ω => SmP A (leanSim pI) (leanSim pR) (pubOf A ω)) = gS simJ (xJ A) := by
  funext ω l c
  unfold SmP gS simJ xJ
  cases xN A (pubOf A ω) l with
  | none => rfl
  | some x =>
    rcases x with x | x
    · simp only [simO, simU, sumSim, pairO, osumSim, simI, φI, leanSim]
    · simp only [simO, simU, sumSim, pairO, osumSim, simR, φR, leanSim]

/-- **The game's programming is the joint programming's.** -/
theorem pgP_eq : (fun ω => pgP A (leanProgIUX hbX) (leanProgRUX hbX) (pubOf A ω)) =
    gPg progJ (xJ A) := by
  funext ω l c t
  unfold pgP gPg progJ xJ
  cases xN A (pubOf A ω) l with
  | none => rfl
  | some x => rcases x with x | x <;> rfl

/-! ## `ZKExp` of the joint system -/

/-- **The joint system is `ZKExp`** at the point charge of `ivJ` for the active slots and `0` for
the refused ones. -/
theorem zkExpJ (ivN : XU L → ℕ → Option ByteArray) (x : XU L) {q3 q5 qE : ℕ}
    (h3 : (q3 : ℝ) < 2 ^ 128) (hE : 221 * ((qE + 4607 : ℕ) : ℝ) < 2 ^ 128) (hβ : βZK q5 qE < 1) :
    ZKExp (p := Privacy.Moussaka.pI) RelJ (proveJ x) simJ (progJ x) q3 q5 qE
      (εZK qE / (1 - βZK q5 qE))
      (fun xI o Q3 Q5 QE => if actJ xI then
        chPt Privacy.Moussaka.pI CrtGen.tables q3 qE (ivJ ivN x xI o) Q3 Q5 QE /
          (1 - βZK q5 qE) else 0) := by
  have h₁ := lean_zkExpD pI (hbX x) Privacy.MoussakaUnbound.stI (fun _ => rfl) rfl
    (fun _ w => toBA w) IssueRelW csI zkHypI (hbX_wf x)
    (smallParams_of_le (by decide) (by decide)) φI (fun xI o => ivA x (.inl xI) o) (ivA_φI x)
    h3 hE hβ
  have h₂ := lean_zkExpD pR (hbX x) Privacy.MoussakaUnbound.stR (fun _ => rfl) rfl
    (fun _ w => toBA w) RedeemRelW csR zkHypR (hbX_wf x)
    (smallParams_of_le (by decide) (by decide)) φR (fun xR o => ivA x (.inr xR) o) (ivA_φR x)
    h3 hE hβ
  have e₁ : (fun xI o Q3 Q5 QE => chPt pI CrtGen.tables q3 qE (ivA x (.inl xI) o) Q3 Q5 QE /
      (1 - βZK q5 qE)) = (fun xI o Q3 Q5 QE => chPt Privacy.Moussaka.pI CrtGen.tables q3 qE
        (ivA x (.inl xI) o) Q3 Q5 QE / (1 - βZK q5 qE)) := by
    funext xI o Q3 Q5 QE
    rw [chPt_params pI Privacy.Moussaka.pI]
  have e₂ : (fun xR o Q3 Q5 QE => chPt pR CrtGen.tables q3 qE (ivA x (.inr xR) o) Q3 Q5 QE /
      (1 - βZK q5 qE)) = (fun xR o Q3 Q5 QE => chPt Privacy.Moussaka.pI CrtGen.tables q3 qE
        (ivA x (.inr xR) o) Q3 Q5 QE / (1 - βZK q5 qE)) := by
    funext xR o Q3 Q5 QE
    rw [chPt_params pR Privacy.Moussaka.pI]
  rw [e₁] at h₁
  rw [e₂] at h₂
  have h₁' := ZKExp.toMI h₁
  have h₂' := ZKExp.toMR h₂
  have hden : 0 < 1 - βZK q5 qE := by linarith
  have hε : 0 ≤ εZK qE / (1 - βZK q5 qE) :=
    div_nonneg (add_nonneg (add_nonneg (pr_nonneg _)
      (div_nonneg (by norm_num) (dEZK_pos hE).le)) (by norm_num)) hden.le
  have hs := ZKExp.osum (p := Privacy.Moussaka.pI) (ch := fun xI o Q3 Q5 QE => match xI with
      | none => 0
      | some y => chPt Privacy.Moussaka.pI CrtGen.tables q3 qE (ivA x y o) Q3 Q5 QE /
          (1 - βZK q5 qE))
    (p₁ := proveI x) (p₂ := proveR x) (s₁ := simI) (s₂ := simR) (g₁ := progI x) (g₂ := progR x)
    h₁' h₂' hε (fun _ _ _ _ => le_rfl) none
  refine ZKExp.of_ch (ZKExp.comap (fun xI : JI => xI.2) hs) fun xI o Q3 Q5 QE => ?_
  obtain ⟨j, _ | y⟩ := xI
  · simp [actJ]
  · simp [actJ, ivJ]

/-! ## The honest readers -/

lemma ivJ_some (ivN : XU L → ℕ → Option ByteArray) (x : XU L) (j : ℕ) (y : UI) (o : EntU) :
    ivJ ivN x (j, some y) o = ivA x y o := rfl

lemma simJ_inl (j : ℕ) (xI : IssueInstance) (c : SimCoins pI × SimCoins pR) :
    simJ (j, some (.inl xI)) c = simI xI c.1 := by
  simp only [simJ, osumSim]

lemma simJ_inr (j : ℕ) (xR : RedeemInstance) (c : SimCoins pI × SimCoins pR) :
    simJ (j, some (.inr xR)) c = simR xR c.2 := by
  simp only [simJ, osumSim]

lemma proveJ_inl (x : XU L) (j : ℕ) (xI : IssueInstance) (w : Bytes × Bytes)
    (r : ZK.Sim.Bytes 16) (g' : Tab3) (s : Sh Privacy.Moussaka.pI) :
    proveJ x (j, some (.inl xI)) w r g' s = proveI x xI w.1 r g' s := by
  simp only [proveJ, osumProve]

lemma proveJ_inr (x : XU L) (j : ℕ) (xR : RedeemInstance) (w : Bytes × Bytes)
    (r : ZK.Sim.Bytes 16) (g' : Tab3) (s : Sh Privacy.Moussaka.pI) :
    proveJ x (j, some (.inr xR)) w r g' s = proveR x xR w.2 r g' s := by
  simp only [proveJ, osumProve]

/-- **The joint programmings as point readers.** -/
noncomputable def progRdJ (x : XU L) :
    (xI : JI) → (c : SimCoins pI × SimCoins pR) →
      TRd (fun (_ : Tab3) (s : Sh Privacy.Moussaka.pI) => (progJ x xI c s).1)
  | (_, none), _ => h23Rd
  | (_, some (.inl xI)), c =>
      (TRd.toMI (progPtRd (p := pI) (hbX x) (Privacy.MoussakaUnbound.stI xI) c.1) :
        TRd (fun (_ : Tab3) (s : Sh Privacy.Moussaka.pI) => (progI x xI c.1 s).1))
  | (_, some (.inr xR)), c =>
      (TRd.toMR (progPtRd (p := pR) (hbX x) (Privacy.MoussakaUnbound.stR xR) c.2) :
        TRd (fun (_ : Tab3) (s : Sh Privacy.Moussaka.pI) => (progR x xR c.2 s).1))

/-- **The joint programmings are confined to the simulated proofs' `iv`s**, within
`(312, 4607)`. -/
theorem progRdJ_conf (ivN : XU L → ℕ → Option ByteArray) (x : XU L) (xI : JI)
    (c : SimCoins pI × SimCoins pR) :
    Conf (progRdJ x xI c) (fun _ => ivJ ivN x xI (simJ xI c)) 312 4607 := by
  obtain ⟨j, _ | xI | xR⟩ := xI
  · exact ⟨fun _ _ => rfl, fun _ _ => by simp [progRdJ, h23Rd], fun _ _ => by simp [progRdJ, h23Rd],
      fun _ _ _ _ k hk => by simp [progRdJ, h23Rd] at hk,
      fun _ _ _ _ kz hkz => by simp [progRdJ, h23Rd] at hkz⟩
  · refine Conf.toMI ((progPtRd_conf (p := pI) (hbX_wf x) rfl c.1).of_iv fun _ v h => ?_)
    rw [ivJ_some, simJ_inl] at h
    exact ivA_φI x xI (simulate pI c.1) v h
  · refine Conf.toMR ((progPtRd_conf (p := pR) (hbX_wf x) rfl c.2).of_iv fun _ v h => ?_)
    rw [ivJ_some, simJ_inr] at h
    exact ivA_φR x xR (simulate pR c.2) v h

/-- The issuance prover as a point reader. -/
noncomputable def proveRdI (x : XU L) (xI : IssueInstance) (w : Bytes) (r : ZK.Sim.Bytes 16)
    (g' : Tab3) : TRd (fun (_ : Tab3) (s : Sh Privacy.Moussaka.pI) => proveI x xI w r g' s) :=
  TRd.toMI ((realPtRdP (p := pI) (hbX x) (Privacy.MoussakaUnbound.stI xI) (toBA w) rfl (hbX_wf x)
    r g').map (φI xI))

/-- The redemption prover as a point reader. -/
noncomputable def proveRdR (x : XU L) (xR : RedeemInstance) (w : Bytes) (r : ZK.Sim.Bytes 16)
    (g' : Tab3) : TRd (fun (_ : Tab3) (s : Sh Privacy.Moussaka.pI) => proveR x xR w r g' s) :=
  TRd.toMR ((realPtRdP (p := pR) (hbX x) (Privacy.MoussakaUnbound.stR xR) (toBA w) rfl (hbX_wf x)
    r g').map (φR xR))

/-- **The joint real provers as point readers.** -/
noncomputable def proveRdJ (x : XU L) :
    (xI : JI) → (w : Bytes × Bytes) → (r : ZK.Sim.Bytes 16) → (g' : Tab3) →
      TRd (fun (_ : Tab3) (s : Sh Privacy.Moussaka.pI) => proveJ x xI w r g' s)
  | (_, none), _, _, _ => TRd.const none
  | (j, some (.inl xI)), w, r, g' =>
      (proveRdI x xI w.1 r g').congr fun _ s => proveJ_inl x j xI w r g' s
  | (j, some (.inr xR)), w, r, g' =>
      (proveRdR x xR w.2 r g').congr fun _ s => proveJ_inr x j xR w r g' s

/-- **The joint real provers are confined to their proofs' `iv`s**, within `(624, 4607)`. -/
theorem proveRdJ_conf (ivN : XU L → ℕ → Option ByteArray) (x : XU L) (xI : JI)
    (w : Bytes × Bytes) (r : ZK.Sim.Bytes 16) (g' : Tab3) (hw : RelJ xI w) :
    Conf (proveRdJ x xI w r g') (fun s => ivJ ivN x xI (proveJ x xI w r g' s)) 624 4607 := by
  obtain ⟨j, _ | xI | xR⟩ := xI
  · exact ⟨fun _ _ => rfl, fun _ _ => by simp [proveRdJ, TRd.const],
      fun _ _ => by simp [proveRdJ, TRd.const],
      fun _ _ _ _ k hk => by simp [proveRdJ, TRd.const] at hk,
      fun _ _ _ _ kz hkz => by simp [proveRdJ, TRd.const] at hkz⟩
  · refine (Conf.toMI (((realPtRdP_conf (p := pI) (zkHypI xI w.1 hw) (hbX_wf x) rfl rfl r
      g').map (φI xI)).of_iv fun s v h => ?_)).congr fun _ s => proveJ_inl x j xI w r g' s
    rw [ivJ_some] at h
    simp only [proveJ, osumProve, proveI] at h
    exact ivA_φI x xI _ v h
  · refine (Conf.toMR (((realPtRdP_conf (p := pR) (zkHypR xR w.2 hw) (hbX_wf x) rfl rfl r
      g').map (φR xR)).of_iv fun s v h => ?_)).congr fun _ s => proveJ_inr x j xR w r g' s
    rw [ivJ_some] at h
    simp only [proveJ, osumProve, proveR] at h
    exact ivA_φR x xR _ v h

end Joint

/-! ## The joint step for the unbound game -/

section Step

variable {U M L : ℕ}

/-- The game reader's `H₅` budget. -/
def a5U (N : ℕ) (q : Kind → ℕ) : ℕ := N * 312 + q .h5 + 312

/-- The game reader's cipher budget (keys). -/
def aEU (N qE : ℕ) : ℕ := 2 * (N * verifyCellBound pR + qE) + 9215

variable (A : ThiefN U M Tab3 (TabU L)) {q : Kind → ℕ} {qE nG : ℕ}
  (hA : ∀ reqs reds, AdmLN (QBudT q qE nG) ansPN (A.out reqs reds))

/-- The game's real event, as the joint game's. -/
lemma nmRealNE_eq (Ev : SecN U → Log → (Fin (U + M) → Tab3) → TabU L → Prop) :
    nmRealNE (CI := SimCoins pI) (CR := SimCoins pR) A (leanPIUX hbX) (leanPRUX hbX) Ev =
      realGN (C := SimCoins pI × SimCoins pR) (gP proveJ (xJ A) (wJ A)) Ev := by
  unfold nmRealNE
  rw [PN_eq]

/-- The game's simulated event, as the joint game's. -/
lemma nmSimN_eq (Ev : SecN U → Log → (Fin (U + M) → Tab3) → TabU L → Prop) :
    nmSimN A (leanSim pI) (leanProgIUX hbX) (leanSim pR) (leanProgRUX hbX) Ev =
      simGN (ρ := ZK.Sim.Bytes 16) (gS simJ (xJ A)) (gPg progJ (xJ A)) Ev := by
  unfold nmSimN
  rw [SmP_eq, pgP_eq]

lemma deltaNU_eq (i : Fin (U + M)) :
    deltaNU A (leanPIUX hbX) (leanPRUX hbX) (leanSim pI) (leanProgIUX hbX) (leanSim pR)
        (leanProgRUX hbX) i =
      deltaN (gP proveJ (xJ A) (wJ A)) (gS simJ (xJ A)) (gPg progJ (xJ A)) i := by
  unfold deltaNU
  rw [PN_eq, SmP_eq, pgP_eq]

set_option maxHeartbeats 1000000 in
/-- **The joint step for the unbound game.** For an adversary whose last stage is the run of an
oracle computation within `QBudT q q_E n_G` (`hA`), `ROM/`'s extractor, any `iv` for the refused
slots (`ivN`), and any `J` bounding the summed charges of the active slots in the simulated
game:

    |Pr_real[BadN] − Pr_sim[BadN]| ≤ (Σ_i (εZK/(1 − βZK) + (1 + B)·Pr[deltaNU i]) + J)/(1 − N·B),

`N = U + M`, budgets `(a₃, a₅, a_E) = (q h3, N·312 + q h5 + 312, 2·(N·cells(pR) + q_E) + 9215)`,
honest readers `(624, 4607)`. -/
theorem nmU_joint_le (ivN : XU L → ℕ → Option ByteArray)
    (h3 : (q .h3 : ℝ) < 2 ^ 128)
    (hE : 221 * ((aEU (U + M) qE + (U + M) * max 4607 4607 + 4607 : ℕ) : ℝ) < 2 ^ 128)
    (hβ : βZK (a5U (U + M) q + (U + M) * max 312 624)
      (aEU (U + M) qE + (U + M) * max 4607 4607) < 1)
    {J : ℝ}
    (hJ : ∑ i ∈ range (U + M), ∑ k, wZK (q .h3) (a5U (U + M) q + (U + M) * max 312 624)
        (aEU (U + M) qE + (U + M) * max 4607 4607) k *
      exU _ (fun z => (nZKA actJ (ivJ ivN) (xJ A) (badGRd A hA) (max 312 624) (max 4607 4607) i k
        (VoleMole.Theft.viewN (C := SimCoins pI × SimCoins pR) (ρ := ZK.Sim.Bytes 16)
          (gP proveJ (xJ A) (wJ A)) (gS simJ (xJ A)) (gPg progJ (xJ A)) (U + M) z) : ℝ)) ≤ J)
    (hNB : ((U + M : ℕ) : ℝ) * ∑ k, wZK (q .h3) (a5U (U + M) q + (U + M) * max 312 624)
        (aEU (U + M) qE + (U + M) * max 4607 4607) k *
      MZK (U + M) (q .h3) (a5U (U + M) q) (aEU (U + M) qE) (max 312 624) (max 4607 4607) k < 1) :
    |pr (TapeN U M (SimCoins pI) (SimCoins pR) Tab3 (TabU L))
        (nmRealNE A (leanPIUX hbX) (leanPRUX hbX)
          (BadN A (verILUX hbX) (verRLUX hbX) (extRomUN q qE nG))) -
      pr (TapeN U M (SimCoins pI) (SimCoins pR) Tab3 (TabU L))
        (nmSimN A (leanSim pI) (leanProgIUX hbX) (leanSim pR) (leanProgRUX hbX)
          (BadN A (verILUX hbX) (verRLUX hbX) (extRomUN q qE nG)))| ≤
      (∑ i : Fin (U + M), (εZK (aEU (U + M) qE + (U + M) * max 4607 4607) /
          (1 - βZK (a5U (U + M) q + (U + M) * max 312 624)
            (aEU (U + M) qE + (U + M) * max 4607 4607)) +
        (1 + ∑ k, wZK (q .h3) (a5U (U + M) q + (U + M) * max 312 624)
            (aEU (U + M) qE + (U + M) * max 4607 4607) k *
          MZK (U + M) (q .h3) (a5U (U + M) q) (aEU (U + M) qE) (max 312 624) (max 4607 4607) k) *
          pr (TapeN U M (SimCoins pI) (SimCoins pR) Tab3 (TabU L))
            (deltaNU A (leanPIUX hbX) (leanPRUX hbX) (leanSim pI) (leanProgIUX hbX) (leanSim pR)
              (leanProgRUX hbX) i)) + J) /
        (1 - ((U + M : ℕ) : ℝ) * ∑ k, wZK (q .h3) (a5U (U + M) q + (U + M) * max 312 624)
            (aEU (U + M) qE + (U + M) * max 4607 4607) k *
          MZK (U + M) (q .h3) (a5U (U + M) q) (aEU (U + M) qE) (max 312 624) (max 4607 4607) k) := by
  rw [nmRealNE_eq, nmSimN_eq]
  simp only [deltaNU_eq]
  have hb := badGRd_bnd A hA
  rw [show (U + M) * 312 + q .h5 + 312 = a5U (U + M) q by unfold a5U; ring,
    show 2 * ((U + M) * verifyCellBound pR + qE) + 9215 = aEU (U + M) qE from rfl] at hb
  exact real_sim_leN_leanA proveJ simJ progJ
    (fun x xI c s => osumProg_keep (g₁ := progI x) (g₂ := progR x) (fun _ _ _ => rfl)
      (fun _ _ _ => rfl) xI.2 c s) RelJ actJ (ivJ ivN) (xJ A) (wJ A)
    (relJ_xJ A) progRdJ (progRdJ_conf ivN) proveRdJ
    (fun x xI w r g' hw => proveRdJ_conf ivN x xI w r g' hw) (badGRd A hA) (badGRd_cons A hA)
    hb h3 hE hβ (fun x => zkExpJ ivN x h3 hE hβ) hJ hNB _ (badGRd_reads A hA)

end Step

end MoussakaUnbound

end VoleMole.Theft
