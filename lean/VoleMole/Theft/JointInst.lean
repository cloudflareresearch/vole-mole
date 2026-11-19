import VoleMole.Theft.JointBad

/-!
# The Ratatouille theft game as a game of Lean proofs with point charges

`real_sim_leN_leanA` (`Theft/JointLeanSum.lean`) is stated for a game `gP prove xOf wOf` of one
proof system with `ZKExp` at the point charge. Here the theft game THEFT^{U,M}
(`Theft/RatatouilleMany.lean`, with the Lean provers on the tables, `leanPIRX hbX`, `leanPSRX hbX`)
is shown to be such a game:

* **`TRd.toI`, `Conf.toI`, `ZKExp.toI`**: the spend system runs at the parameters `pS` on the
  tables of `pI` (`Sh pS` is `Sh pI` by definition: the `H₂³` keys have the same length); a reader,
  a confinement (`gate5_params`) and `ZKExp` (the charge by `chPt_params`) at `pS` are ones at `pI`;
* the instance of slot `j` is `(j, xN …)` (`xJ`): its index and its statement (none if the Client
  refused); the index lets the `iv` decoder give a refused slot an `iv` of its own
  (`ivJ`; see `Theft/JointIv.lean`);
* **`PN_eq`, `SmP_eq`, `pgP_eq`**: the theft game's real slot, simulated slot and programming are
  `gP`, `gS`, `gPg` of `proveJ`, `simJ`, `progJ`, the `osum` of the two Lean systems with "no
  proof" (`osumProve`, `osumSim`, `osumProg`); the tape `Coins 16` is `Bytes 16`;
* **`zkExpJ`**: `ZKExp` of the joint system at the point charge for active slots and `0` for the
  others (`lean_zkExpD` for each system with the `vecOf` output map and its `iv` decoder,
  `ZKExp.osum`);
* **`progRdJ_conf`, `proveRdJ_conf`**: the programmings and the real proofs are point readers
  confined to their `iv`s (`progPtRd_conf`, `realPtRdP_conf`, transported to `pI`).
-/

open Finset

set_option synthInstance.maxSize 1024

namespace VoleMole.Theft

open VoleMole.Privacy VoleMole.ZK.Sim VoleMole.ZK VoleMole.Verifier VoleMole.Verifier.Bridge
open VoleMole.ROM VoleMole.ROM.IC VoleMole.ROM.Reads

namespace Ratatouille

open VoleMole.Privacy.Ratatouille VoleMole.Spec.Ratatouille

/-! ## The spend system's parameters on the issuance system's tables -/

section Params

variable {Y : Type*}

/-- **A table reader at `pS` is one at `pI`.** -/
def TRd.toI {F : Tab3 → Sh pS → Y} (R : TRd (p := pS) F) : TRd (p := pI) (fun g (s : Sh pI) => F g s) :=
  ⟨R.Q3, R.Q5, R.QE, R.cons⟩

/-- A table reader at `pI` is one at `pS`. -/
def TRd.toS {F : Tab3 → Sh pI → Y} (R : TRd (p := pI) F) : TRd (p := pS) (fun g (s : Sh pS) => F g s) :=
  ⟨R.Q3, R.Q5, R.QE, R.cons⟩

lemma TRd.bnd_toS {F : Tab3 → Sh pI → Y} {R : TRd (p := pI) F} {q3 q5 qE : ℕ} (h : R.Bnd q3 q5 qE) :
    (TRd.toS R).Bnd q3 q5 qE :=
  ⟨h.h3, h.h5, h.hE⟩

/-- A confinement of a reader is one of the reader of an equal function. -/
theorem _root_.VoleMole.Theft.Conf.congr {p : Params} {F F' : Tab3 → Sh p → Y} {R : TRd F} {iv : Sh p → Option ByteArray}
    {a5 aE : ℕ} (h : Conf R iv a5 aE) (hF : ∀ g s, F' g s = F g s) : Conf (R.congr hF) iv a5 aE :=
  ⟨h.h3, h.h5, h.hE, h.in5, h.inE⟩

/-- **A confinement at `pS` is one at `pI`** (`gate5_params`). -/
theorem Conf.toI {F : Tab3 → Sh pS → Y} {R : TRd (p := pS) F} {iv : Sh pS → Option ByteArray}
    {a5 aE : ℕ} (h : Conf R iv a5 aE) : Conf (TRd.toI R) (fun s : Sh pI => iv s) a5 aE :=
  ⟨h.h3, h.h5, h.hE, fun g s v hv k hk => gate5_params (h.in5 g s v hv k hk), h.inE⟩

/-- **`ZKExp` at `pS` is `ZKExp` at `pI`**, for the same functions on the tables. -/
theorem ZKExp.toI {I W ρ C O : Type*} [Fintype ρ] [Fintype C] {Rel : I → W → Prop}
    {prove : I → W → ρ → Tab3 → Sh pI → O} {sim : I → C → O} {prog : I → C → Sh pI → Sh pI}
    {q3 q5 qE : ℕ} {ε : ℝ}
    {ch : I → O → Finset (ZK.Sim.Bytes 16) → Finset (ZK.Sim.Bytes 37) → Finset (Blk × Blk) → ℝ}
    (h : ZKExp (p := pS) Rel prove sim prog q3 q5 qE ε ch) :
    ZKExp (p := pI) Rel prove sim prog q3 q5 qE ε ch := by
  intro x w hxw D R hR
  exact h x w hxw D (fun o => TRd.toS (R o)) (fun o => TRd.bnd_toS (hR o))

end Params

/-! ## The joint system -/

section Joint

variable {L : ℕ}

/-- The extra table of the Ratatouille games. -/
abbrev XR (L : ℕ) := XTab L Arith.Ratatouille.uovM

/-- **The instance of a slot**: its index and its statement (none: the Client refused). -/
abbrev JI := ℕ × Option RI

/-- Whether a slot makes a proof. -/
def actJ (xI : JI) : Prop := xI.2.isSome = true

instance : DecidablePred actJ := fun xI => inferInstanceAs (Decidable (xI.2.isSome = true))

/-- The output map of the issuance system: the log entry. -/
def φI (x : IssueInstance) (e : Except String ByteArray) : Ent Sizes.labelRows :=
  (vecOf Sizes.labelRows.issue e).map fun π => (Sum.inl x, Sum.inl π)

/-- The output map of the spend system: the log entry. -/
def φS (x : SpendInstance) (e : Except String ByteArray) : Ent Sizes.labelRows :=
  (vecOf Sizes.labelRows.spend e).map fun π => (Sum.inr x, Sum.inr π)

/-- **The `iv` of an active slot's log entry**: `H₄(iv_pre ‖ μ₁ ‖ 4)` of its proof. -/
noncomputable def ivA (x : XR L) : RI → Ent Sizes.labelRows → Option ByteArray
  | .inl xI, some (_, .inl π) =>
      some (ivOf (hbX x) ⟨pI, bOf π⟩ ((Privacy.Ratatouille.stI xI).mu1 (hbX x)))
  | .inr xS, some (_, .inr π) =>
      some (ivOf (hbX x) ⟨pS, bOf π⟩ ((Privacy.Ratatouille.stS xS).mu1 (hbX x)))
  | _, _ => none

/-- **The `iv` decoder of the joint system**: `ivA` for an active slot, `ivN x j` (to be chosen)
for a refused slot `j`. -/
noncomputable def ivJ (ivN : XR L → ℕ → Option ByteArray) (x : XR L) :
    JI → Ent Sizes.labelRows → Option ByteArray
  | (_, some xI), o => ivA x xI o
  | (j, none), _ => ivN x j

lemma ivA_φI (x : XR L) (xI : IssueInstance) (e : Except String ByteArray) (v : ByteArray)
    (h : ivA x (.inl xI) (φI xI e) = some v) :
    ivV (hbX x) (Privacy.Ratatouille.stI xI) e = some v := by
  rcases e with er | b
  · simp [φI, vecOf, ivA] at h
  · by_cases hb : b.size = Sizes.labelRows.issue
    · obtain ⟨e1, e2⟩ := vecOf_ok_bOf hb
      simp only [φI, e1, Option.map_some, ivA, e2, Option.some.injEq] at h
      rw [← h]; rfl
    · simp [φI, vecOf, hb, ivA] at h

lemma ivA_φS (x : XR L) (xS : SpendInstance) (e : Except String ByteArray) (v : ByteArray)
    (h : ivA x (.inr xS) (φS xS e) = some v) :
    ivV (hbX x) (Privacy.Ratatouille.stS xS) e = some v := by
  rcases e with er | b
  · simp [φS, vecOf, ivA] at h
  · by_cases hb : b.size = Sizes.labelRows.spend
    · obtain ⟨e1, e2⟩ := vecOf_ok_bOf hb
      simp only [φS, e1, Option.map_some, ivA, e2, Option.some.injEq] at h
      rw [← h]; rfl
    · simp [φS, vecOf, hb, ivA] at h

/-- The issuance prover with the base record of the extra table. -/
noncomputable def proveI (x : XR L) (xI : IssueInstance) (w : IssueWitness) (r : ZK.Sim.Bytes 16)
    (g : Tab3) (s : Sh pI) : Ent Sizes.labelRows :=
  φI xI (realRO pI (hbX x) (Privacy.Ratatouille.stI xI) (encI xI w) r g s)

/-- The spend prover (parameters `pS`) on the tables of `pI`. -/
noncomputable def proveS (x : XR L) (xS : SpendInstance) (w : SpendWitness) (r : ZK.Sim.Bytes 16)
    (g : Tab3) (s : Sh pI) : Ent Sizes.labelRows :=
  φS xS (realRO pS (hbX x) (Privacy.Ratatouille.stS xS) (encS xS w) r g s)

def simI (xI : IssueInstance) (c : SimCoins pI) : Ent Sizes.labelRows := φI xI (simulate pI c)
def simS (xS : SpendInstance) (c : SimCoins pS) : Ent Sizes.labelRows := φS xS (simulate pS c)

noncomputable def progI (x : XR L) (xI : IssueInstance) (c : SimCoins pI) (s : Sh pI) : Sh pI :=
  progRO pI (hbX x) (Privacy.Ratatouille.stI xI) c s
noncomputable def progS (x : XR L) (xS : SpendInstance) (c : SimCoins pS) (s : Sh pI) : Sh pI :=
  progRO pS (hbX x) (Privacy.Ratatouille.stS xS) c s

/-- **The joint prover**: the two Lean provers, and no proof when the Client refused. -/
noncomputable def proveJ (x : XR L) (xI : JI) : Wit → ZK.Sim.Bytes 16 → Tab3 → Sh pI →
    Ent Sizes.labelRows :=
  osumProve (proveI x) (proveS x) none xI.2

/-- **The joint simulator.** -/
def simJ (xI : JI) : SimCoins pI × SimCoins pS → Ent Sizes.labelRows :=
  osumSim simI simS none xI.2

/-- **The joint programming.** -/
noncomputable def progJ (x : XR L) (xI : JI) : SimCoins pI × SimCoins pS → Sh pI → Sh pI :=
  osumProg (progI x) (progS x) xI.2

/-- The joint relation. -/
def RelJ (xI : JI) (w : Wit) : Prop := osumRel IssueRel SpendRel xI.2 w

variable {U M : ℕ} (A : ThiefN Sizes.labelRows U M Tab3 (TabR L))

/-- **The instance of the next slot**: its index and `xN`. -/
noncomputable def xJ (ω : SecN U M) (l : LogR Sizes.labelRows) : JI := (l.length, xN A (pubOf ω) l)

/-- **The witness of the next slot** (the slot's coins and, for a spend, the token). -/
noncomputable def wJ (ω : SecN U M) (l : LogR Sizes.labelRows) : Wit :=
  ((xwN A ω l).map Prod.snd).getD (witE A ω (stOf A (pubOf ω) l) 0)

/-- **The witness is a witness.** -/
theorem relJ_xJ (ω : SecN U M) (l : LogR Sizes.labelRows) : RelJ (xJ A ω l) (wJ A ω l) := by
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
    · have := xwN_relS A ω l hl x w hx
      rcases x with x | x
      · exact this.elim
      · exact this

/-! ## The theft game is the joint game -/

/-- **The theft game's real slot is the joint prover's.** -/
theorem PN_eq : PN A (leanPIRX hbX) (leanPSRX hbX) = gP proveJ (xJ A) (wJ A) := by
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
    · simp only [PM, sumProveO, PI', leanPIRX, leanPIRH, osumProve, proveI, φI, realRO, bOf_vec]
      cases vecOf _ _ <;> rfl
    · simp only [PM, sumProveO, PS', leanPSRX, leanPSRH, osumProve, proveS, φS, realRO, bOf_vec]
      cases vecOf _ _ <;> rfl

/-- **The theft game's simulated slot is the joint simulator's.** -/
theorem SmP_eq : (fun ω => SmP A leanSimIR leanSimSR (pubOf ω)) = gS simJ (xJ A) := by
  funext ω l c
  unfold SmP gS simJ xJ
  cases xN A (pubOf ω) l with
  | none => rfl
  | some x =>
    rcases x with x | x
    · simp only [simO, simM, sumSimO, leanSimIR, osumSim, simI, φI]
      cases vecOf _ _ <;> rfl
    · simp only [simO, simM, sumSimO, leanSimSR, osumSim, simS, φS]
      cases vecOf _ _ <;> rfl

/-- **The theft game's programming is the joint programming's.** -/
theorem pgP_eq : (fun ω => pgP A (leanProgIRX hbX) (leanProgSRX hbX) (pubOf ω)) =
    gPg progJ (xJ A) := by
  funext ω l c t
  unfold pgP gPg progJ xJ
  cases xN A (pubOf ω) l with
  | none => rfl
  | some x => rcases x with x | x <;> rfl

/-! ## `ZKExp` of the joint system -/

/-- **`ZKExp` along a map of instances.** -/
theorem _root_.VoleMole.ZK.ZKExp.comap {I I' W ρ C O : Type*} [Fintype ρ] [Fintype C] {p : Params}
    {Rel : I → W → Prop} {prove : I → W → ρ → Tab3 → Sh p → O} {sim : I → C → O}
    {prog : I → C → Sh p → Sh p} {q3 q5 qE : ℕ} {ε : ℝ}
    {ch : I → O → Finset (ZK.Sim.Bytes 16) → Finset (ZK.Sim.Bytes 37) → Finset (Blk × Blk) → ℝ}
    (f : I' → I) (h : ZKExp Rel prove sim prog q3 q5 qE ε ch) :
    ZKExp (fun x w => Rel (f x) w) (fun x => prove (f x)) (fun x => sim (f x))
      (fun x => prog (f x)) q3 q5 qE ε (fun x => ch (f x)) :=
  fun x w hxw D R hR => h (f x) w hxw D R hR

/-- **`ZKExp` with an equal charge.** -/
theorem _root_.VoleMole.ZK.ZKExp.of_ch {I W ρ C O : Type*} [Fintype ρ] [Fintype C] {p : Params}
    {Rel : I → W → Prop} {prove : I → W → ρ → Tab3 → Sh p → O} {sim : I → C → O}
    {prog : I → C → Sh p → Sh p} {q3 q5 qE : ℕ} {ε : ℝ}
    {ch ch' : I → O → Finset (ZK.Sim.Bytes 16) → Finset (ZK.Sim.Bytes 37) → Finset (Blk × Blk) → ℝ}
    (h : ZKExp Rel prove sim prog q3 q5 qE ε ch)
    (hch : ∀ x o Q3 Q5 QE, ch x o Q3 Q5 QE = ch' x o Q3 Q5 QE) :
    ZKExp Rel prove sim prog q3 q5 qE ε ch' := by
  intro x w hxw D R hR
  have := h x w hxw D R hR
  simp only [hch] at this
  exact this

/-- **The joint system is `ZKExp`** at the point charge of `ivJ` for the active slots and `0` for
the refused ones. -/
theorem zkExpJ (ivN : XR L → ℕ → Option ByteArray) (x : XR L) {q3 q5 qE : ℕ}
    (h3 : (q3 : ℝ) < 2 ^ 128) (hE : 221 * ((qE + 4607 : ℕ) : ℝ) < 2 ^ 128) (hβ : βZK q5 qE < 1) :
    ZKExp RelJ (proveJ x) simJ (progJ x) q3 q5 qE (εZK qE / (1 - βZK q5 qE))
      (fun xI o Q3 Q5 QE => if actJ xI then
        chPt pI CrtGen.tables q3 qE (ivJ ivN x xI o) Q3 Q5 QE / (1 - βZK q5 qE) else 0) := by
  have h₁ := lean_zkExpD pI (hbX x) Privacy.Ratatouille.stI (fun _ => rfl) rfl encI IssueRel csI
    zkHypI (hbX_wf x) (smallParams_of_le (by decide) (by decide)) φI
    (fun xI o => ivA x (.inl xI) o) (ivA_φI x) h3 hE hβ
  have h₂ := lean_zkExpD pS (hbX x) Privacy.Ratatouille.stS (fun _ => rfl) rfl encS SpendRel csS
    zkHypS (hbX_wf x) (smallParams_of_le (by decide) (by decide)) φS
    (fun xS o => ivA x (.inr xS) o) (ivA_φS x) h3 hE hβ
  have e₂ : (fun xS o Q3 Q5 QE => chPt pS CrtGen.tables q3 qE (ivA x (.inr xS) o) Q3 Q5 QE /
      (1 - βZK q5 qE)) = (fun xS o Q3 Q5 QE => chPt pI CrtGen.tables q3 qE
        (ivA x (.inr xS) o) Q3 Q5 QE / (1 - βZK q5 qE)) := by
    funext xS o Q3 Q5 QE
    rw [chPt_params pS pI]
  rw [e₂] at h₂
  have h₂' := ZKExp.toI h₂
  have hden : 0 < 1 - βZK q5 qE := by linarith
  have hε : 0 ≤ εZK qE / (1 - βZK q5 qE) :=
    div_nonneg (add_nonneg (add_nonneg (pr_nonneg _)
      (div_nonneg (by norm_num) (dEZK_pos hE).le)) (by norm_num)) hden.le
  have hs := ZKExp.osum (ch := fun xI o Q3 Q5 QE => match xI with
      | none => 0
      | some y => chPt pI CrtGen.tables q3 qE (ivA x y o) Q3 Q5 QE / (1 - βZK q5 qE))
    (p₁ := proveI x) (p₂ := proveS x) (s₁ := simI) (s₂ := simS) (g₁ := progI x) (g₂ := progS x)
    h₁ h₂' hε (fun _ _ _ _ => le_rfl) none
  refine ZKExp.of_ch (ZKExp.comap (fun xI : JI => xI.2) hs) fun xI o Q3 Q5 QE => ?_
  obtain ⟨j, _ | y⟩ := xI
  · simp [actJ]
  · simp [actJ, ivJ]

/-! ## The honest readers -/

lemma ivJ_some (ivN : XR L → ℕ → Option ByteArray) (x : XR L) (j : ℕ) (y : RI)
    (o : Ent Sizes.labelRows) : ivJ ivN x (j, some y) o = ivA x y o := rfl

lemma simJ_inl (j : ℕ) (xI : IssueInstance) (c : SimCoins pI × SimCoins pS) :
    simJ (j, some (.inl xI)) c = simI xI c.1 := by
  simp only [simJ, osumSim]

lemma simJ_inr (j : ℕ) (xS : SpendInstance) (c : SimCoins pI × SimCoins pS) :
    simJ (j, some (.inr xS)) c = simS xS c.2 := by
  simp only [simJ, osumSim]

lemma proveJ_inl (x : XR L) (j : ℕ) (xI : IssueInstance) (w : Wit) (r : ZK.Sim.Bytes 16) (g' : Tab3)
    (s : Sh pI) : proveJ x (j, some (.inl xI)) w r g' s = proveI x xI w.1 r g' s := by
  simp only [proveJ, osumProve]

lemma proveJ_inr (x : XR L) (j : ℕ) (xS : SpendInstance) (w : Wit) (r : ZK.Sim.Bytes 16) (g' : Tab3)
    (s : Sh pI) : proveJ x (j, some (.inr xS)) w r g' s = proveS x xS w.2 r g' s := by
  simp only [proveJ, osumProve]

/-- **The joint programmings as point readers.** -/
noncomputable def progRdJ (x : XR L) :
    (xI : JI) → (c : SimCoins pI × SimCoins pS) → TRd (fun (_ : Tab3) (s : Sh pI) => (progJ x xI c s).1)
  | (_, none), _ => h23Rd
  | (_, some (.inl xI)), c => (progPtRd (p := pI) (hbX x) (Privacy.Ratatouille.stI xI) c.1 :
      TRd (fun (_ : Tab3) (s : Sh pI) => (progI x xI c.1 s).1))
  | (_, some (.inr xS)), c => (TRd.toI (progPtRd (p := pS) (hbX x) (Privacy.Ratatouille.stS xS) c.2) :
      TRd (fun (_ : Tab3) (s : Sh pI) => (progS x xS c.2 s).1))

/-- **The joint programmings are confined to the simulated proofs' `iv`s**, within
`(312, 4607)`. -/
theorem progRdJ_conf (ivN : XR L → ℕ → Option ByteArray) (x : XR L) (xI : JI)
    (c : SimCoins pI × SimCoins pS) :
    Conf (progRdJ x xI c) (fun _ => ivJ ivN x xI (simJ xI c)) 312 4607 := by
  obtain ⟨j, _ | xI | xS⟩ := xI
  · exact ⟨fun _ _ => rfl, fun _ _ => by simp [progRdJ, h23Rd], fun _ _ => by simp [progRdJ, h23Rd],
      fun _ _ _ _ k hk => by simp [progRdJ, h23Rd] at hk,
      fun _ _ _ _ kz hkz => by simp [progRdJ, h23Rd] at hkz⟩
  · refine (progPtRd_conf (p := pI) (hbX_wf x) rfl c.1).of_iv fun _ v h => ?_
    rw [ivJ_some, simJ_inl] at h
    exact ivA_φI x xI (simulate pI c.1) v h
  · refine Conf.toI ((progPtRd_conf (p := pS) (hbX_wf x) rfl c.2).of_iv fun _ v h => ?_)
    rw [ivJ_some, simJ_inr] at h
    exact ivA_φS x xS (simulate pS c.2) v h

/-- The issuance prover as a point reader. -/
noncomputable def proveRdI (x : XR L) (xI : IssueInstance) (w : IssueWitness) (r : ZK.Sim.Bytes 16)
    (g' : Tab3) : TRd (fun (_ : Tab3) (s : Sh pI) => proveI x xI w r g' s) :=
  (realPtRdP (p := pI) (hbX x) (Privacy.Ratatouille.stI xI) (encI xI w) rfl (hbX_wf x) r g').map (φI xI)

/-- The spend prover as a point reader (on the tables of `pI`). -/
noncomputable def proveRdS (x : XR L) (xS : SpendInstance) (w : SpendWitness) (r : ZK.Sim.Bytes 16)
    (g' : Tab3) : TRd (fun (_ : Tab3) (s : Sh pI) => proveS x xS w r g' s) :=
  TRd.toI ((realPtRdP (p := pS) (hbX x) (Privacy.Ratatouille.stS xS) (encS xS w) rfl (hbX_wf x) r
    g').map (φS xS))

/-- **The joint real provers as point readers.** -/
noncomputable def proveRdJ (x : XR L) :
    (xI : JI) → (w : Wit) → (r : ZK.Sim.Bytes 16) → (g' : Tab3) →
      TRd (fun (_ : Tab3) (s : Sh pI) => proveJ x xI w r g' s)
  | (_, none), _, _, _ => TRd.const none
  | (j, some (.inl xI)), w, r, g' => (proveRdI x xI w.1 r g').congr fun _ s => proveJ_inl x j xI w r g' s
  | (j, some (.inr xS)), w, r, g' => (proveRdS x xS w.2 r g').congr fun _ s => proveJ_inr x j xS w r g' s

/-- **The joint real provers are confined to their proofs' `iv`s**, within `(624, 4607)`. -/
theorem proveRdJ_conf (ivN : XR L → ℕ → Option ByteArray) (x : XR L) (xI : JI) (w : Wit)
    (r : ZK.Sim.Bytes 16) (g' : Tab3) (hw : RelJ xI w) :
    Conf (proveRdJ x xI w r g') (fun s => ivJ ivN x xI (proveJ x xI w r g' s)) 624 4607 := by
  obtain ⟨j, _ | xI | xS⟩ := xI
  · exact ⟨fun _ _ => rfl, fun _ _ => by simp [proveRdJ, TRd.const],
      fun _ _ => by simp [proveRdJ, TRd.const],
      fun _ _ _ _ k hk => by simp [proveRdJ, TRd.const] at hk,
      fun _ _ _ _ kz hkz => by simp [proveRdJ, TRd.const] at hkz⟩
  · refine (((realPtRdP_conf (p := pI) (zkHypI xI w.1 hw) (hbX_wf x) rfl rfl r g').map
      (φI xI)).of_iv fun s v h => ?_).congr fun _ s => proveJ_inl x j xI w r g' s
    rw [ivJ_some, proveJ_inl] at h
    exact ivA_φI x xI _ v h
  · refine (Conf.toI (((realPtRdP_conf (p := pS) (zkHypS xS w.2 hw) (hbX_wf x) rfl rfl r g').map
      (φS xS)).of_iv fun s v h => ?_)).congr fun _ s => proveJ_inr x j xS w r g' s
    rw [ivJ_some] at h
    simp only [proveJ, osumProve, proveS] at h
    exact ivA_φS x xS _ v h

end Joint

end Ratatouille

end VoleMole.Theft
