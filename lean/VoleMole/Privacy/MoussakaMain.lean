import VoleMole.ZK.MainGame
import VoleMole.Privacy.MoussakaLean

/-!
# Moussaka issuer hiding and unlinkability on `main` (no dedicated label rows), under (PU)

`Privacy.Moussaka.anonymity` (Theorem 4(a)) assumes per-proof zero knowledge, which holds only
with the label-row fix. On `main` the issuance and redemption proofs of a token both start their
witness with the commitment opening `r`, and a proof is zero-knowledge only as long as `r` cannot
be predicted (`ZK/HopsMain.lean`). Here the theorem is proved for `main`'s layout with the joint
hop of `ZK/MainGame.lean` in place of the four per-proof hops.

## The game (`realMain`)

The colluding adversary of `Moussaka.Adversary` (contexts, keys, responses and Anchor Sets chosen
from the issuance requests, without reading the tables, as in `Privacy/MoussakaRO.lean`), whose
guess also sees, for each of the four proofs, its `H₃`, `H₅` and cipher tables (`VisM`). The four
proofs are the executable prover in the model of `zk_rom_ic` (`ZK.Sim.realSlot`, each proof with
its own tables) for `main`'s statements (`stI`, `stR` with the parameters `pIm`, `pRm`:
`labelRows = false`), run as in `Spec/Moussaka.lean`: issuance requests `t ++ π`, redemptions
`nf ++ π` when the Client's check passes (`redOut`), and the guess as in `Moussaka.post`.

## The bound (`anonymity_main`)

    |Pr[world 0] − Pr[world 1]| ≤ 8·(q₃·2⁻¹²⁸ + 221·(4607 + q_E)·2⁻¹²⁸) + 15·(PU₀ + PU₁) + 2·εhide

* `8·…`: H1–H4 for the four proofs of each world (`ZK.Sim.real_fill_close`);
* `PU_b` (`puTerm`): the probability, **in world `b` with all four proofs simulated**, that the
  adversary's `H₅` read set on some proof's table contains a candidate for that proof's witness
  prefix, which is the Client's opening `r` (`wPre_issue`, `wPre_redeem`): this is the (PU) event of
  `security/moussaka.md` §6, measured where `r` enters the view only through the commitments.
  (PU) is the assumption that it is small; it is one-wayness of Keccak-p[800] in `r` towards an
  adversary that holds `t = Com(nf, ctx_iss, ctx_red, r)`, and it is not proved here;
* `εhide`: hiding of `Com`, for the reductions `Moussaka.reduction` of the adversary with the
  tables fixed (`hiding_hop`, `idealGame_eq`, as in `Moussaka.anonymity`).

The `15` is a cost of the proof of the joint H6 (`MainChain.fill_ideal_le`). The adversary's `H₅`
read sets must be consistent (`AdversaryM.Cons`); its `H₃` and cipher reads are budgets
(`AdversaryM.Budget`).
-/

open Finset

-- (The coin types are large products: their `Fintype` instances exceed the default size.)
set_option synthInstance.maxSize 1024

set_option linter.unusedSectionVars false
set_option linter.constructorNameAsVariable false

namespace VoleMole.Privacy.Moussaka

open VoleMole.Spec VoleMole.Spec.Moussaka VoleMole.ZK.Sim VoleMole.Privacy.MainChain
open VoleMole.Verifier VoleMole.Verifier.Bridge

-- `Com` evaluates Keccak-p[800]; nothing below needs to unfold it.
attribute [local irreducible] com UOVKey.eval
attribute [local irreducible] simulate proveIdeal proveE firstHit

/-! ## `main`'s statements -/

/-- The issuance parameters on `main` (no label rows). -/
abbrev pIm : Params := { witnessBytes := 256, qsDegree := 9, labelRows := false }

/-- The redemption parameters on `main`. -/
abbrev pRm : Params := { witnessBytes := 343, qsDegree := 9, labelRows := false }

lemma mainP_pIm : MainP pIm := ⟨rfl, by decide⟩
lemma mainP_pRm : MainP pRm := ⟨rfl, by decide⟩
lemma small_pIm : SmallParams pIm := smallParams_of_le (by decide) (by decide)
lemma small_pRm : SmallParams pRm := smallParams_of_le (by decide) (by decide)

/-- `withP (stI x) pIm` is `main`'s issuance statement `moussakaIssue … false`. -/
lemma withP_stI (x : IssueInstance) :
    withP (stI x) pIm = moussakaIssue (toBA x.t) (toBA x.ctxIss) false := rfl

/-- **`ZKHyp` for `main`'s issuance statement** (the system and the witness do not depend on the
label rows). -/
theorem zkHypIm (x : IssueInstance) (w : Spec.Bytes) (h : IssueRelW x w) :
    ZKHyp CrtGen.tables (withP (stI x) pIm) (toBA w) (csI x) :=
  let z := zkHypI x w h
  { hvals := z.hvals, hdeg := z.hdeg, hd := z.hd, hd' := z.hd', hsat := z.hsat, hw := z.hw,
    hnm := z.hnm, hT := z.hT, hI := z.hI }

/-- **`ZKHyp` for `main`'s redemption statement.** -/
theorem zkHypRm (x : RedeemInstance) (w : Spec.Bytes) (h : RedeemRelW x w) :
    ZKHyp CrtGen.tables (withP (stR x) pRm) (toBA w) (csR x) :=
  let z := zkHypR x w h
  { hvals := z.hvals, hdeg := z.hdeg, hd := z.hd, hd' := z.hd', hsat := z.hsat, hw := z.hw,
    hnm := z.hnm, hT := z.hT, hI := z.hI }

/-! ## The adversary and the game -/

/-- The tables the guess sees: each proof's `H₃`, `H₅` and cipher (issuance 0, 1; redemption left,
right). -/
abbrev VisM := Vis pIm × Vis pIm × Vis pRm × Vis pRm

/-- **The colluding adversary on `main`**: `Adversary`'s interaction (not reading the tables) and a
guess that also sees the four proofs' tables, with `H₅` read sets `R₁ … R₄`. -/
structure AdversaryM where
  ctxIss : Coins ctxBytes
  ctxRed : Coins ctxBytes
  pk : Bool → UOVKey
  respond : Bytes → Bytes → Bool → Coins uovN
  choose : Bytes → Bytes → Bool → AnchorSet × Bytes
  guess : Bytes → Bytes → Option (Except Error Bytes × Except Error Bytes) → VisM → Prop
  R₁ : Bytes → Bytes → Option (Except Error Bytes × Except Error Bytes) → VisM → Finset (SKey pIm)
  R₂ : Bytes → Bytes → Option (Except Error Bytes × Except Error Bytes) → VisM → Finset (SKey pIm)
  R₃ : Bytes → Bytes → Option (Except Error Bytes × Except Error Bytes) → VisM → Finset (SKey pRm)
  R₄ : Bytes → Bytes → Option (Except Error Bytes × Except Error Bytes) → VisM → Finset (SKey pRm)

namespace AdversaryM

variable (A : AdversaryM)

/-- The adversary with its guess at fixed tables. -/
def atV (v : VisM) : Adversary :=
  ⟨A.ctxIss, A.ctxRed, A.pk, A.respond, A.choose, fun q₀ q₁ y => A.guess q₀ q₁ y v⟩

/-- Its interaction (the guess is not used). -/
def int : Adversary := ⟨A.ctxIss, A.ctxRed, A.pk, A.respond, A.choose, fun _ _ _ => True⟩

/-- **The guess's budget**: it reads each proof's `H₃` table at `q3` and cipher at `qE` keys. -/
structure Budget (q3 qE : ℕ) : Prop where
  b₁ : ∀ q₀ q₁ y v₂ v₃ v₄, RdV q3 qE fun v₁ => A.guess q₀ q₁ y (v₁, v₂, v₃, v₄)
  b₂ : ∀ q₀ q₁ y v₁ v₃ v₄, RdV q3 qE fun v₂ => A.guess q₀ q₁ y (v₁, v₂, v₃, v₄)
  b₃ : ∀ q₀ q₁ y v₁ v₂ v₄, RdV q3 qE fun v₃ => A.guess q₀ q₁ y (v₁, v₂, v₃, v₄)
  b₄ : ∀ q₀ q₁ y v₁ v₂ v₃, RdV q3 qE fun v₄ => A.guess q₀ q₁ y (v₁, v₂, v₃, v₄)

/-- **Consistent `H₅` read sets** (`ZK.Sim.VCons` for the guess, the requests fixed). -/
def Cons : Prop :=
  ∀ q₀ q₁ y, VCons (S := Unit) (fun _ _ _ _ _ v₁ v₂ v₃ v₄ => A.guess q₀ q₁ y (v₁, v₂, v₃, v₄))
    (fun _ _ _ _ _ v₁ v₂ v₃ v₄ => A.R₁ q₀ q₁ y (v₁, v₂, v₃, v₄))
    (fun _ _ _ _ _ v₁ v₂ v₃ v₄ => A.R₂ q₀ q₁ y (v₁, v₂, v₃, v₄))
    (fun _ _ _ _ _ v₁ v₂ v₃ v₄ => A.R₃ q₀ q₁ y (v₁, v₂, v₃, v₄))
    (fun _ _ _ _ _ v₁ v₂ v₃ v₄ => A.R₄ q₀ q₁ y (v₁, v₂, v₃, v₄))

end AdversaryM

variable (A : AdversaryM) (idx : AnchorSet → UOVKey → ℕ)

/-- The two Clients' `(nf, r)`. -/
abbrev SecM := (Coins nfBytes × Coins rBytes) × (Coins nfBytes × Coins rBytes)

/-- A proof's bytes (empty if it was not made or failed). -/
def pf (o : Option Out) : Bytes :=
  match o with
  | some (.ok b) => toL b
  | _ => []

/-- Client `c`'s commitment. -/
def tM (s : SecM) (c : Bool) : Bytes :=
  com (List.ofFn (bif c then s.2 else s.1).1) A.int.ci A.int.cr (List.ofFn (bif c then s.2 else s.1).2)

/-- Client `c`'s issuance output, with the proof `o`. -/
def issM (s : SecM) (c : Bool) (o : Option Out) : PendingToken × Bytes :=
  (⟨List.ofFn (bif c then s.2 else s.1).1, List.ofFn (bif c then s.2 else s.1).2, A.int.ci, A.int.cr,
    tM A s c⟩, tM A s c ++ pf o)

/-- Client `c`'s issuance statement and witness. -/
def issStmt (s : SecM) (c : Bool) : SW :=
  (stI ⟨tM A s c, A.int.ci⟩, toBA (encodeIssueWitness (List.ofFn (bif c then s.2 else s.1).1)
    A.int.ci A.int.cr (List.ofFn (bif c then s.2 else s.1).2)))

/-- The redemption instance at a redemption point. -/
def xRM (P : RedeemPt) : RedeemInstance := ⟨P.anchors.keys, P.tok.nf, A.int.ci, A.int.cr, P.cd⟩

/-- **The redemption statement and witness**, when the Client's check passes (`redeemRequestOf`). -/
def redStmt (P : RedeemPt) : Option SW :=
  match P.anchors.keys[P.i]? with
  | none => none
  | some pk =>
    if pk.eval P.tok.s = com P.tok.nf A.int.ci A.int.cr P.tok.r then
      some (stR (xRM A P), toBA (encodeRedeemWitness P.tok.nf A.int.ci A.int.cr P.tok.r P.tok.s P.i))
    else none

/-- **The redemption output** (`redeemRequestOf`, with the proof `o`). -/
def redOut (P : RedeemPt) (o : Option Out) : Except Error Bytes :=
  match P.anchors.keys[P.i]? with
  | none => .error .indexOutOfRange
  | some pk =>
    if pk.eval P.tok.s = com P.tok.nf A.int.ci A.int.cr P.tok.r then .ok (P.tok.nf ++ pf o)
    else .error .invalidToken

/-- The redemption point of side `side` in world `b`. -/
def ptM (b : Bool) (s : SecM) (o₁ o₂ : Option Out) (side : Bool) : RedeemPt :=
  pt A.int idx b (issM A s false o₁) (issM A s true o₂) side

/-- **The game of world `b`**, as four proofs in sequence. -/
def gameM (b : Bool) : Game SecM Out SW SW SW SW where
  σ₁ s := some (issStmt A s false)
  σ₂ s _ := some (issStmt A s true)
  σ₃ s o₁ o₂ := redStmt A (ptM A idx b s o₁ o₂ false)
  σ₄ s o₁ o₂ _ := redStmt A (ptM A idx b s o₁ o₂ true)

/-- The guess's input in world `b`: the requests and the redemptions (if §6's rule allows them). -/
def yM (b : Bool) (s : SecM) (o₁ o₂ o₃ o₄ : Option Out) :
    Option (Except Error Bytes × Except Error Bytes) :=
  bif allOk A.int idx (issM A s false o₁) (issM A s true o₂) then
    some (redOut A (ptM A idx b s o₁ o₂ false) o₃, redOut A (ptM A idx b s o₁ o₂ true) o₄)
  else none

/-- **The final event of world `b`.** -/
def evM (b : Bool) : Ev SecM Out (Vis pIm) (Vis pIm) (Vis pRm) (Vis pRm) :=
  fun s o₁ o₂ o₃ o₄ v₁ v₂ v₃ v₄ =>
    A.guess (issM A s false o₁).2 (issM A s true o₂).2 (yM A idx b s o₁ o₂ o₃ o₄) (v₁, v₂, v₃, v₄)

/-- The `H₅` read sets of the final event. -/
def rM₁ (b : Bool) : RSet SecM Out (Vis pIm) (Vis pIm) (Vis pRm) (Vis pRm) (SKey pIm) :=
  fun s o₁ o₂ o₃ o₄ v₁ v₂ v₃ v₄ =>
    A.R₁ (issM A s false o₁).2 (issM A s true o₂).2 (yM A idx b s o₁ o₂ o₃ o₄) (v₁, v₂, v₃, v₄)
def rM₂ (b : Bool) : RSet SecM Out (Vis pIm) (Vis pIm) (Vis pRm) (Vis pRm) (SKey pIm) :=
  fun s o₁ o₂ o₃ o₄ v₁ v₂ v₃ v₄ =>
    A.R₂ (issM A s false o₁).2 (issM A s true o₂).2 (yM A idx b s o₁ o₂ o₃ o₄) (v₁, v₂, v₃, v₄)
def rM₃ (b : Bool) : RSet SecM Out (Vis pIm) (Vis pIm) (Vis pRm) (Vis pRm) (SKey pRm) :=
  fun s o₁ o₂ o₃ o₄ v₁ v₂ v₃ v₄ =>
    A.R₃ (issM A s false o₁).2 (issM A s true o₂).2 (yM A idx b s o₁ o₂ o₃ o₄) (v₁, v₂, v₃, v₄)
def rM₄ (b : Bool) : RSet SecM Out (Vis pIm) (Vis pIm) (Vis pRm) (Vis pRm) (SKey pRm) :=
  fun s o₁ o₂ o₃ o₄ v₁ v₂ v₃ v₄ =>
    A.R₄ (issM A s false o₁).2 (issM A s true o₂).2 (yM A idx b s o₁ o₂ o₃ o₄) (v₁, v₂, v₃, v₄)

variable [HasPrg]

/-- **The real game on `main`** in world `b`: the executable prover (`main`'s statements) in the
model of `zk_rom_ic`, with SHAKE (`Hashes.shake`) for the hashes that are not tables. -/
noncomputable def realMain (b : Bool) : ℝ :=
  pr _ (ev (gameM A idx b) (realSlot Hashes.shake CrtGen.tables pIm)
    (realSlot Hashes.shake CrtGen.tables pIm) (realSlot Hashes.shake CrtGen.tables pRm)
    (realSlot Hashes.shake CrtGen.tables pRm) (evM A idx b))

/-- **The (PU) term of world `b`**: in the game with all four proofs simulated, some proof's witness
prefix is a candidate of the guess's `H₅` read set on that proof's table (`ZK.Sim.predAll`). -/
noncomputable def puTerm (b : Bool) : ℝ :=
  pr _ (ev (gameM A idx b) (simP pIm) (simP pIm) (simP pRm) (simP pRm)
    (predAll Hashes.shake CrtGen.tables mainP_pIm mainP_pIm mainP_pRm mainP_pRm
      (rM₁ A idx b) (rM₂ A idx b) (rM₃ A idx b) (rM₄ A idx b)))

/-! ## The hypotheses of the joint hop -/

lemma issStmt_valid (s : SecM) (c : Bool) : ValidZK CrtGen.tables pIm (issStmt A s c) :=
  ⟨_, zkHypIm _ _ ⟨⟨_, _, _, by simp [nfBytes], by simp [rBytes], by simp [Adversary.cr,
    AdversaryM.int, ctxBytes], rfl, rfl⟩, by simp [Adversary.ci, AdversaryM.int, ctxBytes]⟩⟩

lemma redStmt_valid (P : RedeemPt) (hr : P.tok.r.length = rBytes) (hs : P.tok.s.length = uovN)
    (hn : P.tok.nf.length = nfBytes) : ∀ y ∈ redStmt A P, ValidZK CrtGen.tables pRm y := by
  intro y hy
  unfold redStmt at hy
  split at hy
  · cases hy
  · rename_i pk hk
    split_ifs at hy with he
    · cases hy
      exact ⟨_, zkHypRm _ _ ⟨⟨_, _, _, pk, hr, hs, hk, rfl, he⟩, P.anchors.valid.2.1, hn,
        by simp [xRM, Adversary.ci, AdversaryM.int, ctxBytes],
        by simp [xRM, Adversary.cr, AdversaryM.int, ctxBytes]⟩⟩
    · cases hy

lemma issM_wf (s : SecM) (c : Bool) (o : Option Out) :
    (issM A s c o).1.r.length = rBytes ∧ (issM A s c o).1.nf.length = nfBytes := by
  simp [issM, rBytes, nfBytes]

lemma ptM_valid (b : Bool) (s : SecM) (o₁ o₂ : Option Out) (side : Bool) :
    ∀ y ∈ redStmt A (ptM A idx b s o₁ o₂ side), ValidZK CrtGen.tables pRm y := by
  have h := tokD_wf A.int (issM_wf A s false o₁) (issM_wf A s true o₂) (b ^^ side)
  exact redStmt_valid A _ h.1 h.2.1 h.2.2

lemma vcons_evM (hC : A.Cons) (b : Bool) :
    VCons (evM A idx b) (rM₁ A idx b) (rM₂ A idx b) (rM₃ A idx b) (rM₄ A idx b) := by
  refine ⟨fun s o₁ o₂ o₃ o₄ v₁ v₂ v₃ v₄ g h => ?_, fun s o₁ o₂ o₃ o₄ v₁ v₂ v₃ v₄ g h => ?_,
    fun s o₁ o₂ o₃ o₄ v₁ v₂ v₃ v₄ g h => ?_, fun s o₁ o₂ o₃ o₄ v₁ v₂ v₃ v₄ g h => ?_⟩
  · exact (hC (issM A s false o₁).2 (issM A s true o₂).2 (yM A idx b s o₁ o₂ o₃ o₄)).c₁ () o₁ o₂ o₃ o₄
      v₁ v₂ v₃ v₄ g h
  · exact (hC (issM A s false o₁).2 (issM A s true o₂).2 (yM A idx b s o₁ o₂ o₃ o₄)).c₂ () o₁ o₂ o₃ o₄
      v₁ v₂ v₃ v₄ g h
  · exact (hC (issM A s false o₁).2 (issM A s true o₂).2 (yM A idx b s o₁ o₂ o₃ o₄)).c₃ () o₁ o₂ o₃ o₄
      v₁ v₂ v₃ v₄ g h
  · exact (hC (issM A s false o₁).2 (issM A s true o₂).2 (yM A idx b s o₁ o₂ o₃ o₄)).c₄ () o₁ o₂ o₃ o₄
      v₁ v₂ v₃ v₄ g h

/-- **The joint hop in each world**: real against simulated, `4·εRF + 15·PU_b`. -/
theorem real_sim_main {q3 qE : ℕ} (hA : A.Budget q3 qE) (hC : A.Cons) (b : Bool) :
    |realMain A idx b - pr _ (ev (gameM A idx b) (simSlot pIm) (simSlot pIm) (simSlot pRm)
      (simSlot pRm) (evM A idx b))| ≤ 4 * εRF q3 qE + 15 * puTerm A idx b :=
  main_chain_le Hashes.shake CrtGen.tables mainP_pIm mainP_pIm mainP_pRm mainP_pRm (gameM A idx b)
    (evM A idx b) (rM₁ A idx b) (rM₂ A idx b) (rM₃ A idx b) (rM₄ A idx b) (vcons_evM A idx hC b)
    small_pIm small_pIm small_pRm small_pRm q3 qE
    (fun _ _ _ _ _ v₂ v₃ v₄ => hA.b₁ _ _ _ v₂ v₃ v₄) (fun _ _ _ _ _ v₁ v₃ v₄ => hA.b₂ _ _ _ v₁ v₃ v₄)
    (fun _ _ _ _ _ v₁ v₂ v₄ => hA.b₃ _ _ _ v₁ v₂ v₄) (fun _ _ _ _ _ v₁ v₂ v₃ => hA.b₄ _ _ _ v₁ v₂ v₃)
    (fun s y hy => by cases hy; exact issStmt_valid A s false)
    (fun s _ y hy => by cases hy; exact issStmt_valid A s true)
    (fun s o₁ o₂ => ptM_valid A idx b s o₁ o₂ false)
    (fun s o₁ o₂ _ => ptM_valid A idx b s o₁ o₂ true)

/-! ## With all proofs simulated: the game of `Moussaka.anonymity` at fixed tables -/

/-- The simulated issuance proof's bytes (the simulator ignores the instance). -/
noncomputable def simIM (_ : IssueInstance) (c : SimCoins pIm) : Bytes := pf (some (simulate pIm c))

/-- The simulated redemption proof's bytes. -/
noncomputable def simRM (_ : RedeemInstance) (c : SimCoins pRm) : Bytes :=
  pf (some (simulate pRm c))

lemma redOut_sim (v : VisM) (P : RedeemPt) (c : SimCoins pRm) :
    redOut A P ((redStmt A P).map fun _ => simulate pRm c) = redSim (A.atV v) simRM c P := by
  unfold redOut redStmt redSim
  rcases P.anchors.keys[P.i]? with _ | pk
  · rfl
  · dsimp only
    split_ifs with h1 h2 h2
    · rfl
    · exact absurd h1 h2
    · exact absurd h2 h1
    · rfl

/-- The simulated game's tape, regrouped: the tables, then `Moussaka.simGame`'s tape. -/
def regroupM : SecM × (simSlot pIm).K × (simSlot pIm).K × (simSlot pRm).K × (simSlot pRm).K ≃ VisM × (((Coins nfBytes × Coins rBytes × SimCoins pIm) ×
      (Coins nfBytes × Coins rBytes × SimCoins pIm)) × (SimCoins pRm × SimCoins pRm)) where
  toFun x := ((x.2.1.2, x.2.2.1.2, x.2.2.2.1.2, x.2.2.2.2.2),
    (((x.1.1.1, x.1.1.2, x.2.1.1), (x.1.2.1, x.1.2.2, x.2.2.1.1)), (x.2.2.2.1.1, x.2.2.2.2.1)))
  invFun y := (((y.2.1.1.1, y.2.1.1.2.1), (y.2.1.2.1, y.2.1.2.2.1)), (y.2.1.1.2.2, y.1.1),
    (y.2.1.2.2.2, y.1.2.1), (y.2.2.1, y.1.2.2.1), (y.2.2.2, y.1.2.2.2))
  left_inv _ := rfl
  right_inv _ := rfl

/-- **With all four proofs simulated, the game is `Moussaka.simGame` of the adversary at the tables**
(which are then independent of everything else). -/
theorem sim_eq (b : Bool) :
    pr _ (ev (gameM A idx b) (simSlot pIm) (simSlot pIm) (simSlot pRm) (simSlot pRm) (evM A idx b)) =
      @pr (VisM × (((Coins nfBytes × Coins rBytes × SimCoins pIm) ×
        (Coins nfBytes × Coins rBytes × SimCoins pIm)) × (SimCoins pRm × SimCoins pRm)))
        (@instFintypeProd _ _ _ _)
        (fun z => simGame (A.atV z.1) idx simIM simRM b z.2) := by
  rw [← @pr_equiv _ _ _ (@instFintypeProd _ _ _ _) regroupM]
  refine pr_congr fun x => ?_
  show A.guess _ _ (yM A idx b x.1 _ _ _ _) _ ↔ _
  unfold yM
  simp only [gameM, Slot.out, simSlot]
  rw [redOut_sim A (x.2.1.2, x.2.2.1.2, x.2.2.2.1.2, x.2.2.2.2.2),
    redOut_sim A (x.2.1.2, x.2.2.1.2, x.2.2.2.1.2, x.2.2.2.2.2)]
  rfl

/-! ## Issuer hiding and unlinkability on `main` -/

/-- **Theorem 4(a) on `main` (no label rows), under (PU).** For the colluding adversary with the
tables (`H₃` and cipher budgets `q3`, `qE`, consistent `H₅` read sets), if every hiding reduction
of the adversary at fixed tables has advantage at most `εhide`, the two worlds of the real game on
`main` differ by at most

    8·εRF(q3, qE) + 15·(puTerm 0 + puTerm 1) + 2·εhide

where `puTerm b` is the (PU) event of world `b` on simulated proofs (`puTerm`). -/
theorem anonymity_main {q3 qE : ℕ} (hA : A.Budget q3 qE) (hC : A.Cons) {εhide : ℝ}
    (hhide : ∀ v b c, hidingAdv (A.atV v).ci (A.atV v).cr
      (reduction (A.atV v) idx simIM simRM b c) ≤ εhide) :
    |realMain A idx false - realMain A idx true| ≤
      8 * εRF q3 qE + 15 * (puTerm A idx false + puTerm A idx true) + 2 * εhide := by
  have r0 := real_sim_main A idx hA hC false
  have r1 := real_sim_main A idx hA hC true
  rw [sim_eq] at r0 r1
  have h0 := avg_close (fun v => simGame (A.atV v) idx simIM simRM false)
    (fun v => idealGame (A.atV v) idx simIM simRM false)
    fun v => hiding_hop (A.atV v) idx simIM simRM false (hhide v false)
  have h1 := avg_close (fun v => simGame (A.atV v) idx simIM simRM true)
    (fun v => idealGame (A.atV v) idx simIM simRM true)
    fun v => hiding_hop (A.atV v) idx simIM simRM true (hhide v true)
  have e := avg_eq (fun v => idealGame (A.atV v) idx simIM simRM false)
    (fun v => idealGame (A.atV v) idx simIM simRM true) fun v => idealGame_eq (A.atV v) idx simIM simRM
  beta_reduce at h0 h1 e
  have := abs_sub_le_iff.1 r0; have := abs_sub_le_iff.1 r1; have := abs_sub_le_iff.1 h0
  have := abs_sub_le_iff.1 h1
  rw [abs_sub_le_iff]
  constructor <;> linarith

end VoleMole.Privacy.Moussaka
