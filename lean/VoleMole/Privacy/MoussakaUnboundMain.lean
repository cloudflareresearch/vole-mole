import VoleMole.Privacy.MoussakaMain
import VoleMole.Privacy.MoussakaUnboundLean

/-!
# Unbound Moussaka issuer hiding and unlinkability on `main` (Theorem U5(a)), under (PU)

`MoussakaUnbound.anonymity` (Theorem U5(a), `Privacy/MoussakaUnbound.lean`) assumes per-proof
zero knowledge of the two unbound relations, which holds only with dedicated label rows. On `main`
the unbound issuance and redemption witnesses both start with the token's opening `r`
(`r ‖ nf_key ‖ …`), and the CRT masks are taken from the witness, so the label term of each proof
is a prediction of `r` (UF6 of `security/moussaka-unbound.md`). Here U5(a) is proved for `main`'s
layout with the joint hop of `ZK/MainGame.lean` in place of the per-proof hops, as
`Privacy/MoussakaMain.lean` does for the bound protocol.

## The game (`realU`)

The colluding adversary of `MoussakaUnbound.Adversary` with **two redemption queries** (the game
has four proofs: two issuances and two redemptions; the joint hop of `ZK/MainGame.lean` is for four
proofs). It chooses `ctx_iss`, the keys, the responses and the queries from the issuance requests
without reading the tables, and its guess also sees the four proofs' `H₃`, `H₅` and cipher tables
(`VisU`). Each proof is the executable prover in the model of `zk_rom_ic` (`ZK.Sim.realSlot`) for
`main`'s statements (`stI`, `stR` with the parameters `pIu`, `pRu`: `labelRows = false`), run as in
`Spec/MoussakaUnbound.lean`: issuance requests `t ‖ π`, redemptions `Derive(nf_key, ctx_red) ‖ π`
when `find_issuer` succeeds (`redOutU`), and the guess as in `MoussakaUnbound.post` (the
redemptions are shown only if both tokens finalized, both are redeemable in both queried sets, and
the context rule holds).

## The bound (`anonymityU_main`)

    |Pr[world 0] − Pr[world 1]| ≤ 8·εRF(q₃, q_E) + 15·(PU₀ + PU₁) + 2·εprf

* `8·εRF`: H1–H4 for the four proofs of each world (`main_chain_le`);
* `PU_b` (`puTermU`): in world `b` with all four proofs simulated, some proof's witness prefix
  (the Client's opening `r`) is a candidate of the guess's `H₅` read set on that proof's table.
  `Privacy/MoussakaUnboundMainPU.lean` reduces it to the game `PU.puAdv` for `UCom`;
* `εprf`: the PRF advantage of `MoussakaUnbound.reduction` for the adversary at fixed tables
  (`prf_hop`, `idealGame_eq` of `Privacy/MoussakaUnbound.lean`, applied table by table).
-/

open Finset

-- (The coin types are large products: their `Fintype` instances exceed the default size.)
set_option synthInstance.maxSize 1024

set_option linter.unusedSectionVars false
set_option linter.constructorNameAsVariable false

namespace VoleMole.Privacy.MoussakaUnbound

open VoleMole.Spec VoleMole.Spec.MoussakaUnbound VoleMole.ZK.Sim VoleMole.Privacy.MainChain
open VoleMole.Verifier VoleMole.Verifier.Bridge
open VoleMole.Spec.Moussaka (NIZK AnchorSet Error ctxBytes proveSeedBytes rBytes nfBytes maxAnchors)
open VoleMole.Privacy.Moussaka (pf)

-- `UCom` and `Derive` evaluate Keccak-p[800]; nothing below needs to unfold them.
attribute [local irreducible] ucom derive UOVKey.eval
attribute [local irreducible] simulate proveIdeal proveE firstHit

/-! ## `main`'s statements -/

/-- The unbound issuance parameters on `main` (no label rows). -/
abbrev pIu : Params := { witnessBytes := 232, qsDegree := 9, labelRows := false }

/-- The unbound redemption parameters on `main`. -/
abbrev pRu : Params := { witnessBytes := 559, qsDegree := 9, labelRows := false }

lemma mainP_pIu : MainP pIu := ⟨rfl, by decide⟩
lemma mainP_pRu : MainP pRu := ⟨rfl, by decide⟩
lemma small_pIu : SmallParams pIu := smallParams_of_le (by decide) (by decide)
lemma small_pRu : SmallParams pRu := smallParams_of_le (by decide) (by decide)

/-- **`ZKHyp` for `main`'s unbound issuance statement.** -/
theorem zkHypIu (x : IssueInstance) (w : Spec.Bytes) (h : IssueRelW x w) :
    ZKHyp CrtGen.tables (withP (stI x) pIu) (toBA w) (csI x) :=
  let z := zkHypI x w h
  { hvals := z.hvals, hdeg := z.hdeg, hd := z.hd, hd' := z.hd', hsat := z.hsat, hw := z.hw,
    hnm := z.hnm, hT := z.hT, hI := z.hI }

/-- **`ZKHyp` for `main`'s unbound redemption statement.** -/
theorem zkHypRu (x : RedeemInstance) (w : Spec.Bytes) (h : RedeemRelW x w) :
    ZKHyp CrtGen.tables (withP (stR x) pRu) (toBA w) (csR x) :=
  let z := zkHypR x w h
  { hvals := z.hvals, hdeg := z.hdeg, hd := z.hd, hd' := z.hd', hsat := z.hsat, hw := z.hw,
    hnm := z.hnm, hT := z.hT, hI := z.hI }

/-! ## The adversary and the game -/

/-- The tables the guess sees: each proof's `H₃`, `H₅` and cipher (issuance 0, 1; queries 0, 1). -/
abbrev VisU := Vis pIu × Vis pIu × Vis pRu × Vis pRu

/-- **The colluding adversary on `main` with two redemption queries**: `Adversary 2`'s interaction
(not reading the tables) and a guess that also sees the four proofs' tables, with `H₅` read sets
`R₁ … R₄`. -/
structure AdversaryUM where
  ctxIss : Coins ctxBytes
  pk : Bool → UOVKey
  respond : Bytes → Bytes → Bool → Coins uovN
  queries : Bytes → Bytes → Fin 2 → Query
  guess : Bytes → Bytes → Option (Fin 2 → Except Error Bytes) → VisU → Prop
  R₁ : Bytes → Bytes → Option (Fin 2 → Except Error Bytes) → VisU → Finset (SKey pIu)
  R₂ : Bytes → Bytes → Option (Fin 2 → Except Error Bytes) → VisU → Finset (SKey pIu)
  R₃ : Bytes → Bytes → Option (Fin 2 → Except Error Bytes) → VisU → Finset (SKey pRu)
  R₄ : Bytes → Bytes → Option (Fin 2 → Except Error Bytes) → VisU → Finset (SKey pRu)

namespace AdversaryUM

variable (A : AdversaryUM)

/-- The adversary with its guess at fixed tables. -/
def atV (v : VisU) : Adversary 2 :=
  ⟨A.ctxIss, A.pk, A.respond, A.queries, fun q₀ q₁ y => A.guess q₀ q₁ y v⟩

/-- Its interaction (the guess is not used). -/
def int : Adversary 2 := ⟨A.ctxIss, A.pk, A.respond, A.queries, fun _ _ _ => True⟩

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

end AdversaryUM

variable (A : AdversaryUM)

/-- The two Clients' `(nf_key, r)`. -/
abbrev SecU := (Coins nfKeyBytes × Coins rBytes) × (Coins nfKeyBytes × Coins rBytes)

/-- Client `c`'s commitment. -/
def tUM (s : SecU) (c : Bool) : Bytes :=
  ucom (List.ofFn (bif c then s.2 else s.1).1) A.int.ci (List.ofFn (bif c then s.2 else s.1).2)

/-- Client `c`'s issuance output, with the proof `o`. -/
def issU (s : SecU) (c : Bool) (o : Option Out) : PendingToken × Bytes :=
  (⟨List.ofFn (bif c then s.2 else s.1).1, List.ofFn (bif c then s.2 else s.1).2, A.int.ci,
    tUM A s c⟩, tUM A s c ++ pf o)

/-- Client `c`'s issuance statement and witness. -/
def issStmtU (s : SecU) (c : Bool) : SW :=
  (stI ⟨tUM A s c, A.int.ci⟩, toBA (encodeIssueWitness (List.ofFn (bif c then s.2 else s.1).1)
    A.int.ci (List.ofFn (bif c then s.2 else s.1).2)))

/-- The redemption instance at a redemption point. -/
def xRU (P : RedeemPt) : RedeemInstance :=
  ⟨P.anchors.keys, derive P.tok.k P.ctxRed, A.int.ci, P.ctxRed, P.cd⟩

/-- **The redemption statement and witness**, at the index `find_issuer` returns
(`redeemRequestOf`); none if it fails. -/
def redStmtU (P : RedeemPt) : Option SW :=
  (findIssuer P.anchors (ucom P.tok.k A.int.ci P.tok.r) P.tok.s).map fun i =>
    (stR (xRU A P), toBA (encodeRedeemWitness P.tok.k A.int.ci P.ctxRed P.tok.r P.tok.s i))

/-- **The redemption output** (`redeemRequestOf`, with the proof `o`). -/
def redOutU (P : RedeemPt) (o : Option Out) : Except Error Bytes :=
  match findIssuer P.anchors (ucom P.tok.k A.int.ci P.tok.r) P.tok.s with
  | none => .error .invalidToken
  | some _ => .ok (derive P.tok.k P.ctxRed ++ pf o)

/-- Query `j`'s redemption point in world `b`. -/
def ptU (b : Bool) (s : SecU) (o₁ o₂ : Option Out) (j : Fin 2) : RedeemPt :=
  pt A.int b (issU A s false o₁) (issU A s true o₂) j

/-- **The game of world `b`**, as four proofs in sequence. -/
def gameU (b : Bool) : Game SecU Out SW SW SW SW where
  σ₁ s := some (issStmtU A s false)
  σ₂ s _ := some (issStmtU A s true)
  σ₃ s o₁ o₂ := redStmtU A (ptU A b s o₁ o₂ 0)
  σ₄ s o₁ o₂ _ := redStmtU A (ptU A b s o₁ o₂ 1)

/-- The guess's third input in world `b`: the two redemptions, if the game's rule allows them. -/
def yU (b : Bool) (s : SecU) (o₁ o₂ o₃ o₄ : Option Out) : Option (Fin 2 → Except Error Bytes) :=
  bif allOk A.int (issU A s false o₁) (issU A s true o₂) then
    some ![redOutU A (ptU A b s o₁ o₂ 0) o₃, redOutU A (ptU A b s o₁ o₂ 1) o₄]
  else none

/-- **The final event of world `b`.** -/
def evU (b : Bool) : Ev SecU Out (Vis pIu) (Vis pIu) (Vis pRu) (Vis pRu) :=
  fun s o₁ o₂ o₃ o₄ v₁ v₂ v₃ v₄ =>
    A.guess (issU A s false o₁).2 (issU A s true o₂).2 (yU A b s o₁ o₂ o₃ o₄) (v₁, v₂, v₃, v₄)

/-- The `H₅` read sets of the final event. -/
def rU₁ (b : Bool) : RSet SecU Out (Vis pIu) (Vis pIu) (Vis pRu) (Vis pRu) (SKey pIu) :=
  fun s o₁ o₂ o₃ o₄ v₁ v₂ v₃ v₄ =>
    A.R₁ (issU A s false o₁).2 (issU A s true o₂).2 (yU A b s o₁ o₂ o₃ o₄) (v₁, v₂, v₃, v₄)
def rU₂ (b : Bool) : RSet SecU Out (Vis pIu) (Vis pIu) (Vis pRu) (Vis pRu) (SKey pIu) :=
  fun s o₁ o₂ o₃ o₄ v₁ v₂ v₃ v₄ =>
    A.R₂ (issU A s false o₁).2 (issU A s true o₂).2 (yU A b s o₁ o₂ o₃ o₄) (v₁, v₂, v₃, v₄)
def rU₃ (b : Bool) : RSet SecU Out (Vis pIu) (Vis pIu) (Vis pRu) (Vis pRu) (SKey pRu) :=
  fun s o₁ o₂ o₃ o₄ v₁ v₂ v₃ v₄ =>
    A.R₃ (issU A s false o₁).2 (issU A s true o₂).2 (yU A b s o₁ o₂ o₃ o₄) (v₁, v₂, v₃, v₄)
def rU₄ (b : Bool) : RSet SecU Out (Vis pIu) (Vis pIu) (Vis pRu) (Vis pRu) (SKey pRu) :=
  fun s o₁ o₂ o₃ o₄ v₁ v₂ v₃ v₄ =>
    A.R₄ (issU A s false o₁).2 (issU A s true o₂).2 (yU A b s o₁ o₂ o₃ o₄) (v₁, v₂, v₃, v₄)

variable [HasPrg]

/-- **The real game on `main`** in world `b`: the executable prover (`main`'s unbound statements)
in the model of `zk_rom_ic`, with SHAKE (`Hashes.shake`) for the hashes that are not tables. -/
noncomputable def realU (b : Bool) : ℝ :=
  pr _ (ev (gameU A b) (realSlot Hashes.shake CrtGen.tables pIu)
    (realSlot Hashes.shake CrtGen.tables pIu) (realSlot Hashes.shake CrtGen.tables pRu)
    (realSlot Hashes.shake CrtGen.tables pRu) (evU A b))

/-- **The (PU) term of world `b`**: in the game with all four proofs simulated, some proof's witness
prefix is a candidate of the guess's `H₅` read set on that proof's table (`ZK.Sim.predAll`). -/
noncomputable def puTermU (b : Bool) : ℝ :=
  pr _ (ev (gameU A b) (simP pIu) (simP pIu) (simP pRu) (simP pRu)
    (predAll Hashes.shake CrtGen.tables mainP_pIu mainP_pIu mainP_pRu mainP_pRu
      (rU₁ A b) (rU₂ A b) (rU₃ A b) (rU₄ A b)))

/-! ## The hypotheses of the joint hop -/

lemma issStmtU_valid (s : SecU) (c : Bool) : ValidZK CrtGen.tables pIu (issStmtU A s c) :=
  ⟨_, zkHypIu _ _ ⟨⟨_, _, by simp [nfKeyBytes], by simp [rBytes], rfl, rfl⟩,
    by simp [Adversary.ci, AdversaryUM.int, ctxBytes]⟩⟩

lemma redStmtU_valid (P : RedeemPt) (hp : tokWF P.tok) (hc : P.ctxRed.length = ctxBytes) :
    ∀ y ∈ redStmtU A P, ValidZK CrtGen.tables pRu y := by
  intro y hy
  unfold redStmtU at hy
  cases hf : findIssuer P.anchors (ucom P.tok.k A.int.ci P.tok.r) P.tok.s with
  | none => rw [hf] at hy; cases hy
  | some i =>
    rw [hf] at hy
    cases hy
    obtain ⟨pk, hk, he⟩ := findIssuer_some hf
    exact ⟨_, zkHypRu _ _ ⟨⟨_, _, _, i, pk, hp.1, hp.2.1, hp.2.2, hk, rfl, he, rfl⟩,
      P.anchors.valid.2.1, length_derive _ _, by simp [xRU, Adversary.ci, AdversaryUM.int, ctxBytes],
      hc⟩⟩

lemma issU_wf (s : SecU) (c : Bool) (o : Option Out) :
    (issU A s c o).1.k.length = nfKeyBytes ∧ (issU A s c o).1.r.length = rBytes := by
  simp [issU, rBytes, nfKeyBytes]

lemma ptU_valid (b : Bool) (s : SecU) (o₁ o₂ : Option Out) (j : Fin 2) :
    ∀ y ∈ redStmtU A (ptU A b s o₁ o₂ j), ValidZK CrtGen.tables pRu y :=
  redStmtU_valid A _ (tokD_wf A.int (issU_wf A s false o₁) (issU_wf A s true o₂) _)
    (by simp [ptU, pt, ctxBytes])

lemma vcons_evU (hC : A.Cons) (b : Bool) :
    VCons (evU A b) (rU₁ A b) (rU₂ A b) (rU₃ A b) (rU₄ A b) := by
  refine ⟨fun s o₁ o₂ o₃ o₄ v₁ v₂ v₃ v₄ g h => ?_, fun s o₁ o₂ o₃ o₄ v₁ v₂ v₃ v₄ g h => ?_,
    fun s o₁ o₂ o₃ o₄ v₁ v₂ v₃ v₄ g h => ?_, fun s o₁ o₂ o₃ o₄ v₁ v₂ v₃ v₄ g h => ?_⟩
  · exact (hC (issU A s false o₁).2 (issU A s true o₂).2 (yU A b s o₁ o₂ o₃ o₄)).c₁ () o₁ o₂ o₃ o₄
      v₁ v₂ v₃ v₄ g h
  · exact (hC (issU A s false o₁).2 (issU A s true o₂).2 (yU A b s o₁ o₂ o₃ o₄)).c₂ () o₁ o₂ o₃ o₄
      v₁ v₂ v₃ v₄ g h
  · exact (hC (issU A s false o₁).2 (issU A s true o₂).2 (yU A b s o₁ o₂ o₃ o₄)).c₃ () o₁ o₂ o₃ o₄
      v₁ v₂ v₃ v₄ g h
  · exact (hC (issU A s false o₁).2 (issU A s true o₂).2 (yU A b s o₁ o₂ o₃ o₄)).c₄ () o₁ o₂ o₃ o₄
      v₁ v₂ v₃ v₄ g h

/-- **The joint hop in each world**: real against simulated, `4·εRF + 15·PU_b`. -/
theorem real_sim_U {q3 qE : ℕ} (hA : A.Budget q3 qE) (hC : A.Cons) (b : Bool) :
    |realU A b - pr _ (ev (gameU A b) (simSlot pIu) (simSlot pIu) (simSlot pRu)
      (simSlot pRu) (evU A b))| ≤ 4 * εRF q3 qE + 15 * puTermU A b :=
  main_chain_le Hashes.shake CrtGen.tables mainP_pIu mainP_pIu mainP_pRu mainP_pRu (gameU A b)
    (evU A b) (rU₁ A b) (rU₂ A b) (rU₃ A b) (rU₄ A b) (vcons_evU A hC b)
    small_pIu small_pIu small_pRu small_pRu q3 qE
    (fun _ _ _ _ _ v₂ v₃ v₄ => hA.b₁ _ _ _ v₂ v₃ v₄) (fun _ _ _ _ _ v₁ v₃ v₄ => hA.b₂ _ _ _ v₁ v₃ v₄)
    (fun _ _ _ _ _ v₁ v₂ v₄ => hA.b₃ _ _ _ v₁ v₂ v₄) (fun _ _ _ _ _ v₁ v₂ v₃ => hA.b₄ _ _ _ v₁ v₂ v₃)
    (fun s y hy => by cases hy; exact issStmtU_valid A s false)
    (fun s _ y hy => by cases hy; exact issStmtU_valid A s true)
    (fun s o₁ o₂ => ptU_valid A b s o₁ o₂ 0)
    (fun s o₁ o₂ _ => ptU_valid A b s o₁ o₂ 1)

/-! ## With all proofs simulated: the game of `MoussakaUnbound.anonymity` at fixed tables -/

/-- The simulated issuance proof's bytes (the simulator ignores the instance). -/
noncomputable def simIU (_ : IssueInstance) (c : SimCoins pIu) : Bytes := pf (some (simulate pIu c))

/-- The simulated redemption proof's bytes. -/
noncomputable def simRU (_ : RedeemInstance) (c : SimCoins pRu) : Bytes :=
  pf (some (simulate pRu c))

lemma redOutU_sim (v : VisU) (P : RedeemPt) (c : SimCoins pRu) :
    redOutU A P ((redStmtU A P).map fun _ => simulate pRu c) = redSim (A.atV v) simRU c P := by
  unfold redOutU redStmtU redSim
  rw [show (A.atV v).ci = A.int.ci from rfl]
  cases findIssuer P.anchors (ucom P.tok.k A.int.ci P.tok.r) P.tok.s <;> rfl

/-- The simulated game's tape, regrouped: the tables, then `MoussakaUnbound.simGame`'s tape. -/
def regroupU : SecU × (simSlot pIu).K × (simSlot pIu).K × (simSlot pRu).K × (simSlot pRu).K ≃
    VisU × (((Coins nfKeyBytes × Coins rBytes × SimCoins pIu) ×
      (Coins nfKeyBytes × Coins rBytes × SimCoins pIu)) × (Fin 2 → SimCoins pRu)) where
  toFun x := ((x.2.1.2, x.2.2.1.2, x.2.2.2.1.2, x.2.2.2.2.2),
    (((x.1.1.1, x.1.1.2, x.2.1.1), (x.1.2.1, x.1.2.2, x.2.2.1.1)), ![x.2.2.2.1.1, x.2.2.2.2.1]))
  invFun y := (((y.2.1.1.1, y.2.1.1.2.1), (y.2.1.2.1, y.2.1.2.2.1)), (y.2.1.1.2.2, y.1.1),
    (y.2.1.2.2.2, y.1.2.1), (y.2.2 0, y.1.2.2.1), (y.2.2 1, y.1.2.2.2))
  left_inv _ := rfl
  right_inv y := by
    refine Prod.ext rfl (Prod.ext rfl ?_)
    funext j
    fin_cases j <;> rfl

/-- **With all four proofs simulated, the game is `MoussakaUnbound.simGame` of the adversary at the
tables** (which are then independent of everything else). -/
theorem simU_eq (b : Bool) :
    pr _ (ev (gameU A b) (simSlot pIu) (simSlot pIu) (simSlot pRu) (simSlot pRu) (evU A b)) =
      @pr (VisU × (((Coins nfKeyBytes × Coins rBytes × SimCoins pIu) ×
        (Coins nfKeyBytes × Coins rBytes × SimCoins pIu)) × (Fin 2 → SimCoins pRu)))
        (@instFintypeProd _ _ _ _)
        (fun z => simGame (A.atV z.1) simIU simRU b z.2) := by
  rw [← @pr_equiv _ _ _ (@instFintypeProd _ _ _ _) regroupU]
  refine pr_congr fun x => ?_
  show A.guess _ _ (yU A b x.1 _ _ _ _) _ ↔ _
  unfold yU
  simp only [gameU, Slot.out, simSlot]
  rw [redOutU_sim A (x.2.1.2, x.2.2.1.2, x.2.2.2.1.2, x.2.2.2.2.2),
    redOutU_sim A (x.2.1.2, x.2.2.1.2, x.2.2.2.1.2, x.2.2.2.2.2)]
  refine iff_of_eq ?_
  have e : ∀ f : Fin 2 → Except Error Bytes, (some ![f 0, f 1] : Option _) = some f := fun f => by
    congr 1; funext j; fin_cases j <;> rfl
  exact congrArg (fun y => A.guess _ _ y _) (congrArg (fun y => bif _ then y else none)
    (e fun j => redSim (A.atV (regroupU x).1) simRU ((regroupU x).2.2 j)
      (pt (A.atV (regroupU x).1) b (issSim (A.atV (regroupU x).1) simIU (regroupU x).2.1.1)
        (issSim (A.atV (regroupU x).1) simIU (regroupU x).2.1.2) j)))

/-! ## Theorem U5(a) on `main` -/

/-- **Theorem U5(a) on `main` (no label rows), under (PU), with two redemption queries.** For the
colluding adversary with the tables (`H₃` and cipher budgets `q3`, `qE`, consistent `H₅` read
sets), if every PRF reduction of the adversary at fixed tables has advantage at most `εprf`, the two
worlds of the real game on `main` differ by at most

    8·εRF(q3, qE) + 15·(puTermU 0 + puTermU 1) + 2·εprf

where `puTermU b` is the (PU) event of world `b` on simulated proofs. -/
theorem anonymityU_main {q3 qE : ℕ} (hA : A.Budget q3 qE) (hC : A.Cons) {εprf : ℝ}
    (hprf : ∀ v b cc, prfAdv (A.atV v).ci (reduction (A.atV v) simIU simRU b cc) ≤ εprf) :
    |realU A false - realU A true| ≤
      8 * εRF q3 qE + 15 * (puTermU A false + puTermU A true) + 2 * εprf := by
  have r0 := real_sim_U A hA hC false
  have r1 := real_sim_U A hA hC true
  rw [simU_eq] at r0 r1
  have h0 := avg_close (fun v => simGame (A.atV v) simIU simRU false)
    (fun v => idealGame (A.atV v) simIU simRU false)
    fun v => prf_hop (A.atV v) simIU simRU false (hprf v false)
  have h1 := avg_close (fun v => simGame (A.atV v) simIU simRU true)
    (fun v => idealGame (A.atV v) simIU simRU true)
    fun v => prf_hop (A.atV v) simIU simRU true (hprf v true)
  have e := avg_eq (fun v => idealGame (A.atV v) simIU simRU false)
    (fun v => idealGame (A.atV v) simIU simRU true) fun v => idealGame_eq (A.atV v) simIU simRU
  beta_reduce at h0 h1 e
  have := abs_sub_le_iff.1 r0; have := abs_sub_le_iff.1 r1; have := abs_sub_le_iff.1 h0
  have := abs_sub_le_iff.1 h1
  rw [abs_sub_le_iff]
  constructor <;> linarith

end VoleMole.Privacy.MoussakaUnbound
