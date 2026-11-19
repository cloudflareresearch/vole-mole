import VoleMole.Privacy.MoussakaUnboundMainPU
import VoleMole.Privacy.MoussakaUnboundNC

/-!
# Unbound Moussaka against a non-colluding Moderator on `main` (Theorem U5(b)), two queries

`MoussakaUnbound.anonymityNC` (Theorem U5(b), corrected, `Privacy/MoussakaUnboundNC.lean`) takes
per-proof zero knowledge of the redemption proofs, which holds only with dedicated label rows.
Here the game is run on `main`: the two redemption proofs are the executable prover with `main`'s
layout (`pRu`, no label rows) in the model of `zk_rom_ic` with per-proof tables, and the joint hop
of `ZK/MainGame.lean` replaces both at once. As for the bound protocol's 4(b') on `main`
(`Privacy/MoussakaNCMain.lean`), **the (PU) term is statistical**: the Moderator sees no
issuance, so the view depends on the Clients' openings only through the refusal bit.

## The game (`realNU`)

The Moderator (`AdversaryUNC`) chooses `ctx_iss`, the two issuing keys and **two adaptive
redemption queries** (`next`: the second is chosen from the first query and its answer); it does
not read the tables, and its guess sees the history (or `none` if a token did not finalize) and the
two redemption proofs' tables. Honest Anchors answer with `unbound_issue_response` (the issuance
proof system `PI` stays abstract: the issuance proofs are never shown). Four slots of a
`MainChain.Game`: the first two prove nothing, the third and fourth are the two queries, each
proved iff both tokens finalized and the query is valid (`validNC`: both tokens redeemable in its
set, and the context rule). Every queried Anchor Set must contain both issuers (`Contains`), as in
`anonymityNC`.

## The steps

1. The joint hop (`real_sim_NU`, `main_chain_le`): `4·εRF + 15·PU_b`.
2. **The (PU) term is statistical** (`puTermNU_le`): with both proofs simulated and both tokens
   finalized, the history is `hNC`'s, a function of the keys and the simulators' coins
   (`yNU_sim_good`, from `simNC_iff`), and so are the redemption statements; each proof's witness
   prefix is the answering Client's opening, uniform and independent of them. So
   `PU_b ≤ 4·(q₅ + 1)·2⁻¹²⁸` (`pr_mem_uniform_le`). No assumption on `UCom`.
3. With both proofs simulated, the game is `simGameNC` at fixed tables (`simNU_eq`), and the abort
   hop, the PRF hop and the swap of `anonymityNC` finish, table by table.

## The bound (`anonymityNC_main_U`)

    |Pr[W₀] − Pr[W₁]| ≤ 8·εRF(q₃, q_E) + 15·4·(q₅ + 1)·2⁻¹²⁸ + 2·(ψ false + ψ true) + 2·εprf
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

/-! ## The Moderator on `main` -/

/-- The redemption proofs' tables. -/
abbrev VisR := Vis pRu × Vis pRu

/-- **The non-colluding Moderator on `main`**: `ctx_iss`, the two issuing keys, the two adaptive
queries (`next`, not reading the tables), and a guess that sees the history and the two
redemption proofs' tables, with `H₅` read sets `R₃`, `R₄`. -/
structure AdversaryUNC where
  ctxIss : Coins ctxBytes
  pk : Bool → UOVKey
  next : Hist → Query
  guess : Option Hist → VisR → Prop
  R₃ : Option Hist → VisR → Finset (SKey pRu)
  R₄ : Option Hist → VisR → Finset (SKey pRu)

namespace AdversaryUNC

variable (A : AdversaryUNC)

/-- The Moderator with its guess at fixed tables. -/
def atV (v : VisR) : AdversaryNC := ⟨A.ctxIss, A.pk, A.next, fun h => A.guess h v⟩

/-- Its contexts, keys and queries (the guess is not used). -/
def nc : AdversaryNC := ⟨A.ctxIss, A.pk, A.next, fun _ => True⟩

/-- The same as an `AdversaryUM` (for `main`'s redemption statements `redStmtU`, `redOutU`). -/
def um : AdversaryUM :=
  ⟨A.ctxIss, A.pk, fun _ _ _ => 0, fun _ _ _ => A.next [], fun _ _ _ _ => True,
    fun _ _ _ _ => ∅, fun _ _ _ _ => ∅, fun _ _ _ _ => ∅, fun _ _ _ _ => ∅⟩

/-- **The guess's budget**: it reads each redemption proof's `H₃` table at `q3` and cipher at `qE`
keys. -/
structure Budget (q3 qE : ℕ) : Prop where
  b₃ : ∀ y v₄, RdV q3 qE fun v₃ => A.guess y (v₃, v₄)
  b₄ : ∀ y v₃, RdV q3 qE fun v₄ => A.guess y (v₃, v₄)

/-- **Consistent `H₅` read sets** (`ZK.Sim.VCons` for the guess, the history fixed; the issuance
slots' tables are not read). -/
def Cons : Prop :=
  ∀ y, VCons (S := Unit) (p₁ := pIu) (p₂ := pIu) (fun _ _ _ _ _ _ _ v₃ v₄ => A.guess y (v₃, v₄))
    (fun _ _ _ _ _ _ _ _ _ => ∅) (fun _ _ _ _ _ _ _ _ _ => ∅)
    (fun _ _ _ _ _ _ _ v₃ v₄ => A.R₃ y (v₃, v₄)) (fun _ _ _ _ _ _ _ v₃ v₄ => A.R₄ y (v₃, v₄))

end AdversaryUNC

/-- A reader that does not read its table. -/
lemma rdV_constU {p : Params} (q3 qE : ℕ) (P : Prop) : RdV (p := p) q3 qE fun _ => P :=
  ⟨⟨fun _ _ _ => ∅, fun _ _ _ => by simp, fun _ _ _ _ _ => Iff.rfl⟩,
    ⟨fun _ _ _ => ∅, fun _ _ _ => by simp, fun _ _ _ _ _ => Iff.rfl⟩⟩

variable (A : AdversaryUNC) (PI : NIZK IssueInstance) (sk : Bool → Signer)

/-! ## The game -/

/-- The two Clients' issuance tapes `(nf_key, r, ρ_iss)`. -/
abbrev SecN := IssT × IssT

/-- **The refusal bit**: both Clients' tokens finalized. -/
def gN (s : SecN) : Bool :=
  (tokNC A.nc PI sk false s.1).isSome && (tokNC A.nc PI sk true s.2).isSome

/-- The answer to query `q` after history `H` in world `b`, with the proof `o`. -/
def ansN (b : Bool) (s : SecN) (H : Hist) (q : Query) (o : Option Out) : Except Error Bytes :=
  if validNC A.nc PI sk s.1 s.2 H q then redOutU A.um (ptNC A.nc PI sk b s.1 s.2 q) o else refused

/-- The history after the first query. -/
def hist₁ (b : Bool) (s : SecN) (o₃ : Option Out) : Hist :=
  [] ++ [(A.next [], ansN A PI sk b s [] (A.next []) o₃)]

/-- The second query. -/
def qN₁ (b : Bool) (s : SecN) (o₃ : Option Out) : Query := A.next (hist₁ A PI sk b s o₃)

/-- The history after both queries. -/
def histN (b : Bool) (s : SecN) (o₃ o₄ : Option Out) : Hist :=
  hist₁ A PI sk b s o₃ ++ [(qN₁ A PI sk b s o₃, ansN A PI sk b s (hist₁ A PI sk b s o₃)
    (qN₁ A PI sk b s o₃) o₄)]

/-- **The game of world `b`**: no issuance slot, the two queries if both tokens finalized and the
query is valid. -/
def gameNU (b : Bool) : Game SecN Out SW SW SW SW where
  σ₁ _ := none
  σ₂ _ _ := none
  σ₃ s _ _ := bif gN A PI sk s && validNC A.nc PI sk s.1 s.2 [] (A.next []) then
    redStmtU A.um (ptNC A.nc PI sk b s.1 s.2 (A.next [])) else none
  σ₄ s _ _ o₃ := bif gN A PI sk s && validNC A.nc PI sk s.1 s.2 (hist₁ A PI sk b s o₃)
      (qN₁ A PI sk b s o₃) then
    redStmtU A.um (ptNC A.nc PI sk b s.1 s.2 (qN₁ A PI sk b s o₃)) else none

/-- What the guess gets besides the tables: the history, or `none`. -/
def yNU (b : Bool) (s : SecN) (o₃ o₄ : Option Out) : Option Hist :=
  bif gN A PI sk s then some (histN A PI sk b s o₃ o₄) else none

/-- **The final event of world `b`.** -/
def evNU (b : Bool) : Ev SecN Out (Vis pIu) (Vis pIu) (Vis pRu) (Vis pRu) :=
  fun s _ _ o₃ o₄ _ _ v₃ v₄ => A.guess (yNU A PI sk b s o₃ o₄) (v₃, v₄)

/-- The `H₅` read sets of the final event. -/
def rNU₁ : RSet SecN Out (Vis pIu) (Vis pIu) (Vis pRu) (Vis pRu) (SKey pIu) :=
  fun _ _ _ _ _ _ _ _ _ => ∅
def rNU₂ : RSet SecN Out (Vis pIu) (Vis pIu) (Vis pRu) (Vis pRu) (SKey pIu) :=
  fun _ _ _ _ _ _ _ _ _ => ∅
def rNU₃ (b : Bool) : RSet SecN Out (Vis pIu) (Vis pIu) (Vis pRu) (Vis pRu) (SKey pRu) :=
  fun s _ _ o₃ o₄ _ _ v₃ v₄ => A.R₃ (yNU A PI sk b s o₃ o₄) (v₃, v₄)
def rNU₄ (b : Bool) : RSet SecN Out (Vis pIu) (Vis pIu) (Vis pRu) (Vis pRu) (SKey pRu) :=
  fun s _ _ o₃ o₄ _ _ v₃ v₄ => A.R₄ (yNU A PI sk b s o₃ o₄) (v₃, v₄)

variable [HasPrg]

/-- **The real game on `main`** in world `b`: the executable prover for the two redemptions. -/
noncomputable def realNU (b : Bool) : ℝ :=
  pr _ (ev (gameNU A PI sk b) (realSlot Hashes.shake CrtGen.tables pIu)
    (realSlot Hashes.shake CrtGen.tables pIu) (realSlot Hashes.shake CrtGen.tables pRu)
    (realSlot Hashes.shake CrtGen.tables pRu) (evNU A PI sk b))

/-- **The (PU) term of world `b`**, on simulated proofs. -/
noncomputable def puTermNU (b : Bool) : ℝ :=
  pr _ (ev (gameNU A PI sk b) (simP pIu) (simP pIu) (simP pRu) (simP pRu)
    (predAll Hashes.shake CrtGen.tables mainP_pIu mainP_pIu mainP_pRu mainP_pRu
      rNU₁ rNU₂ (rNU₃ A PI sk b) (rNU₄ A PI sk b)))

/-! ## The joint hop -/

lemma redStmtNU_valid (hsk : ∀ c, (sk c).Correct (A.pk c)) (b : Bool) (s : SecN) (q : Query) :
    ∀ y ∈ redStmtU A.um (ptNC A.nc PI sk b s.1 s.2 q), ValidZK CrtGen.tables pRu y :=
  redStmtU_valid A.um _ (by
    unfold ptNC
    cases who b q
    · exact tokDNC_wf A.nc PI sk hsk false s.1
    · exact tokDNC_wf A.nc PI sk hsk true s.2) (by simp [ptNC, ctxBytes])

lemma vcons_evNU (hC : A.Cons) (b : Bool) :
    VCons (evNU A PI sk b) rNU₁ rNU₂ (rNU₃ A PI sk b) (rNU₄ A PI sk b) := by
  refine ⟨fun s o₁ o₂ o₃ o₄ v₁ v₂ v₃ v₄ g h => ?_, fun s o₁ o₂ o₃ o₄ v₁ v₂ v₃ v₄ g h => ?_,
    fun s o₁ o₂ o₃ o₄ v₁ v₂ v₃ v₄ g h => ?_, fun s o₁ o₂ o₃ o₄ v₁ v₂ v₃ v₄ g h => ?_⟩
  · exact (hC (yNU A PI sk b s o₃ o₄)).c₁ () o₁ o₂ o₃ o₄ v₁ v₂ v₃ v₄ g h
  · exact (hC (yNU A PI sk b s o₃ o₄)).c₂ () o₁ o₂ o₃ o₄ v₁ v₂ v₃ v₄ g h
  · exact (hC (yNU A PI sk b s o₃ o₄)).c₃ () o₁ o₂ o₃ o₄ v₁ v₂ v₃ v₄ g h
  · exact (hC (yNU A PI sk b s o₃ o₄)).c₄ () o₁ o₂ o₃ o₄ v₁ v₂ v₃ v₄ g h

/-- **The joint hop in each world**: real against simulated, `4·εRF + 15·PU_b`. -/
theorem real_sim_NU (hsk : ∀ c, (sk c).Correct (A.pk c)) {q3 qE : ℕ} (hA : A.Budget q3 qE)
    (hC : A.Cons) (b : Bool) :
    |realNU A PI sk b - pr _ (ev (gameNU A PI sk b) (simSlot pIu) (simSlot pIu) (simSlot pRu)
      (simSlot pRu) (evNU A PI sk b))| ≤ 4 * εRF q3 qE + 15 * puTermNU A PI sk b :=
  main_chain_le Hashes.shake CrtGen.tables mainP_pIu mainP_pIu mainP_pRu mainP_pRu (gameNU A PI sk b)
    (evNU A PI sk b) rNU₁ rNU₂ (rNU₃ A PI sk b) (rNU₄ A PI sk b) (vcons_evNU A PI sk hC b)
    small_pIu small_pIu small_pRu small_pRu q3 qE
    (fun _ _ _ _ _ _ _ _ => rdV_constU _ _ _) (fun _ _ _ _ _ _ _ _ => rdV_constU _ _ _)
    (fun _ _ _ _ _ _ _ v₄ => hA.b₃ _ v₄) (fun _ _ _ _ _ _ _ v₃ => hA.b₄ _ v₃)
    (fun _ y hy => by cases hy) (fun _ _ y hy => by cases hy)
    (fun s _ _ y hy => by
      have hy' : y ∈ (bif gN A PI sk s && validNC A.nc PI sk s.1 s.2 [] (A.next []) then
        redStmtU A.um (ptNC A.nc PI sk b s.1 s.2 (A.next [])) else none) := hy
      cases h : (gN A PI sk s && validNC A.nc PI sk s.1 s.2 [] (A.next []))
      · rw [h] at hy'; cases hy'
      · rw [h] at hy'; exact redStmtNU_valid A PI sk hsk b s _ y hy')
    (fun s _ _ o₃ y hy => by
      have hy' : y ∈ (bif gN A PI sk s && validNC A.nc PI sk s.1 s.2 (hist₁ A PI sk b s o₃)
          (qN₁ A PI sk b s o₃) then
        redStmtU A.um (ptNC A.nc PI sk b s.1 s.2 (qN₁ A PI sk b s o₃)) else none) := hy
      cases h : (gN A PI sk s && validNC A.nc PI sk s.1 s.2 (hist₁ A PI sk b s o₃)
        (qN₁ A PI sk b s o₃))
      · rw [h] at hy'; cases hy'
      · rw [h] at hy'; exact redStmtNU_valid A PI sk hsk b s _ y hy')

/-! ## With both proofs simulated -/

lemma redOutU_simNC (P : RedeemPt) (c : SimCoins pRu) :
    redOutU A.um P ((redStmtU A.um P).map fun _ => simulate pRu c) = redSim A.nc.base simRU c P := by
  unfold redOutU redStmtU redSim
  rw [show A.nc.base.ci = A.um.int.ci from rfl]
  cases findIssuer P.anchors (ucom P.tok.k A.um.int.ci P.tok.r) P.tok.s <;> rfl

/-- The answer to a query, with the simulated proof of the game's gating. -/
lemma ansN_sim (b : Bool) (s : SecN) (H : Hist) (q : Query) (c : SimCoins pRu)
    (hg : gN A PI sk s = true) :
    ansN A PI sk b s H q ((bif gN A PI sk s && validNC A.nc PI sk s.1 s.2 H q then
      redStmtU A.um (ptNC A.nc PI sk b s.1 s.2 q) else none).map fun _ => simulate pRu c) =
      if validNC A.nc PI sk s.1 s.2 H q then redSim A.nc.base simRU c (ptNC A.nc PI sk b s.1 s.2 q)
      else refused := by
  unfold ansN
  rw [hg]
  cases validNC A.nc PI sk s.1 s.2 H q
  · rfl
  · exact redOutU_simNC A _ _

/-- **With both proofs simulated, the history is `simGameNC`'s**: the label-row game's
interaction with simulated redemptions. -/
theorem yNU_sim (b : Bool) (s : SecN) (c₃ c₄ : SimCoins pRu) :
    yNU A PI sk b s (((gameNU A PI sk b).σ₃ s none none).map fun _ => simulate pRu c₃)
      (((gameNU A PI sk b).σ₄ s none none
        (((gameNU A PI sk b).σ₃ s none none).map fun _ => simulate pRu c₃)).map fun _ =>
          simulate pRu c₄) =
      bif (tokNC A.nc PI sk false s.1).isSome && (tokNC A.nc PI sk true s.2).isSome then
        some (interact A.next (validNC A.nc PI sk s.1 s.2) refused
          (List.ofFn fun j q => redSim A.nc.base simRU (![c₃, c₄] j)
            (ptNC A.nc PI sk b s.1 s.2 q)) [])
      else none := by
  unfold yNU
  cases hg : gN A PI sk s
  · show none = bif gN A PI sk s then _ else none
    rw [hg]; rfl
  · show some _ = bif gN A PI sk s then _ else none
    rw [hg]
    simp only [Bool.cond_true, Option.some.injEq]
    have e₃ := ansN_sim A PI sk b s [] (A.next []) c₃ hg
    unfold histN qN₁ hist₁
    show _ = interact A.next (validNC A.nc PI sk s.1 s.2) refused
      [fun q => redSim A.nc.base simRU c₃ (ptNC A.nc PI sk b s.1 s.2 q),
        fun q => redSim A.nc.base simRU c₄ (ptNC A.nc PI sk b s.1 s.2 q)] []
    simp only [interact]
    have e₀ : ansN A PI sk b s [] (A.next [])
        (((gameNU A PI sk b).σ₃ s none none).map fun _ => simulate pRu c₃) =
        if validNC A.nc PI sk s.1 s.2 [] (A.next []) then
          redSim A.nc.base simRU c₃ (ptNC A.nc PI sk b s.1 s.2 (A.next [])) else refused := e₃
    rw [e₀]
    set H₁ : Hist := [] ++ [(A.next [], if validNC A.nc PI sk s.1 s.2 [] (A.next []) then
          redSim A.nc.base simRU c₃ (ptNC A.nc PI sk b s.1 s.2 (A.next [])) else refused)]
    have e₄ := ansN_sim A PI sk b s H₁ (A.next H₁) c₄ hg
    have e₁ : hist₁ A PI sk b s (Option.map (fun _ => simulate pRu c₃)
        (bif gN A PI sk s && validNC A.nc PI sk s.1 s.2 [] (A.next []) then
          redStmtU A.um (ptNC A.nc PI sk b s.1 s.2 (A.next [])) else none)) = H₁ := by
      unfold hist₁; rw [e₃]
    simp only [gameNU, qN₁, e₁] at e₄ ⊢
    rw [e₄]

/-- The simulated game's tape, regrouped: the issuance slots' coins and the redemption tables,
then `simGameNC`'s tape. -/
def regroupNU : SecN × (simSlot pIu).K × (simSlot pIu).K × (simSlot pRu).K × (simSlot pRu).K ≃
    ((SimCoins pIu × Vis pIu) × (SimCoins pIu × Vis pIu) × VisR) ×
      ((IssT × IssT) × (Fin 2 → SimCoins pRu)) where
  toFun x := ((x.2.1, x.2.2.1, (x.2.2.2.1.2, x.2.2.2.2.2)),
    ((x.1.1, x.1.2), ![x.2.2.2.1.1, x.2.2.2.2.1]))
  invFun y := ((y.2.1.1, y.2.1.2), y.1.1, y.1.2.1, (y.2.2 0, y.1.2.2.1), (y.2.2 1, y.1.2.2.2))
  left_inv _ := rfl
  right_inv y := by
    refine Prod.ext rfl (Prod.ext rfl ?_)
    funext j
    fin_cases j <;> rfl

/-- **With both proofs simulated, the game is `simGameNC` of the Moderator at the tables.** -/
theorem simNU_eq (b : Bool) :
    pr _ (ev (gameNU A PI sk b) (simSlot pIu) (simSlot pIu) (simSlot pRu) (simSlot pRu)
      (evNU A PI sk b)) =
      @pr (((SimCoins pIu × Vis pIu) × (SimCoins pIu × Vis pIu) × VisR) ×
        ((IssT × IssT) × (Fin 2 → SimCoins pRu))) (@instFintypeProd _ _ _ _)
        (fun z => simGameNC (n := 2) (A.atV z.1.2.2) PI sk simRU b z.2) := by
  rw [← @pr_equiv _ _ _ (@instFintypeProd _ _ _ _) regroupNU]
  refine pr_congr fun x => ?_
  exact iff_of_eq (congrArg (fun y => A.guess y (x.2.2.2.1.2, x.2.2.2.2.2))
    (yNU_sim A PI sk b x.1 x.2.2.2.1.1 x.2.2.2.2.1))

/-! ## The (PU) term is statistical -/

/-- The history with both tokens finalized and the proofs simulated, as a function of the keys and
the simulators' coins (`hNC`'s). -/
noncomputable def histT (b : Bool) (k : Coins nfKeyBytes × Coins nfKeyBytes)
    (c₃ c₄ : SimCoins pRu) : Hist :=
  interact A.next (fun H q => ctxOk H q) refused
    (List.ofFn fun j q => ySim A.nc.base simRU b (keyTable k) q (![c₃, c₄] j)) []

/-- The history after the first query, likewise. -/
noncomputable def histT₁ (b : Bool) (k : Coins nfKeyBytes × Coins nfKeyBytes) (c₃ : SimCoins pRu) :
    Hist :=
  [] ++ [(A.next [], if ctxOk [] (A.next []) then
    ySim A.nc.base simRU b (keyTable k) (A.next []) c₃ else refused)]

/-- The redemption instance of query `q` in world `b`, from the keys. -/
def xKey (b : Bool) (k : Coins nfKeyBytes × Coins nfKeyBytes) (q : Query) : RedeemInstance :=
  ⟨q.anchors.keys, keyTable k (who b q) q.ctxRed, A.um.int.ci, List.ofFn q.ctxRed, q.cd⟩

/-- **The candidates of the two redemption proofs**, from the keys, the simulators' coins and the
tables (no opening). -/
noncomputable def candNU (b : Bool) (k : Coins nfKeyBytes × Coins nfKeyBytes) (a : AuxU) :
    Finset (Coins rBytes) :=
  candJ Hashes.shake CrtGen.tables mainP_pRu (stR (xKey A b k (A.next [])))
      (A.R₃ (some (histT A b k a.2.2.1.1 a.2.2.2.1)) (a.2.2.1.2, a.2.2.2.2)) a.2.2.1.1 ∪
    candJ Hashes.shake CrtGen.tables mainP_pRu (stR (xKey A b k (A.next (histT₁ A b k a.2.2.1.1))))
      (A.R₄ (some (histT A b k a.2.2.1.1 a.2.2.2.1)) (a.2.2.1.2, a.2.2.2.2)) a.2.2.2.1

lemma card_candNU_le {q5 : ℕ} (h₃ : ∀ y v, (A.R₃ y v).card ≤ q5) (h₄ : ∀ y v, (A.R₄ y v).card ≤ q5)
    (b : Bool) (k : Coins nfKeyBytes × Coins nfKeyBytes) (a : AuxU) :
    (candNU A b k a).card ≤ (2 * q5 + 1) + 1 :=
  (Finset.card_union_le _ _).trans ((Nat.add_le_add
    ((card_candJ_le Hashes.shake CrtGen.tables mainP_pRu _ _ _).trans (Nat.succ_le_succ (h₃ _ _)))
    ((card_candJ_le Hashes.shake CrtGen.tables mainP_pRu _ _ _).trans
      (Nat.succ_le_succ (h₄ _ _)))).trans (by omega))

variable {A PI sk}

/-- Both responses of a good tape. -/
lemma resp_of_gN (hsk : ∀ c, (sk c).Correct (A.pk c)) {s : SecN} (hg : gN A PI sk s = true) :
    (∃ s₀, respNC A.nc PI sk false s.1 = some s₀) ∧ (∃ s₁, respNC A.nc PI sk true s.2 = some s₁) := by
  unfold gN at hg
  rw [tokNC_isSome A.nc PI sk hsk, tokNC_isSome A.nc PI sk hsk] at hg
  simp only [Bool.and_eq_true, Bool.not_eq_true', failNC, Option.isNone_eq_false_iff,
    Option.isSome_iff_exists] at hg
  exact hg

/-- With both tokens finalized, every query is valid iff it passes the context rule. -/
lemma validNC_good (hsk : ∀ c, (sk c).Correct (A.pk c)) (hK : Contains A.nc) {s : SecN}
    (hg : gN A PI sk s = true) (H : Hist) :
    validNC A.nc PI sk s.1 s.2 H (A.next H) = ctxOk H (A.next H) := by
  obtain ⟨⟨s₀, hr₀⟩, ⟨s₁, hr₁⟩⟩ := resp_of_gN hsk hg
  unfold validNC
  rw [redeemable_of_contains A.nc PI sk hsk false _ hr₀ (A.next H).anchors (hK H false),
    redeemable_of_contains A.nc PI sk hsk true _ hr₁ (A.next H).anchors (hK H true)]
  rfl

/-- With both tokens finalized, a simulated answer is `ySim` on the key table. -/
lemma redSim_good (hsk : ∀ c, (sk c).Correct (A.pk c)) (hK : Contains A.nc) {s : SecN}
    (hg : gN A PI sk s = true) (b : Bool) (H : Hist) (c : SimCoins pRu) :
    redSim A.nc.base simRU c (ptNC A.nc PI sk b s.1 s.2 (A.next H)) =
      ySim A.nc.base simRU b (keyTable (s.1.1, s.2.1)) (A.next H) c := by
  obtain ⟨⟨s₀, hr₀⟩, ⟨s₁, hr₁⟩⟩ := resp_of_gN hsk hg
  exact redSim_ptNC A.nc PI sk simRU hsk b s.1 s.2 hr₀ hr₁ _ (hK H) c

/-- **With both tokens finalized and the proofs simulated, the history is `histT`**, a function of
the keys and the simulators' coins (`simNC_iff`). -/
lemma hist_good (hsk : ∀ c, (sk c).Correct (A.pk c)) (hK : Contains A.nc) (b : Bool) (s : SecN)
    (c₃ c₄ : SimCoins pRu) (hg : gN A PI sk s = true) :
    interact A.next (validNC A.nc PI sk s.1 s.2) refused
      (List.ofFn fun j q => redSim A.nc.base simRU (![c₃, c₄] j) (ptNC A.nc PI sk b s.1 s.2 q)) [] =
      histT A b (s.1.1, s.2.1) c₃ c₄ := by
  let A' : AdversaryNC := ⟨A.ctxIss, A.pk, A.next, fun h => h = some (histT A b (s.1.1, s.2.1) c₃ c₄)⟩
  have hg' : (!failNC A' PI sk false s.1 && !failNC A' PI sk true s.2) = true := by
    rw [← tokNC_isSome A' PI sk hsk, ← tokNC_isSome A' PI sk hsk]
    exact hg
  have h := (simNC_iff A' PI sk simRU hsk hK b ((s.1, s.2), ![c₃, c₄])).2 (by
    show (bif _ then _ else none) = _
    rw [hg']
    rfl)
  have hg'' : ((tokNC A' PI sk false s.1).isSome && (tokNC A' PI sk true s.2).isSome) = true := hg
  unfold simGameNC gameNC at h
  dsimp only at h
  rw [hg''] at h
  exact Option.some.inj h

/-- The history after the first query, with both tokens finalized and the proof simulated. -/
lemma hist₁_good (hsk : ∀ c, (sk c).Correct (A.pk c)) (hK : Contains A.nc) (b : Bool) (s : SecN)
    (c₃ : SimCoins pRu) (hg : gN A PI sk s = true) :
    hist₁ A PI sk b s (((gameNU A PI sk b).σ₃ s none none).map fun _ => simulate pRu c₃) =
      histT₁ A b (s.1.1, s.2.1) c₃ := by
  unfold hist₁ histT₁
  rw [show (gameNU A PI sk b).σ₃ s none none =
      (bif gN A PI sk s && validNC A.nc PI sk s.1 s.2 [] (A.next []) then
        redStmtU A.um (ptNC A.nc PI sk b s.1 s.2 (A.next [])) else none) from rfl,
    ansN_sim A PI sk b s [] (A.next []) c₃ hg, validNC_good hsk hK hg [],
    redSim_good hsk hK hg b [] c₃]

/-- A redemption statement of a good tape: its instance is `xKey`'s, its witness prefix the
answering Client's opening. -/
lemma redStmt_good (hsk : ∀ c, (sk c).Correct (A.pk c)) {s : SecN} (hg : gN A PI sk s = true)
    (b : Bool) (q : Query) (y : SW)
    (hy : redStmtU A.um (ptNC A.nc PI sk b s.1 s.2 q) = some y) :
    y.1 = stR (xKey A b (s.1.1, s.2.1) q) ∧
      wPre y.2 = (bif who b q then s.2 else s.1).2.1 := by
  obtain ⟨⟨s₀, hr₀⟩, ⟨s₁, hr₁⟩⟩ := resp_of_gN hsk hg
  have ht : (ptNC A.nc PI sk b s.1 s.2 q).tok = ⟨List.ofFn (bif who b q then s.2 else s.1).1,
      List.ofFn (bif who b q then s.2 else s.1).2.1, bif who b q then s₁ else s₀⟩ := by
    unfold ptNC
    cases who b q
    · exact (tokDNC_of_resp A.nc PI sk hsk false s.1 hr₀).1
    · exact (tokDNC_of_resp A.nc PI sk hsk true s.2 hr₁).1
  unfold redStmtU at hy
  cases hf : findIssuer (ptNC A.nc PI sk b s.1 s.2 q).anchors
    (ucom (ptNC A.nc PI sk b s.1 s.2 q).tok.k A.um.int.ci (ptNC A.nc PI sk b s.1 s.2 q).tok.r)
    (ptNC A.nc PI sk b s.1 s.2 q).tok.s with
  | none => rw [hf] at hy; cases hy
  | some i =>
    rw [hf] at hy
    cases hy
    refine ⟨?_, ?_⟩
    · refine congrArg stR ?_
      unfold xRU xKey keyTable
      rw [ht]
      cases who b q <;> rfl
    · rw [ht]
      exact wPre_redeemWitnessU _ _ _ _ _ _

variable (A PI sk)

-- (The defeq checks on the nested tape exceed the default recursion depth.)
set_option maxRecDepth 8192 in
/-- **The (PU) event implies that an opening is a candidate computed without the openings.** -/
theorem puEvNU_imp (hsk : ∀ c, (sk c).Correct (A.pk c)) (hK : Contains A.nc) (b : Bool)
    (x : SecN × AuxU)
    (h : ev (gameNU A PI sk b) (simP pIu) (simP pIu) (simP pRu) (simP pRu)
      (predAll Hashes.shake CrtGen.tables mainP_pIu mainP_pIu mainP_pRu mainP_pRu
        rNU₁ rNU₂ (rNU₃ A PI sk b) (rNU₄ A PI sk b)) x) :
    x.1.1.2.1 ∈ candNU A b (x.1.1.1, x.1.2.1) x.2 ∨ x.1.2.2.1 ∈ candNU A b (x.1.1.1, x.1.2.1) x.2 := by
  obtain ⟨s, k⟩ := x
  have hY := yNU_sim A PI sk b s k.2.2.1.1 k.2.2.2.1
  rcases h with h | h | h | h
  · exact (predJ_simP_none _ _ _ _ _ h).elim
  · exact (predJ_simP_none _ _ _ _ _ h).elim
  · -- query `0`
    change predJ Hashes.shake CrtGen.tables mainP_pRu
      (A.R₃ (yNU A PI sk b s (((gameNU A PI sk b).σ₃ s none none).map fun _ => simulate pRu k.2.2.1.1)
        (((gameNU A PI sk b).σ₄ s none none (((gameNU A PI sk b).σ₃ s none none).map fun _ =>
          simulate pRu k.2.2.1.1)).map fun _ => simulate pRu k.2.2.2.1)) (k.2.2.1.2, k.2.2.2.2))
      ((simP pRu).obs ((gameNU A PI sk b).σ₃ s none none) k.2.2.1) at h
    cases hg : gN A PI sk s
    · have : (gameNU A PI sk b).σ₃ s none none = none := by
        show (bif gN A PI sk s && _ then _ else none) = none
        rw [hg]; rfl
      rw [this] at h
      exact (predJ_simP_none _ _ _ _ _ h).elim
    · have hg' : ((tokNC A.nc PI sk false s.1).isSome && (tokNC A.nc PI sk true s.2).isSome) =
          true := hg
      rw [hY, hg', hist_good hsk hK b s _ _ hg] at h
      rcases hσ : (gameNU A PI sk b).σ₃ s none none with _ | y
      · rw [hσ] at h; exact (predJ_simP_none _ _ _ _ _ h).elim
      · rw [hσ, predJ_simP] at h
        have hy : redStmtU A.um (ptNC A.nc PI sk b s.1 s.2 (A.next [])) = some y := by
          have e : (gameNU A PI sk b).σ₃ s none none =
              bif gN A PI sk s && validNC A.nc PI sk s.1 s.2 [] (A.next []) then
                redStmtU A.um (ptNC A.nc PI sk b s.1 s.2 (A.next [])) else none := rfl
          rw [e, hg] at hσ
          cases hv : validNC A.nc PI sk s.1 s.2 [] (A.next [])
          · rw [hv] at hσ; cases hσ
          · rw [hv] at hσ; exact hσ
        obtain ⟨h1, h2⟩ := redStmt_good hsk hg b _ y hy
        rw [h1, h2] at h
        have hin : (bif who b (A.next []) then s.2 else s.1).2.1 ∈ candNU A b (s.1.1, s.2.1) k :=
          Finset.mem_union_left _ h
        generalize who b (A.next []) = w at hin
        cases w
        · exact Or.inl hin
        · exact Or.inr hin
  · -- query `1`
    change predJ Hashes.shake CrtGen.tables mainP_pRu
      (A.R₄ (yNU A PI sk b s (((gameNU A PI sk b).σ₃ s none none).map fun _ => simulate pRu k.2.2.1.1)
        (((gameNU A PI sk b).σ₄ s none none (((gameNU A PI sk b).σ₃ s none none).map fun _ =>
          simulate pRu k.2.2.1.1)).map fun _ => simulate pRu k.2.2.2.1)) (k.2.2.1.2, k.2.2.2.2))
      ((simP pRu).obs ((gameNU A PI sk b).σ₄ s none none
        (((gameNU A PI sk b).σ₃ s none none).map fun _ => simulate pRu k.2.2.1.1)) k.2.2.2) at h
    cases hg : gN A PI sk s
    · have : (gameNU A PI sk b).σ₄ s none none
          (((gameNU A PI sk b).σ₃ s none none).map fun _ => simulate pRu k.2.2.1.1) = none := by
        show (bif gN A PI sk s && _ then _ else none) = none
        rw [hg]; rfl
      rw [this] at h
      exact (predJ_simP_none _ _ _ _ _ h).elim
    · have hg' : ((tokNC A.nc PI sk false s.1).isSome && (tokNC A.nc PI sk true s.2).isSome) =
          true := hg
      rw [hY, hg', hist_good hsk hK b s _ _ hg] at h
      rcases hσ : (gameNU A PI sk b).σ₄ s none none
        (((gameNU A PI sk b).σ₃ s none none).map fun _ => simulate pRu k.2.2.1.1) with _ | y
      · rw [hσ] at h; exact (predJ_simP_none _ _ _ _ _ h).elim
      · rw [hσ, predJ_simP] at h
        have h₁ := hist₁_good hsk hK b s k.2.2.1.1 hg
        have hy : redStmtU A.um (ptNC A.nc PI sk b s.1 s.2 (A.next (histT₁ A b (s.1.1, s.2.1)
            k.2.2.1.1))) = some y := by
          have e : (gameNU A PI sk b).σ₄ s none none
              (((gameNU A PI sk b).σ₃ s none none).map fun _ => simulate pRu k.2.2.1.1) =
              bif gN A PI sk s && validNC A.nc PI sk s.1 s.2 (hist₁ A PI sk b s
                (((gameNU A PI sk b).σ₃ s none none).map fun _ => simulate pRu k.2.2.1.1))
                (qN₁ A PI sk b s (((gameNU A PI sk b).σ₃ s none none).map fun _ =>
                  simulate pRu k.2.2.1.1)) then
                redStmtU A.um (ptNC A.nc PI sk b s.1 s.2 (qN₁ A PI sk b s
                  (((gameNU A PI sk b).σ₃ s none none).map fun _ => simulate pRu k.2.2.1.1)))
              else none := rfl
          rw [e, hg] at hσ
          unfold qN₁ at hσ
          rw [h₁] at hσ
          cases hv : validNC A.nc PI sk s.1 s.2 (histT₁ A b (s.1.1, s.2.1) k.2.2.1.1)
            (A.next (histT₁ A b (s.1.1, s.2.1) k.2.2.1.1))
          · rw [hv] at hσ; cases hσ
          · rw [hv] at hσ; exact hσ
        obtain ⟨h1, h2⟩ := redStmt_good hsk hg b _ y hy
        rw [h1, h2] at h
        have hin : (bif who b (A.next (histT₁ A b (s.1.1, s.2.1) k.2.2.1.1)) then s.2 else s.1).2.1 ∈
            candNU A b (s.1.1, s.2.1) k :=
          Finset.mem_union_right _ h
        generalize who b (A.next (histT₁ A b (s.1.1, s.2.1) k.2.2.1.1)) = w at hin
        cases w
        · exact Or.inl hin
        · exact Or.inr hin

/-- **The (PU) term is at most `4·(q₅ + 1)·2⁻¹²⁸`**: each Client's uniform opening is independent
of the candidates. -/
theorem puTermNU_le (hsk : ∀ c, (sk c).Correct (A.pk c)) (hK : Contains A.nc) {q5 : ℕ}
    (h₃ : ∀ y v, (A.R₃ y v).card ≤ q5) (h₄ : ∀ y v, (A.R₄ y v).card ≤ q5) (b : Bool) :
    puTermNU A PI sk b ≤ 4 * ((q5 + 1) / 2 ^ 128) := by
  have e : puTermNU A PI sk b = pr (SecN × AuxU) (ev (gameNU A PI sk b) (simP pIu) (simP pIu)
      (simP pRu) (simP pRu) (predAll Hashes.shake CrtGen.tables mainP_pIu mainP_pIu mainP_pRu
        mainP_pRu rNU₁ rNU₂ (rNU₃ A PI sk b) (rNU₄ A PI sk b))) := by
    unfold puTermNU
    exact pr_inst_irrel _ _ _
  rw [e]
  refine (pr_mono (puEvNU_imp A PI sk hsk hK b)).trans ((pr_or_le _ _).trans ?_)
  -- the rest of the tape, without the two openings
  let R := ((Coins nfKeyBytes × Coins proveSeedBytes) × (Coins nfKeyBytes × Coins rBytes ×
    Coins proveSeedBytes)) × AuxU
  let e₀ : Coins rBytes × R ≃ SecN × AuxU :=
    { toFun := fun z => (((z.2.1.1.1, z.1, z.2.1.1.2), z.2.1.2), z.2.2)
      invFun := fun x => (x.1.1.2.1, ((x.1.1.1, x.1.1.2.2), x.1.2), x.2)
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  let R' := ((Coins nfKeyBytes × Coins rBytes × Coins proveSeedBytes) ×
    (Coins nfKeyBytes × Coins proveSeedBytes)) × AuxU
  let e₁ : Coins rBytes × R' ≃ SecN × AuxU :=
    { toFun := fun z => ((z.2.1.1, (z.2.1.2.1, z.1, z.2.1.2.2)), z.2.2)
      invFun := fun x => (x.1.2.2.1, (x.1.1, (x.1.2.1, x.1.2.2.2)), x.2)
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have p0 : pr (SecN × AuxU) (fun x => x.1.1.2.1 ∈ candNU A b (x.1.1.1, x.1.2.1) x.2) ≤
      ((2 * q5 + 1 : ℕ) + 1) / 2 ^ 128 := by
    rw [← pr_equiv e₀]
    exact pr_mem_uniform_le (X := R) (fun z => candNU A b (z.1.1.1, z.1.2.1) z.2) (q := 2 * q5 + 1)
      (fun z => card_candNU_le A h₃ h₄ b _ _)
  have p1 : pr (SecN × AuxU) (fun x => x.1.2.2.1 ∈ candNU A b (x.1.1.1, x.1.2.1) x.2) ≤
      ((2 * q5 + 1 : ℕ) + 1) / 2 ^ 128 := by
    rw [← pr_equiv e₁]
    exact pr_mem_uniform_le (X := R') (fun z => candNU A b (z.1.1.1, z.1.2.1) z.2) (q := 2 * q5 + 1)
      (fun z => card_candNU_le A h₃ h₄ b _ _)
  have hn : (((2 * q5 + 1 : ℕ) : ℝ) + 1) / 2 ^ 128 = 2 * ((q5 + 1) / 2 ^ 128) := by
    push_cast; ring
  rw [hn] at p0 p1
  linarith

/-! ## Theorem U5(b) on `main` -/

/-- **Theorem U5(b) on `main` (no label rows), corrected, two adaptive queries.** For every
non-colluding Moderator whose two queries' Anchor Sets contain both issuers (`Contains`), honest
Anchors whose signers are correct for their keys, any issuance proof system, and the executable
prover for the two redemptions (per-proof tables): if the guess reads each redemption proof's `H₃`
and cipher at `q3`, `qE` keys and `H₅` at consistent read sets of at most `q5` keys, and every PRF
reduction at fixed tables has advantage (without the commitments) at most `εprf`,

    |Pr[W₀] − Pr[W₁]| ≤ 8·εRF(q3, qE) + 15·8·(q5 + 1)·2⁻¹²⁸ + 2·(ψ false + ψ true) + 2·εprf.

The (PU) term is statistical: no assumption on `UCom`. `ψ c ≤ κ + φ c` (`psi_le`), `κ = 0` for a
complete issuance proof system (`kappa_eq_zero`). -/
theorem anonymityNC_main_U (hsk : ∀ c, (sk c).Correct (A.pk c)) (hK : Contains A.nc)
    {q3 qE q5 : ℕ} (hA : A.Budget q3 qE) (hC : A.Cons)
    (h₃ : ∀ y v, (A.R₃ y v).card ≤ q5) (h₄ : ∀ y v, (A.R₄ y v).card ≤ q5) {εprf : ℝ}
    (hprf : ∀ v b (cs : Fin 2 → SimCoins pRu), prfAdvNC (reductionNC (A.atV v) simRU b cs) ≤ εprf) :
    |realNU A PI sk false - realNU A PI sk true| ≤
      8 * εRF q3 qE + 15 * (8 * ((q5 + 1) / 2 ^ 128)) +
        2 * (psi A.nc PI sk false + psi A.nc PI sk true) + 2 * εprf := by
  have r0 := real_sim_NU A PI sk hsk hA hC false
  have r1 := real_sim_NU A PI sk hsk hA hC true
  rw [simNU_eq] at r0 r1
  have p0 := puTermNU_le A PI sk hsk hK h₃ h₄ false
  have p1 := puTermNU_le A PI sk hsk hK h₃ h₄ true
  have hw (b : Bool) (v : VisR) :
      |pr _ (simGameNC (n := 2) (A.atV v) PI sk simRU b) - pr _ (idealNC (n := 2) (A.atV v) simRU b)| ≤
        (psi A.nc PI sk false + psi A.nc PI sk true) + εprf := by
    have h2 := sim_hyb_NC (n := 2) (A.atV v) PI sk simRU hsk hK b
    have h3 := prf_hop_NC (A.atV v) simRU b (hprf v b)
    have := abs_sub_le (pr _ (simGameNC (n := 2) (A.atV v) PI sk simRU b))
      (pr _ (hybNC (n := 2) (A.atV v) simRU b)) (pr _ (idealNC (n := 2) (A.atV v) simRU b))
    exact this.trans (add_le_add h2 h3)
  have h0 := avg_close (fun w : (SimCoins pIu × Vis pIu) × (SimCoins pIu × Vis pIu) × VisR =>
      simGameNC (n := 2) (A.atV w.2.2) PI sk simRU false)
    (fun w => idealNC (n := 2) (A.atV w.2.2) simRU false) fun w => hw false w.2.2
  have h1 := avg_close (fun w : (SimCoins pIu × Vis pIu) × (SimCoins pIu × Vis pIu) × VisR =>
      simGameNC (n := 2) (A.atV w.2.2) PI sk simRU true)
    (fun w => idealNC (n := 2) (A.atV w.2.2) simRU true) fun w => hw true w.2.2
  have e := avg_eq (fun w : (SimCoins pIu × Vis pIu) × (SimCoins pIu × Vis pIu) × VisR =>
      idealNC (n := 2) (A.atV w.2.2) simRU false)
    (fun w => idealNC (n := 2) (A.atV w.2.2) simRU true) fun w => idealNC_eq (A.atV w.2.2) simRU
  beta_reduce at h0 h1 e
  have := abs_sub_le_iff.1 r0; have := abs_sub_le_iff.1 r1; have := abs_sub_le_iff.1 h0
  have := abs_sub_le_iff.1 h1
  rw [abs_sub_le_iff]
  constructor <;> nlinarith

end VoleMole.Privacy.MoussakaUnbound
