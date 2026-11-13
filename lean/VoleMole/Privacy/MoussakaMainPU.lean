import VoleMole.Privacy.MoussakaMain
import VoleMole.ZK.MainPU
import VoleMole.ZK.Relations
import VoleMole.Privacy.PUKeccak

/-!
# Moussaka on `main`: the (PU) term as the advantage of explicit predictors

`anonymity_main` (`Privacy/MoussakaMain.lean`) bounds Theorem 4(a) on `main` by
`8·εRF + 15·(puTerm 0 + puTerm 1) + 2·εhide`, with `puTerm b` an event of the game with all four
proofs simulated. Here that event is reduced to the game `Privacy.PU.puAdv` for `Com`.

**The predictors** (`predM`, `predM₀`, `predM₁`). With all proofs simulated, everything the
adversary sees is a function of the commitments `t₀, t₁`, the nullifiers `n₀, n₁`, the four
simulators' coins and the tables (`yM_sim`, from `Moussaka.post_redSim`). So are the statements of
the proofs (`redStmt_allOk`), the `H₅` read sets and hence the candidate sets `candJ`. For Client
`c`, `predM b … c` is the union of the candidates of its issuance proof and, when §6's rule lets
the redemptions run (`allOkT`), of its redemption proof. Both proofs have the Client's opening
`r_c` as witness prefix (`wPre_issueWitness`, `wPre_redeemWitness`).

**The reduction** (`puTerm_le`). If every `H₅` read set of the guess has at most `q₅` keys,

    puTerm b ≤ puAdv Com (predM₀ b) + puAdv Com (predM₁ b) + 2·(q₅ + 1)·2⁻¹²⁸,

`predM_c b` the predictor for Client `c` (it draws the other Client's nullifier and opening itself,
as auxiliary coins), with at most `2·(q₅ + 1)` candidates (`card_predM_le`). The last term is for
the redemption proofs that are computed but not shown (when `allOkT` fails the guess gets no
redemption, and the proof's uniform field `d` is independent of its read set: `pr_d3_le`,
`pr_d4_le`); there the prover's token may be the dummy of a failed finalization, so the witness
prefix is not a secret and the event is not a prediction.

**`anonymity_main_pu`**: Theorem 4(a) on `main` with the bound

    8·εRF(q₃, q_E) + 15·(Σ_{b, c} puAdv Com (predM_c b) + 4·(q₅ + 1)·2⁻¹²⁸) + 2·εhide.

`Com` here is the concrete `Spec.Moussaka.com`, one truncated call of Keccak-p[800,12]
(`puAdv_comM_eq`: it is `PU.comP PU.kp800 (PU.XM ci cr) (PU.trunc 45 55)`), and the predictors are
arbitrary functions, so `puAdv` is an assumption on Keccak-p[800,12]: (PU). In the
ideal-permutation model, a predictor with `q` forward and inverse queries and `c` candidates has
advantage at most `(c + q)/(2¹²⁸ − q) + q/(2⁴⁴⁰ − q)` (`PU.puAdvPerm_moussaka_le`).
-/

open Finset

-- (The coin types are large products: their `Fintype` instances exceed the default size.)
set_option synthInstance.maxSize 1024

set_option linter.unusedSectionVars false
set_option linter.constructorNameAsVariable false

namespace VoleMole.Privacy.Moussaka

open VoleMole.Spec VoleMole.Spec.Moussaka VoleMole.ZK.Sim VoleMole.Privacy.MainChain
open VoleMole.Verifier VoleMole.Verifier.Bridge VoleMole.Privacy.PU

-- `Com` evaluates Keccak-p[800]; nothing below needs to unfold it.
attribute [local irreducible] com UOVKey.eval
attribute [local irreducible] simulate proveIdeal proveE firstHit

/-! ## Witness prefixes -/

lemma getD_of_take {l : Bytes} {r : Coins 16} (h : l.take 16 = List.ofFn r) (k : Fin 16) :
    l.getD k.1 0 = r k := by
  have h1 : (l.take 16)[k.1]? = l[k.1]? := List.getElem?_take_of_lt k.2
  rw [List.getD_eq_getElem?_getD, ← h1, h, List.getElem?_ofFn]
  simp

/-- **The issuance witness starts with the opening.** -/
lemma wPre_issueWitness (nf ci cr : Bytes) (r : Coins 16) :
    wPre (toBA (encodeIssueWitness nf ci cr (List.ofFn r))) = r := by
  funext k
  show (toBA _).get! k.1 = r k
  rw [toBA_get!]
  exact getD_of_take (ZK.encodeIssueWitness_take nf ci cr _ (by simp)) k

/-- **The redemption witness starts with the opening.** -/
lemma wPre_redeemWitness (nf ci cr s : Bytes) (i : ℕ) (r : Coins 16) :
    wPre (toBA (encodeRedeemWitness nf ci cr (List.ofFn r) s i)) = r := by
  funext k
  show (toBA _).get! k.1 = r k
  rw [toBA_get!]
  exact getD_of_take (ZK.encodeRedeemWitness_take nf ci cr _ s i (by simp)) k

/-! ## The simulated game as a function of the commitments and the nullifiers -/

variable (A : AdversaryM) (idx : AnchorSet → UOVKey → ℕ)

/-- `Com` on the Clients' coins, with the adversary's contexts. -/
def comM (n : Coins nfBytes) (r : Coins rBytes) : Bytes :=
  com (List.ofFn n) A.int.ci A.int.cr (List.ofFn r)

/-- **`Com` is `PU.comP` at Keccak-p[800,12]**: the (PU) game for the concrete commitment is the
game of `Privacy/PU.lean` with `kp800` for the permutation. -/
theorem puAdv_comM_eq {Aux : Type} [Fintype Aux]
    (P : Coins nfBytes → Bytes → Aux → Finset (Coins rBytes)) :
    puAdv (comM A) P = puAdv (comP kp800 (XM A.int.ci A.int.cr) (trunc 45 55))
      (fun n t a => P n (List.ofFn t) a) := by
  unfold puAdv
  refine pr_congr fun z => ?_
  rw [comM, com_eq_comP]

/-- Client `c`'s opening. -/
def rOf (s : SecM) (c : Bool) : Coins rBytes := (bif c then s.2 else s.1).2

/-- Client `c`'s nullifier. -/
def nOf (s : SecM) (c : Bool) : Bytes := List.ofFn (bif c then s.2 else s.1).1

lemma tM_eq (s : SecM) (c : Bool) : tM A s c = comM A (bif c then s.2 else s.1).1 (rOf s c) := rfl

/-- The four simulators' coins and tables (the tape of the simulated game without the secret). -/
abbrev AuxM := (SimCoins pIm × Vis pIm) × (SimCoins pIm × Vis pIm) × (SimCoins pRm × Vis pRm) ×
  (SimCoins pRm × Vis pRm)

variable [HasPrg]

/-- A simulated issuance request. -/
noncomputable def reqS (t : Bytes) (c : SimCoins pIm) : Bytes := t ++ pf (some (simulate pIm c))

/-- The tables. -/
def visM (k : AuxM) : VisM := (k.1.2, k.2.1.2, k.2.2.1.2, k.2.2.2.2)

/-- **The guess's third input with all proofs simulated**, from the commitments, the nullifiers
and the simulators' coins. -/
noncomputable def ySimM (b : Bool) (t₀ t₁ n₀ n₁ : Bytes) (k : AuxM) :
    Option (Except Error Bytes × Except Error Bytes) :=
  bif allOkT A.int idx (reqS t₀ k.1.1) (reqS t₁ k.2.1.1) t₀ t₁ then
    some (ySim A.int simRM b (reqS t₀ k.1.1) (reqS t₁ k.2.1.1) n₀ n₁ k.2.2.1.1 false,
      ySim A.int simRM b (reqS t₀ k.1.1) (reqS t₁ k.2.1.1) n₀ n₁ k.2.2.2.1 true)
  else none

/-- The redemption instance of side `side` in world `b`, from the requests and the nullifiers. -/
def xSideM (b : Bool) (q₀ q₁ n₀ n₁ : Bytes) (side : Bool) : RedeemInstance :=
  ⟨(A.choose q₀ q₁ side).1.keys, bif b ^^ side then n₁ else n₀, A.int.ci, A.int.cr,
    (A.choose q₀ q₁ side).2⟩

/-- **The candidate sets of the four simulated proofs**, from the commitments, the nullifiers, the
simulators' coins and the tables. -/
noncomputable def candM₁ (b : Bool) (t₀ t₁ n₀ n₁ : Bytes) (k : AuxM) : Finset (Coins rBytes) :=
  candJ Hashes.shake CrtGen.tables mainP_pIm (stI ⟨t₀, A.int.ci⟩)
    (A.R₁ (reqS t₀ k.1.1) (reqS t₁ k.2.1.1) (ySimM A idx b t₀ t₁ n₀ n₁ k) (visM k)) k.1.1

noncomputable def candM₂ (b : Bool) (t₀ t₁ n₀ n₁ : Bytes) (k : AuxM) : Finset (Coins rBytes) :=
  candJ Hashes.shake CrtGen.tables mainP_pIm (stI ⟨t₁, A.int.ci⟩)
    (A.R₂ (reqS t₀ k.1.1) (reqS t₁ k.2.1.1) (ySimM A idx b t₀ t₁ n₀ n₁ k) (visM k)) k.2.1.1

noncomputable def candM₃ (b : Bool) (t₀ t₁ n₀ n₁ : Bytes) (k : AuxM) : Finset (Coins rBytes) :=
  candJ Hashes.shake CrtGen.tables mainP_pRm
    (stR (xSideM A b (reqS t₀ k.1.1) (reqS t₁ k.2.1.1) n₀ n₁ false))
    (A.R₃ (reqS t₀ k.1.1) (reqS t₁ k.2.1.1) (ySimM A idx b t₀ t₁ n₀ n₁ k) (visM k)) k.2.2.1.1

noncomputable def candM₄ (b : Bool) (t₀ t₁ n₀ n₁ : Bytes) (k : AuxM) : Finset (Coins rBytes) :=
  candJ Hashes.shake CrtGen.tables mainP_pRm
    (stR (xSideM A b (reqS t₀ k.1.1) (reqS t₁ k.2.1.1) n₀ n₁ true))
    (A.R₄ (reqS t₀ k.1.1) (reqS t₁ k.2.1.1) (ySimM A idx b t₀ t₁ n₀ n₁ k) (visM k)) k.2.2.2.1

/-- **The predictor for Client `c`'s opening in world `b`**: the candidates of its issuance proof
and, if the redemptions run (`allOkT`), of its redemption proof (side `b ^^ c`). -/
noncomputable def predM (b : Bool) (t₀ t₁ n₀ n₁ : Bytes) (k : AuxM) (c : Bool) :
    Finset (Coins rBytes) :=
  (bif c then candM₂ A idx b t₀ t₁ n₀ n₁ k else candM₁ A idx b t₀ t₁ n₀ n₁ k) ∪
    (bif allOkT A.int idx (reqS t₀ k.1.1) (reqS t₁ k.2.1.1) t₀ t₁ then
      (bif b ^^ c then candM₄ A idx b t₀ t₁ n₀ n₁ k else candM₃ A idx b t₀ t₁ n₀ n₁ k)
    else ∅)

/-- **At most `2·(q₅ + 1)` candidates**, if every read set has at most `q₅` keys. -/
theorem card_predM_le {q5 : ℕ}
    (h₁ : ∀ q₀ q₁ y v, (A.R₁ q₀ q₁ y v).card ≤ q5) (h₂ : ∀ q₀ q₁ y v, (A.R₂ q₀ q₁ y v).card ≤ q5)
    (h₃ : ∀ q₀ q₁ y v, (A.R₃ q₀ q₁ y v).card ≤ q5) (h₄ : ∀ q₀ q₁ y v, (A.R₄ q₀ q₁ y v).card ≤ q5)
    (b : Bool) (t₀ t₁ n₀ n₁ : Bytes) (k : AuxM) (c : Bool) :
    (predM A idx b t₀ t₁ n₀ n₁ k c).card ≤ 2 * (q5 + 1) := by
  have e₁ : (candM₁ A idx b t₀ t₁ n₀ n₁ k).card ≤ q5 + 1 :=
    (card_candJ_le Hashes.shake CrtGen.tables mainP_pIm _ _ _).trans (Nat.succ_le_succ (h₁ _ _ _ _))
  have e₂ : (candM₂ A idx b t₀ t₁ n₀ n₁ k).card ≤ q5 + 1 :=
    (card_candJ_le Hashes.shake CrtGen.tables mainP_pIm _ _ _).trans (Nat.succ_le_succ (h₂ _ _ _ _))
  have e₃ : (candM₃ A idx b t₀ t₁ n₀ n₁ k).card ≤ q5 + 1 :=
    (card_candJ_le Hashes.shake CrtGen.tables mainP_pRm _ _ _).trans (Nat.succ_le_succ (h₃ _ _ _ _))
  have e₄ : (candM₄ A idx b t₀ t₁ n₀ n₁ k).card ≤ q5 + 1 :=
    (card_candJ_le Hashes.shake CrtGen.tables mainP_pRm _ _ _).trans (Nat.succ_le_succ (h₄ _ _ _ _))
  unfold predM
  generalize candM₁ A idx b t₀ t₁ n₀ n₁ k = C₁ at e₁ ⊢
  generalize candM₂ A idx b t₀ t₁ n₀ n₁ k = C₂ at e₂ ⊢
  generalize candM₃ A idx b t₀ t₁ n₀ n₁ k = C₃ at e₃ ⊢
  generalize candM₄ A idx b t₀ t₁ n₀ n₁ k = C₄ at e₄ ⊢
  generalize allOkT A.int idx (reqS t₀ k.1.1) (reqS t₁ k.2.1.1) t₀ t₁ = ok
  refine (Finset.card_union_le _ _).trans ?_
  have a : (bif c then C₂ else C₁).card ≤ q5 + 1 := by
    cases c
    · exact e₁
    · exact e₂
  have a' : (bif ok then (bif b ^^ c then C₄ else C₃) else ∅).card ≤ q5 + 1 := by
    cases ok
    · exact Nat.zero_le _
    · cases b ^^ c
      · exact e₃
      · exact e₄
  exact (Nat.add_le_add a a').trans (by omega)

/-! ## The simulated game, rewritten -/

/-- **With all proofs simulated, the guess's third input is a function of the commitments, the
nullifiers and the simulators' coins** (`Moussaka.post_redSim`, for the adversary whose guess
compares its input with `ySimM`). -/
theorem yM_sim (b : Bool) (s : SecM) (k : AuxM) :
    yM A idx b s (some (simulate pIm k.1.1)) (some (simulate pIm k.2.1.1))
      ((redStmt A (ptM A idx b s (some (simulate pIm k.1.1)) (some (simulate pIm k.2.1.1))
        false)).map fun _ => simulate pRm k.2.2.1.1)
      ((redStmt A (ptM A idx b s (some (simulate pIm k.1.1)) (some (simulate pIm k.2.1.1))
        true)).map fun _ => simulate pRm k.2.2.2.1) =
      ySimM A idx b (tM A s false) (tM A s true) (nOf s false) (nOf s true) k := by
  unfold yM
  rw [redOut_sim A (visM k), redOut_sim A (visM k)]
  let A' : Adversary := ⟨A.ctxIss, A.ctxRed, A.pk, A.respond, A.choose, fun _ _ y =>
    y = ySimM A idx b (tM A s false) (tM A s true) (nOf s false) (nOf s true) k⟩
  exact (post_redSim A' idx simRM b (issM A s false (some (simulate pIm k.1.1)))
    (issM A s true (some (simulate pIm k.2.1.1))) k.2.2.1.1 k.2.2.2.1 rfl rfl).2 rfl

/-- **A redemption statement of a finalized token**: its instance is public (`xSideM`), and its
witness prefix is the Client's opening. -/
theorem redStmt_fin (b : Bool) (s : SecM) (k : AuxM) (side : Bool)
    (hf : finT A.int (reqS (tM A s false) k.1.1) (reqS (tM A s true) k.2.1.1) (tM A s false)
      (tM A s true) (b ^^ side) = true) (y : SW)
    (hy : redStmt A (ptM A idx b s (some (simulate pIm k.1.1)) (some (simulate pIm k.2.1.1))
      side) = some y) :
    y.1 = stR (xSideM A b (reqS (tM A s false) k.1.1) (reqS (tM A s true) k.2.1.1) (nOf s false)
      (nOf s true) side) ∧ wPre y.2 = rOf s (b ^^ side) := by
  set i₀ := issM A s false (some (simulate pIm k.1.1)) with hi₀
  set i₁ := issM A s true (some (simulate pIm k.2.1.1)) with hi₁
  have hf' : finT A.int i₀.2 i₁.2 i₀.1.t i₁.1.t (b ^^ side) = true := hf
  have htok : tokD A.int i₀ i₁ (b ^^ side) = ⟨nOf s (b ^^ side), List.ofFn (rOf s (b ^^ side)),
      resp A.int i₀.2 i₁.2 (b ^^ side)⟩ := by
    unfold tokD
    rw [tok_of_fin A.int i₀ i₁ (b ^^ side)]
    simp only [hf', ↓reduceIte, Option.getD_some]
    cases b ^^ side <;> rfl
  have hP : ptM A idx b s (some (simulate pIm k.1.1)) (some (simulate pIm k.2.1.1)) side =
      ⟨⟨nOf s (b ^^ side), List.ofFn (rOf s (b ^^ side)), resp A.int i₀.2 i₁.2 (b ^^ side)⟩,
        (A.int.choose i₀.2 i₁.2 side).1, idx (A.int.choose i₀.2 i₁.2 side).1 (A.int.pk (b ^^ side)),
        (A.int.choose i₀.2 i₁.2 side).2⟩ := by
    unfold ptM pt
    rw [htok]
  rw [hP] at hy
  unfold redStmt at hy
  split at hy
  · cases hy
  · split_ifs at hy with he
    · cases hy
      refine ⟨?_, wPre_redeemWitness _ _ _ _ _ _⟩
      refine congrArg stR ?_
      unfold xRM xSideM nOf
      cases b ^^ side <;> rfl

/-! ## The hidden redemption proofs -/

/-- The witness prefix of the redemption statement of side `side` (zero if there is none). -/
noncomputable def hidR (b side : Bool) (s : SecM) (c₁ c₂ : SimCoins pIm) : Bytes 16 :=
  match redStmt A (ptM A idx b s (some (simulate pIm c₁)) (some (simulate pIm c₂)) side) with
  | some y => wPre y.2
  | none => fun _ => 0

/-- The candidates for the label offset of that proof, from a read set, the simulator's shared
tape and its corrections. -/
noncomputable def hidG (b side : Bool) (s : SecM) (c₁ c₂ : SimCoins pIm) (S5 : Finset (SKey pRm))
    (sh : Shared) (c : Bytes (16 * pRm.correctionBytes)) : Finset W128 :=
  match redStmt A (ptM A idx b s (some (simulate pIm c₁)) (some (simulate pIm c₂)) side) with
  | some y => guessSet Hashes.shake CrtGen.tables (withP y.1 pRm) S5 sh (fieldsCD c (zeroB _))
  | none => ∅

lemma card_hidG_le (b side : Bool) (s : SecM) (c₁ c₂ : SimCoins pIm) (S5 : Finset (SKey pRm))
    (sh : Shared) (c : Bytes (16 * pRm.correctionBytes)) :
    (hidG A idx b side s c₁ c₂ S5 sh c).card ≤ S5.card + 1 := by
  unfold hidG
  split
  · exact card_guessSet_le _ _ _ _ _ _
  · exact Nat.zero_le _

/-- **The prediction of a redemption proof, with `d` separated**: the target and the candidates do
not read the simulator's `d`. -/
lemma predJ_hid (b side : Bool) (s : SecM) (c₁ c₂ : SimCoins pIm) (S5 : Finset (SKey pRm))
    (k : SimCoins pRm × Vis pRm) :
    predJ Hashes.shake CrtGen.tables mainP_pRm S5 ((simP pRm).obs
      (redStmt A (ptM A idx b s (some (simulate pIm c₁)) (some (simulate pIm c₂)) side)) k) →
    thetaMain (pre16 mainP_pRm.hw k.1.2.2.2.2.1) (hidR A idx b side s c₁ c₂) ∈
      hidG A idx b side s c₁ c₂ S5 k.1.1 k.1.2.1 := by
  unfold hidR hidG
  generalize redStmt A (ptM A idx b s (some (simulate pIm c₁)) (some (simulate pIm c₂)) side) = y
  cases y with
  | none => exact fun h => (predJ_simP_none _ _ _ _ _ h).elim
  | some y =>
    intro h
    rw [predJ_simP, mem_candJ] at h
    have e := guessSet_fieldsCD Hashes.shake CrtGen.tables y.1 S5 k.1.1 k.1.2.1 (zeroB _)
      k.1.2.2.2.2.1
    show _ ∈ guessSet Hashes.shake CrtGen.tables (withP y.1 pRm) S5 k.1.1
      (fieldsCD k.1.2.1 (zeroB _))
    rw [e]
    exact h

/-! ## The reduction -/

/-- The event of `puTerm`, unfolded. -/
lemma puEv_iff (b : Bool) (x : SecM × AuxM) :
    ev (gameM A idx b) (simP pIm) (simP pIm) (simP pRm) (simP pRm)
      (predAll Hashes.shake CrtGen.tables mainP_pIm mainP_pIm mainP_pRm mainP_pRm
        (rM₁ A idx b) (rM₂ A idx b) (rM₃ A idx b) (rM₄ A idx b)) x ↔
    (predJ Hashes.shake CrtGen.tables mainP_pIm
        (A.R₁ (reqS (tM A x.1 false) x.2.1.1) (reqS (tM A x.1 true) x.2.2.1.1)
          (ySimM A idx b (tM A x.1 false) (tM A x.1 true) (nOf x.1 false) (nOf x.1 true) x.2)
          (visM x.2))
        ((simP pIm).obs (some (issStmt A x.1 false)) x.2.1) ∨
      predJ Hashes.shake CrtGen.tables mainP_pIm
        (A.R₂ (reqS (tM A x.1 false) x.2.1.1) (reqS (tM A x.1 true) x.2.2.1.1)
          (ySimM A idx b (tM A x.1 false) (tM A x.1 true) (nOf x.1 false) (nOf x.1 true) x.2)
          (visM x.2))
        ((simP pIm).obs (some (issStmt A x.1 true)) x.2.2.1) ∨
      predJ Hashes.shake CrtGen.tables mainP_pRm
        (A.R₃ (reqS (tM A x.1 false) x.2.1.1) (reqS (tM A x.1 true) x.2.2.1.1)
          (ySimM A idx b (tM A x.1 false) (tM A x.1 true) (nOf x.1 false) (nOf x.1 true) x.2)
          (visM x.2))
        ((simP pRm).obs (redStmt A (ptM A idx b x.1 (some (simulate pIm x.2.1.1))
          (some (simulate pIm x.2.2.1.1)) false)) x.2.2.2.1) ∨
      predJ Hashes.shake CrtGen.tables mainP_pRm
        (A.R₄ (reqS (tM A x.1 false) x.2.1.1) (reqS (tM A x.1 true) x.2.2.1.1)
          (ySimM A idx b (tM A x.1 false) (tM A x.1 true) (nOf x.1 false) (nOf x.1 true) x.2)
          (visM x.2))
        ((simP pRm).obs (redStmt A (ptM A idx b x.1 (some (simulate pIm x.2.1.1))
          (some (simulate pIm x.2.2.1.1)) true)) x.2.2.2.2)) := by
  rw [← yM_sim A idx b x.1 x.2]
  exact Iff.rfl

/-- The event that Client `c`'s opening is among its predictor's candidates. -/
def winM (b c : Bool) (x : SecM × AuxM) : Prop :=
  rOf x.1 c ∈ predM A idx b (tM A x.1 false) (tM A x.1 true) (nOf x.1 false) (nOf x.1 true) x.2 c

/-- The hidden redemption of side `side`: its `d` makes the dummy or real target a candidate. -/
def hidEv₃ (b : Bool) (x : SecM × AuxM) : Prop :=
  thetaMain (pre16 mainP_pRm.hw x.2.2.2.1.1.2.2.2.2.1) (hidR A idx b false x.1 x.2.1.1 x.2.2.1.1) ∈
    hidG A idx b false x.1 x.2.1.1 x.2.2.1.1
      (A.R₃ (reqS (tM A x.1 false) x.2.1.1) (reqS (tM A x.1 true) x.2.2.1.1) none (visM x.2))
      x.2.2.2.1.1.1 x.2.2.2.1.1.2.1

def hidEv₄ (b : Bool) (x : SecM × AuxM) : Prop :=
  thetaMain (pre16 mainP_pRm.hw x.2.2.2.2.1.2.2.2.2.1) (hidR A idx b true x.1 x.2.1.1 x.2.2.1.1) ∈
    hidG A idx b true x.1 x.2.1.1 x.2.2.1.1
      (A.R₄ (reqS (tM A x.1 false) x.2.1.1) (reqS (tM A x.1 true) x.2.2.1.1) none (visM x.2))
      x.2.2.2.2.1.1 x.2.2.2.2.1.2.1

-- (The defeq checks on the nested tape exceed the default recursion depth.)
set_option maxRecDepth 8192 in
/-- **The (PU) event implies a prediction or a hit of a hidden proof's `d`.** -/
theorem puEv_imp (b : Bool) (x : SecM × AuxM)
    (h : ev (gameM A idx b) (simP pIm) (simP pIm) (simP pRm) (simP pRm)
      (predAll Hashes.shake CrtGen.tables mainP_pIm mainP_pIm mainP_pRm mainP_pRm
        (rM₁ A idx b) (rM₂ A idx b) (rM₃ A idx b) (rM₄ A idx b)) x) :
    (winM A idx b false x ∨ winM A idx b true x) ∨ hidEv₃ A idx b x ∨ hidEv₄ A idx b x := by
  rw [puEv_iff] at h
  obtain ⟨s, k⟩ := x
  dsimp only at h ⊢
  have hY : allOkT A.int idx (reqS (tM A s false) k.1.1) (reqS (tM A s true) k.2.1.1)
      (tM A s false) (tM A s true) = false →
      ySimM A idx b (tM A s false) (tM A s true) (nOf s false) (nOf s true) k = none := by
    intro hok
    unfold ySimM
    rw [hok]
    rfl
  rcases h with h | h | h | h
  · -- issuance of Client `false`
    rw [predJ_simP] at h
    refine Or.inl (Or.inl ?_)
    unfold winM predM
    refine Finset.mem_union_left _ ?_
    have hw : wPre (issStmt A s false).2 = rOf s false := wPre_issueWitness _ _ _ _
    rw [hw] at h
    exact h
  · -- issuance of Client `true`
    rw [predJ_simP] at h
    refine Or.inl (Or.inr ?_)
    unfold winM predM
    refine Finset.mem_union_left _ ?_
    have hw : wPre (issStmt A s true).2 = rOf s true := wPre_issueWitness _ _ _ _
    rw [hw] at h
    exact h
  · -- redemption of the left side: Client `b`
    cases hok : allOkT A.int idx (reqS (tM A s false) k.1.1) (reqS (tM A s true) k.2.1.1)
      (tM A s false) (tM A s true)
    · rw [hY hok] at h
      exact Or.inr (Or.inl (predJ_hid A idx b false s k.1.1 k.2.1.1 _ k.2.2.1 h))
    · have hfin : ∀ c, finT A.int (reqS (tM A s false) k.1.1) (reqS (tM A s true) k.2.1.1)
          (tM A s false) (tM A s true) c = true := by
        have := hok
        unfold allOkT at this
        simp only [Bool.and_eq_true] at this
        intro c
        cases c
        · exact this.1.1.1.1.1
        · exact this.1.1.1.1.2
      rcases hy : redStmt A (ptM A idx b s (some (simulate pIm k.1.1)) (some (simulate pIm k.2.1.1))
        false) with _ | y
      · rw [hy] at h
        exact (predJ_simP_none _ _ _ _ _ h).elim
      · rw [hy, predJ_simP] at h
        obtain ⟨h1, h2⟩ := redStmt_fin A idx b s k false (hfin _) y hy
        rw [h1, h2] at h
        have hc : (b ^^ false) = b := Bool.xor_false b
        rw [hc] at h
        have hin : rOf s b ∈ predM A idx b (tM A s false) (tM A s true) (nOf s false) (nOf s true)
            k b := by
          unfold predM
          refine Finset.mem_union_right _ ?_
          rw [hok, Bool.xor_self]
          exact h
        cases b
        · exact Or.inl (Or.inl hin)
        · exact Or.inl (Or.inr hin)
  · -- redemption of the right side: Client `!b`
    cases hok : allOkT A.int idx (reqS (tM A s false) k.1.1) (reqS (tM A s true) k.2.1.1)
      (tM A s false) (tM A s true)
    · rw [hY hok] at h
      exact Or.inr (Or.inr (predJ_hid A idx b true s k.1.1 k.2.1.1 _ k.2.2.2 h))
    · have hfin : ∀ c, finT A.int (reqS (tM A s false) k.1.1) (reqS (tM A s true) k.2.1.1)
          (tM A s false) (tM A s true) c = true := by
        have := hok
        unfold allOkT at this
        simp only [Bool.and_eq_true] at this
        intro c
        cases c
        · exact this.1.1.1.1.1
        · exact this.1.1.1.1.2
      rcases hy : redStmt A (ptM A idx b s (some (simulate pIm k.1.1)) (some (simulate pIm k.2.1.1))
        true) with _ | y
      · rw [hy] at h
        exact (predJ_simP_none _ _ _ _ _ h).elim
      · rw [hy, predJ_simP] at h
        obtain ⟨h1, h2⟩ := redStmt_fin A idx b s k true (hfin _) y hy
        rw [h1, h2] at h
        have hc : (b ^^ true) = !b := Bool.xor_true b
        rw [hc] at h
        have hin : rOf s (!b) ∈ predM A idx b (tM A s false) (tM A s true) (nOf s false)
            (nOf s true) k (!b) := by
          unfold predM
          refine Finset.mem_union_right _ ?_
          rw [hok, show (b ^^ !b) = true by cases b <;> rfl]
          exact h
        cases b
        · exact Or.inl (Or.inr hin)
        · exact Or.inl (Or.inl hin)

/-- **The predictor for Client `false`** in the game `PU.puAdv`: public part `nf₀`, commitment
`t₀`, auxiliary coins the other Client's `(nf₁, r₁)`, the simulators' coins and the tables. -/
noncomputable def predM₀ (b : Bool) (n : Coins nfBytes) (t : Bytes)
    (a : (Coins nfBytes × Coins rBytes) × AuxM) : Finset (Coins rBytes) :=
  predM A idx b t (comM A a.1.1 a.1.2) (List.ofFn n) (List.ofFn a.1.1) a.2 false

/-- **The predictor for Client `true`.** -/
noncomputable def predM₁ (b : Bool) (n : Coins nfBytes) (t : Bytes)
    (a : (Coins nfBytes × Coins rBytes) × AuxM) : Finset (Coins rBytes) :=
  predM A idx b (comM A a.1.1 a.1.2) t (List.ofFn a.1.1) (List.ofFn n) a.2 true

theorem pr_winM_false (b : Bool) :
    pr (SecM × AuxM) (winM A idx b false) = puAdv (comM A) (predM₀ A idx b) := by
  let e : (Coins nfBytes × Coins rBytes) × ((Coins nfBytes × Coins rBytes) × AuxM) ≃ SecM × AuxM :=
    { toFun := fun z => ((z.1, z.2.1), z.2.2)
      invFun := fun x => (x.1.1, (x.1.2, x.2))
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [← pr_equiv e]
  rfl

theorem pr_winM_true (b : Bool) :
    pr (SecM × AuxM) (winM A idx b true) = puAdv (comM A) (predM₁ A idx b) := by
  let e : (Coins nfBytes × Coins rBytes) × ((Coins nfBytes × Coins rBytes) × AuxM) ≃ SecM × AuxM :=
    { toFun := fun z => ((z.2.1, z.1), z.2.2)
      invFun := fun x => (x.1.2, (x.1.1, x.2))
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [← pr_equiv e]
  rfl

theorem pr_hidEv₃_le {q5 : ℕ} (h₃ : ∀ q₀ q₁ y v, (A.R₃ q₀ q₁ y v).card ≤ q5) (b : Bool) :
    pr (SecM × AuxM) (hidEv₃ A idx b) ≤ (q5 + 1) / 2 ^ 128 := by
  have key := pr_d3_le (S := SecM) (K₁ := SimCoins pIm × Vis pIm) (K₂ := SimCoins pIm × Vis pIm)
    (Sh := Shared) (C := Bytes (16 * pRm.correctionBytes)) (X := Bytes (pRm.nMask * pRm.nMultBytes))
    (Y := Bytes 64) (Z := Bytes (16 * (pRm.qsDegree - 1))) (V := Vis pRm)
    (K₄ := SimCoins pRm × Vis pRm) mainP_pRm.hw
    (fun ω => hidR A idx b false ω.1 ω.2.1.1 ω.2.2.1.1)
    (fun ω => hidG A idx b false ω.1 ω.2.1.1 ω.2.2.1.1
      (A.R₃ (reqS (tM A ω.1 false) ω.2.1.1) (reqS (tM A ω.1 true) ω.2.2.1.1) none
        (ω.2.1.2, ω.2.2.1.2, ω.2.2.2.1.2, ω.2.2.2.2.2)) ω.2.2.2.1.1.1 ω.2.2.2.1.1.2.1)
    (q := q5)
    (fun ω => (card_hidG_le A idx b false _ _ _ _ _ _).trans (Nat.succ_le_succ (h₃ _ _ _ _)))
  exact le_trans (le_of_eq (pr_inst_irrel _ _ _)) key

theorem pr_hidEv₄_le {q5 : ℕ} (h₄ : ∀ q₀ q₁ y v, (A.R₄ q₀ q₁ y v).card ≤ q5) (b : Bool) :
    pr (SecM × AuxM) (hidEv₄ A idx b) ≤ (q5 + 1) / 2 ^ 128 := by
  have key := pr_d4_le (S := SecM) (K₁ := SimCoins pIm × Vis pIm) (K₂ := SimCoins pIm × Vis pIm)
    (K₃ := SimCoins pRm × Vis pRm)
    (Sh := Shared) (C := Bytes (16 * pRm.correctionBytes)) (X := Bytes (pRm.nMask * pRm.nMultBytes))
    (Y := Bytes 64) (Z := Bytes (16 * (pRm.qsDegree - 1))) (V := Vis pRm) mainP_pRm.hw
    (fun ω => hidR A idx b true ω.1 ω.2.1.1 ω.2.2.1.1)
    (fun ω => hidG A idx b true ω.1 ω.2.1.1 ω.2.2.1.1
      (A.R₄ (reqS (tM A ω.1 false) ω.2.1.1) (reqS (tM A ω.1 true) ω.2.2.1.1) none
        (ω.2.1.2, ω.2.2.1.2, ω.2.2.2.1.2, ω.2.2.2.2.2)) ω.2.2.2.2.1.1 ω.2.2.2.2.1.2.1)
    (q := q5)
    (fun ω => (card_hidG_le A idx b true _ _ _ _ _ _).trans (Nat.succ_le_succ (h₄ _ _ _ _)))
  exact le_trans (le_of_eq (pr_inst_irrel _ _ _)) key

/-- `puTerm` on the tape `SecM × AuxM`. -/
theorem puTerm_eq (b : Bool) :
    puTerm A idx b = pr (SecM × AuxM) (ev (gameM A idx b) (simP pIm) (simP pIm) (simP pRm) (simP pRm)
      (predAll Hashes.shake CrtGen.tables mainP_pIm mainP_pIm mainP_pRm mainP_pRm
        (rM₁ A idx b) (rM₂ A idx b) (rM₃ A idx b) (rM₄ A idx b))) := by
  unfold puTerm
  exact pr_inst_irrel _ _ _

/-- **The (PU) term is at most the advantage of the two explicit predictors**, plus
`2·(q₅ + 1)·2⁻¹²⁸` for the redemption proofs that are not shown. -/
theorem puTerm_le {q5 : ℕ} (h₃ : ∀ q₀ q₁ y v, (A.R₃ q₀ q₁ y v).card ≤ q5)
    (h₄ : ∀ q₀ q₁ y v, (A.R₄ q₀ q₁ y v).card ≤ q5) (b : Bool) :
    puTerm A idx b ≤ puAdv (comM A) (predM₀ A idx b) + puAdv (comM A) (predM₁ A idx b) +
      2 * ((q5 + 1) / 2 ^ 128) := by
  rw [puTerm_eq]
  have h := (pr_mono (puEv_imp A idx b)).trans ((pr_or_le _ _).trans (add_le_add (pr_or_le _ _)
    (pr_or_le _ _)))
  rw [pr_winM_false, pr_winM_true] at h
  have a₃ := pr_hidEv₃_le A idx h₃ b
  have a₄ := pr_hidEv₄_le A idx h₄ b
  exact h.trans (by linarith)

/-! ## Theorem 4(a) on `main`, with (PU) as a game -/

/-- **Theorem 4(a) on `main` (no label rows), with the (PU) advantage of explicit predictors.**
`anonymity_main` with `puTerm` replaced by `puTerm_le`: for the colluding adversary whose guess
reads each `H₃` and cipher table at `q3`, `qE` keys and each `H₅` table at a consistent read set
of at most `q5` keys,

    |Pr[world 0] − Pr[world 1]| ≤ 8·εRF(q3, qE)
      + 15·(Σ_{b, c} puAdv Com (predM_c b) + 4·(q5 + 1)·2⁻¹²⁸) + 2·εhide.

Each predictor outputs at most `2·(q5 + 1)` candidates (`card_predM_le`). The four `puAdv` terms
are the only ones that are not explicit numbers besides `εhide`: they are (PU), an assumption on
Keccak-p[800,12]. -/
theorem anonymity_main_pu {q3 q5 qE : ℕ} (hA : A.Budget q3 qE) (hC : A.Cons)
    (h₃ : ∀ q₀ q₁ y v, (A.R₃ q₀ q₁ y v).card ≤ q5) (h₄ : ∀ q₀ q₁ y v, (A.R₄ q₀ q₁ y v).card ≤ q5)
    {εhide : ℝ} (hhide : ∀ v b c, hidingAdv (A.atV v).ci (A.atV v).cr
      (reduction (A.atV v) idx simIM simRM b c) ≤ εhide) :
    |realMain A idx false - realMain A idx true| ≤
      8 * εRF q3 qE + 15 * (puAdv (comM A) (predM₀ A idx false) +
        puAdv (comM A) (predM₁ A idx false) + puAdv (comM A) (predM₀ A idx true) +
        puAdv (comM A) (predM₁ A idx true) + 4 * ((q5 + 1) / 2 ^ 128)) + 2 * εhide := by
  have h := anonymity_main A idx hA hC hhide
  have p0 := puTerm_le A idx h₃ h₄ false
  have p1 := puTerm_le A idx h₃ h₄ true
  linarith

end VoleMole.Privacy.Moussaka
