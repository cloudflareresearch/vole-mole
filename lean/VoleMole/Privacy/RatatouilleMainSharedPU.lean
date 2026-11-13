import VoleMole.Privacy.RatatouilleMainShared
import VoleMole.ZK.MainSharedSim

/-!
# Ratatouille on `main` with shared tables: the (PU) term as explicit predictors and numbers

`unlinkability_main_shared0` (`Privacy/RatatouilleMainShared.lean`) bounds Theorem 2 on `main` with
a shared `H₅` table and cipher by `30·εS + 15·(puTermSR (b₁, b₂) + puTermSR (b₁', b₂')) + 2·εhide`,
with `puTermSR` the event `ZK.Sim.bstar` in the game with all four proofs simulated. Here that
event is bounded, as `Privacy/MoussakaMainSharedPU.lean` does for Moussaka.

**With all proofs simulated** (`ZK.Sim.bstar_sim`) `bstar` implies one of:

* a simulation failed: `noHitProb` each (`pr_errSR₁_le` …);
* **a prediction**: for some proof, the opening that is its witness prefix is a candidate
  (`ZK.Sim.candC`) of the **public key set** `spubR`: the guess's `H₅` read set and the active gate
  inputs of the four simulated proofs. The statements, the guess's input and the tables the guess
  sees are functions of the nullifiers, the commitments, the simulators' coins and the raw tables
  (`simSR_eq`, `Privacy/RatatouilleMainPub.lean`). The three openings are those of
  `Privacy/RatatouilleMainPU.lean`: the two issued tokens' (`predSR₀`, `predSR₁`, for
  `comI = Com(nf, ctx, T_init, r)`), and round 1's change token's (`predSRC`, for `comCh`: the
  commitment at the credit `clientCheck(τ₁.t, τ₁.x, d₁)`, which is part of the public input);
* **a collision between two simulated proofs**: a sibling gate input of one is a sibling gate input
  of another. The later proof's field `d` is uniform and independent of the earlier proofs and of
  its own statement and opening, so this has probability `≤ (312·j + 1)·2⁻¹²⁸` for the `j` earlier
  proofs (`ZK.Sim.pr_sib_hit_le`; `pr_collR₂_le`, `pr_collR₃_le`, `pr_collR₄_le`): `1875·2⁻¹²⁸`.

**`puTermSR_le`**: `puTermSR (b₁, b₂) ≤ 4·noHitProb + puAdv comI predSR₀ + puAdv comI predSR₁ +
puAdv comCh predSRC + 1875·2⁻¹²⁸`. The predictors of the issued tokens' openings output at most
`3·(q₅ + 1249)` candidates and the change token's at most `q₅ + 1249`, if the guess's `H₅` read set
has at most `q₅` keys (`card_predIS_le`, `card_predCS_le`).

**`unlinkability_main_shared`**: Theorem 2 on `main` with a shared `H₅` table and cipher,

    |Pr[world (b₁, b₂)] − Pr[world (b₁', b₂')]| ≤ 30·εS(q₃, q_E + 8·4607)
      + 15·(PU(b₁, b₂) + PU(b₁', b₂') + 8·noHitProb + 3750·2⁻¹²⁸) + 2·εhide,

`PU(b₁, b₂)` the sum of the three `puAdv` terms of the world. They are (PU), an assumption on
Keccak-p[800,12] (`Privacy/PU.lean`, `lean/docs/zk.md` §4.3); `εhide` is hiding of `Com`;
everything else is a number (`noHitProb ≤ 2^{−2¹⁵}`, `ZK.Sim.noHitProb_le`).
-/

open Finset

-- (The coin types are large products: their `Fintype` instances exceed the default size.)
set_option synthInstance.maxSize 1024

set_option linter.unusedSectionVars false
set_option linter.constructorNameAsVariable false

namespace VoleMole.Privacy.Ratatouille

open VoleMole.Spec.Ratatouille VoleMole.ZK.Sim VoleMole.Privacy.MainChain
open VoleMole.Verifier VoleMole.Verifier.Bridge VoleMole.Privacy.PU

attribute [local irreducible] simulate realRO progRO

variable [HasPrg]

/-! ## Optional statements -/

/-- A statement with the opening that is its witness prefix. -/
def qo (st : Option Statement) (r : ZK.Sim.Bytes 16) : Option (Statement × ZK.Sim.Bytes 16) :=
  st.map fun st => (st, r)

/-- The active gate inputs of a simulated proof (none without a statement). -/
noncomputable def actLo {p : Params} (st : Option Statement) (E : Cipher) (c : SimCoins p) :
    List ByteArray :=
  match st with
  | some st => actL Hashes.shake p st E c
  | none => []

/-- The candidates of a simulated proof (none without a statement). -/
noncomputable def candCo {p : Params} (st : Option Statement) (E : Cipher) (c : SimCoins p)
    (S : Finset (ZK.Sim.Bytes 37)) : Finset (ZK.Sim.Bytes 16) :=
  match st with
  | some st => candC Hashes.shake st E c S
  | none => ∅

lemma actO_qo {p : Params} (st : Option Statement) (r : ZK.Sim.Bytes 16) (E : Cipher)
    (c : SimCoins p) : actO Hashes.shake p (qo st r) E c = actLo st E c := by
  rcases st with _ | st <;> rfl

set_option maxRecDepth 8000 in
lemma candO_qo {p : Params} (st : Option Statement) (r : ZK.Sim.Bytes 16) (E : Cipher)
    (c : SimCoins p) (S : Finset (ZK.Sim.Bytes 37)) (h : candO Hashes.shake (qo st r) E c S) :
    r ∈ candCo st E c S := by
  rcases st with _ | st
  · exact h.elim
  · exact h

/-- The slot of a statement whose first component and witness prefix are known. -/
lemma qOf_of (y : Option SW) (st : Option Statement) (r : ZK.Sim.Bytes 16)
    (hst : y.map Prod.fst = st) (hr : ∀ z ∈ y, wPre z.2 = r) : qOf y = qo st r := by
  rcases y with _ | y
  · rw [← hst]; rfl
  · rw [← hst]
    simp only [qOf, qo, Option.map_some, hr y rfl]

lemma card_imgo_le {p : Params} (st : Option Statement) (E : Cipher) (c : SimCoins p) :
    ((actLo st E c).toFinset.image (blk 37)).card ≤ 312 := by
  refine card_image_le.trans ((List.toFinset_card_le _).trans ?_)
  rcases st with _ | st
  · simp [actLo]
  · exact actL_length_le _ _ _ _

lemma card_candCo_le {p : Params} (hm : MainP p) (st : Option Statement) (E : Cipher)
    (c : SimCoins p) (S : Finset (ZK.Sim.Bytes 37)) : (candCo st E c S).card ≤ S.card + 1 := by
  rcases st with _ | st
  · exact Nat.zero_le _
  · exact card_candC_le Hashes.shake hm st E c S

variable (A : AdversarySR)

/-! ## The public key set and the predictors -/

section Pred

variable (b₁ b₂ : Bool) (n : Quad Nullifier) (t : Commitment × Commitment)
  (cf₂ cf₃ : Credits → Commitment) (a : AuxSR)

/-- The guess's `H₅` read set with all proofs simulated, from public values. -/
noncomputable def r5R : Finset (ZK.Sim.Bytes 37) :=
  A.R5 (gP A.toM b₁ b₂ n t cf₂ cf₃ (coSR a)) (vtab A (gP A.toM b₁ b₂ n t cf₂ cf₃ (coSR a)) a)

/-- **The public key set**: the guess's `H₅` read set and the active gate inputs of the four
simulated proofs. -/
noncomputable def spubR : Finset (ZK.Sim.Bytes 37) :=
  r5R A b₁ b₂ n t cf₂ cf₃ a ∪
    ((actLo (stIP A.toM t.1) a.1.2 a.2.1.1.2).toFinset.image (blk 37) ∪
      (actLo (stIP A.toM t.2) a.1.2 a.2.2.1.1.2).toFinset.image (blk 37) ∪
      (actLo (st₃P A.toM b₁ n t cf₂ (coSR a)) a.1.2 a.2.2.2.1.1.2).toFinset.image (blk 37) ∪
      (actLo (st₄P A.toM b₁ b₂ n t cf₂ cf₃ (coSR a)) a.1.2 a.2.2.2.2.1.2).toFinset.image (blk 37))

/-- **The predictor for the opening of Client `c`'s issued token**: the candidates, for the public
key set, of its issuance proof, of round 1's spend proof if `c = b₁`, and of round 2's spend proof
if Client `c = !b₁` spends there (`b₂ ≠ b₁`). -/
noncomputable def predIS (c : Bool) : Finset (Coins 16) :=
  (bif c then candCo (stIP A.toM t.2) a.1.2 a.2.2.1.1.2 (spubR A b₁ b₂ n t cf₂ cf₃ a)
    else candCo (stIP A.toM t.1) a.1.2 a.2.1.1.2 (spubR A b₁ b₂ n t cf₂ cf₃ a)) ∪
    ((bif b₁ == c then candCo (st₃P A.toM b₁ n t cf₂ (coSR a)) a.1.2 a.2.2.2.1.1.2
        (spubR A b₁ b₂ n t cf₂ cf₃ a) else ∅) ∪
      (bif (b₂ != b₁) && (c != b₁) then
        candCo (st₄P A.toM b₁ b₂ n t cf₂ cf₃ (coSR a)) a.1.2 a.2.2.2.2.1.2
          (spubR A b₁ b₂ n t cf₂ cf₃ a) else ∅))

/-- **The predictor for the opening of round 1's change token**: the candidates of round 2's spend
proof, if the change token is spent there (`b₂ = b₁`). -/
noncomputable def predCS : Finset (Coins 16) :=
  bif b₂ == b₁ then candCo (st₄P A.toM b₁ b₂ n t cf₂ cf₃ (coSR a)) a.1.2 a.2.2.2.2.1.2
    (spubR A b₁ b₂ n t cf₂ cf₃ a) else ∅

/-- The predictor of the change token reads `cf₂` at the credit `cr₁P` only. -/
lemma predCS_const :
    predCS A b₁ b₂ n t cf₂ cf₃ a =
      predCS A b₁ b₂ n t (fun _ => cf₂ (cr₁P A.toM b₁ n.1 t (coSR a).1)) cf₃ a := by
  unfold predCS spubR r5R
  rw [gP_const A.toM b₁ b₂ n t cf₂ cf₃ (coSR a), st₃P_const A.toM b₁ n t cf₂ (coSR a),
    st₄P_const A.toM b₁ b₂ n t cf₂ cf₃ (coSR a)]

variable {q5 : ℕ} (h : ∀ g v, (A.R5 g v).card ≤ q5)
include h

lemma card_spubR_le : (spubR A b₁ b₂ n t cf₂ cf₃ a).card ≤ q5 + 1248 := by
  unfold spubR
  have a₁ := card_imgo_le (p := pIr) (stIP A.toM t.1) a.1.2 a.2.1.1.2
  have a₂ := card_imgo_le (p := pIr) (stIP A.toM t.2) a.1.2 a.2.2.1.1.2
  have a₃ := card_imgo_le (p := pSr) (st₃P A.toM b₁ n t cf₂ (coSR a)) a.1.2 a.2.2.2.1.1.2
  have a₄ := card_imgo_le (p := pSr) (st₄P A.toM b₁ b₂ n t cf₂ cf₃ (coSR a)) a.1.2 a.2.2.2.2.1.2
  have hr : (r5R A b₁ b₂ n t cf₂ cf₃ a).card ≤ q5 := h _ _
  generalize r5R A b₁ b₂ n t cf₂ cf₃ a = R at hr ⊢
  generalize image (blk 37) (actLo (stIP A.toM t.1) a.1.2 a.2.1.1.2).toFinset = X₁ at a₁ ⊢
  generalize image (blk 37) (actLo (stIP A.toM t.2) a.1.2 a.2.2.1.1.2).toFinset = X₂ at a₂ ⊢
  generalize image (blk 37) (actLo (st₃P A.toM b₁ n t cf₂ (coSR a)) a.1.2
    a.2.2.2.1.1.2).toFinset = X₃ at a₃ ⊢
  generalize image (blk 37) (actLo (st₄P A.toM b₁ b₂ n t cf₂ cf₃ (coSR a)) a.1.2
    a.2.2.2.2.1.2).toFinset = X₄ at a₄ ⊢
  have u₀ := card_union_le R (X₁ ∪ X₂ ∪ X₃ ∪ X₄)
  have u₁ := card_union_le (X₁ ∪ X₂ ∪ X₃) X₄
  have u₂ := card_union_le (X₁ ∪ X₂) X₃
  have u₃ := card_union_le X₁ X₂
  omega

/-- **At most `3·(q₅ + 1249)` candidates**, if the read set has at most `q₅` keys. -/
theorem card_predIS_le (c : Bool) : (predIS A b₁ b₂ n t cf₂ cf₃ a c).card ≤ 3 * (q5 + 1249) := by
  have hS := card_spubR_le A b₁ b₂ n t cf₂ cf₃ a h
  have hI : ∀ (st : Option Statement) (cc : SimCoins pIr),
      (candCo st a.1.2 cc (spubR A b₁ b₂ n t cf₂ cf₃ a)).card ≤ q5 + 1249 :=
    fun st cc => (card_candCo_le mainP_pIr st a.1.2 cc _).trans (by omega)
  have hSp : ∀ (st : Option Statement) (cc : SimCoins pSr),
      (candCo st a.1.2 cc (spubR A b₁ b₂ n t cf₂ cf₃ a)).card ≤ q5 + 1249 :=
    fun st cc => (card_candCo_le mainP_pSr st a.1.2 cc _).trans (by omega)
  unfold predIS
  generalize spubR A b₁ b₂ n t cf₂ cf₃ a = Sp at hI hSp ⊢
  have e₁ : (bif c then candCo (stIP A.toM t.2) a.1.2 a.2.2.1.1.2 Sp
      else candCo (stIP A.toM t.1) a.1.2 a.2.1.1.2 Sp).card ≤ q5 + 1249 := by
    cases c
    · exact hI _ _
    · exact hI _ _
  have e₂ : (bif b₁ == c then candCo (st₃P A.toM b₁ n t cf₂ (coSR a)) a.1.2 a.2.2.2.1.1.2 Sp
      else ∅).card ≤ q5 + 1249 := by
    cases b₁ == c
    · exact Nat.zero_le _
    · exact hSp _ _
  have e₃ : (bif (b₂ != b₁) && (c != b₁) then
      candCo (st₄P A.toM b₁ b₂ n t cf₂ cf₃ (coSR a)) a.1.2 a.2.2.2.2.1.2 Sp else ∅).card ≤
      q5 + 1249 := by
    cases (b₂ != b₁) && (c != b₁)
    · exact Nat.zero_le _
    · exact hSp _ _
  have u₁ := card_union_le (bif c then candCo (stIP A.toM t.2) a.1.2 a.2.2.1.1.2 Sp
      else candCo (stIP A.toM t.1) a.1.2 a.2.1.1.2 Sp)
    ((bif b₁ == c then candCo (st₃P A.toM b₁ n t cf₂ (coSR a)) a.1.2 a.2.2.2.1.1.2 Sp else ∅) ∪
      (bif (b₂ != b₁) && (c != b₁) then
        candCo (st₄P A.toM b₁ b₂ n t cf₂ cf₃ (coSR a)) a.1.2 a.2.2.2.2.1.2 Sp else ∅))
  have u₂ := card_union_le
    (bif b₁ == c then candCo (st₃P A.toM b₁ n t cf₂ (coSR a)) a.1.2 a.2.2.2.1.1.2 Sp else ∅)
    (bif (b₂ != b₁) && (c != b₁) then
      candCo (st₄P A.toM b₁ b₂ n t cf₂ cf₃ (coSR a)) a.1.2 a.2.2.2.2.1.2 Sp else ∅)
  omega

/-- **At most `q₅ + 1249` candidates.** -/
theorem card_predCS_le : (predCS A b₁ b₂ n t cf₂ cf₃ a).card ≤ q5 + 1249 := by
  have hS := card_spubR_le A b₁ b₂ n t cf₂ cf₃ a h
  unfold predCS
  cases b₂ == b₁
  · exact Nat.zero_le _
  · exact (card_candCo_le mainP_pSr _ a.1.2 _ _).trans (by omega)

end Pred

/-! ## The slots of the simulated game -/

/-- The spend statements depend on the simulators' coins of the earlier proofs only. -/
lemma st₃P_congr (B : AdversaryRM) (b₁ : Bool) (n : Quad Nullifier) (t : Commitment × Commitment)
    (cf₂ : Credits → Commitment) (co co' : CoR) (h : co.1 = co'.1) :
    st₃P B b₁ n t cf₂ co = st₃P B b₁ n t cf₂ co' := by
  unfold st₃P
  rw [h]

lemma st₄P_congr (B : AdversaryRM) (b₁ b₂ : Bool) (n : Quad Nullifier)
    (t : Commitment × Commitment) (cf₂ cf₃ : Credits → Commitment) (co co' : CoR)
    (h : co.1 = co'.1) (h' : co.2.1 = co'.2.1) :
    st₄P B b₁ b₂ n t cf₂ cf₃ co = st₄P B b₁ b₂ n t cf₂ cf₃ co' := by
  unfold st₄P ok₂P τ₂P d₂P oP
  rw [h, h']

/-- The statement and opening of Client `c`'s issuance proof. -/
def qS₁ (s : SecR) : Option (Statement × ZK.Sim.Bytes 16) :=
  qo (stIP A.toM (tS A.toM s).1) s.1.1.2

def qS₂ (s : SecR) : Option (Statement × ZK.Sim.Bytes 16) :=
  qo (stIP A.toM (tS A.toM s).2) s.1.2.2

/-- The statement and opening of round 1's spend proof (none unless the round runs). -/
noncomputable def qS₃ (b₁ : Bool) (s : SecR) (a : AuxSR) : Option (Statement × ZK.Sim.Bytes 16) :=
  qo (st₃P A.toM b₁ (nS s) (tS A.toM s) (cfS A.toM s.2.1) (coSR a)) (rIss s b₁)

/-- The statement and opening of round 2's spend proof (none unless both rounds run). -/
noncomputable def qS₄ (b₁ b₂ : Bool) (s : SecR) (a : AuxSR) :
    Option (Statement × ZK.Sim.Bytes 16) :=
  qo (st₄P A.toM b₁ b₂ (nS s) (tS A.toM s) (cfS A.toM s.2.1) (cfS A.toM s.2.2) (coSR a))
    (bif b₂ == b₁ then s.2.1.2 else rIss s (!b₁))

lemma qOf_σ₁R (s : SecR) : qOf (issStmtR A.toM s.1.1) = qS₁ A s :=
  qOf_of _ _ _ (issStmtR_pub A.toM s.1.1).1 (issStmtR_pub A.toM s.1.1).2

lemma qOf_σ₂R (s : SecR) : qOf (issStmtR A.toM s.1.2) = qS₂ A s :=
  qOf_of _ _ _ (issStmtR_pub A.toM s.1.2).1 (issStmtR_pub A.toM s.1.2).2

lemma qOf_σ₃R (b₁ b₂ : Bool) (s : SecR) (a : AuxSR) :
    qOf ((gameSR A b₁ b₂).σ₃ s (oS₁ A s a) (oS₂ A s a)) = qS₃ A b₁ s a := by
  show qOf (bif ok₁ₘ A.toM s (oS₁ A s a) (oS₂ A s a) then _ else none) = _
  cases h : ok₁ₘ A.toM s (oS₁ A s a) (oS₂ A s a)
  · have hk : ok₁P A.toM (nS s).1 (tS A.toM s) (coSR a).1 = false := by
      rw [← ok₁ₘ_pub A.toM s (coSR a) _ _ rfl rfl]; exact h
    unfold qS₃ st₃P
    rw [hk]
    rfl
  · exact qOf_of _ _ _ (σ₃_pub A.toM b₁ s (coSR a) _ _ rfl rfl h)
      (σ₃_wPre A.toM b₁ s (coSR a) _ _ rfl rfl h)

lemma qOf_σ₄R (b₁ b₂ : Bool) (s : SecR) (a : AuxSR) :
    qOf ((gameSR A b₁ b₂).σ₄ s (oS₁ A s a) (oS₂ A s a) (oS₃ A b₁ b₂ s a)) =
      qS₄ A b₁ b₂ s a := by
  show qOf (bif ok₁ₘ A.toM s (oS₁ A s a) (oS₂ A s a) &&
    ok₂ₘ A.toM b₁ s (oS₁ A s a) (oS₂ A s a) (oS₃ A b₁ b₂ s a) then _ else none) = _
  cases h : ok₁ₘ A.toM s (oS₁ A s a) (oS₂ A s a)
  · have hk : ok₁P A.toM (nS s).1 (tS A.toM s) (coSR a).1 = false := by
      rw [← ok₁ₘ_pub A.toM s (coSR a) _ _ rfl rfl]; exact h
    unfold qS₄ st₄P
    rw [hk]
    rfl
  · cases h' : ok₂ₘ A.toM b₁ s (oS₁ A s a) (oS₂ A s a) (oS₃ A b₁ b₂ s a)
    · have hk : ok₁P A.toM (nS s).1 (tS A.toM s) (coSR a).1 = true := by
        rw [← ok₁ₘ_pub A.toM s (coSR a) _ _ rfl rfl]; exact h
      have hk₂ : ok₂P A.toM b₁ (nS s) (tS A.toM s) (cfS A.toM s.2.1) (coSR a) = false := by
        rw [← ok₂ₘ_pub A.toM b₁ s (coSR a) _ _ _ rfl rfl (oS₃_eq A b₁ b₂ s a) h]; exact h'
      unfold qS₄ st₄P
      rw [hk, hk₂]
      rfl
    · exact qOf_of _ _ _ (σ₄_pub A.toM b₁ b₂ s (coSR a) _ _ _ rfl rfl (oS₃_eq A b₁ b₂ s a) h h')
        (σ₄_wPre A.toM b₁ b₂ s (coSR a) _ _ _ rfl rfl (oS₃_eq A b₁ b₂ s a) h h')

/-! ## The events -/

/-- The opening of Client `c`'s issued token is among its predictor's candidates. -/
def winIS (b₁ b₂ c : Bool) (x : GTape SecR pIr pIr pSr pSr) : Prop :=
  rIss x.1 c ∈ predIS A b₁ b₂ (nS x.1) (tS A.toM x.1) (cfS A.toM x.1.2.1) (cfS A.toM x.1.2.2)
    x.2 c

/-- The opening of round 1's change token is among its predictor's candidates, the commitment
taken at the credit `cr₁P`. -/
def winCS (b₁ b₂ : Bool) (x : GTape SecR pIr pIr pSr pSr) : Prop :=
  x.1.2.1.2 ∈ predCS A b₁ b₂ (nS x.1) (tS A.toM x.1)
    (fun _ => cfS A.toM x.1.2.1 (cr₁P A.toM b₁ (nS x.1).1 (tS A.toM x.1) (coSR x.2).1))
    (cfS A.toM x.1.2.2) x.2

/-- A sibling gate input of the first issuance proof is one of the second. -/
noncomputable def collR₂ (x : GTape SecR pIr pIr pSr pSr) : Prop :=
  ∃ y ∈ sibO Hashes.shake pIr (qS₁ A x.1) x.2.1.2 x.2.2.1.1.2,
    y ∈ sibO Hashes.shake pIr (qS₂ A x.1) x.2.1.2 x.2.2.2.1.1.2

/-- A sibling gate input of an issuance proof is one of round 1's spend proof. -/
noncomputable def collR₃ (b₁ : Bool) (x : GTape SecR pIr pIr pSr pSr) : Prop :=
  ∃ y ∈ sibO Hashes.shake pIr (qS₁ A x.1) x.2.1.2 x.2.2.1.1.2 ++
      sibO Hashes.shake pIr (qS₂ A x.1) x.2.1.2 x.2.2.2.1.1.2,
    y ∈ sibO Hashes.shake pSr (qS₃ A b₁ x.1 x.2) x.2.1.2 x.2.2.2.2.1.1.2

/-- A sibling gate input of an earlier proof is one of round 2's spend proof. -/
noncomputable def collR₄ (b₁ b₂ : Bool) (x : GTape SecR pIr pIr pSr pSr) : Prop :=
  ∃ y ∈ sibO Hashes.shake pIr (qS₁ A x.1) x.2.1.2 x.2.2.1.1.2 ++
      sibO Hashes.shake pIr (qS₂ A x.1) x.2.1.2 x.2.2.2.1.1.2 ++
      sibO Hashes.shake pSr (qS₃ A b₁ x.1 x.2) x.2.1.2 x.2.2.2.2.1.1.2,
    y ∈ sibO Hashes.shake pSr (qS₄ A b₁ b₂ x.1 x.2) x.2.1.2 x.2.2.2.2.2.1.2

-- (The defeq checks on the nested tape exceed the default recursion depth.)
set_option maxRecDepth 8192 in
/-- **`bstar` with all proofs simulated**: a failed simulation, a prediction, or a collision. -/
theorem puSR_imp (b₁ b₂ : Bool) (x : GTape SecR pIr pIr pSr pSr)
    (h : bstar Hashes.shake (gameSR A b₁ b₂) (r5SR A b₁ b₂)
      (hybV Hashes.shake (gameSR A b₁ b₂) true true true true x)) :
    (errC pIr x.2.2.1.1.2 ∨ errC pIr x.2.2.2.1.1.2 ∨ errC pSr x.2.2.2.2.1.1.2 ∨
        errC pSr x.2.2.2.2.2.1.2) ∨
      (winIS A b₁ b₂ false x ∨ winIS A b₁ b₂ true x ∨ winCS A b₁ b₂ x) ∨
      (collR₂ A x ∨ collR₃ A b₁ x ∨ collR₄ A b₁ b₂ x) := by
  obtain ⟨s, a⟩ := x
  have hR : r5SR A b₁ b₂ (hybV Hashes.shake (gameSR A b₁ b₂) true true true true (s, a)) =
      r5R A b₁ b₂ (nS s) (tS A.toM s) (cfS A.toM s.2.1) (cfS A.toM s.2.2) a :=
    simSR_eq A A.R5 b₁ b₂ (s, a)
  have key := bstar_sim Hashes.shake (gameSR A b₁ b₂) hashesWF_shake s a.1.2 a.2.1.1.2 a.2.2.1.1.2
    a.2.2.2.1.1.2 a.2.2.2.2.1.2
    (r5R A b₁ b₂ (nS s) (tS A.toM s) (cfS A.toM s.2.1) (cfS A.toM s.2.2) a)
    (oS₁ A s a) (oS₂ A s a) (oS₃ A b₁ b₂ s a) (oS₄ A b₁ b₂ s a)
    (qS₁ A s) (qS₂ A s) (qS₃ A b₁ s a) (qS₄ A b₁ b₂ s a)
    rfl rfl rfl rfl (qOf_σ₁R A s).symm (qOf_σ₂R A s).symm (qOf_σ₃R A b₁ b₂ s a).symm
    (qOf_σ₄R A b₁ b₂ s a).symm
    (spubR A b₁ b₂ (nS s) (tS A.toM s) (cfS A.toM s.2.1) (cfS A.toM s.2.2) a)
    (by
      unfold spubR qS₁ qS₂ qS₃ qS₄
      rw [actO_qo, actO_qo, actO_qo, actO_qo])
    (by
      have h' := h
      unfold bstar at h'
      rw [hR] at h'
      exact h')
  rcases key with he | hc | hcoll
  · exact Or.inl he
  · refine Or.inr (Or.inl ?_)
    rcases hc with hc | hc | hc | hc
    · exact Or.inl (mem_union_left _ (candO_qo _ _ _ _ _ hc))
    · exact Or.inr (Or.inl (mem_union_left _ (candO_qo _ _ _ _ _ hc)))
    · have hin := candO_qo _ _ _ _ _ hc
      have hw : winIS A b₁ b₂ b₁ (s, a) := by
        unfold winIS predIS
        refine mem_union_right _ (mem_union_left _ ?_)
        rw [beq_self_eq_true]
        exact hin
      cases b₁
      · exact Or.inl hw
      · exact Or.inr (Or.inl hw)
    · have hin := candO_qo _ _ _ _ _ hc
      cases hb : b₂ == b₁
      · rw [hb] at hin
        have hw : winIS A b₁ b₂ (!b₁) (s, a) := by
          unfold winIS predIS
          refine mem_union_right _ (mem_union_right _ ?_)
          have e : ((b₂ != b₁) && ((!b₁) != b₁)) = true := by
            cases b₁ <;> cases b₂ <;> simp_all
          rw [e]
          exact hin
        cases b₁
        · exact Or.inr (Or.inl hw)
        · exact Or.inl hw
      · rw [hb] at hin
        refine Or.inr (Or.inr ?_)
        unfold winCS
        rw [← predCS_const]
        unfold predCS
        rw [hb]
        exact hin
  · exact Or.inr (Or.inr hcoll)

/-! ## The probabilities -/

theorem pr_errSR₁_le : pr (GTape SecR pIr pIr pSr pSr) (fun x => errC pIr x.2.2.1.1.2) ≤
    noHitProb :=
  pr_le_of_fst fun _ => pr_le_of_fst fun _ => pr_le_of_snd fun _ => pr_errC_le

theorem pr_errSR₂_le : pr (GTape SecR pIr pIr pSr pSr) (fun x => errC pIr x.2.2.2.1.1.2) ≤
    noHitProb :=
  pr_le_of_fst fun _ => pr_le_of_fst fun _ => pr_le_of_fst fun _ => pr_le_of_snd fun _ =>
    pr_errC_le

theorem pr_errSR₃_le : pr (GTape SecR pIr pIr pSr pSr) (fun x => errC pSr x.2.2.2.2.1.1.2) ≤
    noHitProb :=
  pr_le_of_fst fun _ => pr_le_of_fst fun _ => pr_le_of_fst fun _ => pr_le_of_fst fun _ =>
    pr_le_of_snd fun _ => pr_errC_le

theorem pr_errSR₄_le : pr (GTape SecR pIr pIr pSr pSr) (fun x => errC pSr x.2.2.2.2.2.1.2) ≤
    noHitProb :=
  pr_le_of_fst fun _ => pr_le_of_fst fun _ => pr_le_of_fst fun _ => pr_le_of_fst fun _ =>
    pr_le_of_fst fun _ => pr_errC_le

set_option maxRecDepth 8192 in
/-- **The two issuance proofs collide with probability `≤ 313·2⁻¹²⁸`**: the second proof's `d` is
uniform and independent of the first proof. -/
theorem pr_collR₂_le :
    pr (GTape SecR pIr pIr pSr pSr) (collR₂ A) ≤ ((312 : ℕ) + 1) / 2 ^ 128 := by
  refine pr_le_of_fst fun s => pr_le_of_fst fun u => pr_le_of_fst fun k₁ => pr_le_of_snd fun r =>
    pr_KS_d_le _ fun ρ sh c1 c2 c3 c5 V => ?_
  rcases hst : stIP A.toM (tS A.toM s).2 with _ | st
  · refine le_trans (le_of_eq ?_) (by positivity)
    rw [pr_congr (Q := fun _ => False) fun d => by
      unfold collR₂ qS₂
      rw [hst]
      simp [sibO, qo]]
    exact pr_false
  · refine le_trans (pr_mono fun d hd => ?_) (pr_sib_hit_le Hashes.shake mainP_pIr st u.2 sh c1 c2
      c3 c5 s.1.2.2 (sibO Hashes.shake pIr (qS₁ A s) u.2 k₁.1.2) (sibO_length_le _ _ _ _))
    unfold collR₂ qS₂ at hd
    rw [hst] at hd
    exact hd

set_option maxRecDepth 8192 in
/-- **Round 1's spend proof collides with an issuance proof with probability `≤ 625·2⁻¹²⁸`.** -/
theorem pr_collR₃_le (b₁ : Bool) :
    pr (GTape SecR pIr pIr pSr pSr) (collR₃ A b₁) ≤ ((624 : ℕ) + 1) / 2 ^ 128 := by
  refine pr_le_of_fst fun s => pr_le_of_fst fun u => pr_le_of_fst fun k₁ => pr_le_of_fst fun k₂ =>
    pr_le_of_snd fun k₄ => pr_KS_d_le _ fun ρ sh c1 c2 c3 c5 V => ?_
  have hlen : (sibO Hashes.shake pIr (qS₁ A s) u.2 k₁.1.2 ++
      sibO Hashes.shake pIr (qS₂ A s) u.2 k₂.1.2).length ≤ 624 := by
    rw [List.length_append]
    have := sibO_length_le Hashes.shake (qS₁ A s) u.2 k₁.1.2
    have := sibO_length_le Hashes.shake (qS₂ A s) u.2 k₂.1.2
    omega
  have hq : ∀ d : ZK.Sim.Bytes pSr.witnessBytes,
      qS₃ A b₁ s (u, k₁, k₂, ((ρ, (sh, (c1, c2, c3, d, c5))), V), k₄) =
      qo (st₃P A.toM b₁ (nS s) (tS A.toM s) (cfS A.toM s.2.1)
        (coSR (u, k₁, k₂, ((ρ, (sh, (c1, c2, c3, fun _ => 0, c5))), V), k₄))) (rIss s b₁) :=
    fun d => congrArg (fun st => qo st (rIss s b₁)) (st₃P_congr A.toM b₁ _ _ _ _ _ rfl)
  rcases hst : st₃P A.toM b₁ (nS s) (tS A.toM s) (cfS A.toM s.2.1)
    (coSR (u, k₁, k₂, ((ρ, (sh, (c1, c2, c3, fun _ => 0, c5))), V), k₄)) with _ | st
  · refine le_trans (le_of_eq ?_) (by positivity)
    rw [pr_congr (Q := fun _ => False) fun d => by
      unfold collR₃
      rw [hq d, hst]
      simp [sibO, qo]]
    exact pr_false
  · refine le_trans (pr_mono fun d hd => ?_) (pr_sib_hit_le Hashes.shake mainP_pSr st u.2 sh c1 c2
      c3 c5 (rIss s b₁) _ hlen)
    unfold collR₃ at hd
    rw [hq d, hst] at hd
    exact hd

set_option maxRecDepth 8192 in
/-- **Round 2's spend proof collides with an earlier proof with probability `≤ 937·2⁻¹²⁸`.** -/
theorem pr_collR₄_le (b₁ b₂ : Bool) :
    pr (GTape SecR pIr pIr pSr pSr) (collR₄ A b₁ b₂) ≤ ((936 : ℕ) + 1) / 2 ^ 128 := by
  refine pr_le_of_fst fun s => pr_le_of_fst fun u => pr_le_of_fst fun k₁ => pr_le_of_fst fun k₂ =>
    pr_le_of_fst fun k₃ => pr_KS_d_le _ fun ρ sh c1 c2 c3 c5 V => ?_
  have hlen : (sibO Hashes.shake pIr (qS₁ A s) u.2 k₁.1.2 ++
      sibO Hashes.shake pIr (qS₂ A s) u.2 k₂.1.2 ++
      sibO Hashes.shake pSr (qS₃ A b₁ s (u, k₁, k₂, k₃,
        ((ρ, (sh, (c1, c2, c3, fun _ => 0, c5))), V))) u.2 k₃.1.2).length ≤ 936 := by
    rw [List.length_append, List.length_append]
    have := sibO_length_le Hashes.shake (qS₁ A s) u.2 k₁.1.2
    have := sibO_length_le Hashes.shake (qS₂ A s) u.2 k₂.1.2
    have := sibO_length_le Hashes.shake (qS₃ A b₁ s (u, k₁, k₂, k₃,
        ((ρ, (sh, (c1, c2, c3, fun _ => 0, c5))), V))) u.2 k₃.1.2
    omega
  have hq : ∀ d : ZK.Sim.Bytes pSr.witnessBytes,
      qS₄ A b₁ b₂ s (u, k₁, k₂, k₃, ((ρ, (sh, (c1, c2, c3, d, c5))), V)) =
      qo (st₄P A.toM b₁ b₂ (nS s) (tS A.toM s) (cfS A.toM s.2.1) (cfS A.toM s.2.2)
        (coSR (u, k₁, k₂, k₃, ((ρ, (sh, (c1, c2, c3, fun _ => 0, c5))), V))))
        (bif b₂ == b₁ then s.2.1.2 else rIss s (!b₁)) :=
    fun d => congrArg (fun st => qo st (bif b₂ == b₁ then s.2.1.2 else rIss s (!b₁)))
      (st₄P_congr A.toM b₁ b₂ _ _ _ _ _ _ rfl rfl)
  have hq' : ∀ d : ZK.Sim.Bytes pSr.witnessBytes,
      qS₃ A b₁ s (u, k₁, k₂, k₃, ((ρ, (sh, (c1, c2, c3, d, c5))), V)) =
      qS₃ A b₁ s (u, k₁, k₂, k₃, ((ρ, (sh, (c1, c2, c3, fun _ => 0, c5))), V)) :=
    fun d => congrArg (fun st => qo st (rIss s b₁)) (st₃P_congr A.toM b₁ _ _ _ _ _ rfl)
  rcases hst : st₄P A.toM b₁ b₂ (nS s) (tS A.toM s) (cfS A.toM s.2.1) (cfS A.toM s.2.2)
    (coSR (u, k₁, k₂, k₃, ((ρ, (sh, (c1, c2, c3, fun _ => 0, c5))), V))) with _ | st
  · refine le_trans (le_of_eq ?_) (by positivity)
    rw [pr_congr (Q := fun _ => False) fun d => by
      unfold collR₄
      rw [hq d, hst]
      simp [sibO, qo]]
    exact pr_false
  · refine le_trans (pr_mono fun d hd => ?_) (pr_sib_hit_le Hashes.shake mainP_pSr st u.2 sh c1 c2
      c3 c5 (bif b₂ == b₁ then s.2.1.2 else rIss s (!b₁)) _ hlen)
    unfold collR₄ at hd
    rw [hq d, hq' d, hst] at hd
    exact hd

/-! ## The predictors in the game `PU.puAdv` -/

/-- **The predictor for the opening of Client `false`'s issued token** in the game `PU.puAdv`:
public part `nf₀`, commitment `t₀ = Com(nf₀, ctx, T_init, r₀)`; auxiliary coins the other three
tokens' `(nf, r)`, the simulators' coins and the raw tables. -/
noncomputable def predSR₀ (b₁ b₂ : Bool) (n : Coins 24) (t : Commitment)
    (a : ((Coins 24 × Coins 16) × ((Coins 24 × Coins 16) × (Coins 24 × Coins 16))) × AuxSR) :
    Finset (Coins 16) :=
  predIS A b₁ b₂ ((vec n, vec a.1.1.1), (vec a.1.2.1.1, vec a.1.2.2.1))
    (t, comI A.toM a.1.1.1 a.1.1.2) (cfS A.toM a.1.2.1) (cfS A.toM a.1.2.2) a.2 false

/-- **The predictor for the opening of Client `true`'s issued token.** -/
noncomputable def predSR₁ (b₁ b₂ : Bool) (n : Coins 24) (t : Commitment)
    (a : ((Coins 24 × Coins 16) × ((Coins 24 × Coins 16) × (Coins 24 × Coins 16))) × AuxSR) :
    Finset (Coins 16) :=
  predIS A b₁ b₂ ((vec a.1.1.1, vec n), (vec a.1.2.1.1, vec a.1.2.2.1))
    (comI A.toM a.1.1.1 a.1.1.2, t) (cfS A.toM a.1.2.1) (cfS A.toM a.1.2.2) a.2 true

/-- The raw tables, the provers' coins `ρ` and the spend simulators' coins (the change predictor's
auxiliary coins besides round 2's new token). -/
abbrev AuxCS := USh × ((ZK.Sim.Bytes 16 × VP pIr) × (ZK.Sim.Bytes 16 × VP pIr)) × KS pSr × KS pSr

/-- The tape without the secret, from the issuance simulators' coins (public input) and the
rest. -/
def auxOfS (c : SimCoins pIr × SimCoins pIr) (a : AuxCS) : AuxSR :=
  (a.1, ((a.2.1.1.1, c.1), a.2.1.1.2), ((a.2.1.2.1, c.2), a.2.1.2.2), a.2.2.1, a.2.2.2)

/-- **The predictor for the opening of round 1's change token** in the game `PU.puAdv` for
`comCh`: public part `nf'` and the issuance part `b` (the issued tokens' `(nf, r)` and the issuance
simulators' coins, which determine the credit), commitment `t = Com(nf', ctx, crCh b, r')`;
auxiliary coins round 2's new token's `(nf, r)`, the spend simulators' coins and the raw tables. -/
noncomputable def predSRC (b₁ b₂ : Bool) (n : Coins 24 × BCh) (t : Commitment)
    (a : (Coins 24 × Coins 16) × AuxCS) : Finset (Coins 16) :=
  predCS A b₁ b₂ ((vec n.2.1.1.1, vec n.2.1.2.1), (vec n.1, vec a.1.1))
    (comI A.toM n.2.1.1.1 n.2.1.1.2, comI A.toM n.2.1.2.1 n.2.1.2.2) (fun _ => t) (cfS A.toM a.1)
    (auxOfS n.2.2 a.2)

theorem pr_winIS_false (b₁ b₂ : Bool) :
    pr (GTape SecR pIr pIr pSr pSr) (winIS A b₁ b₂ false) =
      puAdv (comI A.toM) (predSR₀ A b₁ b₂) := by
  let e : (Coins 24 × Coins 16) ×
      (((Coins 24 × Coins 16) × ((Coins 24 × Coins 16) × (Coins 24 × Coins 16))) × AuxSR) ≃
      GTape SecR pIr pIr pSr pSr :=
    { toFun := fun z => (((z.1, z.2.1.1), z.2.1.2), z.2.2)
      invFun := fun x => (x.1.1.1, ((x.1.1.2, x.1.2), x.2))
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [← pr_equiv e]
  rfl

theorem pr_winIS_true (b₁ b₂ : Bool) :
    pr (GTape SecR pIr pIr pSr pSr) (winIS A b₁ b₂ true) =
      puAdv (comI A.toM) (predSR₁ A b₁ b₂) := by
  let e : (Coins 24 × Coins 16) ×
      (((Coins 24 × Coins 16) × ((Coins 24 × Coins 16) × (Coins 24 × Coins 16))) × AuxSR) ≃
      GTape SecR pIr pIr pSr pSr :=
    { toFun := fun z => (((z.2.1.1, z.1), z.2.1.2), z.2.2)
      invFun := fun x => (x.1.1.2, ((x.1.1.1, x.1.2), x.2))
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [← pr_equiv e]
  rfl

theorem pr_winCS (b₁ b₂ : Bool) :
    pr (GTape SecR pIr pIr pSr pSr) (winCS A b₁ b₂) =
      puAdv (comCh A.toM b₁) (predSRC A b₁ b₂) := by
  let e : ((Coins 24 × BCh) × Coins 16) × ((Coins 24 × Coins 16) × AuxCS) ≃
      GTape SecR pIr pIr pSr pSr :=
    { toFun := fun z => ((z.1.1.2.1, ((z.1.1.1, z.1.2), z.2.1)), auxOfS z.1.1.2.2 z.2.2)
      invFun := fun x => (((x.1.2.1.1, (x.1.1, (x.2.2.1.1.2, x.2.2.2.1.1.2))), x.1.2.1.2),
        (x.1.2.2, (x.2.1, ((x.2.2.1.1.1, x.2.2.1.2), (x.2.2.2.1.1.1, x.2.2.2.1.2)),
          x.2.2.2.2.1, x.2.2.2.2.2)))
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [← pr_equiv e]
  rfl

/-- **The (PU) term with shared tables is at most the advantage of the three explicit
predictors**, plus `4·noHitProb` (failed simulations) and `1875·2⁻¹²⁸` (collisions between
simulated proofs). -/
theorem puTermSR_le (b₁ b₂ : Bool) :
    puTermSR A b₁ b₂ ≤ 4 * noHitProb + puAdv (comI A.toM) (predSR₀ A b₁ b₂) +
      puAdv (comI A.toM) (predSR₁ A b₁ b₂) + puAdv (comCh A.toM b₁) (predSRC A b₁ b₂) +
      1875 / 2 ^ 128 := by
  unfold puTermSR hyb
  have h := (pr_mono (puSR_imp A b₁ b₂)).trans ((pr_or_le _ _).trans (add_le_add
    ((pr_or_le _ _).trans (add_le_add le_rfl ((pr_or_le _ _).trans (add_le_add le_rfl
      (pr_or_le _ _)))))
    ((pr_or_le _ _).trans (add_le_add
      ((pr_or_le _ _).trans (add_le_add le_rfl (pr_or_le _ _)))
      ((pr_or_le _ _).trans (add_le_add le_rfl (pr_or_le _ _)))))))
  rw [pr_winIS_false, pr_winIS_true, pr_winCS] at h
  have e₁ := pr_errSR₁_le
  have e₂ := pr_errSR₂_le
  have e₃ := pr_errSR₃_le
  have e₄ := pr_errSR₄_le
  have c₂ := pr_collR₂_le A
  have c₃ := pr_collR₃_le A b₁
  have c₄ := pr_collR₄_le A b₁ b₂
  have hn : (((312 : ℕ) + 1 : ℝ) / 2 ^ 128) + (((624 : ℕ) + 1 : ℝ) / 2 ^ 128) +
      (((936 : ℕ) + 1 : ℝ) / 2 ^ 128) = 1875 / 2 ^ 128 := by norm_num
  linarith

/-! ## Theorem 2 on `main`, shared tables, with (PU) as a game -/

/-- **Theorem 2 on `main` (no label rows) with one `H₅` table and one cipher for the four proofs,
with the (PU) advantage of explicit predictors.** For the malicious Issuer whose guess reads each
`H₃` slice at `q3` keys, the cipher at `qE` keys and `H₅` at the consistent read set `R5`
(`AdversarySR.Cons`), any two worlds of the real game differ by at most

    30·εS(q3, qE + 8·4607) + 15·(PU(b₁, b₂) + PU(b₁', b₂') + 8·noHitProb + 3750·2⁻¹²⁸) + 2·εhide,

`PU(b₁, b₂) = puAdv comI (predSR₀ b₁ b₂) + puAdv comI (predSR₁ b₁ b₂) + puAdv (comCh b₁)
(predSRC b₁ b₂)`. The six `puAdv` terms are (PU), an assumption on Keccak-p[800,12], and `εhide`
is hiding of `Com`; every other term is a number (`noHitProb ≤ 2^{−2¹⁵}`). The predictors output
at most `3·(q5 + 1249)` (issued tokens) and `q5 + 1249` (change token) candidates if `R5` has at
most `q5` keys (`card_predIS_le`, `card_predCS_le`). -/
theorem unlinkability_main_shared {q3 qE : ℕ} (hC : A.Cons q3 qE) {εhide : ℝ}
    (hhide : ∀ b₁ b₂ a, hidingAdv A.ctx (redSR A b₁ b₂ a) ≤ εhide) (b₁ b₂ b₁' b₂' : Bool) :
    |realSR A b₁ b₂ - realSR A b₁' b₂'| ≤
      30 * εS q3 (qE + 8 * 4607) + 15 * (puAdv (comI A.toM) (predSR₀ A b₁ b₂) +
        puAdv (comI A.toM) (predSR₁ A b₁ b₂) + puAdv (comCh A.toM b₁) (predSRC A b₁ b₂) +
        (puAdv (comI A.toM) (predSR₀ A b₁' b₂') + puAdv (comI A.toM) (predSR₁ A b₁' b₂') +
        puAdv (comCh A.toM b₁') (predSRC A b₁' b₂')) + 8 * noHitProb + 3750 / 2 ^ 128) +
        2 * εhide := by
  have h := unlinkability_main_shared0 A hC hhide b₁ b₂ b₁' b₂'
  have p0 := puTermSR_le A b₁ b₂
  have p1 := puTermSR_le A b₁' b₂'
  linarith

end VoleMole.Privacy.Ratatouille
