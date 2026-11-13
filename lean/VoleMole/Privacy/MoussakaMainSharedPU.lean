import VoleMole.Privacy.MoussakaMainShared
import VoleMole.ZK.MainSharedSim

/-!
# Moussaka on `main` with shared tables: the (PU) term as explicit predictors and numbers

`anonymity_main_shared0` (`Privacy/MoussakaMainShared.lean`) bounds Theorem 4(a) on `main` with a
shared `H₅` table and cipher by `30·εS + 15·(puTermS 0 + puTermS 1) + 2·εhide`, with `puTermS b`
the event `ZK.Sim.bstar` in the game with all four proofs simulated. Here that event is bounded.

**With all proofs simulated** (`ZK.Sim.bstar_sim`) `bstar` implies one of:

* a simulation failed: `noHitProb` each (`pr_errS_le`);
* **a prediction**: for some proof, the opening `r` of its token is a candidate (`ZK.Sim.candC`)
  of the **public key set** `spubP`: the guess's `H₅` read set and the active gate inputs of the
  four simulated proofs. Everything in it is a function of the commitments, the nullifiers, the
  simulators' coins and the tables (`simS_eq`), so this is the event that the predictor `predS`
  of Client `c` (the candidates of its issuance proof and of its redemption proof) contains `r_c`:
  the game `Privacy.PU.puAdv` for `Com` (`pr_winS_false`, `pr_winS_true`);
* **a collision between two simulated proofs**: a sibling gate input of one is a sibling gate input
  of another. The later proof's field `d` is uniform and independent of the earlier proof and of
  both openings, so this has probability `≤ (312·j + 1)·2⁻¹²⁸` for the `j` earlier proofs
  (`ZK.Sim.pr_sib_hit_le`, `pr_coll₂_le`, `pr_coll₃_le`, `pr_coll₄_le`): `1875·2⁻¹²⁸` in all. This
  is the `ε_iv`-type term of `lean/docs/zk.md` §4.2; it uses nothing about `H₄`.

**`puTermS_le`**: `puTermS b ≤ 4·noHitProb + puAdv Com (predS₀ b) + puAdv Com (predS₁ b) +
1875·2⁻¹²⁸`. Each predictor outputs at most `2·(q₅ + 1249)` candidates if the guess's `H₅` read
set has at most `q₅` keys (`card_predS_le`).

**`anonymity_main_shared`**: Theorem 4(a) on `main` with a shared `H₅` table and cipher,

    |Pr[world 0] − Pr[world 1]| ≤ 30·εS(q₃, q_E + 8·4607)
      + 15·(Σ_{b, c} puAdv Com (predS_c b) + 8·noHitProb + 3750·2⁻¹²⁸) + 2·εhide.

The four `puAdv` terms are (PU), an assumption on Keccak-p[800,12] (`Privacy/PU.lean`,
`lean/docs/zk.md` §4.3); `εhide` is hiding of `Com`; everything else is a number
(`noHitProb ≤ 2^{−2¹⁵}`, `ZK.Sim.noHitProb_le`).
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
attribute [local irreducible] simulate realRO progRO

variable (A : AdversaryS) (idx : AnchorSet → UOVKey → ℕ)

/-! ## The public key set and the predictors -/

/-- The guess's `H₅` read set with all proofs simulated, from public values. -/
noncomputable def r5P (b : Bool) (t₀ t₁ n₀ n₁ : Bytes) (a : AuxS) : Finset (ZK.Sim.Bytes 37) :=
  A.R5 (reqS t₀ a.2.1.1.2) (reqS t₁ a.2.2.1.1.2) (YP A idx b t₀ t₁ n₀ n₁ a)
    (visP A idx b t₀ t₁ n₀ n₁ a)

/-- The active gate inputs of a simulated redemption proof (none unless §6's rule holds). -/
noncomputable def actRP (st : Option Statement) (E : Cipher) (c : SimCoins pRm) : List ByteArray :=
  match st with
  | some st => actL Hashes.shake pRm st E c
  | none => []

/-- **The public key set**: the guess's `H₅` read set and the active gate inputs of the four
simulated proofs. -/
noncomputable def spubP (b : Bool) (t₀ t₁ n₀ n₁ : Bytes) (a : AuxS) : Finset (ZK.Sim.Bytes 37) :=
  r5P A idx b t₀ t₁ n₀ n₁ a ∪
    ((actL Hashes.shake pIm (stI ⟨t₀, A.toM.int.ci⟩) a.1.2 a.2.1.1.2).toFinset.image (blk 37) ∪
      (actL Hashes.shake pIm (stI ⟨t₁, A.toM.int.ci⟩) a.1.2 a.2.2.1.1.2).toFinset.image (blk 37) ∪
      (actRP (stRP A idx b t₀ t₁ n₀ n₁ a false) a.1.2 a.2.2.2.1.1.2).toFinset.image (blk 37) ∪
      (actRP (stRP A idx b t₀ t₁ n₀ n₁ a true) a.1.2 a.2.2.2.2.1.2).toFinset.image (blk 37))

/-- The candidates of a simulated redemption proof (none unless §6's rule holds). -/
noncomputable def candRP (st : Option Statement) (E : Cipher) (c : SimCoins pRm)
    (S : Finset (ZK.Sim.Bytes 37)) : Finset (Coins rBytes) :=
  match st with
  | some st => candC Hashes.shake st E c S
  | none => ∅

/-- **The predictor for Client `c`'s opening in world `b`**: the candidates of its issuance proof
and of its redemption proof (side `b ^^ c`), for the public key set. -/
noncomputable def predS (b : Bool) (t₀ t₁ n₀ n₁ : Bytes) (a : AuxS) (c : Bool) :
    Finset (Coins rBytes) :=
  (bif c then candC Hashes.shake (stI ⟨t₁, A.toM.int.ci⟩) a.1.2 a.2.2.1.1.2
      (spubP A idx b t₀ t₁ n₀ n₁ a)
    else candC Hashes.shake (stI ⟨t₀, A.toM.int.ci⟩) a.1.2 a.2.1.1.2
      (spubP A idx b t₀ t₁ n₀ n₁ a)) ∪
  (bif b ^^ c then candRP (stRP A idx b t₀ t₁ n₀ n₁ a true) a.1.2 a.2.2.2.2.1.2
      (spubP A idx b t₀ t₁ n₀ n₁ a)
    else candRP (stRP A idx b t₀ t₁ n₀ n₁ a false) a.1.2 a.2.2.2.1.1.2
      (spubP A idx b t₀ t₁ n₀ n₁ a))

lemma card_img_le (l : List ByteArray) (h : l.length ≤ 312) :
    (l.toFinset.image (blk 37)).card ≤ 312 :=
  card_image_le.trans ((List.toFinset_card_le _).trans h)

lemma actRP_length_le (st : Option Statement) (E : Cipher) (c : SimCoins pRm) :
    (actRP st E c).length ≤ 312 := by
  rcases st with _ | st
  · simp [actRP]
  · exact actL_length_le _ _ _ _

/-- **At most `2·(q₅ + 1249)` candidates**, if the read set has at most `q₅` keys. -/
theorem card_predS_le {q5 : ℕ} (h : ∀ q₀ q₁ y v, (A.R5 q₀ q₁ y v).card ≤ q5) (b : Bool)
    (t₀ t₁ n₀ n₁ : Bytes) (a : AuxS) (c : Bool) :
    (predS A idx b t₀ t₁ n₀ n₁ a c).card ≤ 2 * (q5 + 1249) := by
  have hS : (spubP A idx b t₀ t₁ n₀ n₁ a).card ≤ q5 + 1248 := by
    unfold spubP
    have a₁ := card_img_le _ (actL_length_le Hashes.shake (p := pIm) (stI ⟨t₀, A.toM.int.ci⟩)
      a.1.2 a.2.1.1.2)
    have a₂ := card_img_le _ (actL_length_le Hashes.shake (p := pIm) (stI ⟨t₁, A.toM.int.ci⟩)
      a.1.2 a.2.2.1.1.2)
    have a₃ := card_img_le _ (actRP_length_le (stRP A idx b t₀ t₁ n₀ n₁ a false) a.1.2
      a.2.2.2.1.1.2)
    have a₄ := card_img_le _ (actRP_length_le (stRP A idx b t₀ t₁ n₀ n₁ a true) a.1.2
      a.2.2.2.2.1.2)
    have hr : (r5P A idx b t₀ t₁ n₀ n₁ a).card ≤ q5 := h _ _ _ _
    generalize r5P A idx b t₀ t₁ n₀ n₁ a = R at hr ⊢
    generalize image (blk 37) (actL Hashes.shake pIm (stI ⟨t₀, A.toM.int.ci⟩) a.1.2
      a.2.1.1.2).toFinset = X₁ at a₁ ⊢
    generalize image (blk 37) (actL Hashes.shake pIm (stI ⟨t₁, A.toM.int.ci⟩) a.1.2
      a.2.2.1.1.2).toFinset = X₂ at a₂ ⊢
    generalize image (blk 37) (actRP (stRP A idx b t₀ t₁ n₀ n₁ a false) a.1.2
      a.2.2.2.1.1.2).toFinset = X₃ at a₃ ⊢
    generalize image (blk 37) (actRP (stRP A idx b t₀ t₁ n₀ n₁ a true) a.1.2
      a.2.2.2.2.1.2).toFinset = X₄ at a₄ ⊢
    have u₀ := card_union_le R (X₁ ∪ X₂ ∪ X₃ ∪ X₄)
    have u₁ := card_union_le (X₁ ∪ X₂ ∪ X₃) X₄
    have u₂ := card_union_le (X₁ ∪ X₂) X₃
    have u₃ := card_union_le X₁ X₂
    omega
  have hI : ∀ (st : Statement) (cc : SimCoins pIm),
      (candC Hashes.shake st a.1.2 cc (spubP A idx b t₀ t₁ n₀ n₁ a)).card ≤ q5 + 1249 :=
    fun st cc => (card_candC_le Hashes.shake mainP_pIm st a.1.2 cc _).trans (by omega)
  have hRd : ∀ (st : Option Statement) (cc : SimCoins pRm),
      (candRP st a.1.2 cc (spubP A idx b t₀ t₁ n₀ n₁ a)).card ≤ q5 + 1249 := by
    intro st cc
    rcases st with _ | st
    · simp [candRP]
    · exact (card_candC_le Hashes.shake mainP_pRm st a.1.2 cc _).trans (by omega)
  unfold predS
  refine (card_union_le _ _).trans ?_
  have e₁ : (bif c then candC Hashes.shake (stI ⟨t₁, A.toM.int.ci⟩) a.1.2 a.2.2.1.1.2
      (spubP A idx b t₀ t₁ n₀ n₁ a)
    else candC Hashes.shake (stI ⟨t₀, A.toM.int.ci⟩) a.1.2 a.2.1.1.2
      (spubP A idx b t₀ t₁ n₀ n₁ a)).card ≤ q5 + 1249 := by
    cases c
    · exact hI _ _
    · exact hI _ _
  have e₂ : (bif b ^^ c then candRP (stRP A idx b t₀ t₁ n₀ n₁ a true) a.1.2 a.2.2.2.2.1.2
      (spubP A idx b t₀ t₁ n₀ n₁ a)
    else candRP (stRP A idx b t₀ t₁ n₀ n₁ a false) a.1.2 a.2.2.2.1.1.2
      (spubP A idx b t₀ t₁ n₀ n₁ a)).card ≤ q5 + 1249 := by
    cases b ^^ c
    · exact hRd _ _
    · exact hRd _ _
  omega

/-! ## The slots of the simulated game -/

/-- The statement and opening of Client `c`'s issuance proof. -/
def qI (s : SecM) (c : Bool) : Option (Statement × ZK.Sim.Bytes 16) :=
  some (stI ⟨tM A.toM s c, A.toM.int.ci⟩, rOf s c)

/-- The statement and opening of the redemption proof of side `side` (none unless §6's rule
holds). -/
noncomputable def qR (b : Bool) (x : GTape SecM pIm pIm pRm pRm) (side : Bool) :
    Option (Statement × ZK.Sim.Bytes 16) :=
  (stRP A idx b (tM A.toM x.1 false) (tM A.toM x.1 true) (nOf x.1 false) (nOf x.1 true) x.2
    side).map fun st => (st, rOf x.1 (b ^^ side))

/-- The redemption statements depend on the tape only through the secret and the issuance
simulators' coins. -/
lemma qR_congr (b : Bool) (x x' : GTape SecM pIm pIm pRm pRm) (side : Bool) (hs : x.1 = x'.1)
    (h₁ : x.2.2.1.1.2 = x'.2.2.1.1.2) (h₂ : x.2.2.2.1.1.2 = x'.2.2.2.1.1.2) :
    qR A idx b x side = qR A idx b x' side := by
  unfold qR stRP okP
  rw [hs, h₁, h₂]

lemma qOf_iss (s : SecM) (c : Bool) : qOf (some (issStmt A.toM s c)) = qI A s c := by
  unfold qOf qI
  simp only [Option.map_some, Option.some.injEq]
  exact Prod.ext rfl (wPre_issueWitness _ _ _ _)

lemma qOf_σ₃ (b : Bool) (s : SecM) (a : AuxS) :
    qOf ((gameS A idx b).σ₃ s (some (simulate pIm a.2.1.1.2)) (some (simulate pIm a.2.2.1.1.2))) =
      qR A idx b (s, a) false := by
  have h := redStmt_sim A idx b s a.2.1.1.2 a.2.2.1.1.2 false
  rw [σ₃_sim]
  unfold qR stRP okP
  cases hok : allOkT A.toM.int idx (reqS (tM A.toM s false) a.2.1.1.2)
    (reqS (tM A.toM s true) a.2.2.1.1.2) (tM A.toM s false) (tM A.toM s true)
  · rfl
  · rw [hok] at h
    obtain ⟨y, hy, hy1, hy2⟩ := h
    simp only [Bool.cond_true, hy, qOf, Option.map_some, hy1, hy2]

lemma qOf_σ₄ (b : Bool) (s : SecM) (a : AuxS) (o : Option Out) :
    qOf ((gameS A idx b).σ₄ s (some (simulate pIm a.2.1.1.2)) (some (simulate pIm a.2.2.1.1.2))
      o) = qR A idx b (s, a) true := by
  have h := redStmt_sim A idx b s a.2.1.1.2 a.2.2.1.1.2 true
  rw [σ₄_sim]
  unfold qR stRP okP
  cases hok : allOkT A.toM.int idx (reqS (tM A.toM s false) a.2.1.1.2)
    (reqS (tM A.toM s true) a.2.2.1.1.2) (tM A.toM s false) (tM A.toM s true)
  · rfl
  · rw [hok] at h
    obtain ⟨y, hy, hy1, hy2⟩ := h
    simp only [Bool.cond_true, hy, qOf, Option.map_some, hy1, hy2]

lemma actO_qR (b : Bool) (x : GTape SecM pIm pIm pRm pRm) (side : Bool) (E : Cipher)
    (c : SimCoins pRm) :
    actO Hashes.shake pRm (qR A idx b x side) E c =
      actRP (stRP A idx b (tM A.toM x.1 false) (tM A.toM x.1 true) (nOf x.1 false) (nOf x.1 true)
        x.2 side) E c := by
  unfold qR
  rcases stRP A idx b (tM A.toM x.1 false) (tM A.toM x.1 true) (nOf x.1 false) (nOf x.1 true) x.2
    side with _ | st <;> rfl

set_option maxRecDepth 8000 in
lemma candO_qR (b : Bool) (x : GTape SecM pIm pIm pRm pRm) (side : Bool) (E : Cipher)
    (c : SimCoins pRm) (S : Finset (ZK.Sim.Bytes 37))
    (h : candO Hashes.shake (qR A idx b x side) E c S) :
    rOf x.1 (b ^^ side) ∈ candRP (stRP A idx b (tM A.toM x.1 false) (tM A.toM x.1 true)
      (nOf x.1 false) (nOf x.1 true) x.2 side) E c S := by
  unfold qR at h
  rcases hst : stRP A idx b (tM A.toM x.1 false) (tM A.toM x.1 true) (nOf x.1 false)
    (nOf x.1 true) x.2 side with _ | st
  · rw [hst] at h; exact h.elim
  · rw [hst] at h; exact h

/-! ## The events -/

/-- Client `c`'s opening is among its predictor's candidates. -/
def winS (b c : Bool) (x : GTape SecM pIm pIm pRm pRm) : Prop :=
  rOf x.1 c ∈ predS A idx b (tM A.toM x.1 false) (tM A.toM x.1 true) (nOf x.1 false)
    (nOf x.1 true) x.2 c

/-- A sibling gate input of the first issuance proof is one of the second. -/
noncomputable def coll₂ (x : GTape SecM pIm pIm pRm pRm) : Prop :=
  ∃ y ∈ sibO Hashes.shake pIm (qI A x.1 false) x.2.1.2 x.2.2.1.1.2,
    y ∈ sibO Hashes.shake pIm (qI A x.1 true) x.2.1.2 x.2.2.2.1.1.2

/-- A sibling gate input of an issuance proof is one of the left redemption proof. -/
noncomputable def coll₃ (b : Bool) (x : GTape SecM pIm pIm pRm pRm) : Prop :=
  ∃ y ∈ sibO Hashes.shake pIm (qI A x.1 false) x.2.1.2 x.2.2.1.1.2 ++
      sibO Hashes.shake pIm (qI A x.1 true) x.2.1.2 x.2.2.2.1.1.2,
    y ∈ sibO Hashes.shake pRm (qR A idx b x false) x.2.1.2 x.2.2.2.2.1.1.2

/-- A sibling gate input of an earlier proof is one of the right redemption proof. -/
noncomputable def coll₄ (b : Bool) (x : GTape SecM pIm pIm pRm pRm) : Prop :=
  ∃ y ∈ sibO Hashes.shake pIm (qI A x.1 false) x.2.1.2 x.2.2.1.1.2 ++
      sibO Hashes.shake pIm (qI A x.1 true) x.2.1.2 x.2.2.2.1.1.2 ++
      sibO Hashes.shake pRm (qR A idx b x false) x.2.1.2 x.2.2.2.2.1.1.2,
    y ∈ sibO Hashes.shake pRm (qR A idx b x true) x.2.1.2 x.2.2.2.2.2.1.2

-- (The defeq checks on the nested tape exceed the default recursion depth.)
set_option maxRecDepth 8192 in
/-- **`bstar` with all proofs simulated**: a failed simulation, a prediction, or a collision. -/
theorem puS_imp (b : Bool) (x : GTape SecM pIm pIm pRm pRm)
    (h : bstar Hashes.shake (gameS A idx b) (r5S A idx b)
      (hybV Hashes.shake (gameS A idx b) true true true true x)) :
    (errC pIm x.2.2.1.1.2 ∨ errC pIm x.2.2.2.1.1.2 ∨ errC pRm x.2.2.2.2.1.1.2 ∨
        errC pRm x.2.2.2.2.2.1.2) ∨
      (winS A idx b false x ∨ winS A idx b true x) ∨
      (coll₂ A x ∨ coll₃ A idx b x ∨ coll₄ A idx b x) := by
  obtain ⟨s, a⟩ := x
  have hR : r5S A idx b (hybV Hashes.shake (gameS A idx b) true true true true (s, a)) =
      r5P A idx b (tM A.toM s false) (tM A.toM s true) (nOf s false) (nOf s true) a :=
    simS_eq A idx A.R5 b (s, a)
  have key := bstar_sim Hashes.shake (gameS A idx b) hashesWF_shake s a.1.2 a.2.1.1.2 a.2.2.1.1.2
    a.2.2.2.1.1.2 a.2.2.2.2.1.2
    (r5P A idx b (tM A.toM s false) (tM A.toM s true) (nOf s false) (nOf s true) a)
    (some (simulate pIm a.2.1.1.2)) (some (simulate pIm a.2.2.1.1.2))
    (((gameS A idx b).σ₃ s (some (simulate pIm a.2.1.1.2)) (some (simulate pIm a.2.2.1.1.2))).map
      fun _ => simulate pRm a.2.2.2.1.1.2)
    (((gameS A idx b).σ₄ s (some (simulate pIm a.2.1.1.2)) (some (simulate pIm a.2.2.1.1.2))
      (((gameS A idx b).σ₃ s (some (simulate pIm a.2.1.1.2))
        (some (simulate pIm a.2.2.1.1.2))).map fun _ => simulate pRm a.2.2.2.1.1.2)).map
      fun _ => simulate pRm a.2.2.2.2.1.2)
    (qI A s false) (qI A s true) (qR A idx b (s, a) false) (qR A idx b (s, a) true)
    rfl rfl rfl rfl (qOf_iss A s false).symm (qOf_iss A s true).symm (qOf_σ₃ A idx b s a).symm
    (qOf_σ₄ A idx b s a _).symm
    (spubP A idx b (tM A.toM s false) (tM A.toM s true) (nOf s false) (nOf s true) a)
    (by
      unfold spubP
      rw [actO_qR, actO_qR]
      rfl)
    (by
      have h' := h
      unfold bstar at h'
      rw [hR] at h'
      exact h')
  rcases key with he | hc | hcoll
  · exact Or.inl he
  · refine Or.inr (Or.inl ?_)
    rcases hc with hc | hc | hc | hc
    · exact Or.inl (mem_union_left _ hc)
    · exact Or.inr (mem_union_left _ hc)
    · have hin := candO_qR A idx b (s, a) false _ _ _ hc
      have e : (b ^^ false) = b := Bool.xor_false b
      rw [e] at hin
      have hw : winS A idx b b (s, a) := by
        unfold winS predS
        refine mem_union_right _ ?_
        rw [Bool.xor_self]
        exact hin
      cases b
      · exact Or.inl hw
      · exact Or.inr hw
    · have hin := candO_qR A idx b (s, a) true _ _ _ hc
      have e : (b ^^ true) = !b := Bool.xor_true b
      rw [e] at hin
      have hw : winS A idx b (!b) (s, a) := by
        unfold winS predS
        refine mem_union_right _ ?_
        rw [show (b ^^ !b) = true by cases b <;> rfl]
        exact hin
      cases b
      · exact Or.inr hw
      · exact Or.inl hw
  · exact Or.inr (Or.inr hcoll)


/-! ## The probabilities -/

theorem pr_errS₁_le : pr (GTape SecM pIm pIm pRm pRm) (fun x => errC pIm x.2.2.1.1.2) ≤
    noHitProb :=
  pr_le_of_fst fun _ => pr_le_of_fst fun _ => pr_le_of_snd fun _ => pr_errC_le

theorem pr_errS₂_le : pr (GTape SecM pIm pIm pRm pRm) (fun x => errC pIm x.2.2.2.1.1.2) ≤
    noHitProb :=
  pr_le_of_fst fun _ => pr_le_of_fst fun _ => pr_le_of_fst fun _ => pr_le_of_snd fun _ =>
    pr_errC_le

theorem pr_errS₃_le : pr (GTape SecM pIm pIm pRm pRm) (fun x => errC pRm x.2.2.2.2.1.1.2) ≤
    noHitProb :=
  pr_le_of_fst fun _ => pr_le_of_fst fun _ => pr_le_of_fst fun _ => pr_le_of_fst fun _ =>
    pr_le_of_snd fun _ => pr_errC_le

theorem pr_errS₄_le : pr (GTape SecM pIm pIm pRm pRm) (fun x => errC pRm x.2.2.2.2.2.1.2) ≤
    noHitProb :=
  pr_le_of_fst fun _ => pr_le_of_fst fun _ => pr_le_of_fst fun _ => pr_le_of_fst fun _ =>
    pr_le_of_fst fun _ => pr_errC_le

set_option maxRecDepth 8192 in
/-- **The two issuance proofs collide with probability `≤ 313·2⁻¹²⁸`**: the second proof's `d` is
uniform and independent of the first proof. -/
theorem pr_coll₂_le : pr (GTape SecM pIm pIm pRm pRm) (coll₂ A) ≤ ((312 : ℕ) + 1) / 2 ^ 128 := by
  refine pr_le_of_fst fun s => pr_le_of_fst fun u => pr_le_of_fst fun k₁ => pr_le_of_snd fun r =>
    pr_KS_d_le _ fun ρ sh c1 c2 c3 c5 V => ?_
  exact pr_sib_hit_le Hashes.shake mainP_pIm (stI ⟨tM A.toM s true, A.toM.int.ci⟩) u.2 sh c1 c2 c3
    c5 (rOf s true) (sibO Hashes.shake pIm (qI A s false) u.2 k₁.1.2) (sibO_length_le _ _ _ _)

set_option maxRecDepth 8192 in
/-- **The left redemption proof collides with an issuance proof with probability
`≤ 625·2⁻¹²⁸`.** -/
theorem pr_coll₃_le (b : Bool) :
    pr (GTape SecM pIm pIm pRm pRm) (coll₃ A idx b) ≤ ((624 : ℕ) + 1) / 2 ^ 128 := by
  refine pr_le_of_fst fun s => pr_le_of_fst fun u => pr_le_of_fst fun k₁ => pr_le_of_fst fun k₂ =>
    pr_le_of_snd fun k₄ => pr_KS_d_le _ fun ρ sh c1 c2 c3 c5 V => ?_
  have hlen : (sibO Hashes.shake pIm (qI A s false) u.2 k₁.1.2 ++
      sibO Hashes.shake pIm (qI A s true) u.2 k₂.1.2).length ≤ 624 := by
    rw [List.length_append]
    have := sibO_length_le Hashes.shake (qI A s false) u.2 k₁.1.2
    have := sibO_length_le Hashes.shake (qI A s true) u.2 k₂.1.2
    omega
  have hq : ∀ d : ZK.Sim.Bytes pRm.witnessBytes,
      qR A idx b (s, u, k₁, k₂, ((ρ, (sh, (c1, c2, c3, d, c5))), V), k₄) false =
      (stRP A idx b (tM A.toM s false) (tM A.toM s true) (nOf s false) (nOf s true)
        (u, k₁, k₂, ((ρ, (sh, (c1, c2, c3, fun _ => 0, c5))), V), k₄) false).map
        fun st => (st, rOf s (b ^^ false)) := fun d => qR_congr A idx b
          (s, u, k₁, k₂, ((ρ, (sh, (c1, c2, c3, d, c5))), V), k₄)
          (s, u, k₁, k₂, ((ρ, (sh, (c1, c2, c3, fun _ => 0, c5))), V), k₄) false rfl rfl rfl
  rcases hst : stRP A idx b (tM A.toM s false) (tM A.toM s true) (nOf s false) (nOf s true)
    (u, k₁, k₂, ((ρ, (sh, (c1, c2, c3, fun _ => 0, c5))), V), k₄) false with _ | st
  · refine le_trans (le_of_eq ?_) (by positivity)
    rw [pr_congr (Q := fun _ => False) fun d => by
      unfold coll₃
      rw [hq d, hst]
      simp [sibO]]
    exact pr_false
  · refine le_trans (pr_mono fun d hd => ?_) (pr_sib_hit_le Hashes.shake mainP_pRm st u.2 sh c1 c2
      c3 c5 (rOf s (b ^^ false)) _ hlen)
    unfold coll₃ at hd
    rw [hq d, hst] at hd
    exact hd

set_option maxRecDepth 8192 in
/-- **The right redemption proof collides with an earlier proof with probability
`≤ 937·2⁻¹²⁸`.** -/
theorem pr_coll₄_le (b : Bool) :
    pr (GTape SecM pIm pIm pRm pRm) (coll₄ A idx b) ≤ ((936 : ℕ) + 1) / 2 ^ 128 := by
  refine pr_le_of_fst fun s => pr_le_of_fst fun u => pr_le_of_fst fun k₁ => pr_le_of_fst fun k₂ =>
    pr_le_of_fst fun k₃ => pr_KS_d_le _ fun ρ sh c1 c2 c3 c5 V => ?_
  have hlen : (sibO Hashes.shake pIm (qI A s false) u.2 k₁.1.2 ++
      sibO Hashes.shake pIm (qI A s true) u.2 k₂.1.2 ++
      sibO Hashes.shake pRm (qR A idx b (s, u, k₁, k₂, k₃,
        ((ρ, (sh, (c1, c2, c3, fun _ => 0, c5))), V)) false) u.2 k₃.1.2).length ≤ 936 := by
    rw [List.length_append, List.length_append]
    have := sibO_length_le Hashes.shake (qI A s false) u.2 k₁.1.2
    have := sibO_length_le Hashes.shake (qI A s true) u.2 k₂.1.2
    have := sibO_length_le Hashes.shake (qR A idx b (s, u, k₁, k₂, k₃,
        ((ρ, (sh, (c1, c2, c3, fun _ => 0, c5))), V)) false) u.2 k₃.1.2
    omega
  have hq : ∀ d : ZK.Sim.Bytes pRm.witnessBytes,
      qR A idx b (s, u, k₁, k₂, k₃, ((ρ, (sh, (c1, c2, c3, d, c5))), V)) true =
      (stRP A idx b (tM A.toM s false) (tM A.toM s true) (nOf s false) (nOf s true)
        (u, k₁, k₂, k₃, ((ρ, (sh, (c1, c2, c3, fun _ => 0, c5))), V)) true).map
        fun st => (st, rOf s (b ^^ true)) := fun d => qR_congr A idx b
          (s, u, k₁, k₂, k₃, ((ρ, (sh, (c1, c2, c3, d, c5))), V))
          (s, u, k₁, k₂, k₃, ((ρ, (sh, (c1, c2, c3, fun _ => 0, c5))), V)) true rfl rfl rfl
  have hq' : ∀ d : ZK.Sim.Bytes pRm.witnessBytes,
      qR A idx b (s, u, k₁, k₂, k₃, ((ρ, (sh, (c1, c2, c3, d, c5))), V)) false =
      qR A idx b (s, u, k₁, k₂, k₃, ((ρ, (sh, (c1, c2, c3, fun _ => 0, c5))), V)) false :=
    fun d => qR_congr A idx b (s, u, k₁, k₂, k₃, ((ρ, (sh, (c1, c2, c3, d, c5))), V))
      (s, u, k₁, k₂, k₃, ((ρ, (sh, (c1, c2, c3, fun _ => 0, c5))), V)) false rfl rfl rfl
  rcases hst : stRP A idx b (tM A.toM s false) (tM A.toM s true) (nOf s false) (nOf s true)
    (u, k₁, k₂, k₃, ((ρ, (sh, (c1, c2, c3, fun _ => 0, c5))), V)) true with _ | st
  · refine le_trans (le_of_eq ?_) (by positivity)
    rw [pr_congr (Q := fun _ => False) fun d => by
      unfold coll₄
      rw [hq d, hst]
      simp [sibO]]
    exact pr_false
  · refine le_trans (pr_mono fun d hd => ?_) (pr_sib_hit_le Hashes.shake mainP_pRm st u.2 sh c1 c2
      c3 c5 (rOf s (b ^^ true)) _ hlen)
    unfold coll₄ at hd
    rw [hq d, hq' d, hst] at hd
    exact hd

/-- **The predictor for Client `false`** in the game `PU.puAdv`: public part `nf₀`, commitment
`t₀`, auxiliary coins the other Client's `(nf₁, r₁)`, the simulators' coins and the tables. -/
noncomputable def predS₀ (b : Bool) (n : Coins nfBytes) (t : Bytes)
    (a : (Coins nfBytes × Coins rBytes) × AuxS) : Finset (Coins rBytes) :=
  predS A idx b t (comM A.toM a.1.1 a.1.2) (List.ofFn n) (List.ofFn a.1.1) a.2 false

/-- **The predictor for Client `true`.** -/
noncomputable def predS₁ (b : Bool) (n : Coins nfBytes) (t : Bytes)
    (a : (Coins nfBytes × Coins rBytes) × AuxS) : Finset (Coins rBytes) :=
  predS A idx b (comM A.toM a.1.1 a.1.2) t (List.ofFn a.1.1) (List.ofFn n) a.2 true

theorem pr_winS_false (b : Bool) :
    pr (GTape SecM pIm pIm pRm pRm) (winS A idx b false) =
      puAdv (comM A.toM) (predS₀ A idx b) := by
  let e : (Coins nfBytes × Coins rBytes) × ((Coins nfBytes × Coins rBytes) × AuxS) ≃
      GTape SecM pIm pIm pRm pRm :=
    { toFun := fun z => ((z.1, z.2.1), z.2.2)
      invFun := fun x => (x.1.1, (x.1.2, x.2))
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [← pr_equiv e]
  rfl

theorem pr_winS_true (b : Bool) :
    pr (GTape SecM pIm pIm pRm pRm) (winS A idx b true) =
      puAdv (comM A.toM) (predS₁ A idx b) := by
  let e : (Coins nfBytes × Coins rBytes) × ((Coins nfBytes × Coins rBytes) × AuxS) ≃
      GTape SecM pIm pIm pRm pRm :=
    { toFun := fun z => ((z.2.1, z.1), z.2.2)
      invFun := fun x => (x.1.2, (x.1.1, x.2))
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [← pr_equiv e]
  rfl

/-- **The (PU) term with shared tables is at most the advantage of the two explicit predictors**,
plus `4·noHitProb` (failed simulations) and `1875·2⁻¹²⁸` (collisions between simulated
proofs). -/
theorem puTermS_le (b : Bool) :
    puTermS A idx b ≤ 4 * noHitProb + puAdv (comM A.toM) (predS₀ A idx b) +
      puAdv (comM A.toM) (predS₁ A idx b) + 1875 / 2 ^ 128 := by
  unfold puTermS hyb
  have h := (pr_mono (puS_imp A idx b)).trans ((pr_or_le _ _).trans (add_le_add
    ((pr_or_le _ _).trans (add_le_add le_rfl ((pr_or_le _ _).trans (add_le_add le_rfl
      (pr_or_le _ _)))))
    ((pr_or_le _ _).trans (add_le_add (pr_or_le _ _) ((pr_or_le _ _).trans
      (add_le_add le_rfl (pr_or_le _ _)))))))
  rw [pr_winS_false, pr_winS_true] at h
  have e₁ := pr_errS₁_le
  have e₂ := pr_errS₂_le
  have e₃ := pr_errS₃_le
  have e₄ := pr_errS₄_le
  have c₂ := pr_coll₂_le A
  have c₃ := pr_coll₃_le A idx b
  have c₄ := pr_coll₄_le A idx b
  have hn : (((312 : ℕ) + 1 : ℝ) / 2 ^ 128) + (((624 : ℕ) + 1 : ℝ) / 2 ^ 128) +
      (((936 : ℕ) + 1 : ℝ) / 2 ^ 128) = 1875 / 2 ^ 128 := by norm_num
  linarith

/-! ## Theorem 4(a) on `main`, shared tables, with (PU) as a game -/

/-- **Theorem 4(a) on `main` (no label rows) with one `H₅` table and one cipher for the four
proofs, with the (PU) advantage of explicit predictors.** For the colluding adversary whose guess
reads each `H₃` slice at `q3` keys, the cipher at `qE` keys and `H₅` at the consistent read set
`R5` (`AdversaryS.Cons`),

    |Pr[world 0] − Pr[world 1]| ≤ 30·εS(q3, qE + 8·4607)
      + 15·(Σ_{b, c} puAdv Com (predS_c b) + 8·noHitProb + 3750·2⁻¹²⁸) + 2·εhide.

The four `puAdv` terms are (PU), an assumption on Keccak-p[800,12], and `εhide` is hiding of
`Com`; every other term is a number (`noHitProb ≤ 2^{−2¹⁵}`). Each predictor outputs at most
`2·(q5 + 1249)` candidates if `R5` has at most `q5` keys (`card_predS_le`). -/
theorem anonymity_main_shared {q3 qE : ℕ} (hC : A.Cons q3 qE) {εhide : ℝ}
    (hhide : ∀ b a, hidingAdv A.toM.int.ci A.toM.int.cr (redS A idx b a) ≤ εhide) :
    |realS A idx false - realS A idx true| ≤
      30 * εS q3 (qE + 8 * 4607) + 15 * (puAdv (comM A.toM) (predS₀ A idx false) +
        puAdv (comM A.toM) (predS₁ A idx false) + puAdv (comM A.toM) (predS₀ A idx true) +
        puAdv (comM A.toM) (predS₁ A idx true) + 8 * noHitProb + 3750 / 2 ^ 128) +
        2 * εhide := by
  have h := anonymity_main_shared0 A idx hC hhide
  have p0 := puTermS_le A idx false
  have p1 := puTermS_le A idx true
  linarith

end VoleMole.Privacy.Moussaka
