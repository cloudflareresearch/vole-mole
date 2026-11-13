import VoleMole.Theft.HitLevel

/-!
# `ε_hit` for Ratatouille's Lean verifiers, with the chain hashes random tables

The programming step of the theft theorems (`weakSE2_of_plain`) leaves `ε_hit`: the probability
that a fresh forgery's verifier `H₂³` point is a point a simulator programmed (`ProgEv … HitOpX`).
`Theft/HitLevel.lean` bounds it for any two proof systems (`progEv_chain`). Here are the facts it
needs for Ratatouille, in the model of `noTheft_leanX_plain` with the extra table `XTab L M`.

* **The forgery** of an operation (`fd`): its statement (the spend's with the adversary's key)
  and proof bytes. All its chain inputs have at most `Lmin = 14357` bytes (`fd_fOk`), so they are
  table points when `L ≥ Lmin`.
* Equal `H₂⁰` inputs mean equal statements (`muIn_stI_inj`, `muIn_stS_inj`; issuance and spend
  inputs have 64 and 88 bytes), which freshness excludes (`fresh_ne₁`, `fresh_ne₂`).
* **Freshness with the adversary's key** (`FreshOk`). The Lean spend statement does not hash the
  key `pk` (`Privacy.Ratatouille.stS`), so a spend statement that differs from a simulated one only
  in the key has the same chain; the bound is for `FreshOk`, which compares a spend with the
  simulated spend's statement under the adversary's key. In the game this is `FreshOp`
  (`freshOk_stS`), and `FreshOk` implies `FreshOp` (`FreshOk.freshOp`).
* The Lean simulators' programmings are `SimProg` (`simProgI`, `simProgS`).
* **`progEv_hit`**: for `L ≥ 14357` and an adversary whose last stage reads `H₂⁰`, `H₂¹`, `H₂²` with
  `q_μ`, `q₂₁`, `q₂₂` queries,

      ε_hit ≤ 2·((q_μ+3)·2⁻²⁵⁶ + (q₂₁+3)·2⁻¹⁰⁸⁸ + (q₂₂+3)·2⁻⁴⁴⁸)   (`epsHit`).

`Theft/HitTheft.lean` puts it into the theft theorem (`noTheft_leanX_hit`).
-/

-- (The coin types are large products: their `Fintype` instances exceed the default size.)
set_option synthInstance.maxSize 1024

namespace VoleMole.Theft.Hit.Rata

open VoleMole.Privacy
open VoleMole.Verifier VoleMole.Verifier.Bridge VoleMole.ZK.Sim VoleMole.ZK
open VoleMole.Privacy.Ratatouille VoleMole.Spec.Ratatouille VoleMole.Theft.Ratatouille
open VoleMole.Theft.Chain
open VoleMole.ROM.IC (muIn)

variable {R : Type} [CipherRow R] {L M : ℕ}

/-- **The forgery of an operation**: its statement (the spend's with the adversary's key) and
proof bytes. -/
def fd {G S : Type} (A : Thief Sizes.labelRows G S) : Op Sizes.labelRows → FD
  | .issue q t c => (Privacy.Ratatouille.stI (opXI q t c), bOf (issueReqProof q))
  | .spend q c _ => (Privacy.Ratatouille.stS (opXS A q c), bOf (SpendReq.parse q).proof)

/-- **The weak freshness of the theft game with the adversary's key**: a spend is compared with
the simulated spend's statement with its key replaced by the adversary's. In the game the
Client's spend statement has the adversary's key (`stS`), so this is `FreshOp` there
(`freshOk_stS`); it never holds where `FreshOp` fails (`FreshOk.freshOp`). The Lean spend
statement does not hash the key (`Privacy.Ratatouille.stS`), so two spend statements that differ
only in the key have the same chain. -/
def FreshOk {Z : Sizes} {G S : Type} (A : Thief Z G S) (p₁ : Option (IssueInstance × IssueProof Z))
    (p₂ : Option (SpendInstance × SpendProof Z)) (op : Op Z) : Prop :=
  FreshOp A p₁ (p₂.map fun y => ({ y.1 with pk := A.pk }, y.2)) op

/-! ### The statements' `H₂⁰` inputs -/

lemma size_bOf {n : ℕ} (v : Spec.Ratatouille.Bytes n) : (bOf v).size = n := by
  simp [bOf, size_toBA]

lemma bOf_inj {n : ℕ} {v w : Spec.Ratatouille.Bytes n} (h : bOf v = bOf w) : v = w :=
  Vector.toList_inj.1 (EndToEnd.SpecRel.toBA_inj h)

lemma append_split {a b a' b' : ByteArray} (h : a ++ b = a' ++ b') (hs : a.size = a'.size) :
    a = a' ∧ b = b' := by
  have ha : a = a' := by
    have e : (a ++ b).extract 0 a.size = (a' ++ b').extract 0 a.size := by rw [h]
    rwa [ByteArray.extract_append_eq_left rfl, ByteArray.extract_append_eq_left hs] at e
  subst ha
  exact ⟨rfl, (ByteArray.append_right_inj _).1 h⟩

lemma le64_toNat_inj {a b : UInt64} (h : le64 a.toNat = le64 b.toNat) : a = b :=
  UInt64.toNat_inj.1 (EndToEnd.SpecRel.le64_inj (UInt64.toNat_lt a) (UInt64.toNat_lt b) h)

lemma muIn_stI (x : IssueInstance) : muIn (Privacy.Ratatouille.stI x) =
    (bOf x.c ++ le64 x.tInit.toNat ++ bOf x.ctx ++ toBA (Spec.makeDst "rata" 0 'i' '0')).push 8 :=
  rfl

lemma muIn_stS (x : SpendInstance) : muIn (Privacy.Ratatouille.stS x) =
    (bOf x.nf ++ le64 x.d.toNat ++ bOf x.cNext ++ bOf x.ctx ++
      toBA (Spec.makeDst "rata" 0 'p' '0')).push 8 :=
  rfl

lemma size_muIn_stI (x : IssueInstance) : (muIn (Privacy.Ratatouille.stI x)).size = 64 := by
  rw [muIn_stI]
  simp only [ByteArray.size_push, ByteArray.size_append, size_bOf, EndToEnd.SpecRel.size_le64]
  have : (toBA (Spec.makeDst "rata" 0 'i' '0')).size = 7 := by decide
  omega

lemma size_muIn_stS (x : SpendInstance) : (muIn (Privacy.Ratatouille.stS x)).size = 88 := by
  rw [muIn_stS]
  simp only [ByteArray.size_push, ByteArray.size_append, size_bOf, EndToEnd.SpecRel.size_le64]
  have : (toBA (Spec.makeDst "rata" 0 'p' '0')).size = 7 := by decide
  omega

/-- **The issuance statement is determined by its `H₂⁰` input.** -/
lemma muIn_stI_inj {x y : IssueInstance}
    (h : muIn (Privacy.Ratatouille.stI x) = muIn (Privacy.Ratatouille.stI y)) : x = y := by
  rw [muIn_stI, muIn_stI] at h
  have h1 := (ByteArray.append_left_inj _).1 (push_injective 8 h)
  obtain ⟨h2, hctx⟩ := append_split h1 (by simp [size_bOf, EndToEnd.SpecRel.size_le64])
  obtain ⟨hc, ht⟩ := append_split h2 (by simp [size_bOf])
  cases x
  cases y
  simp only at hc ht hctx
  rw [bOf_inj hc, le64_toNat_inj ht, bOf_inj hctx]

/-- **The spend statement is determined by its `H₂⁰` input, but for the key.** -/
lemma muIn_stS_inj {x y : SpendInstance}
    (h : muIn (Privacy.Ratatouille.stS x) = muIn (Privacy.Ratatouille.stS y)) :
    { x with pk := y.pk } = y := by
  rw [muIn_stS, muIn_stS] at h
  have h1 := (ByteArray.append_left_inj _).1 (push_injective 8 h)
  obtain ⟨h2, hctx⟩ := append_split h1
    (by simp [size_bOf, EndToEnd.SpecRel.size_le64])
  obtain ⟨h3, hcn⟩ := append_split h2 (by simp [size_bOf, EndToEnd.SpecRel.size_le64])
  obtain ⟨hnf, hd⟩ := append_split h3 (by simp [size_bOf])
  cases x
  cases y
  simp only at hnf hd hcn hctx ⊢
  rw [bOf_inj hnf, le64_toNat_inj hd, bOf_inj hcn, bOf_inj hctx]

/-! ### Freshness with the adversary's key -/

section Fresh

variable {Z : Sizes} {G S : Type} (B : Thief Z G S)

lemma FreshOk.freshOp {p₁ : Option (IssueInstance × IssueProof Z)}
    {p₂ : Option (SpendInstance × SpendProof Z)} {op : Op Z} (h : FreshOk B p₁ p₂ op) :
    FreshOp B p₁ p₂ op := by
  cases op with
  | issue q t c => exact h
  | spend q c x =>
    intro y hy he
    refine h ({ y.1 with pk := B.pk }, y.2) (by rw [hy]; rfl) ?_
    rw [he]
    simp only [opXS] at he ⊢
    rw [← he]

lemma freshOk_stS (p₁ : Option (IssueInstance × IssueProof Z)) (o₂ : Except Error (SpendRequest Z))
    (op : Op Z) : FreshOk B p₁ (Theft.Ratatouille.stS B o₂) op ↔
      FreshOp B p₁ (Theft.Ratatouille.stS B o₂) op := by
  have e : (Theft.Ratatouille.stS B o₂).map (fun y => ({ y.1 with pk := B.pk }, y.2)) =
      Theft.Ratatouille.stS B o₂ := by
    unfold Theft.Ratatouille.stS
    cases o₂ <;> rfl
  unfold FreshOk
  rw [e]

end Fresh


/-! ### The forgery's chain inputs are table points -/

/-- The shortest table length that holds every chain input of the forgeries:
`H₂¹` inputs of the spend relation (`14357` bytes). -/
def Lmin : ℕ := 14357

lemma fd_fOk {G S : Type} (A : Thief Sizes.labelRows G S) (hL : Lmin ≤ L)
    (op : Op Sizes.labelRows) : FOk L (fd A op).1 := by
  cases op with
  | issue q t c =>
    refine ⟨rfl, rfl, rfl, le_trans ?_ hL, le_trans ?_ hL, le_trans ?_ hL⟩
    · show 64 + 16 * pI.correctionBytes + pI.nMask * pI.nMultBytes + 16 + 0 + 1 ≤ Lmin
      decide
    · show 264 + 0 + pI.witnessBytes + 1 ≤ Lmin
      decide
    · simp only [fd, size_muIn_stI, Lmin]
      omega
  | spend q c x =>
    refine ⟨rfl, rfl, rfl, le_trans ?_ hL, le_trans ?_ hL, le_trans ?_ hL⟩
    · show 64 + 16 * pS.correctionBytes + pS.nMask * pS.nMultBytes + 16 + 0 + 1 ≤ Lmin
      decide
    · show 264 + 0 + pS.witnessBytes + 1 ≤ Lmin
      decide
    · simp only [fd, size_muIn_stS, Lmin]
      omega

lemma simO_some_I {i : IssueInstance} {c : SimCoins pI} {b : ByteArray} (h : simulate pI c = .ok b) :
    ∃ π, simO leanSimIR (some i) c = some π := by
  rcases h' : leanSimIR i c with _ | π
  · have h'' : vecOf Sizes.labelRows.issue (simulate pI c) = none := h'
    rw [h] at h''
    have hn : pI.proofBytes = Sizes.labelRows.issue := by decide
    simp only [vecOf, simulate_ok_size h, hn, ↓reduceDIte, reduceCtorEq] at h''
  · exact ⟨π, by simp only [simO]; exact h'⟩

lemma simO_some_S {i : SpendInstance} {c : SimCoins pS} {b : ByteArray} (h : simulate pS c = .ok b) :
    ∃ π, simO leanSimSR (some i) c = some π := by
  rcases h' : leanSimSR i c with _ | π
  · have h'' : vecOf Sizes.labelRows.spend (simulate pS c) = none := h'
    rw [h] at h''
    have hn : pS.proofBytes = Sizes.labelRows.spend := by decide
    simp only [vecOf, simulate_ok_size h, hn, ↓reduceDIte, reduceCtorEq] at h''
  · exact ⟨π, by simp only [simO]; exact h'⟩


/-! ### The programmings, the hit, freshness -/

/-- The issuance simulator's programming. -/
lemma simProgI : SimProg (R := R) (L := L) (M := M) (leanProgIRX hbX)
    (fun i c => (Privacy.Ratatouille.stI i, simulate pI c)) :=
  simProg_progRO Privacy.Ratatouille.stI fun _ => rfl

/-- The spend simulator's programming. -/
lemma simProgS : SimProg (R := R) (p := pI) (L := L) (M := M) (leanProgSRX hbX)
    (fun i c => (Privacy.Ratatouille.stS i, simulate pS c)) :=
  simProg_progRO (p := pS) Privacy.Ratatouille.stS fun _ => rfl

variable (A : Thief Sizes.labelRows Tab3 (ShT R pI L M))

/-- **A programmed point of the verifier is a hit of the forgery.** -/
lemma hitG_of_hitOpX (op : Op Sizes.labelRows) (t' t : ShT R pI L M)
    (h : HitOpX (Hb := hbX) A op t' t) : HitG (fd A op) t' t := by
  cases op with
  | issue q tc c => exact hitG_of_hitPt _ _ t' t h
  | spend q c x => exact hitG_of_hitPt (p := pS) _ _ t' t h

omit [CipherRow R] in
/-- **A fresh forgery's `H₂⁰` input is not the simulated issuance's.** -/
lemma fresh_ne₁ (x₁ : Option IssueInstance) (c₁ : SimCoins pI)
    (p₂ : Option (SpendInstance × SpendProof Sizes.labelRows)) (op : Op Sizes.labelRows)
    (i : IssueInstance) (hfr : FreshOk A (pairO x₁ (simO leanSimIR x₁ c₁)) p₂ op)
    (hi : x₁ = some i) (hok : ∃ b, simulate pI c₁ = .ok b) :
    muIn (fd A op).1 ≠ muIn (Privacy.Ratatouille.stI i) := by
  subst hi
  intro hm
  cases op with
  | issue q tc c =>
    obtain ⟨b, hb⟩ := hok
    obtain ⟨π, hπ⟩ := simO_some_I (i := i) hb
    exact hfr (i, π) (by rw [hπ]; rfl) (muIn_stI_inj hm)
  | spend q c x =>
    have := congrArg ByteArray.size hm
    simp only [fd, size_muIn_stI, size_muIn_stS] at this
    omega

omit [CipherRow R] in
/-- **A fresh forgery's `H₂⁰` input is not the simulated spend's.** -/
lemma fresh_ne₂ (p₁ : Option (IssueInstance × IssueProof Sizes.labelRows))
    (x₂ : Option SpendInstance) (c₂ : SimCoins pS) (op : Op Sizes.labelRows) (i : SpendInstance)
    (hfr : FreshOk A p₁ (pairO x₂ (simO leanSimSR x₂ c₂)) op) (hi : x₂ = some i)
    (hok : ∃ b, simulate pS c₂ = .ok b) :
    muIn (fd A op).1 ≠ muIn (Privacy.Ratatouille.stS i) := by
  subst hi
  intro hm
  cases op with
  | issue q tc c =>
    have := congrArg ByteArray.size hm
    simp only [fd, size_muIn_stI, size_muIn_stS] at this
    omega
  | spend q c x =>
    obtain ⟨b, hb⟩ := hok
    obtain ⟨π, hπ⟩ := simO_some_S (i := i) hb
    refine hfr ({ i with pk := A.pk }, π) (by rw [hπ]; rfl) ?_
    have := muIn_stS_inj hm.symm
    rw [← this]
    rfl

/-- **`ε_hit` for the Lean verifiers and simulators of Ratatouille, with the chain hashes random
tables.** With `H₂⁰`, `H₂¹`, `H₂²` uniform tables on the inputs of at most `L ≥ 14357` bytes
(`hbX`), against adversaries that read them with `q_μ`, `q₂₁`, `q₂₂` queries (`AdmHit`), a fresh
forgery (`FreshOk`) hits a programmed `H₂³` point with probability

    ≤ 2·((q_μ+3)·2⁻²⁵⁶ + (q₂₁+3)·2⁻¹⁰⁸⁸ + (q₂₂+3)·2⁻⁴⁴⁸)

(`progEv_chain`). -/
theorem progEv_hit [Fintype R] [Nonempty R] (hL : Lmin ≤ L) (qMu q21 q22 : ℕ) :
    ProgEv leanSimIR (leanProgIRX (R := R) hbX) leanSimSR (leanProgSRX hbX) (FreshOk A)
      (HitOpX (Hb := hbX) A) (AdmHit (R := R) (p := pI) (L := L) (M := M) (G := Tab3) qMu q21 q22) (epsHit qMu q21 q22) :=
  progEv_chain (R := R) (G := Tab3) (sim₁ := leanSimIR) (sim₂ := leanSimSR) simProgI simProgS (fd A)
    (Fresh := FreshOk A) (fun _ _ op _ => fd_fOk A hL op) (hitG_of_hitOpX A)
    (fun x₁ c₁ p₂ op i hfr hi hok => by
      dsimp only at hok ⊢
      exact fresh_ne₁ A x₁ c₁ p₂ op i hfr hi hok)
    (fun p₁ x₂ c₂ op i hfr hi hok => by
      dsimp only at hok ⊢
      exact fresh_ne₂ A p₁ x₂ c₂ op i hfr hi hok) qMu q21 q22

end VoleMole.Theft.Hit.Rata
