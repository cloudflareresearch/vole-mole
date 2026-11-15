import VoleMole.Theft.MoussakaUnboundTables
import VoleMole.Theft.MoussakaManyHit

/-!
# Unbound Moussaka for `U` tokens and `M` redemptions with `ε_hit` bounded

`nmUN_leanX_plain` (`Theft/MoussakaUnboundTables.lean`) leaves the programming term `ε_moves`.
Here it is bounded for the concrete extra table `XTab L M'`, as `Theft/MoussakaManyHit.lean`
does for bound Moussaka (`Theft/HitMany.lean`, `progMovesN_chain`).

* The unbound statements' `H₂⁰` inputs are the bound ones with other domain separators (the
  issuance encoding `t ‖ ctx_iss` is the bound one, the redemption is hashed as the bound
  redemption, `hash_redeem_instance`). So well-formed statements are determined by their `H₂⁰`
  inputs as for bound Moussaka (`muIn_stIU_inj`, `muIn_stRU_inj`, from `Hit.Mous`), and issuance
  and redemption inputs differ (`muIn_stIU_ne_stRU`).
* `fdU_fOk`: a well-formed forgery's chain inputs have at most `LminU = 9749` bytes (`H₂¹` inputs
  of the unbound redemption relation, whose witness has 559 bytes).
* **`FreshOkN`**, **`HitWfN`**: as for bound Moussaka; the redemption context is the
  adversary's choice (`choose`), and the API checks both contexts' lengths (`AccOp`), so
  `HitWfN` asks only for the digests' lengths and that a redemption whose Anchor Set has the
  digests of a set the adversary chose for an honest redemption is under that set
  (`freshOkN_of_sim`, `sim_se_leN_ok`).
* **`nmUN_leanX_hit`**: with `XTab L M'` (`L ≥ 9749`), a `HitWfN` adversary and a last stage
  that reads the chain tables with `q_μ`, `q₂₁`, `q₂₂` queries (`AdmHitN`),

      Pr[BadN] ≤ U·εz(pI; q) + M·εz(pR; q) + Σ_i δ_i + ε_plain
        + N·((q₂₂+N+1)·2⁻⁴⁴⁸ + (q₂₁+N+1)·2⁻¹⁰⁸⁸ + (q_μ+N+1)·2⁻²⁵⁶)
        + Σ_h (ε_prf + (M+1)·2⁻¹⁹² + Adv^bind(B₁ h) + Adv^spr-k(B₂ h)),

  `N = U + M`. **`nmUN_leanX_hit_one`**: one token and one redemption (`U = M = 1`), where the
  programming term is `2·((q₂₂+3)·2⁻⁴⁴⁸ + (q₂₁+3)·2⁻¹⁰⁸⁸ + (q_μ+3)·2⁻²⁵⁶)`, the term of the
  one-token bound Moussaka theorem (`noRedirect_leanX_hit`).
-/

-- (The coin types are large products: their `Fintype` instances exceed the default size.)
set_option synthInstance.maxSize 1024

namespace VoleMole.Theft.MoussakaUnbound

open VoleMole.Privacy VoleMole.Privacy.MoussakaUnbound VoleMole.Spec VoleMole.Spec.MoussakaUnbound
  VoleMole.ZK.Sim VoleMole.Verifier VoleMole.Verifier.Bridge VoleMole.ZK VoleMole.Theft.Chain
open VoleMole.Spec.Moussaka (AnchorSet Error ctxBytes proveSeedBytes rBytes nfBytes cdBytes)
open VoleMole.Privacy.Moussaka (ShM leanSim)
open VoleMole.Theft.Hit.Mous (WfI WfR hashedR)
open VoleMole.ROM.IC (muIn)
open VoleMole.EndToEnd.SpecRel (toL_toBA toBA_inj)

-- `UCom`, `Derive` and `Com` evaluate Keccak-p[800]; nothing below needs to unfold them.
attribute [local irreducible] ucom derive UOVKey.eval

variable {U M : ℕ}

/-! ## The statements' `H₂⁰` inputs -/

/-- The unbound issuance instance as a bound one (the same fields, the same encoding). -/
def toBI (x : IssueInstance) : Spec.Moussaka.IssueInstance := ⟨x.t, x.ctxIss⟩

/-- **A well-formed unbound issuance instance**: `t` of `uov::M` bytes, a 16-byte context. -/
def WfIU (x : IssueInstance) : Prop := WfI (toBI x)

/-- **A well-formed unbound redemption instance**: as a bound one (`hash_redeem_instance`). -/
def WfRU (x : RedeemInstance) : Prop := WfR (toBound x)

/-- **What an unbound redemption statement hashes**: as a bound one. -/
def hashedRU (x : RedeemInstance) : List Bytes × Bytes × Bytes × Bytes × Bytes :=
  hashedR (toBound x)

lemma muIn_stIU (x : IssueInstance) : muIn (Privacy.MoussakaUnbound.stI x) =
    (toBA (toBI x).encode ++ toBA (makeDst "mous" 1 'i' '0')).push 8 := by
  simp [muIn, Privacy.MoussakaUnbound.stI, moussakaUnboundIssue, toL_toBA, toBI,
    IssueInstance.encode, Spec.Moussaka.IssueInstance.encode]

lemma muIn_stRU (x : RedeemInstance) : muIn (Privacy.MoussakaUnbound.stR x) =
    (toBA (toBound x).encode ++ toBA (makeDst "mous" 1 'r' '0')).push 8 :=
  rfl

lemma strip8 {a b d d' : ByteArray} (hd : d = d') (h : (a ++ d).push 8 = (b ++ d').push 8) :
    a = b := by
  subst hd
  exact (ByteArray.append_left_inj _).1 (push_injective 8 h)

/-- **A well-formed unbound issuance statement is determined by its `H₂⁰` input.** -/
lemma muIn_stIU_inj {x y : IssueInstance} (hx : WfIU x) (hy : WfIU y)
    (h : muIn (Privacy.MoussakaUnbound.stI x) = muIn (Privacy.MoussakaUnbound.stI y)) : x = y := by
  rw [muIn_stIU, muIn_stIU] at h
  have h1 := strip8 rfl h
  have h2 : muIn (Privacy.Moussaka.stI (toBI x)) = muIn (Privacy.Moussaka.stI (toBI y)) := by
    rw [Hit.Mous.muIn_stI, Hit.Mous.muIn_stI, h1]
  have e := Hit.Mous.muIn_stI_inj hx hy h2
  cases x
  cases y
  simp only [toBI, Spec.Moussaka.IssueInstance.mk.injEq] at e
  rw [e.1, e.2]

/-- **The hashed fields of a well-formed unbound redemption statement are determined by its
`H₂⁰` input.** -/
lemma muIn_stRU_inj {x y : RedeemInstance} (hx : WfRU x) (hy : WfRU y)
    (h : muIn (Privacy.MoussakaUnbound.stR x) = muIn (Privacy.MoussakaUnbound.stR y)) :
    hashedRU x = hashedRU y := by
  rw [muIn_stRU, muIn_stRU] at h
  have h1 := strip8 rfl h
  have h2 : muIn (Privacy.Moussaka.stR (toBound x)) = muIn (Privacy.Moussaka.stR (toBound y)) := by
    rw [Hit.Mous.muIn_stR, Hit.Mous.muIn_stR, h1]
  exact Hit.Mous.muIn_stR_inj hx hy h2

/-- **Unbound issuance and redemption `H₂⁰` inputs differ** (the domain separators). -/
lemma muIn_stIU_ne_stRU (x : IssueInstance) (y : RedeemInstance) :
    muIn (Privacy.MoussakaUnbound.stI x) ≠ muIn (Privacy.MoussakaUnbound.stR y) := by
  rw [muIn_stIU, muIn_stRU]
  intro h
  have h1 := push_injective 8 h
  have hs := congrArg ByteArray.size h1
  have h7 : (toBA (makeDst "mous" 1 'i' '0')).size = 7 := by decide
  have h7' : (toBA (makeDst "mous" 1 'r' '0')).size = 7 := by decide
  simp only [ByteArray.size_append, h7, h7'] at hs
  have hd := toBA_inj (Hit.append_split h1 (by omega)).2
  revert hd
  decide

lemma size_muIn_stIU {x : IssueInstance} (hx : WfIU x) :
    (muIn (Privacy.MoussakaUnbound.stI x)).size = 69 := by
  have h := Hit.Mous.size_muIn_stI hx
  have h7 : (toBA (makeDst "mous" 1 'i' '0')).size = 7 := by decide
  have h7' : (toBA (makeDst "mous" 0 'i' '0')).size = 7 := by decide
  rw [Hit.Mous.muIn_stI] at h
  rw [muIn_stIU]
  simp only [ByteArray.size_push, ByteArray.size_append, h7, h7'] at h ⊢
  omega

lemma size_muIn_stRU_le {x : RedeemInstance} (hx : WfRU x) :
    (muIn (Privacy.MoussakaUnbound.stR x)).size ≤ 2152 := by
  have h := Hit.Mous.size_muIn_stR_le hx
  have h7 : (toBA (makeDst "mous" 1 'r' '0')).size = 7 := by decide
  have h7' : (toBA (makeDst "mous" 0 'r' '0')).size = 7 := by decide
  rw [Hit.Mous.muIn_stR] at h
  rw [muIn_stRU]
  simp only [ByteArray.size_push, ByteArray.size_append, h7, h7'] at h ⊢
  omega

/-! ## The forgery -/

/-- **The forgery of an operation**: its statement and proof bytes. -/
def fdU : UOp → Hit.FD
  | .issue req ci => (Privacy.MoussakaUnbound.stI (stOfI req ci), toBA (req.drop uovM))
  | .redeem S' req ci cr cd =>
      (Privacy.MoussakaUnbound.stR (stOfR S' req ci cr cd), toBA (req.drop nfBytes))

/-- The operation's statement is well-formed. -/
def WfOpU : UOp → Prop
  | .issue req ci => WfIU (stOfI req ci)
  | .redeem S' req ci cr cd => WfRU (stOfR S' req ci cr cd)

/-- The shortest table length that holds every chain input of the well-formed forgeries:
`H₂¹` inputs of the unbound redemption relation (`9749` bytes). -/
def LminU : ℕ := 9749

lemma fdU_fOk {L : ℕ} (hL : LminU ≤ L) {op : UOp} (h : WfOpU op) : Hit.FOk L (fdU op).1 := by
  cases op with
  | issue req ci =>
    refine ⟨rfl, rfl, rfl, le_trans ?_ hL, le_trans ?_ hL, le_trans ?_ hL⟩
    · show 64 + 16 * pI.correctionBytes + pI.nMask * pI.nMultBytes + 16 + 0 + 1 ≤ LminU
      decide
    · show 264 + 0 + pI.witnessBytes + 1 ≤ LminU
      decide
    · simp only [fdU, size_muIn_stIU (x := stOfI req ci) h, LminU]
      omega
  | redeem S' req ci cr cd =>
    refine ⟨rfl, rfl, rfl, le_trans ?_ hL, le_trans ?_ hL, le_trans ?_ hL⟩
    · show 64 + 16 * pR.correctionBytes + pR.nMask * pR.nMultBytes + 16 + 0 + 1 ≤ LminU
      decide
    · show 264 + 0 + pR.witnessBytes + 1 ≤ LminU
      decide
    · have := size_muIn_stRU_le (x := stOfR S' req ci cr cd) h
      simp only [fdU, LminU]
      omega

/-! ## Freshness of the bound, in the game -/

section Fresh

variable {G S : Type} (A : ThiefN U M G S)

/-- **The freshness of the bound on `ε_hit`** for `U + M` simulated unbound proofs: the
operation's statement is well-formed, and each logged statement of its relation is well-formed
and differs from it in a hashed field. -/
def FreshOkN (l : Log) : UOp → Prop
  | .issue req ci => WfIU (stOfI req ci) ∧
      ∀ x π, some (Sum.inl x, π) ∈ l → WfIU x ∧ stOfI req ci ≠ x
  | .redeem S' req ci cr cd => WfRU (stOfR S' req ci cr cd) ∧
      ∀ x π, some (Sum.inr x, π) ∈ l → WfRU x ∧ hashedRU (stOfR S' req ci cr cd) ≠ hashedRU x

lemma FreshOkN.freshOpN {l : Log} {op : UOp} (h : FreshOkN l op) : FreshOpN l op := by
  cases op with
  | issue req ci => exact fun x π hx => (h.2 x π hx).2
  | redeem S' req ci cr cd => exact fun x π hx he => (h.2 x π hx).2 (by rw [he])

lemma FreshOkN.wf {l : Log} {op : UOp} (h : FreshOkN l op) : WfOpU op := by
  cases op with
  | issue req ci => exact h.1
  | redeem S' req ci cr cd => exact h.1

/-- **The adversaries of the bound**, as `Theft.Moussaka.HitWfN`: the Anchor Sets the adversary
chooses and outputs have 32-byte digests, its challenge digests have 32 bytes, and a redemption
whose Anchor Set has the digests of a set the adversary chose for an honest redemption is under
that set (in C++ the digest is SHAKE256 of the key; in the spec a key is any digest with any
map). The contexts' lengths are checked by the API (`AccOp`). -/
def HitWfN : Prop :=
  (∀ reqs reds, (∀ pk ∈ (A.choose reqs reds).2.1.keys, pk.digest.length = digestBytes) ∧
    (A.choose reqs reds).2.2.2.length = cdBytes) ∧
  ∀ reqs reds g s S' req ci cr cd, A.out reqs reds g s = .redeem S' req ci cr cd →
    (∀ pk ∈ S'.keys, pk.digest.length = digestBytes) ∧ cd.length = cdBytes ∧
      ∀ reqs' reds', S'.keys.map (·.digest) = (A.choose reqs' reds').2.1.keys.map (·.digest) →
        S'.keys = (A.choose reqs' reds').2.1.keys

/-- A logged unbound issuance statement is the issuance of an honest token. -/
lemma xN_inl {p : Pub U} {l : Log} {x : IssueInstance} (h : xN A p l = some (.inl x)) :
    ∃ j, x = ⟨p.1 j, A.ci j⟩ := by
  unfold xN at h
  split_ifs at h with h1 h2
  · cases h
    exact ⟨_, rfl⟩
  · cases hf : findIssuer (A.set l) (p.1 (A.tok l)) (A.sig l) with
    | none => rw [hf] at h; cases h
    | some i => rw [hf] at h; cases h

/-- A logged unbound redemption statement is under the Anchor Set, context and digest the
adversary chose. -/
lemma xN_inr {p : Pub U} {l : Log} {x : RedeemInstance} (h : xN A p l = some (.inr x)) :
    x = ⟨(A.set l).keys, p.2 (A.tok l) (A.crC l), A.ci (A.tok l), List.ofFn (A.crC l), A.cd l⟩ := by
  unfold xN at h
  split_ifs at h with h1 h2
  · cases h
  · cases hf : findIssuer (A.set l) (p.1 (A.tok l)) (A.sig l) with
    | none => rw [hf] at h; cases h
    | some i => rw [hf] at h; cases h; rfl

variable {CI CR : Type} (simI : IssueInstance → CI → Bytes) (progI : IssueInstance → CI → S → S)
  (simR : RedeemInstance → CR → Bytes) (progR : RedeemInstance → CR → S → S)
  (verI : IssueInstance → Bytes → S → Bool) (verR : RedeemInstance → Bytes → S → Bool)

/-- **In the simulated game, an accepted operation that is fresh is `FreshOkN`.** -/
lemma freshOkN_of_sim (hw : HitWfN A) (ω : SecN U) (cs : ℕ → CI × CR) (n : ℕ)
    (g : Fin (U + M) → G) (s : S)
    (hacc : AccOp verI verR (opN A (simPre (fun ω => SmP A simI simR (pubOf A ω))
      (fun ω => pgP A progI progR (pubOf A ω)) ω cs n).1 g s) s)
    (hfr : FreshOpN (simPre (fun ω => SmP A simI simR (pubOf A ω))
      (fun ω => pgP A progI progR (pubOf A ω)) ω cs n).1
      (opN A (simPre (fun ω => SmP A simI simR (pubOf A ω))
        (fun ω => pgP A progI progR (pubOf A ω)) ω cs n).1 g s)) :
    FreshOkN (simPre (fun ω => SmP A simI simR (pubOf A ω))
      (fun ω => pgP A progI progR (pubOf A ω)) ω cs n).1
      (opN A (simPre (fun ω => SmP A simI simR (pubOf A ω))
        (fun ω => pgP A progI progR (pubOf A ω)) ω cs n).1 g s) := by
  set l := (simPre (fun ω => SmP A simI simR (pubOf A ω))
    (fun ω => pgP A progI progR (pubOf A ω)) ω cs n).1 with hl
  have hent : ∀ (y : UI) (π : Bytes), some (y, π) ∈ l →
      ∃ l', xN A (pubOf A ω) l' = some y := by
    intro y π hy
    obtain ⟨j, -, he⟩ := simPre_entry _ _ ω cs n _ hy
    exact ⟨_, VoleMole.Theft.Moussaka.pairO_fst he.symm⟩
  cases hop : opN A l g s with
  | issue req ci =>
    rw [hop] at hacc hfr
    obtain ⟨hlen, hc, -⟩ := hacc
    refine ⟨⟨by simp [toBI, stOfI, hlen, issueProofBytes], hc⟩,
      fun x π hx => ⟨?_, hfr x π hx⟩⟩
    obtain ⟨l', hx'⟩ := hent _ _ hx
    obtain ⟨j, rfl⟩ := xN_inl A hx'
    exact ⟨length_ucom _ _ _, List.length_ofFn⟩
  | redeem S' req ci cr cd =>
    rw [hop] at hacc hfr
    obtain ⟨hlen, hc1, hc2, -⟩ := hacc
    obtain ⟨hd, hc3, hk⟩ := hw.2 _ _ g s S' req ci cr cd hop
    refine ⟨⟨hd, S'.valid.2.1, by simp [toBound, stOfR, hlen, redeemProofBytes], hc1, hc2, hc3⟩,
      fun x π hx => ?_⟩
    obtain ⟨l', hx'⟩ := hent _ _ hx
    have ex := xN_inr A hx'
    refine ⟨?_, fun he => ?_⟩
    · rw [ex]
      exact ⟨(hw.1 _ _).1, (A.set l').valid.2.1, length_derive _ _, List.length_ofFn,
        List.length_ofFn, (hw.1 _ _).2⟩
    · rw [ex] at he
      simp only [hashedRU, hashedR, toBound, stOfR, Prod.mk.injEq] at he
      obtain ⟨e1, e2, e3, e4, e5⟩ := he
      refine hfr x π hx ?_
      rw [ex]
      simp only [stOfR, hk _ _ e1, e2, e3, e4, e5]
      rfl

variable (ext : ExtN U M G S) [Nonempty CI] [Nonempty CR] [Fintype CI] [Fintype CR] [Fintype G]
  [Fintype S] [Nonempty G]

/-- **`sim_se_leN` for `FreshOkN`**, for `HitWfN` adversaries. -/
theorem sim_se_leN_ok (hw : HitWfN A) {AdmE : ((Fin (U + M) → G) → S → UOp) → Prop} {εSE : ℝ}
    (hse : WeakSEN (U + M) (simU simI simR) (progU progI progR) (AccOp verI verR) FreshOkN RelOp
      ext AdmE εSE)
    (hAE : ∀ l, AdmE (opN A l)) :
    pr (TapeN U M CI CR G S) (nmSimN A simI progI simR progR (seEvN A verI verR ext)) ≤ εSE := by
  have h := simGN_le_of_weakSEN (Ω := SecN U) (ρ := Coins proveSeedBytes) hse
    (fun ω l => xN A (pubOf A ω) l) (fun _ l => opN A l) fun _ l => hAE l
  refine (Privacy.pr_mono fun z hz => ?_).trans h
  exact ⟨hz.1, freshOkN_of_sim A simI progI simR progR verI verR hw _ _ _ _ _ hz.1 hz.2.1,
    hz.2.2⟩

end Fresh

/-! ## `ε_hit` bounded -/

section Hit

open VoleMole.Theft.Hit

variable {R : Type} [CipherRow R] {L M' : ℕ}

/-- The two unbound simulations as one, on the sum of the instance types. -/
noncomputable abbrev DU : UI → SimCoins pI × SimCoins pR → SD :=
  sumD (fun i c => (Privacy.MoussakaUnbound.stI i, simulate pI c))
    (fun i c => (Privacy.MoussakaUnbound.stR i, simulate pR c))

/-- The unbound issuance simulator's programming. -/
lemma simProgIU : SimProg (R := R) (p := Privacy.Moussaka.pI) (L := L) (M := M')
    (leanProgIUX hbX) (fun i c => (Privacy.MoussakaUnbound.stI i, simulate pI c)) :=
  simProg_progRO (p := pI) Privacy.MoussakaUnbound.stI fun _ => rfl

/-- The unbound redemption simulator's programming. -/
lemma simProgRU : SimProg (R := R) (p := Privacy.Moussaka.pI) (L := L) (M := M')
    (leanProgRUX hbX) (fun i c => (Privacy.MoussakaUnbound.stR i, simulate pR c)) :=
  simProg_progRO (p := pR) Privacy.MoussakaUnbound.stR fun _ => rfl

lemma simProgU : SimProg (R := R) (L := L) (M := M')
    (progU (leanProgIUX hbX) (leanProgRUX hbX)) DU :=
  simProgIU.sum simProgRU

/-- **A programmed point of the verifier is a hit of the forgery.** -/
lemma hitG_of_hitOpUX (op : UOp) (t' t : ShT R Privacy.Moussaka.pI L M')
    (h : HitOpUX (Hb := hbX) op t' t) : HitG (fdU op) t' t := by
  cases op with
  | issue req ci => exact hitG_of_hitPt (p := pI) _ _ t' t h
  | redeem S' req ci cr cd => exact hitG_of_hitPt (p := pR) _ _ t' t h

/-- **A fresh forgery's `H₂⁰` input is not a logged simulated statement's.** -/
lemma freshN_ne (l : Log) (op : UOp) (xi : UI) (c : SimCoins pI × SimCoins pR)
    (hfr : FreshOkN l op) (hm : pairO (some xi) (simU (leanSim pI) (leanSim pR) xi c) ∈ l) :
    muIn (fdU op).1 ≠ muIn (DU xi c).1 := by
  rcases xi with i | i
  · simp only [sumD_inl]
    intro hmu
    cases op with
    | issue req ci =>
      obtain ⟨hw, hne⟩ := hfr.2 i _ hm
      exact hne (muIn_stIU_inj hfr.1 hw hmu)
    | redeem S' req ci cr cd => exact muIn_stIU_ne_stRU _ _ hmu.symm
  · simp only [sumD_inr]
    intro hmu
    cases op with
    | issue req ci => exact muIn_stIU_ne_stRU _ _ hmu
    | redeem S' req ci cr cd =>
      obtain ⟨hw, hne⟩ := hfr.2 i _ hm
      exact hne (muIn_stRU_inj hfr.1 hw hmu)

variable [Fintype R] [Nonempty R]

/-- **The programming term for `U + M` simulated unbound proofs** (`progMovesN_chain`), for
`FreshOkN`:

    ε_moves ≤ N·((q₂₂+N+1)·2⁻⁴⁴⁸ + (q₂₁+N+1)·2⁻¹⁰⁸⁸ + (q_μ+N+1)·2⁻²⁵⁶),   N = U + M. -/
theorem progMovesN_hitU (hL : LminU ≤ L) (qMu q21 q22 : ℕ) :
    ProgMovesN (U + M) (simU (leanSim pI) (leanSim pR))
      (progU (leanProgIUX hbX) (leanProgRUX hbX)) (AccOp (verILUX hbX) (verRLUX hbX)) FreshOkN
      (AdmHitN (R := R) (p := Privacy.Moussaka.pI) (L := L) (M := M') (N := U + M) (G := Tab3)
        qMu q21 q22)
      ((U + M : ℕ) * epsHitN (U + M) qMu q21 q22) :=
  progMovesN_chain simProgU fdU (fun _ _ h => fdU_fOk hL h.wf)
    (fun o t' t h2 ha hn => hitG_of_hitOpUX o t' t (accOp_movesUX hbX o t' t h2 ha hn))
    (fun l op xi c hfr hm _ => freshN_ne l op xi c hfr hm) qMu q21 q22

variable [ZKRow R] {a3 a5 aE x3 x5 xE : ℕ}

/-- **Unbound non-malleability and no squatting for `U` tokens and `M` redemptions with the
other hashes random tables and `ε_hit` bounded.** As `nmUN_leanX_plain` with the concrete extra
table `XTab L M'` (`hbX`, `L ≥ 9749`) and the programming term bounded by `progMovesN_hitU`: for a
`HitWfN` adversary whose last stage reads `(a₃, a₅, a_E)` and the chain tables with
`(q_μ, q₂₁, q₂₂)` queries (`AdmHitN`, implied by its class `Adm`), and an extractor `extOfN e`
that reads `(x₃, x₅, x_E)`, with `N = U + M`,

    Pr[BadN] ≤ U·εz(pI; q) + M·εz(pR; q) + Σ_i δ_i + ε_plain
      + N·((q₂₂+N+1)·2⁻⁴⁴⁸ + (q₂₁+N+1)·2⁻¹⁰⁸⁸ + (q_μ+N+1)·2⁻²⁵⁶)
      + Σ_h (ε_prf + (M+1)·2⁻¹⁹² + Adv^bind(B₁ h) + Adv^spr-k(B₂ h)),

`q = (a₃ + x₃, a₅ + x₅ + 312 + (N − 1)·624, a_E + x_E + N·4607)`. Plain extraction (`hplain`)
and the PRF bound (`hprf`) stay hypotheses. -/
theorem nmUN_leanX_hit
    (A : ThiefN U M Tab3 (ShX R Privacy.Moussaka.pI (XTab L M'))) (hw : HitWfN A)
    (hL : LminU ≤ L)
    {e : Log → UOp → (Fin (U + M) → Tab3) → (Tab5F × (Blk → R)) × XTab L M' → Bytes}
    {Adm Adm₀ : ((Fin (U + M) → Tab3) → ShX R Privacy.Moussaka.pI (XTab L M') → UOp) → Prop}
    {ε₀ εprf : ℝ} {qMu q21 q22 : ℕ}
    (hA : ∀ reqs reds, StageBudgetNX (A.out reqs reds) a3 a5 aE)
    (hX : ∀ l, StageBudgetNX (extOfN e l (opN A l)) x3 x5 xE)
    (hplain : PlainSEN (U + M) (AccOp (verILUX hbX) (verRLUX hbX)) FreshOpN RelOp e Adm₀ ε₀)
    (hAdm : ∀ reqs reds, Adm (A.out reqs reds)) (hAH : ∀ F, Adm F → AdmHitN qMu q21 q22 F)
    (hadm : ∀ F L, IsProgs (progU (leanProgIUX hbX) (leanProgRUX hbX)) (U + M) L → Adm F →
      Adm₀ (fun g s => F g (L s)))
    (pts : Fin (M + 1) → Coins ctxBytes) (hpts : Function.Injective pts)
    (hprf : ∀ h b, prf1Adv (A.ci h) (owkDN (keyBN A (leanSim pI) (leanProgIUX hbX) (leanSim pR)
      (leanProgRUX hbX) (extOfN e) h) pts b) ≤ εprf) :
    pr (TapeN U M (SimCoins pI) (SimCoins pR) Tab3 (ShX R Privacy.Moussaka.pI (XTab L M')))
        (nmRealNE A (leanPIUX hbX) (leanPRUX hbX)
          (BadN A (verILUX hbX) (verRLUX hbX) (extOfN e))) ≤
      U * ZKRow.εz R pI (a3 + x3) (a5 + x5 + 312 + (U + M - 1) * 624)
          (aE + xE + (U + M) * 4607) +
        M * ZKRow.εz R pR (a3 + x3) (a5 + x5 + 312 + (U + M - 1) * 624)
          (aE + xE + (U + M) * 4607) +
        ∑ i, pr (TapeN U M (SimCoins pI) (SimCoins pR) Tab3 (ShX R Privacy.Moussaka.pI (XTab L M')))
          (deltaNU A (leanPIUX hbX) (leanPRUX hbX) (leanSim pI) (leanProgIUX hbX) (leanSim pR)
            (leanProgRUX hbX) i) +
        (ε₀ + (U + M : ℕ) * epsHitN (U + M) qMu q21 q22) +
        ∑ h : Fin U, (εprf + (M + 1) / 2 ^ 192 +
          bindAdv (bindBN A (leanSim pI) (leanProgIUX hbX) (leanSim pR) (leanProgRUX hbX)
            (extOfN e) h) +
          sprAdvN (A.ci h) (sprBN A (leanSim pI) (leanProgIUX hbX) (leanSim pR)
            (leanProgRUX hbX) (extOfN e) h)) :=
  nmUN_leanX_of_se A e hbX_wf hA hX
    (sim_se_leN_ok A (leanSim pI) (leanProgIUX hbX) (leanSim pR) (leanProgRUX hbX) (verILUX hbX)
      (verRLUX hbX) (extOfN e) hw
      (weakSEN_of_plain (hplain.fresh_mono fun _ _ h => h.freshOpN)
        ((progMovesN_hitU hL qMu q21 q22).mono hAH) progU_sndX hadm) fun _ => hAdm _ _)
    pts hpts hprf

/-- **One token and one redemption** (`U = M = 1`): the programming term is
`2·((q₂₂+3)·2⁻⁴⁴⁸ + (q₂₁+3)·2⁻¹⁰⁸⁸ + (q_μ+3)·2⁻²⁵⁶)`, as in the one-token bound theorem
`noRedirect_leanX_hit`. -/
lemma two_epsHitN (qMu q21 q22 : ℕ) :
    ((1 + 1 : ℕ) : ℝ) * epsHitN (1 + 1) qMu q21 q22 = epsHit qMu q21 q22 := by
  have e : ∀ q : ℕ, q + (1 + 1) + 1 = q + 3 := fun q => by omega
  simp only [epsHitN, epsHit, e]
  generalize (1 / 2 ^ 448 : ℝ) = a
  generalize (1 / 2 ^ 1088 : ℝ) = b
  generalize (1 / 2 ^ 256 : ℝ) = c
  push_cast
  ring

/-- **Unbound non-malleability for one token and one redemption, with `ε_hit` bounded**
(`nmUN_leanX_hit` at `U = M = 1`): the programming term is
`2·((q_μ+3)·2⁻²⁵⁶ + (q₂₁+3)·2⁻¹⁰⁸⁸ + (q₂₂+3)·2⁻⁴⁴⁸)` (`two_epsHitN`), the term of the one-token
bound theorem `noRedirect_leanX_hit`. -/
theorem nmUN_leanX_hit_one
    (A : ThiefN 1 1 Tab3 (ShX R Privacy.Moussaka.pI (XTab L M'))) (hw : HitWfN A)
    (hL : LminU ≤ L)
    {e : Log → UOp → (Fin (1 + 1) → Tab3) → (Tab5F × (Blk → R)) × XTab L M' → Bytes}
    {Adm Adm₀ : ((Fin (1 + 1) → Tab3) → ShX R Privacy.Moussaka.pI (XTab L M') → UOp) → Prop}
    {ε₀ εprf : ℝ} {qMu q21 q22 : ℕ}
    (hA : ∀ reqs reds, StageBudgetNX (A.out reqs reds) a3 a5 aE)
    (hX : ∀ l, StageBudgetNX (extOfN e l (opN A l)) x3 x5 xE)
    (hplain : PlainSEN (1 + 1) (AccOp (verILUX hbX) (verRLUX hbX)) FreshOpN RelOp e Adm₀ ε₀)
    (hAdm : ∀ reqs reds, Adm (A.out reqs reds)) (hAH : ∀ F, Adm F → AdmHitN qMu q21 q22 F)
    (hadm : ∀ F L, IsProgs (progU (leanProgIUX hbX) (leanProgRUX hbX)) (1 + 1) L → Adm F →
      Adm₀ (fun g s => F g (L s)))
    (pts : Fin (1 + 1) → Coins ctxBytes) (hpts : Function.Injective pts)
    (hprf : ∀ h b, prf1Adv (A.ci h) (owkDN (keyBN A (leanSim pI) (leanProgIUX hbX) (leanSim pR)
      (leanProgRUX hbX) (extOfN e) h) pts b) ≤ εprf) :
    pr (TapeN 1 1 (SimCoins pI) (SimCoins pR) Tab3 (ShX R Privacy.Moussaka.pI (XTab L M')))
        (nmRealNE A (leanPIUX hbX) (leanPRUX hbX)
          (BadN A (verILUX hbX) (verRLUX hbX) (extOfN e))) ≤
      ZKRow.εz R pI (a3 + x3) (a5 + x5 + 936) (aE + xE + 9214) +
        ZKRow.εz R pR (a3 + x3) (a5 + x5 + 936) (aE + xE + 9214) +
        ∑ i, pr (TapeN 1 1 (SimCoins pI) (SimCoins pR) Tab3 (ShX R Privacy.Moussaka.pI (XTab L M')))
          (deltaNU A (leanPIUX hbX) (leanPRUX hbX) (leanSim pI) (leanProgIUX hbX) (leanSim pR)
            (leanProgRUX hbX) i) +
        (ε₀ + epsHit qMu q21 q22) +
        ∑ h : Fin 1, (εprf + (1 + 1) / 2 ^ 192 +
          bindAdv (bindBN A (leanSim pI) (leanProgIUX hbX) (leanSim pR) (leanProgRUX hbX)
            (extOfN e) h) +
          sprAdvN (A.ci h) (sprBN A (leanSim pI) (leanProgIUX hbX) (leanSim pR)
            (leanProgRUX hbX) (extOfN e) h)) := by
  have h := nmUN_leanX_hit A hw hL hA hX hplain hAdm hAH hadm pts hpts hprf
  have e1 : a5 + x5 + 312 + (1 + 1 - 1) * 624 = a5 + x5 + 936 := by omega
  have e2 : aE + xE + (1 + 1) * 4607 = aE + xE + 9214 := by omega
  rw [e1, e2, two_epsHitN] at h
  simpa only [Nat.cast_one, one_mul] using h

end Hit

end VoleMole.Theft.MoussakaUnbound
