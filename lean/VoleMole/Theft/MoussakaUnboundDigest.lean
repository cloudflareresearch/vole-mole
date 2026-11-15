import VoleMole.Theft.MoussakaDigest
import VoleMole.Theft.MoussakaUnboundHit

/-!
# Unbound Moussaka: the digest condition of `HitWfN` as an explicit collision term

As `Theft/MoussakaDigest.lean` for bound Moussaka (the unbound redemption hashes the Anchors'
digests as the bound one does): `HitLenN` (`HitWfN` without its digest clause), `KeysOkN` (the
adversary's keys are digests and expansions of compressed keys, `Moussaka.KeyOk`), the collision
finder `collBN` (the simulated game, then `Moussaka.collPair`), and **`nmUN_leanX_hitC`**:
`nmUN_leanX_hit` with the term `Adv^coll_sha(collBN …)` in place of the digest clause.
-/

-- (The coin types are large products: their `Fintype` instances exceed the default size.)
set_option synthInstance.maxSize 1024

namespace VoleMole.Theft.MoussakaUnbound

open VoleMole.Privacy VoleMole.Privacy.MoussakaUnbound VoleMole.Spec VoleMole.Spec.MoussakaUnbound
  VoleMole.ZK.Sim VoleMole.Verifier VoleMole.Verifier.Bridge
open VoleMole.Spec.Moussaka (AnchorSet Error ctxBytes proveSeedBytes rBytes nfBytes cdBytes)
open VoleMole.Privacy.Moussaka (ShM leanSim)
open VoleMole.Theft.Hit.Mous (WfI WfR hashedR)
open VoleMole.Theft.Moussaka (KeyOk)

-- `UCom` and `Derive` evaluate Keccak-p[800]; nothing below needs to unfold them.
attribute [local irreducible] ucom derive UOVKey.eval

/-! ## In the game for `U` tokens and `M` redemptions -/

section Game

variable {U M : ℕ} {G S : Type} (A : ThiefN U M G S) (sha : Bytes → Bytes)
  (exp : Bytes → ℕ → Arith.GF256)

/-- **The lengths the C++ types fix** (`HitWfN` without its digest clause). -/
def HitLenN : Prop :=
  (∀ reqs reds, (∀ pk ∈ (A.choose reqs reds).2.1.keys, pk.digest.length = digestBytes) ∧
    (A.choose reqs reds).2.2.2.length = cdBytes) ∧
  ∀ reqs reds g s S' req ci cr cd, A.out reqs reds g s = .redeem S' req ci cr cd →
    (∀ pk ∈ S'.keys, pk.digest.length = digestBytes) ∧ cd.length = cdBytes

/-- **The adversary's keys are in the C++ shape**: every key of an Anchor Set it chooses for an
honest redemption or outputs is `KeyOk`. -/
def KeysOkN : Prop :=
  (∀ reqs reds, ∀ pk ∈ (A.choose reqs reds).2.1.keys, KeyOk sha exp pk) ∧
  ∀ reqs reds g s S' req ci cr cd, A.out reqs reds g s = .redeem S' req ci cr cd →
    ∀ pk ∈ S'.keys, KeyOk sha exp pk

/-- **A digest collision in the operation**: a redemption whose Anchor Set has the digests of a
logged redemption's set and other keys. -/
def CollN (l : Log) : UOp → Prop
  | .issue _ _ => False
  | .redeem S' _ _ _ _ => ∃ x π, some (Sum.inr x, π) ∈ l ∧
      x.anchors.map (·.digest) = S'.keys.map (·.digest) ∧ x.anchors ≠ S'.keys

open Classical in
/-- **The collision of an operation**: `collPair` of its Anchor Set and a logged set with the same
digests and other keys. -/
noncomputable def collOfN (l : Log) : UOp → Bytes × Bytes
  | .issue _ _ => ([], [])
  | .redeem S' _ _ _ _ =>
      if h : ∃ x : RedeemInstance, (∃ π, some (Sum.inr x, π) ∈ l) ∧
          x.anchors.map (·.digest) = S'.keys.map (·.digest) ∧ x.anchors ≠ S'.keys then
        Moussaka.collPair sha exp S'.keys (Classical.choose h).anchors
      else ([], [])

variable {CI CR : Type} (simI : IssueInstance → CI → Bytes) (progI : IssueInstance → CI → S → S)
  (simR : RedeemInstance → CR → Bytes) (progR : RedeemInstance → CR → S → S)
  (verI : IssueInstance → Bytes → S → Bool) (verR : RedeemInstance → Bytes → S → Bool)

/-- Every logged redemption statement of the simulated game is under a set the adversary chose. -/
lemma logged_set (ω : SecN U) (cs : ℕ → CI × CR) (n : ℕ) {x : RedeemInstance} {π : Bytes}
    (hx : some (Sum.inr x, π) ∈ (simPre (fun ω => SmP A simI simR (pubOf A ω))
      (fun ω => pgP A progI progR (pubOf A ω)) ω cs n).1) :
    ∃ l', x = ⟨(A.set l').keys, (pubOf A ω).2 (A.tok l') (A.crC l'), A.ci (A.tok l'),
      List.ofFn (A.crC l'), A.cd l'⟩ := by
  obtain ⟨j, -, he⟩ := simPre_entry _ _ ω cs n _ hx
  exact ⟨_, xN_inr A (Moussaka.pairO_fst he.symm)⟩

/-- **The operation's digest collision is a collision of `sha`**, for `KeyOk` keys. -/
lemma collOfN_spec (hk : KeysOkN A sha exp) (ω : SecN U) (cs : ℕ → CI × CR) (n : ℕ)
    (g : Fin (U + M) → G) (s : S)
    (hc : CollN (simPre (fun ω => SmP A simI simR (pubOf A ω))
      (fun ω => pgP A progI progR (pubOf A ω)) ω cs n).1
      (opN A (simPre (fun ω => SmP A simI simR (pubOf A ω))
        (fun ω => pgP A progI progR (pubOf A ω)) ω cs n).1 g s)) :
    Moussaka.CollWin sha (collOfN sha exp (simPre (fun ω => SmP A simI simR (pubOf A ω))
      (fun ω => pgP A progI progR (pubOf A ω)) ω cs n).1
      (opN A (simPre (fun ω => SmP A simI simR (pubOf A ω))
        (fun ω => pgP A progI progR (pubOf A ω)) ω cs n).1 g s)) := by
  set l := (simPre (fun ω => SmP A simI simR (pubOf A ω))
    (fun ω => pgP A progI progR (pubOf A ω)) ω cs n).1 with hl
  cases hop : opN A l g s with
  | issue req ci => rw [hop] at hc; exact hc.elim
  | redeem S' req ci cr cd =>
    rw [hop] at hc
    obtain ⟨x, π, hx, hd, hne⟩ := hc
    have hex : ∃ x : RedeemInstance, (∃ π, some (Sum.inr x, π) ∈ l) ∧
        x.anchors.map (·.digest) = S'.keys.map (·.digest) ∧ x.anchors ≠ S'.keys :=
      ⟨x, ⟨π, hx⟩, hd, hne⟩
    simp only [collOfN, dite_eq_left_of_eq_true (eq_true hex)]
    obtain ⟨⟨π', hx'⟩, hd', hne'⟩ := Classical.choose_spec hex
    obtain ⟨l', ex⟩ := logged_set A simI progI simR progR ω cs n hx'
    refine Moussaka.collPair_spec sha exp (hk.2 _ _ g s S' req ci cr cd hop) ?_ hd'.symm
      (fun h => hne' h.symm)
    rw [ex]
    exact hk.1 _ _

/-- **In the simulated game, an accepted fresh operation is `FreshOkN` or a digest collision**,
for adversaries with the lengths of the C++ types (`freshOkN_of_sim` without the digest
clause). -/
lemma freshOkN_or_coll (hw : HitLenN A) (ω : SecN U) (cs : ℕ → CI × CR) (n : ℕ)
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
        (fun ω => pgP A progI progR (pubOf A ω)) ω cs n).1 g s) ∨
    CollN (simPre (fun ω => SmP A simI simR (pubOf A ω))
      (fun ω => pgP A progI progR (pubOf A ω)) ω cs n).1
      (opN A (simPre (fun ω => SmP A simI simR (pubOf A ω))
        (fun ω => pgP A progI progR (pubOf A ω)) ω cs n).1 g s) := by
  set l := (simPre (fun ω => SmP A simI simR (pubOf A ω))
    (fun ω => pgP A progI progR (pubOf A ω)) ω cs n).1 with hl
  have hent : ∀ (y : UI) (π : Bytes), some (y, π) ∈ l →
      ∃ l', xN A (pubOf A ω) l' = some y := by
    intro y π hy
    obtain ⟨j, -, he⟩ := simPre_entry _ _ ω cs n _ hy
    exact ⟨_, Moussaka.pairO_fst he.symm⟩
  cases hop : opN A l g s with
  | issue req ci =>
    rw [hop] at hacc hfr
    obtain ⟨hlen, hc, -⟩ := hacc
    refine Or.inl ⟨⟨by simp [toBI, stOfI, hlen, issueProofBytes], hc⟩,
      fun x π hx => ⟨?_, hfr x π hx⟩⟩
    obtain ⟨l', hx'⟩ := hent _ _ hx
    obtain ⟨j, rfl⟩ := xN_inl A hx'
    exact ⟨length_ucom _ _ _, List.length_ofFn⟩
  | redeem S' req ci cr cd =>
    rw [hop] at hacc hfr
    obtain ⟨hlen, hc1, hc2, -⟩ := hacc
    obtain ⟨hd, hc3⟩ := hw.2 _ _ g s S' req ci cr cd hop
    by_cases hcoll : ∃ x π, some (Sum.inr x, π) ∈ l ∧
        x.anchors.map (·.digest) = S'.keys.map (·.digest) ∧ x.anchors ≠ S'.keys
    · exact Or.inr hcoll
    refine Or.inl ⟨⟨hd, S'.valid.2.1, by simp [toBound, stOfR, hlen, redeemProofBytes], hc1, hc2,
      hc3⟩, fun x π hx => ?_⟩
    obtain ⟨l', hx'⟩ := hent _ _ hx
    have ex := xN_inr A hx'
    refine ⟨?_, fun he => ?_⟩
    · rw [ex]
      exact ⟨(hw.1 _ _).1, (A.set l').valid.2.1, length_derive _ _, List.length_ofFn,
        List.length_ofFn, (hw.1 _ _).2⟩
    · simp only [hashedRU, hashedR, toBound, stOfR, Prod.mk.injEq] at he
      obtain ⟨e1, e2, e3, e4, e5⟩ := he
      have hk : S'.keys = x.anchors := by
        by_contra hne
        exact hcoll ⟨x, π, hx, e1.symm, fun h => hne h.symm⟩
      refine hfr x π hx ?_
      cases x
      simp only [stOfR] at hk e2 e3 e4 e5 ⊢
      rw [hk, e2, e3, e4, e5]

variable (ext : ExtN U M G S) [Nonempty CI] [Nonempty CR] [Fintype CI] [Fintype CR] [Fintype G]
  [Fintype S] [Nonempty G]

/-- **The collision finder**: the simulated game, then the collision of its output
(`collOfN`). -/
noncomputable def collBN (z : TapeN U M CI CR G S) : Bytes × Bytes :=
  collOfN sha exp (simPre (fun ω => SmP A simI simR (pubOf A ω))
      (fun ω => pgP A progI progR (pubOf A ω)) z.1.1 (tapeC z.1.2) (U + M)).1
    (opN A (simPre (fun ω => SmP A simI simR (pubOf A ω))
      (fun ω => pgP A progI progR (pubOf A ω)) z.1.1 (tapeC z.1.2) (U + M)).1 (tapeG z.1.2)
      ((simPre (fun ω => SmP A simI simR (pubOf A ω))
        (fun ω => pgP A progI progR (pubOf A ω)) z.1.1 (tapeC z.1.2) (U + M)).2 z.2))

/-- **`sim_se_leN_ok` with the digest condition replaced by the collision term.** -/
theorem sim_se_leN_coll (hw : HitLenN A) (hk : KeysOkN A sha exp)
    {AdmE : ((Fin (U + M) → G) → S → UOp) → Prop} {εSE : ℝ}
    (hse : WeakSEN (U + M) (simU simI simR) (progU progI progR) (AccOp verI verR) FreshOkN RelOp
      ext AdmE εSE)
    (hAE : ∀ l, AdmE (opN A l)) :
    pr (TapeN U M CI CR G S) (nmSimN A simI progI simR progR (seEvN A verI verR ext)) ≤
      εSE + Moussaka.collAdv sha (collBN A sha exp simI progI simR progR) := by
  have h := simGN_le_of_weakSEN (Ω := SecN U) (ρ := Coins proveSeedBytes) hse
    (fun ω l => xN A (pubOf A ω) l) (fun _ l => opN A l) fun _ l => hAE l
  refine le_trans (Privacy.pr_mono fun z hz => ?_) ((Privacy.pr_or_le _ _).trans
    (add_le_add h le_rfl))
  rcases freshOkN_or_coll A simI progI simR progR verI verR hw _ _ _ _ _ hz.1 hz.2.1 with hf | hc
  · exact Or.inl ⟨hz.1, hf, hz.2.2⟩
  · exact Or.inr (collOfN_spec A sha exp simI progI simR progR hk _ _ _ _ _ hc)

end Game

/-! ## The theorem -/

section Thm

open VoleMole.Theft.Hit

variable {U M : ℕ} {R : Type} [CipherRow R] [Fintype R] [Nonempty R] [ZKRow R] {L M' : ℕ}
  {a3 a5 aE x3 x5 xE : ℕ}

/-- **Unbound non-malleability for `U` tokens and `M` redemptions with `ε_hit` bounded and the
digest condition as a collision term.** As `nmUN_leanX_hit`, for adversaries with the lengths of
the C++ types (`HitLenN`) whose Anchor keys are digests and expansions of compressed keys
(`KeysOkN sha exp`), in place of `HitWfN`'s digest clause, with the term
`Adv^coll_sha(collBN …)` added. -/
theorem nmUN_leanX_hitC (sha : Bytes → Bytes) (exp : Bytes → ℕ → Arith.GF256)
    (A : ThiefN U M Tab3 (ShX R Privacy.Moussaka.pI (XTab L M'))) (hw : HitLenN A)
    (hk : KeysOkN A sha exp) (hL : LminU ≤ L)
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
        ((ε₀ + (U + M : ℕ) * epsHitN (U + M) qMu q21 q22) +
          Moussaka.collAdv sha (collBN A sha exp (leanSim pI) (leanProgIUX hbX) (leanSim pR)
            (leanProgRUX hbX))) +
        ∑ h : Fin U, (εprf + (M + 1) / 2 ^ 192 +
          bindAdv (bindBN A (leanSim pI) (leanProgIUX hbX) (leanSim pR) (leanProgRUX hbX)
            (extOfN e) h) +
          sprAdvN (A.ci h) (sprBN A (leanSim pI) (leanProgIUX hbX) (leanSim pR)
            (leanProgRUX hbX) (extOfN e) h)) :=
  nmUN_leanX_of_se A e hbX_wf hA hX
    (sim_se_leN_coll A sha exp (leanSim pI) (leanProgIUX hbX) (leanSim pR) (leanProgRUX hbX)
      (verILUX hbX) (verRLUX hbX) (extOfN e) hw hk
      (weakSEN_of_plain (hplain.fresh_mono fun _ _ h => h.freshOpN)
        ((progMovesN_hitU hL qMu q21 q22).mono hAH) progU_sndX hadm) fun _ => hAdm _ _)
    pts hpts hprf

end Thm

end VoleMole.Theft.MoussakaUnbound
