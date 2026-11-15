import VoleMole.Theft.MoussakaManyHit

/-!
# Moussaka: the digest condition of `HitWf` as an explicit collision term

The redemption statement hashes the Anchors' digests, not their maps (`Hit.Mous.hashedR`), and in
the spec a key (`UOVKey`) is any digest with any map. So `HitWf`/`HitWfN` ask that a redemption
whose Anchor Set has the digests of a set the adversary chose for an honest redemption is under
that set. In C++ the digest is SHAKE256 of the compressed public key and the expanded map is
computed from it (`src/uov/public_key.hpp`). Here that hypothesis is replaced by the C++ shape of
the keys and an explicit collision term:

* **`KeyOk sha exp pk`**: the key is `⟨sha c, exp c⟩` for some compressed key `c` (`sha`: the
  digest function, SHAKE256 in C++; `exp`: the expansion, pqov's in C++; both arbitrary here).
* `collPair`: from two key lists with the same digests that differ, the compressed keys of the
  first pair of keys that differ; **`collPair_spec`**: for `KeyOk` keys they are a collision of
  `sha` (distinct, with the same digest).
* **`collAdv sha B`**: the probability that `B` outputs a collision of `sha`, for an explicit
  `B` (a computational assumption on SHAKE256, as `Adv^ow` is on Keccak-p[800]).
* **`HitLenN`**, **`KeysOkN`**: `HitWfN` without its digest clause (the lengths), and every key
  the adversary chooses or outputs is `KeyOk`.
* `freshOkN_or_coll`: in the simulated game an accepted fresh operation is `FreshOkN`, or it is a
  redemption whose Anchor Set has the digests of a logged one and other keys (`CollN`).
* **`collBN`**: the collision finder: the simulated game, then `collPair` of the output's set and
  the first such logged set (`collOfN`).
* **`sim_se_leN_coll`**, **`noRedirectN_leanX_hitC`**: `noRedirectN_leanX_hit` for adversaries
  with `HitLenN` and `KeysOkN`, with the term `collAdv sha (collBN …)` added:

      Pr[BadN] ≤ U·εz(pI; q) + M·εz(pR; q) + Σ_i δ_i + ε_plain
        + N·((q₂₂+N+1)·2⁻⁴⁴⁸ + (q₂₁+N+1)·2⁻¹⁰⁸⁸ + (q_μ+N+1)·2⁻²⁵⁶) + Adv^coll_sha(B)
        + Σ_h Adv^ow(inverter h).

The finder picks a compressed key for each key it outputs (`keyRep`, by choice): in C++ these are
the Anchor keys the adversary supplied, so the finder knows them.
-/

-- (The coin types are large products: their `Fintype` instances exceed the default size.)
set_option synthInstance.maxSize 1024

namespace VoleMole.Theft.Moussaka

open VoleMole.Privacy VoleMole.Privacy.Moussaka VoleMole.Spec VoleMole.Spec.Moussaka
  VoleMole.ZK.Sim VoleMole.Verifier VoleMole.Verifier.Bridge
open VoleMole.Theft.Hit.Mous (WfI WfR hashedR)

-- `Com` evaluates Keccak-p[800]; nothing below needs to unfold it.
attribute [local irreducible] com UOVKey.eval

/-! ## Keys with digests of compressed keys, and collisions -/

section Keys

variable (sha : Bytes → Bytes) (exp : Bytes → ℕ → Arith.GF256)

/-- **A key in the C++ shape**: digest and map of one compressed key `c` (`sha`: SHAKE256,
`exp`: the expansion). -/
def KeyOk (pk : UOVKey) : Prop := ∃ c, pk = ⟨sha c, exp c⟩

open Classical in
/-- A compressed key of a key (by choice; `[]` if there is none). -/
noncomputable def keyRep (pk : UOVKey) : Bytes :=
  if h : KeyOk sha exp pk then Classical.choose h else []

lemma keyRep_spec {pk : UOVKey} (h : KeyOk sha exp pk) :
    pk = ⟨sha (keyRep sha exp pk), exp (keyRep sha exp pk)⟩ := by
  unfold keyRep
  rw [dite_eq_left_of_eq_true (eq_true h)]
  exact Classical.choose_spec h

open Classical in
/-- **The compressed keys of the first pair of keys that differ.** -/
noncomputable def collPair : List UOVKey → List UOVKey → Bytes × Bytes
  | k :: ks, k' :: ks' => if k = k' then collPair ks ks' else (keyRep sha exp k, keyRep sha exp k')
  | _, _ => ([], [])

/-- **A collision of the digest function**: distinct inputs with the same digest. -/
def CollWin (p : Bytes × Bytes) : Prop := p.1 ≠ p.2 ∧ sha p.1 = sha p.2

/-- **Two lists of `KeyOk` keys with the same digests that differ give a collision.** -/
theorem collPair_spec : ∀ {ks ks' : List UOVKey}, (∀ k ∈ ks, KeyOk sha exp k) →
    (∀ k ∈ ks', KeyOk sha exp k) → ks.map (·.digest) = ks'.map (·.digest) → ks ≠ ks' →
    CollWin sha (collPair sha exp ks ks')
  | [], [], _, _, _, hne => absurd rfl hne
  | [], _ :: _, _, _, hd, _ => by simp at hd
  | _ :: _, [], _, _, hd, _ => by simp at hd
  | k :: ks, k' :: ks', hk, hk', hd, hne => by
    simp only [List.map_cons, List.cons.injEq] at hd
    unfold collPair
    by_cases e : k = k'
    · rw [ite_eq_left_of_eq_true _ _ (eq_true e)]
      refine collPair_spec (fun a ha => hk a (by simp [ha])) (fun a ha => hk' a (by simp [ha]))
        hd.2 fun h => hne (by rw [e, h])
    · rw [ite_eq_right_of_eq_false _ _ (eq_false e)]
      have h1 := keyRep_spec sha exp (hk k (by simp))
      have h2 := keyRep_spec sha exp (hk' k' (by simp))
      refine ⟨fun h => e ?_, ?_⟩
      · rw [h1, h2]
        simp only at h
        rw [h]
      · have hd1 := hd.1
        rw [h1, h2] at hd1
        exact hd1

/-- **The collision advantage** of an explicit finder `B` with coins `β`. -/
noncomputable def collAdv {β : Type} [Fintype β] (B : β → Bytes × Bytes) : ℝ :=
  pr β fun b => CollWin sha (B b)

end Keys

/-! ## In the game for `U` tokens and `M` redemptions -/

section Game

variable {U M : ℕ} {G S : Type} (A : ThiefN U M G S) (sha : Bytes → Bytes)
  (exp : Bytes → ℕ → Arith.GF256)

/-- **The lengths the C++ types fix** (`HitWfN` without its digest clause). -/
def HitLenN : Prop :=
  (∀ reqs reds, (∀ pk ∈ (A.choose reqs reds).2.1.keys, pk.digest.length = digestBytes) ∧
    (A.choose reqs reds).2.2.length = cdBytes) ∧
  ∀ reqs reds g s S' req ci cr cd, A.out reqs reds g s = .redeem S' req ci cr cd →
    (∀ pk ∈ S'.keys, pk.digest.length = digestBytes) ∧ ci.length = ctxBytes ∧
      cr.length = ctxBytes ∧ cd.length = cdBytes

/-- **The adversary's keys are in the C++ shape**: every key of an Anchor Set it chooses for an
honest redemption or outputs is `KeyOk`. -/
def KeysOkN : Prop :=
  (∀ reqs reds, ∀ pk ∈ (A.choose reqs reds).2.1.keys, KeyOk sha exp pk) ∧
  ∀ reqs reds g s S' req ci cr cd, A.out reqs reds g s = .redeem S' req ci cr cd →
    ∀ pk ∈ S'.keys, KeyOk sha exp pk

/-- **A digest collision in the operation**: a redemption whose Anchor Set has the digests of a
logged redemption's set and other keys. -/
def CollN (l : Log) : MOp → Prop
  | .issue _ _ => False
  | .redeem S' _ _ _ _ => ∃ x π, some (Sum.inr x, π) ∈ l ∧
      x.anchors.map (·.digest) = S'.keys.map (·.digest) ∧ x.anchors ≠ S'.keys

open Classical in
/-- **The collision of an operation**: `collPair` of its Anchor Set and a logged set with the same
digests and other keys. -/
noncomputable def collOfN (l : Log) : MOp → Bytes × Bytes
  | .issue _ _ => ([], [])
  | .redeem S' _ _ _ _ =>
      if h : ∃ x : RedeemInstance, (∃ π, some (Sum.inr x, π) ∈ l) ∧
          x.anchors.map (·.digest) = S'.keys.map (·.digest) ∧ x.anchors ≠ S'.keys then
        collPair sha exp S'.keys (Classical.choose h).anchors
      else ([], [])

variable {CI CR : Type} (simI : IssueInstance → CI → Bytes) (progI : IssueInstance → CI → S → S)
  (simR : RedeemInstance → CR → Bytes) (progR : RedeemInstance → CR → S → S)
  (verI : IssueInstance → Bytes → S → Bool) (verR : RedeemInstance → Bytes → S → Bool)

/-- Every logged redemption statement of the simulated game is under a set the adversary chose. -/
lemma logged_set (ω : SecN U) (cs : ℕ → CI × CR) (n : ℕ) {x : RedeemInstance} {π : Bytes}
    (hx : some (Sum.inr x, π) ∈ (simPre (fun ω => SmP A simI simR (pubOf A ω))
      (fun ω => pgP A progI progR (pubOf A ω)) ω cs n).1) :
    ∃ l', x = ⟨(A.set l').keys, (pubOf A ω).1 (A.tok l'), A.ci (A.tok l'), A.cr (A.tok l'),
      A.cd l'⟩ := by
  obtain ⟨j, -, he⟩ := simPre_entry _ _ ω cs n _ hx
  exact ⟨_, xN_inr A (pairO_fst he.symm)⟩

/-- **The operation's digest collision is a collision of `sha`**, for `KeyOk` keys. -/
lemma collOfN_spec (hk : KeysOkN A sha exp) (ω : SecN U) (cs : ℕ → CI × CR) (n : ℕ)
    (g : Fin (U + M) → G) (s : S)
    (hc : CollN (simPre (fun ω => SmP A simI simR (pubOf A ω))
      (fun ω => pgP A progI progR (pubOf A ω)) ω cs n).1
      (opN A (simPre (fun ω => SmP A simI simR (pubOf A ω))
        (fun ω => pgP A progI progR (pubOf A ω)) ω cs n).1 g s)) :
    CollWin sha (collOfN sha exp (simPre (fun ω => SmP A simI simR (pubOf A ω))
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
    refine collPair_spec sha exp (hk.2 _ _ g s S' req ci cr cd hop) ?_ hd'.symm
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
  have hent : ∀ (y : MI) (π : Bytes), some (y, π) ∈ l →
      ∃ l', xN A (pubOf A ω) l' = some y := by
    intro y π hy
    obtain ⟨j, -, he⟩ := simPre_entry _ _ ω cs n _ hy
    exact ⟨_, pairO_fst he.symm⟩
  cases hop : opN A l g s with
  | issue req ci =>
    rw [hop] at hacc hfr
    obtain ⟨hlen, hc, -⟩ := hacc
    refine Or.inl ⟨⟨by simp [stOfI, hlen, issueRequestBytes], hc⟩, fun x π hx => ⟨?_, hfr x π hx⟩⟩
    obtain ⟨l', hx'⟩ := hent _ _ hx
    obtain ⟨j, rfl⟩ := xN_inl A hx'
    exact ⟨length_com _ _ _ _, List.length_ofFn⟩
  | redeem S' req ci cr cd =>
    rw [hop] at hacc hfr
    obtain ⟨hlen, -⟩ := hacc
    obtain ⟨hd, hc1, hc2, hc3⟩ := hw.2 _ _ g s S' req ci cr cd hop
    by_cases hcoll : ∃ x π, some (Sum.inr x, π) ∈ l ∧
        x.anchors.map (·.digest) = S'.keys.map (·.digest) ∧ x.anchors ≠ S'.keys
    · exact Or.inr hcoll
    refine Or.inl ⟨⟨hd, S'.valid.2.1, by simp [stOfR, hlen, redeemRequestBytes], hc1, hc2, hc3⟩,
      fun x π hx => ?_⟩
    obtain ⟨l', hx'⟩ := hent _ _ hx
    have ex := xN_inr A hx'
    refine ⟨?_, fun he => ?_⟩
    · rw [ex]
      exact ⟨(hw.1 _ _).1, (A.set l').valid.2.1, List.length_ofFn, List.length_ofFn,
        List.length_ofFn, (hw.1 _ _).2⟩
    · simp only [hashedR, stOfR, Prod.mk.injEq] at he
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
    {AdmE : ((Fin (U + M) → G) → S → MOp) → Prop} {εSE : ℝ}
    (hse : WeakSEN (U + M) (simM simI simR) (progM progI progR) (AccOp verI verR) FreshOkN RelOp
      ext AdmE εSE)
    (hAE : ∀ l, AdmE (opN A l)) :
    pr (TapeN U M CI CR G S) (nmSimN A simI progI simR progR (seEvN A verI verR ext)) ≤
      εSE + collAdv sha (collBN A sha exp simI progI simR progR) := by
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

/-- **Redemption non-malleability for `U` tokens and `M` redemptions with `ε_hit` bounded and the
digest condition as a collision term.** As `noRedirectN_leanX_hit`, for adversaries with the
lengths of the C++ types (`HitLenN`) whose Anchor keys are digests and expansions of compressed
keys (`KeysOkN sha exp`), in place of `HitWfN`'s digest clause:

    Pr[BadN] ≤ U·εz(pI; q) + M·εz(pR; q) + Σ_i δ_i + ε_plain
      + N·((q₂₂+N+1)·2⁻⁴⁴⁸ + (q₂₁+N+1)·2⁻¹⁰⁸⁸ + (q_μ+N+1)·2⁻²⁵⁶) + Adv^coll_sha(B)
      + Σ_h Adv^ow(inverter h),

`B = collBN …` the explicit collision finder (the simulated game). -/
theorem noRedirectN_leanX_hitC (sha : Bytes → Bytes) (exp : Bytes → ℕ → Arith.GF256)
    (A : ThiefN U M Tab3 (ShX R pI (XTab L M'))) (hw : HitLenN A) (hk : KeysOkN A sha exp)
    (hL : Hit.Mous.Lmin ≤ L)
    {e : Log → MOp → (Fin (U + M) → Tab3) → (Tab5F × (Blk → R)) × XTab L M' → Bytes}
    {Adm Adm₀ : ((Fin (U + M) → Tab3) → ShX R pI (XTab L M') → MOp) → Prop}
    {ε₀ : ℝ} {qMu q21 q22 : ℕ}
    (hA : ∀ reqs reds, StageBudgetNX (A.out reqs reds) a3 a5 aE)
    (hX : ∀ l, StageBudgetNX (extOfN e l (opN A l)) x3 x5 xE)
    (hplain : PlainSEN (U + M) (AccOp (verILX hbX) (verRLX hbX)) FreshOpN RelOp e Adm₀ ε₀)
    (hAdm : ∀ reqs reds, Adm (A.out reqs reds)) (hAH : ∀ F, Adm F → AdmHitN qMu q21 q22 F)
    (hadm : ∀ F L, IsProgs (progM (leanProgIX hbX) (leanProgRX hbX)) (U + M) L → Adm F →
      Adm₀ (fun g s => F g (L s))) :
    pr (TapeN U M (SimCoins pI) (SimCoins pR) Tab3 (ShX R pI (XTab L M')))
        (nmRealN A (leanPIX hbX) (leanPRX hbX) (verILX hbX) (verRLX hbX) (extOfN e)) ≤
      U * ZKRow.εz R pI (a3 + x3) (a5 + x5 + 312 + (U + M - 1) * 624)
          (aE + xE + (U + M) * 4607) +
        M * ZKRow.εz R pR (a3 + x3) (a5 + x5 + 312 + (U + M - 1) * 624)
          (aE + xE + (U + M) * 4607) +
        ∑ i, pr (TapeN U M (SimCoins pI) (SimCoins pR) Tab3 (ShX R pI (XTab L M')))
          (deltaNM A (leanPIX hbX) (leanPRX hbX) (leanSim pI) (leanProgIX hbX) (leanSim pR)
            (leanProgRX hbX) i) +
        ((ε₀ + (U + M : ℕ) * epsHitN (U + M) qMu q21 q22) +
          collAdv sha (collBN A sha exp (leanSim pI) (leanProgIX hbX) (leanSim pR)
            (leanProgRX hbX))) +
        ∑ h : Fin U, owAdv (A.ci h) (A.cr h)
          (inverterN A (leanSim pI) (leanProgIX hbX) (leanSim pR) (leanProgRX hbX) (extOfN e)
            h) :=
  noRedirectN_leanX_of_se A e hbX_wf hA hX
    (sim_se_leN_coll A sha exp (leanSim pI) (leanProgIX hbX) (leanSim pR) (leanProgRX hbX)
      (verILX hbX) (verRLX hbX) (extOfN e) hw hk
      (weakSEN_of_plain (hplain.fresh_mono fun _ _ h => h.freshOpN)
        ((progMovesN_hit hL qMu q21 q22).mono hAH) progM_sndX hadm) fun _ => hAdm _ _)

end Thm

end VoleMole.Theft.Moussaka
