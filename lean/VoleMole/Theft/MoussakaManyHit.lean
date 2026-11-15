import VoleMole.Theft.MoussakaManyReads
import VoleMole.Theft.MoussakaHit
import VoleMole.Theft.ManyTables
import VoleMole.Theft.HitMany

/-!
# Moussaka for `U` tokens and `M` redemptions, the other hashes random tables and `ε_hit` bounded

`noRedirectN_lean_plain` (`Theft/MoussakaManyReads.lean`) has SHAKE for the chain hashes and the
programmed-point terms `SlotEvN i` as hypotheses. Here the game is in the model of
`noRedirect_leanX_plain` (`Theft/Tables.lean`: `H₁`, `H₂⁰`, `H₂¹`, `H₂²`, `H₄`, `H_comb` read off
one more uniform shared table `x : X`), and for the tables `XTab L M'` the programmed-point terms
are bounded (`Theft/HitMany.lean`), as `Theft/RatatouilleManyHit.lean` does for Ratatouille.

* `atTN`: the adversary at a value of the extra table. `PN_atX`, `pgP_atX`, `badN_atX`: the real
  slot, the simulated slot's programming and the bad event on the tables `atX s x` are those of
  the game at `x`, with the base record `Hb x`.
* **`distPN_budgetXI`**, **`distPN_budgetXR`**: the hops' read budgets at every value of the extra
  table (`distN_budgetX`), with the budget of `noRedirectN_lean_reads`.
* **`noRedirectN_leanX_plain`**: the theorem with the extra table, `WeakSEN` replaced by plain
  extraction and the programming term (`ProgMovesN`), both for uniform `X`.
* **`FreshOkN`**: the freshness of the bound on `ε_hit`, as `Hit.Mous.FreshOk` for one token:
  the operation's statement is well-formed, and each logged statement of its relation is
  well-formed and differs from it in a hashed field (`hashedR`: the redemption statement hashes
  the Anchors' digests, not their maps).
* **`HitWfN`**: the adversaries of the bound, as `Hit.Mous.HitWf`: the lengths the C++ types fix
  (32-byte digests in every Anchor Set, 32-byte challenge digests, 16-byte contexts), and a
  redemption whose Anchor Set has the digests of a set the adversary chose for an honest
  redemption is under that set. For them an accepted operation that is fresh for the game
  (`FreshOpN`) is `FreshOkN` (`freshOkN_of_sim`, `sim_se_leN_ok`).
* **`noRedirectN_leanX_hit`**: with `XTab L M'` (`L ≥ 6293`), a `HitWfN` adversary and a last
  stage that reads the chain tables with `q_μ`, `q₂₁`, `q₂₂` queries (`AdmHitN`),

      Pr[BadN] ≤ U·εz(pI; q) + M·εz(pR; q) + Σ_i δ_i + ε_plain
        + N·((q₂₂+N+1)·2⁻⁴⁴⁸ + (q₂₁+N+1)·2⁻¹⁰⁸⁸ + (q_μ+N+1)·2⁻²⁵⁶) + Σ_h Adv^ow(inverter h),

  `N = U + M`, `q = (a₃ + x₃, a₅ + x₅ + 312 + (N − 1)·624, a_E + x_E + N·4607)`. Plain
  extraction (`PlainSEN`) stays a hypothesis.
-/

-- (The coin types are large products: their `Fintype` instances exceed the default size.)
set_option synthInstance.maxSize 1024

namespace VoleMole.Theft.Moussaka

open VoleMole.Privacy VoleMole.Privacy.Moussaka VoleMole.Spec VoleMole.Spec.Moussaka
  VoleMole.ZK.Sim VoleMole.Verifier VoleMole.Verifier.Bridge
open VoleMole.Theft.Hit.Mous (WfI WfR hashedR)

-- `Com` evaluates Keccak-p[800]; nothing below needs to unfold it.
attribute [local irreducible] com UOVKey.eval

variable {U M : ℕ}

/-! ## Freshness of the bound, in the game -/

section Fresh

variable {G S : Type} (A : ThiefN U M G S)

/-- **The freshness of the bound on `ε_hit`** for `U + M` simulated proofs: the operation's
statement is well-formed, and each logged statement of its relation is well-formed and differs
from it in a hashed field. -/
def FreshOkN (l : Log) : MOp → Prop
  | .issue req ci => WfI (stOfI req ci) ∧
      ∀ x π, some (Sum.inl x, π) ∈ l → WfI x ∧ stOfI req ci ≠ x
  | .redeem S' req ci cr cd => WfR (stOfR S' req ci cr cd) ∧
      ∀ x π, some (Sum.inr x, π) ∈ l → WfR x ∧ hashedR (stOfR S' req ci cr cd) ≠ hashedR x

lemma FreshOkN.freshOpN {l : Log} {op : MOp} (h : FreshOkN l op) : FreshOpN l op := by
  cases op with
  | issue req ci => exact fun x π hx => (h.2 x π hx).2
  | redeem S' req ci cr cd => exact fun x π hx he => (h.2 x π hx).2 (by rw [he])

/-- The operation's statement is well-formed (`Hit.Mous.FreshOk` with no simulated statement). -/
lemma FreshOkN.freshOk {l : Log} {op : MOp} (h : FreshOkN l op) : Hit.Mous.FreshOk none none op := by
  cases op with
  | issue req ci => exact ⟨h.1, fun _ hy => by cases hy⟩
  | redeem S' req ci cr cd => exact ⟨h.1, fun _ hy => by cases hy⟩

/-- **The adversaries of the bound.** The lengths the C++ types fix and the spec's byte lists do
not: the Anchor Sets the adversary chooses have 32-byte digests, its challenge digests have 32
bytes, and its redemptions have 16-byte contexts. And the digest names the key: a redemption
whose Anchor Set has the digests of a set the adversary chose for an honest redemption is under
that set (in C++ the digest is SHAKE256 of the key; in the spec a key is any digest with any
map). -/
def HitWfN : Prop :=
  (∀ reqs reds, (∀ pk ∈ (A.choose reqs reds).2.1.keys, pk.digest.length = digestBytes) ∧
    (A.choose reqs reds).2.2.length = cdBytes) ∧
  ∀ reqs reds g s S' req ci cr cd, A.out reqs reds g s = .redeem S' req ci cr cd →
    (∀ pk ∈ S'.keys, pk.digest.length = digestBytes) ∧ ci.length = ctxBytes ∧
      cr.length = ctxBytes ∧ cd.length = cdBytes ∧
      ∀ reqs' reds', S'.keys.map (·.digest) = (A.choose reqs' reds').2.1.keys.map (·.digest) →
        S'.keys = (A.choose reqs' reds').2.1.keys

lemma pairO_fst {I P : Type*} {a : Option I} {b : Option P} {x : I} {π : P}
    (h : pairO a b = some (x, π)) : a = some x := by
  rcases a with _ | a <;> rcases b with _ | b <;> simp [pairO] at h
  rw [h.1]

/-- A logged issuance statement is the issuance of an honest token. -/
lemma xN_inl {p : Pub U} {l : Log} {x : IssueInstance} (h : xN A p l = some (.inl x)) :
    ∃ j, x = ⟨p.2 j, A.ci j⟩ := by
  unfold xN at h
  split_ifs at h with h1 h2
  · cases h
    exact ⟨_, rfl⟩
  · cases hf : findIssuer (A.set l) (p.2 (A.tok l)) (A.sig l) with
    | none => rw [hf] at h; cases h
    | some i => rw [hf] at h; cases h

/-- A logged redemption statement is under the Anchor Set and digest the adversary chose. -/
lemma xN_inr {p : Pub U} {l : Log} {x : RedeemInstance} (h : xN A p l = some (.inr x)) :
    x = ⟨(A.set l).keys, p.1 (A.tok l), A.ci (A.tok l), A.cr (A.tok l), A.cd l⟩ := by
  unfold xN at h
  split_ifs at h with h1 h2
  · cases h
  · cases hf : findIssuer (A.set l) (p.2 (A.tok l)) (A.sig l) with
    | none => rw [hf] at h; cases h
    | some i => rw [hf] at h; cases h; rfl

variable {CI CR : Type} (simI : IssueInstance → CI → Bytes) (progI : IssueInstance → CI → S → S)
  (simR : RedeemInstance → CR → Bytes) (progR : RedeemInstance → CR → S → S)
  (verI : IssueInstance → Bytes → S → Bool) (verR : RedeemInstance → Bytes → S → Bool)

/-- **In the simulated game, an accepted operation that is fresh is `FreshOkN`.** The logged
statements are well-formed (the commitments have `uov::M` bytes, the nullifiers and contexts
their lengths; the Anchor Sets and digests are the adversary's, `HitWfN`); an accepted operation
has the lengths the API checks; a redemption that differs from the logged ones differs in a
hashed field (`HitWfN`). -/
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
  -- every logged statement is the statement of a slot
  have hent : ∀ (y : MI) (π : Bytes), some (y, π) ∈ l →
      ∃ l', xN A (pubOf A ω) l' = some y := by
    intro y π hy
    obtain ⟨j, -, he⟩ := simPre_entry _ _ ω cs n _ hy
    exact ⟨_, pairO_fst he.symm⟩
  cases hop : opN A l g s with
  | issue req ci =>
    rw [hop] at hacc hfr
    obtain ⟨hlen, hc, -⟩ := hacc
    refine ⟨⟨by simp [stOfI, hlen, issueRequestBytes], hc⟩, fun x π hx => ⟨?_, hfr x π hx⟩⟩
    obtain ⟨l', hx'⟩ := hent _ _ hx
    obtain ⟨j, rfl⟩ := xN_inl A hx'
    exact ⟨length_com _ _ _ _, List.length_ofFn⟩
  | redeem S' req ci cr cd =>
    rw [hop] at hacc hfr
    obtain ⟨hlen, -⟩ := hacc
    obtain ⟨hd, hc1, hc2, hc3, hk⟩ := hw.2 _ _ g s S' req ci cr cd hop
    refine ⟨⟨hd, S'.valid.2.1, by simp [stOfR, hlen, redeemRequestBytes], hc1, hc2, hc3⟩,
      fun x π hx => ?_⟩
    obtain ⟨l', hx'⟩ := hent _ _ hx
    have ex := xN_inr A hx'
    refine ⟨?_, fun he => ?_⟩
    · rw [ex]
      exact ⟨(hw.1 _ _).1, (A.set l').valid.2.1, List.length_ofFn, List.length_ofFn,
        List.length_ofFn, (hw.1 _ _).2⟩
    · rw [ex] at he
      simp only [hashedR, stOfR, Prod.mk.injEq] at he
      obtain ⟨e1, e2, e3, e4, e5⟩ := he
      refine hfr x π hx ?_
      rw [ex]
      simp only [stOfR, hk _ _ e1, e2, e3, e4, e5]
      rfl

variable (ext : ExtN U M G S) [Nonempty CI] [Nonempty CR] [Fintype CI] [Fintype CR] [Fintype G]
  [Fintype S] [Nonempty G]

/-- **`sim_se_leN` for `FreshOkN`**, for `HitWfN` adversaries. -/
theorem sim_se_leN_ok (hw : HitWfN A) {AdmE : ((Fin (U + M) → G) → S → MOp) → Prop} {εSE : ℝ}
    (hse : WeakSEN (U + M) (simM simI simR) (progM progI progR) (AccOp verI verR) FreshOkN RelOp
      ext AdmE εSE)
    (hAE : ∀ l, AdmE (opN A l)) :
    pr (TapeN U M CI CR G S) (nmSimN A simI progI simR progR (seEvN A verI verR ext)) ≤ εSE := by
  have h := simGN_le_of_weakSEN (Ω := SecN U) (ρ := Coins proveSeedBytes) hse
    (fun ω l => xN A (pubOf A ω) l) (fun _ l => opN A l) fun _ l => hAE l
  refine (Privacy.pr_mono fun z hz => ?_).trans h
  exact ⟨hz.1, freshOkN_of_sim A simI progI simR progR verI verR hw _ _ _ _ _ hz.1 hz.2.1,
    hz.2.2⟩

end Fresh

/-! ## The game at a value of the extra table -/

section X

variable {R : Type} [CipherRow R] {X : Type} (Hb : X → Hashes)
  (A : ThiefN U M Tab3 (ShX R pI X))

/-- **The adversary at a value of the extra table.** -/
def atTN (x : X) : ThiefN U M Tab3 (ShM R) :=
  ⟨A.ctxIss, A.ctxRed, A.pk, A.respond, A.choose, fun reqs reds g s => A.out reqs reds g (atX s x)⟩

variable (e : Log → MOp → (Fin (U + M) → Tab3) → (Tab5F × (Blk → R)) × X → Bytes)

/-- The extractor at a value of the extra table. -/
def eAt (x : X) : Log → MOp → (Fin (U + M) → Tab3) → Tab5F × (Blk → R) → Bytes :=
  fun l o g b => e l o g (b, x)

omit [CipherRow R] in
lemma xN_atTN (x : X) (p : Pub U) (l : Log) : xN (atTN A x) p l = xN A p l := rfl

lemma PN_atX (x : X) (ω : SecN U) (l : Log) (ρ : Coins proveSeedBytes) (g : Tab3) (s : ShM R) :
    PN A (leanPIX Hb) (leanPRX Hb) ω l ρ g (atX s x) =
      PN (atTN A x) (leanPIH (Hb x)) (leanPRH (Hb x)) ω l ρ g s := by
  have hw : xwN (atTN A x) ω l = xwN A ω l := rfl
  unfold PN
  rw [xN_atTN, hw]
  rcases xwN A ω l with _ | ⟨xi, w⟩
  · rfl
  · rcases xi with xi | xi <;> rfl

lemma pgP_atX (x : X) (p : Pub U) (l : Log) (c : SimCoins pI × SimCoins pR) (s : ShM R) :
    pgP A (leanProgIX Hb) (leanProgRX Hb) p l c (atX s x) =
      atX (pgP (atTN A x) (leanProgIH (Hb x)) (leanProgRH (Hb x)) p l c s) x := by
  unfold pgP
  rw [xN_atTN]
  rcases xN A p l with _ | xi
  · rfl
  · rcases xi with xi | xi <;> rfl

lemma badN_atX (x : X) (ω : SecN U) (l : Log) (g : Fin (U + M) → Tab3) (s : ShM R) :
    BadN A (verILX Hb) (verRLX Hb) (extOfN e) ω l g (atX s x) =
      BadN (atTN A x) (verILH (Hb x)) (verRLH (Hb x)) (extOfN (eAt e x)) ω l g s := by
  simp only [BadN, accN, accOp_atX]
  rfl

lemma leanPIH_rd5 (H : Hashes) (w : Bytes) (x : IssueInstance) (rho : Bytes) (g : Tab3) :
    Rd5 (leanPIH (R := R) H w x rho g) 624 :=
  (realROb_rd5 (p := pI) (Hb := H) (st := Privacy.Moussaka.stI x) (w := toBA w)
    (toBA rho) g).map fun o => toL (o.toOption.getD .empty)

lemma leanPIH_rdE {H : Hashes} (hH : HashesWF H) (w : Bytes) (x : IssueInstance) (rho : Bytes)
    (g : Tab3) : RdE (leanPIH (R := R) H w x rho g) 4607 :=
  (realROb_rdE (p := pI) (st := Privacy.Moussaka.stI x) (w := toBA w) hH
    (toBA rho) g).map fun o => toL (o.toOption.getD .empty)

variable {Hb} {a3 a5 aE x3 x5 xE : ℕ}

/-- **The budget of every hop's distinguisher, at every value of the extra table.** -/
theorem distN_budgetMX (hHb : ∀ x, HashesWF (Hb x))
    (hA : ∀ reqs reds, StageBudgetNX (A.out reqs reds) a3 a5 aE)
    (hX : ∀ l, StageBudgetNX (extOfN e l (opN A l)) x3 x5 xE) (i : Fin (U + M))
    (ω : SecN U)
    (τ : Fin (U + M) → Slot (Coins proveSeedBytes) (SimCoins pI × SimCoins pR) Tab3) :
    BudgetX pI (a3 + x3) (a5 + x5 + 312 + (U + M - 1) * 624) (aE + xE + (U + M) * 4607)
      (distN (PN A (leanPIX Hb) (leanPRX Hb))
        (fun ω => SmP A (leanSim pI) (leanSim pR) (pubOf A ω))
        (fun ω => pgP A (leanProgIX Hb) (leanProgRX Hb) (pubOf A ω))
        (BadN A (verILX Hb) (verRLX Hb) (extOfN e)) i ω τ) :=
  (distN_budgetX (fun ω => SmP A (leanSim pI) (leanSim pR) (pubOf A ω))
    (fun x => PN (atTN A x) (leanPIH (Hb x)) (leanPRH (Hb x)))
    (fun x ω => pgP (atTN A x) (leanProgIH (Hb x)) (leanProgRH (Hb x)) (pubOf A ω))
    (fun x => BadN (atTN A x) (verILH (Hb x)) (verRLH (Hb x)) (extOfN (eAt e x)))
    (fun x ω l r g s => PN_atX Hb A x ω l r g s)
    (fun x ω l c s => pgP_atX Hb A x (pubOf A ω) l c s)
    (fun x ω l g s => badN_atX Hb A e x ω l g s)
    (fun x => PN_rd5 (atTN A x) _ _ (leanPIH_rd5 (Hb x)) (leanPRH_rd5 (Hb x)))
    (fun x => PN_rdE (atTN A x) _ _ (leanPIH_rdE (hHb x)) (leanPRH_rdE (hHb x)))
    (fun x _ _ c => isProg_progO (isProg_sumProg (leanProgIH_isProg (Hb x))
      (leanProgRH_isProg (Hb x))) _ c)
    (fun x ω l => bad_budgetN (atTN A x) (verILH (Hb x)) (verRLH (Hb x)) (extOfN (eAt e x))
      (fun reqs reds => hA reqs reds x) (fun l => hX l x) (verILH_rd5 (Hb x))
      (verRLH_rd5 (Hb x)) (verILH_rdE (Hb x)) (verRLH_rdE (Hb x)) ω l) i ω τ).mono le_rfl
    (by have := i.isLt; omega) (by have := i.isLt; omega)

/-- **The budget of an issuance hop**, at every value of the extra table. -/
theorem distPN_budgetXI (hHb : ∀ x, HashesWF (Hb x))
    (hA : ∀ reqs reds, StageBudgetNX (A.out reqs reds) a3 a5 aE)
    (hX : ∀ l, StageBudgetNX (extOfN e l (opN A l)) x3 x5 xE) (i : Fin (U + M))
    (ω : SecN U)
    (τ : Fin (U + M) → Slot (Coins proveSeedBytes) (SimCoins pI × SimCoins pR) Tab3) :
    BudgetX pI (a3 + x3) (a5 + x5 + 312 + (U + M - 1) * 624) (aE + xE + (U + M) * 4607)
      (distPN A (leanPIX Hb) (leanPRX Hb) (leanSim pI) (leanProgIX Hb) (leanSim pR)
        (leanProgRX Hb) (verILX Hb) (verRLX Hb) (extOfN e) i ω τ) :=
  (distN_budgetMX A e hHb hA hX i ω τ).comp
    (fun o : Bytes => pairO (xN A (pubOf A ω)
      (simPre (fun ω => SmP A (leanSim pI) (leanSim pR) (pubOf A ω))
        (fun ω => pgP A (leanProgIX Hb) (leanProgRX Hb) (pubOf A ω)) ω (tapeC τ) i).1)
      (some o))

/-- **The budget of a redemption hop**, at every value of the extra table. -/
theorem distPN_budgetXR (hHb : ∀ x, HashesWF (Hb x))
    (hA : ∀ reqs reds, StageBudgetNX (A.out reqs reds) a3 a5 aE)
    (hX : ∀ l, StageBudgetNX (extOfN e l (opN A l)) x3 x5 xE) (i : Fin (U + M))
    (ω : SecN U)
    (τ : Fin (U + M) → Slot (Coins proveSeedBytes) (SimCoins pI × SimCoins pR) Tab3) :
    BudgetX pR (a3 + x3) (a5 + x5 + 312 + (U + M - 1) * 624) (aE + xE + (U + M) * 4607)
      (distPN A (leanPIX Hb) (leanPRX Hb) (leanSim pI) (leanProgIX Hb) (leanSim pR)
        (leanProgRX Hb) (verILX Hb) (verRLX Hb) (extOfN e) i ω τ) := by
  have h := distPN_budgetXI A e hHb hA hX i ω τ
  -- (`pI` and `pR` have the same `H₂³` table type)
  exact fun x => ⟨(h x).h3, (h x).h5, (h x).hE⟩

lemma progM_sndX (x : MI) (c : SimCoins pI × SimCoins pR) (t : ShX R pI X) :
    (progM (leanProgIX Hb) (leanProgRX Hb) x c t).2 = t.2 := by
  rcases x with x | x <;> rfl

variable [Fintype R] [Nonempty R] [ZKRow R] [Fintype X] [Nonempty X]

/-- **Redemption non-malleability for `U` tokens and `M` redemptions with the extra table, from a
bound on the simulated game's `Acc ∧ Fresh ∧ ¬ Rel` event**: the zero-knowledge hops and their
budgets. -/
theorem noRedirectN_leanX_of_se (hHb : ∀ x, HashesWF (Hb x)) {εSE : ℝ}
    (hA : ∀ reqs reds, StageBudgetNX (A.out reqs reds) a3 a5 aE)
    (hX : ∀ l, StageBudgetNX (extOfN e l (opN A l)) x3 x5 xE)
    (hse' : pr (TapeN U M (SimCoins pI) (SimCoins pR) Tab3 (ShX R pI X))
      (nmSimN A (leanSim pI) (leanProgIX Hb) (leanSim pR) (leanProgRX Hb)
        (seEvN A (verILX Hb) (verRLX Hb) (extOfN e))) ≤ εSE) :
    pr (TapeN U M (SimCoins pI) (SimCoins pR) Tab3 (ShX R pI X))
        (nmRealN A (leanPIX Hb) (leanPRX Hb) (verILX Hb) (verRLX Hb) (extOfN e)) ≤
      U * ZKRow.εz R pI (a3 + x3) (a5 + x5 + 312 + (U + M - 1) * 624)
          (aE + xE + (U + M) * 4607) +
        M * ZKRow.εz R pR (a3 + x3) (a5 + x5 + 312 + (U + M - 1) * 624)
          (aE + xE + (U + M) * 4607) +
        ∑ i, pr (TapeN U M (SimCoins pI) (SimCoins pR) Tab3 (ShX R pI X))
          (deltaNM A (leanPIX Hb) (leanPRX Hb) (leanSim pI) (leanProgIX Hb) (leanSim pR)
            (leanProgRX Hb) i) +
        εSE +
        ∑ h : Fin U, owAdv (A.ci h) (A.cr h)
          (inverterN A (leanSim pI) (leanProgIX Hb) (leanSim pR) (leanProgRX Hb) (extOfN e) h) :=
  noRedirectN_of_se (CI := SimCoins pI) (CR := SimCoins pR) A (leanPIX Hb) (leanPRX Hb)
    (leanSim pI) (leanProgIX Hb) (leanSim pR) (leanProgRX Hb) (verILX Hb) (verRLX Hb) (extOfN e)
    (leanPIX_zkRO hHb _ _ _) (ZKRow.εz_nonneg _ _ _ _) (leanPRX_zkRO hHb _ _ _)
    (ZKRow.εz_nonneg _ _ _ _) (fun i _ ω τ => distPN_budgetXI A e hHb hA hX i ω τ)
    (fun i _ ω τ => distPN_budgetXR A e hHb hA hX i ω τ) hse'

/-- **Redemption non-malleability for `U` tokens and `M` redemptions with the other hashes read
off a uniform table, with plain extraction**: as `noRedirectN_lean_plain`, in the model of
`noRedirect_leanX_plain`. The programming term `ε_moves` (`ProgMovesN`: the fresh output is
accepted on the programmed tables and rejected on the unprogrammed ones) and plain extraction are
for the game's freshness `FreshOpN`, against classes `Adm`, `Adm₀` of the caller's choice (`hadm`:
the last stage composed with `U + M` programmings is in `Adm₀`). -/
theorem noRedirectN_leanX_plain (hHb : ∀ x, HashesWF (Hb x))
    {Adm Adm₀ : ((Fin (U + M) → Tab3) → ShX R pI X → MOp) → Prop} {ε₀ εm : ℝ}
    (hA : ∀ reqs reds, StageBudgetNX (A.out reqs reds) a3 a5 aE)
    (hX : ∀ l, StageBudgetNX (extOfN e l (opN A l)) x3 x5 xE)
    (hplain : PlainSEN (U + M) (AccOp (verILX Hb) (verRLX Hb)) FreshOpN RelOp e Adm₀ ε₀)
    (hmoves : ProgMovesN (U + M) (simM (leanSim pI) (leanSim pR))
      (progM (leanProgIX Hb) (leanProgRX Hb)) (AccOp (verILX Hb) (verRLX Hb)) FreshOpN Adm εm)
    (hAdm : ∀ reqs reds, Adm (A.out reqs reds))
    (hadm : ∀ F L, IsProgs (progM (leanProgIX Hb) (leanProgRX Hb)) (U + M) L → Adm F →
      Adm₀ (fun g s => F g (L s))) :
    pr (TapeN U M (SimCoins pI) (SimCoins pR) Tab3 (ShX R pI X))
        (nmRealN A (leanPIX Hb) (leanPRX Hb) (verILX Hb) (verRLX Hb) (extOfN e)) ≤
      U * ZKRow.εz R pI (a3 + x3) (a5 + x5 + 312 + (U + M - 1) * 624)
          (aE + xE + (U + M) * 4607) +
        M * ZKRow.εz R pR (a3 + x3) (a5 + x5 + 312 + (U + M - 1) * 624)
          (aE + xE + (U + M) * 4607) +
        ∑ i, pr (TapeN U M (SimCoins pI) (SimCoins pR) Tab3 (ShX R pI X))
          (deltaNM A (leanPIX Hb) (leanPRX Hb) (leanSim pI) (leanProgIX Hb) (leanSim pR)
            (leanProgRX Hb) i) +
        (ε₀ + εm) +
        ∑ h : Fin U, owAdv (A.ci h) (A.cr h)
          (inverterN A (leanSim pI) (leanProgIX Hb) (leanSim pR) (leanProgRX Hb) (extOfN e) h) :=
  noRedirectN_leanX_of_se A e hHb hA hX
    (sim_se_leN A (leanSim pI) (leanProgIX Hb) (leanSim pR) (leanProgRX Hb) (verILX Hb)
      (verRLX Hb) (extOfN e) (weakSEN_of_plain hplain hmoves progM_sndX hadm) fun _ => hAdm _ _)

end X

/-! ## `ε_hit` bounded -/

section Hit

open VoleMole.Theft.Hit

variable {R : Type} [CipherRow R] {L M' : ℕ}

/-- The two simulations as one, on the sum of the instance types. -/
noncomputable abbrev DM : MI → SimCoins pI × SimCoins pR → SD :=
  sumD (fun i c => (Privacy.Moussaka.stI i, simulate pI c))
    (fun i c => (Privacy.Moussaka.stR i, simulate pR c))

lemma simProgM : SimProg (R := R) (L := L) (M := M')
    (progM (leanProgIX hbX) (leanProgRX hbX)) DM :=
  Hit.Mous.simProgI.sum Hit.Mous.simProgR

/-- **A fresh forgery's `H₂⁰` input is not a logged simulated statement's.** -/
lemma freshN_ne (l : Log) (op : MOp) (xi : MI) (c : SimCoins pI × SimCoins pR)
    (hfr : FreshOkN l op) (hm : pairO (some xi) (simM (leanSim pI) (leanSim pR) xi c) ∈ l) :
    VoleMole.ROM.IC.muIn (Hit.Mous.fd op).1 ≠ VoleMole.ROM.IC.muIn (DM xi c).1 := by
  rcases xi with i | i
  · simp only [sumD_inl]
    intro hmu
    cases op with
    | issue req ci =>
      obtain ⟨hw, hne⟩ := hfr.2 i _ hm
      exact hne (Hit.Mous.muIn_stI_inj hfr.1 hw hmu)
    | redeem S' req ci cr cd => exact Hit.Mous.muIn_stI_ne_stR _ _ hmu.symm
  · simp only [sumD_inr]
    intro hmu
    cases op with
    | issue req ci => exact Hit.Mous.muIn_stI_ne_stR _ _ hmu
    | redeem S' req ci cr cd =>
      obtain ⟨hw, hne⟩ := hfr.2 i _ hm
      exact hne (Hit.Mous.muIn_stR_inj hfr.1 hw hmu)

variable [Fintype R] [Nonempty R]

/-- **The programming term for `U + M` simulated proofs** (`progMovesN_chain`), for `FreshOkN`:

    ε_moves ≤ N·((q₂₂+N+1)·2⁻⁴⁴⁸ + (q₂₁+N+1)·2⁻¹⁰⁸⁸ + (q_μ+N+1)·2⁻²⁵⁶),   N = U + M. -/
theorem progMovesN_hit (hL : Hit.Mous.Lmin ≤ L) (qMu q21 q22 : ℕ) :
    ProgMovesN (U + M) (simM (leanSim pI) (leanSim pR))
      (progM (leanProgIX hbX) (leanProgRX hbX)) (AccOp (verILX hbX) (verRLX hbX)) FreshOkN
      (AdmHitN (R := R) (p := pI) (L := L) (M := M') (N := U + M) (G := Tab3) qMu q21 q22)
      ((U + M : ℕ) * epsHitN (U + M) qMu q21 q22) :=
  progMovesN_chain simProgM Hit.Mous.fd (fun _ _ h => Hit.Mous.fd_fOk hL h.freshOk)
    (fun o t' t h2 ha hn => Hit.Mous.hitG_of_hitOpX o t' t (accOp_movesX hbX o t' t h2 ha hn))
    (fun l op xi c hfr hm _ => freshN_ne l op xi c hfr hm) qMu q21 q22

variable [ZKRow R] {a3 a5 aE x3 x5 xE : ℕ}

/-- **Redemption non-malleability for `U` tokens and `M` redemptions with the other hashes random
tables and `ε_hit` bounded.** As `noRedirectN_leanX_plain` with the concrete extra table
`XTab L M'` (`hbX`, `L ≥ 6293`) and the programming term bounded by `progMovesN_hit`: for a
`HitWfN` adversary whose last stage reads `(a₃, a₅, a_E)` and the chain tables with
`(q_μ, q₂₁, q₂₂)` queries (`AdmHitN`, implied by its class `Adm`), and an extractor `extOfN e`
that reads `(x₃, x₅, x_E)`, with `N = U + M`,

    Pr[BadN] ≤ U·εz(pI; q) + M·εz(pR; q) + Σ_i δ_i + ε_plain
      + N·((q₂₂+N+1)·2⁻⁴⁴⁸ + (q₂₁+N+1)·2⁻¹⁰⁸⁸ + (q_μ+N+1)·2⁻²⁵⁶) + Σ_h Adv^ow(inverter h),

`q = (a₃ + x₃, a₅ + x₅ + 312 + (N − 1)·624, a_E + x_E + N·4607)`. Plain extraction (`hplain`)
stays a hypothesis, against a class `Adm₀` that contains the last stage composed with `N`
programmings (`hadm`). -/
theorem noRedirectN_leanX_hit (A : ThiefN U M Tab3 (ShX R pI (XTab L M'))) (hw : HitWfN A)
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
        (ε₀ + (U + M : ℕ) * epsHitN (U + M) qMu q21 q22) +
        ∑ h : Fin U, owAdv (A.ci h) (A.cr h)
          (inverterN A (leanSim pI) (leanProgIX hbX) (leanSim pR) (leanProgRX hbX) (extOfN e)
            h) :=
  noRedirectN_leanX_of_se A e hbX_wf hA hX
    (sim_se_leN_ok A (leanSim pI) (leanProgIX hbX) (leanSim pR) (leanProgRX hbX) (verILX hbX)
      (verRLX hbX) (extOfN e) hw
      (weakSEN_of_plain (hplain.fresh_mono fun _ _ h => h.freshOpN)
        ((progMovesN_hit hL qMu q21 q22).mono hAH) progM_sndX hadm) fun _ => hAdm _ _)

end Hit

end VoleMole.Theft.Moussaka
