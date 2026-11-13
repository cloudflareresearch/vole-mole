import VoleMole.Theft.HitChain
import VoleMole.Theft.Tables
import VoleMole.Theft.ComOW
import VoleMole.EndToEnd.SpecRelations

/-!
# `ε_hit` for the Lean verifiers, with the chain hashes random tables

WIP: see the module notes at the end of the file.
-/

-- (The coin types are large products: their `Fintype` instances exceed the default size.)
set_option synthInstance.maxSize 1024

open Finset

namespace VoleMole.Theft.Hit

open VoleMole.Privacy VoleMole.Theft.ComOW

/-! ## A tree that hits a target read at one cell -/

section Generic

variable {K Y : Type*} [Fintype K] [DecidableEq K] [Fintype Y] [Nonempty Y]

omit [Fintype K] [Fintype Y] [Nonempty Y] in
lemma fixAt_single (a : K) (v : Y) (T : K → Y) :
    fixAt (Function.update (fun _ => none) a (some v)) T = Function.update T a v := by
  funext k
  by_cases hk : k = a
  · subst hk
    simp [fixAt]
  · simp [fixAt, Function.update_of_ne hk]

/-- **A tree with `q` queries outputs a cell other than `a` whose value is a target read off the
table at `a` only** (or a constant, `a = none`) with probability `≤ (q + 1)/|Y|`: lazy sampling
at `a`, then `pr_tree_bad_fix` with the cell `a` fixed. -/
theorem pr_hit_le {f : (K → Y) → Option K} {q : ℕ} (hf : QTree f q) (a : Option K)
    (τ : (K → Y) → Y) (hτ : ∀ T T', (∀ k, a = some k → T k = T' k) → τ T = τ T') :
    pr (K → Y) (fun T => ∃ k, f T = some k ∧ a ≠ some k ∧ T k = τ T) ≤
      (q + 1 : ℕ) * (1 / Fintype.card Y) := by
  classical
  rcases isEmpty_or_nonempty K with hK | ⟨⟨k₀⟩⟩
  · refine (pr_mono (Q := fun _ => False) fun T ⟨k, _⟩ => hK.elim k).trans ?_
    rw [pr_def]
    simp only [filter_false, card_empty, Nat.cast_zero, zero_div]
    positivity
  have hf' : QTree (fun T => (f T).getD k₀) q := hf.map fun o => o.getD k₀
  let T₀ : K → Y := fun _ => Classical.arbitrary Y
  rcases a with _ | a
  · have hc : ∀ T, τ T = τ T₀ := fun T => hτ T T₀ (by simp)
    have h := pr_tree_bad (Bad := fun y => y = τ T₀) (pr_eq_le (τ T₀)) hf'
    refine (pr_mono fun T hT => ?_).trans h
    obtain ⟨k, hk, -, hv⟩ := hT
    show T ((f T).getD k₀) = τ T₀
    rw [hk, Option.getD_some, hv, hc]
  · rw [pr_resample a]
    refine pr_prod_le' _ fun v => ?_
    have h := pr_tree_bad_fix (Bad := fun y => y = τ (Function.update T₀ a v)) (pr_eq_le _) hf'
      (Function.update (fun _ => none) a (some v))
    refine (pr_mono fun T hT => ?_).trans h
    obtain ⟨k, hk, hka, hv⟩ := hT
    have hka' : k ≠ a := fun h => hka (h ▸ rfl)
    simp only [fixAt_single, hk, Option.getD_some]
    refine ⟨by simp [Function.update_of_ne hka'], ?_⟩
    simp only [Function.update_of_ne hka'] at hv
    rw [hv]
    exact hτ _ _ fun k hk => by cases hk; simp

omit [Fintype K] [Fintype Y] in
/-- **A computation that reads two cells and then runs a tree** is a tree with two more queries. -/
lemma QTree.of_two {O Z : Type*} {F : (K → Y) → O} (H : (K → Y) → Z) (a b : K)
    (hH : ∀ T T', T a = T' a → T b = T' b → H T = H T') (G : Z → (K → Y) → O) {q : ℕ}
    (hG : ∀ z, QTree (G z) q) (hF : ∀ T, F T = G (H T) T) : QTree F (q + 2) := by
  let T₀ : K → Y := fun _ => Classical.arbitrary Y
  let U : Y → Y → K → Y := fun v w => Function.update (Function.update T₀ a v) b w
  have hU : ∀ T, H T = H (U (T a) (T b)) := fun T => hH _ _
    (by by_cases hab : a = b <;> simp [U, hab]) (by simp [U])
  have e : F = fun T => (fun v T => (fun w T => G (H (U v w)) T) (T b) T) (T a) T := by
    funext T
    rw [hF, hU]
  rw [e]
  exact .ask a (fun v T => (fun w T => G (H (U v w)) T) (T b) T) (q + 1) fun v =>
    .ask b (fun w T => G (H (U v w)) T) q fun w => hG _

/-- **Averaging over one component.** For a component `get` with its setter `set` (the laws of a
lens), the probability of `P` is the probability of `P` at a uniform value of the component, the
rest uniform. -/
lemma pr_set {X T : Type*} [Fintype X] [Fintype T] [Nonempty T] (set : T → X → X) (get : X → T)
    (h1 : ∀ x, set (get x) x = x) (h2 : ∀ t x, get (set t x) = t)
    (h3 : ∀ t t' x, set t (set t' x) = set t x) (P : X → Prop) :
    pr X P = pr (X × T) (fun z => P (set z.2 z.1)) := by
  let e : X × T ≃ X × T :=
    ⟨fun z => (set z.2 z.1, get z.1), fun z => (set z.2 z.1, get z.1),
      fun z => by simp [h1, h2, h3], fun z => by simp [h1, h2, h3]⟩
  rw [show (fun z : X × T => P (set z.2 z.1)) = fun z => P (e z).1 from rfl,
    pr_equiv e (fun z => P z.1), pr_prod_fst]

end Generic

/-! ## The chain tables of the extra table -/

section XTab

open VoleMole.Verifier VoleMole.Verifier.Bridge VoleMole.ZK.Sim

variable {L M : ℕ}

/-- **The key of a short input**: `a` with `encL a = b`, if `b` has at most `L` bytes. -/
noncomputable def keyL (L : ℕ) (b : ByteArray) : Option (KL L) := by
  classical
  exact if h : ∃ a : KL L, encL a = b then some h.choose else none

lemma keyL_encL (a : KL L) : keyL L (encL a) = some a := by
  classical
  have h : ∃ a' : KL L, encL a' = encL a := ⟨a, rfl⟩
  simp only [keyL, h, ↓reduceDIte, Option.some.injEq]
  exact encL_injective h.choose_spec

lemma encL_of_keyL {b : ByteArray} {a : KL L} (h : keyL L b = some a) : encL a = b := by
  classical
  unfold keyL at h
  split_ifs at h with h'
  · cases h
    exact h'.choose_spec

/-- An input of at most `L` bytes is a key. -/
lemma exists_encL {b : ByteArray} (h : b.size ≤ L) : ∃ a : KL L, encL a = b :=
  ⟨⟨⟨b.size, Nat.lt_succ_of_le h⟩, blk b.size b⟩, ba_blk_of_size rfl⟩

/-- The `H₂⁰` table. -/
def getMu (x : XTab L M) : KL L → Bytes 32 := x.2.1
def setMu (T : KL L → Bytes 32) (x : XTab L M) : XTab L M := (x.1, T, x.2.2)
/-- The `H₂¹` table. -/
def get21 (x : XTab L M) : KL L → Bytes 136 := x.2.2.2.2.1
def set21 (T : KL L → Bytes 136) (x : XTab L M) : XTab L M :=
  (x.1, x.2.1, x.2.2.1, x.2.2.2.1, T, x.2.2.2.2.2)
/-- The `H₂²` table. -/
def get22 (x : XTab L M) : KL L → Bytes 56 := x.2.2.2.2.2.1
def set22 (T : KL L → Bytes 56) (x : XTab L M) : XTab L M :=
  (x.1, x.2.1, x.2.2.1, x.2.2.2.1, x.2.2.2.2.1, T, x.2.2.2.2.2.2)

/-- `AgreeOff` survives a table on another (or the same) domain. -/
lemma agreeOff_withTable {k j : Kind} {Hs Hs' : Hashes} (h : Hs.AgreeOff k Hs') {K : Type}
    (enc : K → ByteArray) (G : K → Bytes j.outLen) :
    (Hs.withTable j enc G).AgreeOff k (Hs'.withTable j enc G) := by
  intro k' hk'
  funext b
  simp only [Hashes.withTable]
  split_ifs with h1 h2
  · rfl
  · subst h1
    rw [h _ hk']
  · rw [h k' hk']

/-- Two tables on the domain `k` agree off `k`. -/
lemma agreeOff_withTable_self (Hs : Hashes) (k : Kind) {K : Type} (enc : K → ByteArray)
    (G G' : K → Bytes k.outLen) : (Hs.withTable k enc G).AgreeOff k (Hs.withTable k enc G') := by
  intro k' hk'
  funext b
  simp only [Hashes.withTable, hk', ite_false]

open Classical in
lemma withTable_self (Hs : Hashes) (k : Kind) {K : Type} (enc : K → ByteArray)
    (G : K → Bytes k.outLen) (b : ByteArray) :
    (Hs.withTable k enc G).hash k b =
      if h : ∃ a, enc a = b then ba (G h.choose) else Hs.hash k b := by
  simp only [Hashes.withTable, ite_true]

/-- The table `encL` answers a short input at its key. -/
lemma withTable_encL (Hs : Hashes) (k : Kind) (G : KL L → Bytes k.outLen) (b : ByteArray) :
    (Hs.withTable k encL G).hash k b =
      match keyL L b with
      | some a => ba (G a)
      | none => Hs.hash k b := by
  classical
  rw [withTable_self]
  by_cases h : ∃ a : KL L, encL a = b
  · obtain ⟨a, rfl⟩ := h
    have hex : ∃ a' : KL L, encL a' = encL a := ⟨a, rfl⟩
    simp only [keyL_encL, hex, ↓reduceDIte]
    congr 2
    exact encL_injective (Exists.choose_spec (⟨a, rfl⟩ : ∃ a', encL a' = encL a))
  · have : keyL L b = none := by simp only [keyL, h, ↓reduceDIte]
    simp only [h, ↓reduceDIte, this]

lemma hbX_agreeOff_mu (T T' : KL L → Bytes 32) (x : XTab L M) :
    (hbX (setMu T x)).AgreeOff .mu (hbX (setMu T' x)) := by
  unfold hbX setMu
  simp only
  refine agreeOff_withTable (agreeOff_withTable (agreeOff_withTable (agreeOff_withTable
    (agreeOff_withTable (agreeOff_withTable_self _ _ _ _ _) _ _) _ _) _ _) _ _) _ _

lemma hbX_agreeOff_21 (T T' : KL L → Bytes 136) (x : XTab L M) :
    (hbX (set21 T x)).AgreeOff .h21 (hbX (set21 T' x)) := by
  unfold hbX set21
  simp only
  exact agreeOff_withTable (agreeOff_withTable (agreeOff_withTable_self _ _ _ _ _) _ _) _ _

lemma hbX_agreeOff_22 (T T' : KL L → Bytes 56) (x : XTab L M) :
    (hbX (set22 T x)).AgreeOff .h22 (hbX (set22 T' x)) := by
  unfold hbX set22
  simp only
  exact agreeOff_withTable (agreeOff_withTable_self _ _ _ _ _) _ _

lemma hbX_mu_eq (x : XTab L M) (b : ByteArray) :
    (hbX x).hash .mu b = match keyL L b with
      | some a => ba (x.2.1 a)
      | none => Hashes.shake.hash .mu b := by
  refine (Hashes.withTable_ne _ (.comb M) .mu (by simp) _ _ _).trans ?_
  refine (Hashes.withTable_ne _ .h22 .mu (by simp) _ _ _).trans ?_
  refine (Hashes.withTable_ne _ .h21 .mu (by simp) _ _ _).trans ?_
  refine (Hashes.withTable_ne _ .h4 .mu (by simp) _ _ _).trans ?_
  refine (Hashes.withTable_ne _ .muDelayed .mu (by simp) _ _ _).trans ?_
  refine (withTable_encL _ .mu x.2.1 b).trans ?_
  rcases keyL L b with _ | a
  · exact Hashes.withTable_ne _ .h1 .mu (by simp) _ _ _
  · rfl

lemma hbX_21_eq (x : XTab L M) (b : ByteArray) :
    (hbX x).hash .h21 b = match keyL L b with
      | some a => ba (x.2.2.2.2.1 a)
      | none => Hashes.shake.hash .h21 b := by
  refine (Hashes.withTable_ne _ (.comb M) .h21 (by simp) _ _ _).trans ?_
  refine (Hashes.withTable_ne _ .h22 .h21 (by simp) _ _ _).trans ?_
  refine (withTable_encL _ .h21 x.2.2.2.2.1 b).trans ?_
  rcases keyL L b with _ | a
  · exact (Hashes.withTable_ne _ .h4 .h21 (by simp) _ _ _).trans
      ((Hashes.withTable_ne _ .muDelayed .h21 (by simp) _ _ _).trans
      ((Hashes.withTable_ne _ .mu .h21 (by simp) _ _ _).trans
      (Hashes.withTable_ne _ .h1 .h21 (by simp) _ _ _)))
  · rfl

lemma hbX_22_eq (x : XTab L M) (b : ByteArray) :
    (hbX x).hash .h22 b = match keyL L b with
      | some a => ba (x.2.2.2.2.2.1 a)
      | none => Hashes.shake.hash .h22 b := by
  refine (Hashes.withTable_ne _ (.comb M) .h22 (by simp) _ _ _).trans ?_
  refine (withTable_encL _ .h22 x.2.2.2.2.2.1 b).trans ?_
  rcases keyL L b with _ | a
  · exact (Hashes.withTable_ne _ .h21 .h22 (by simp) _ _ _).trans
      ((Hashes.withTable_ne _ .h4 .h22 (by simp) _ _ _).trans
      ((Hashes.withTable_ne _ .muDelayed .h22 (by simp) _ _ _).trans
      ((Hashes.withTable_ne _ .mu .h22 (by simp) _ _ _).trans
      (Hashes.withTable_ne _ .h1 .h22 (by simp) _ _ _))))
  · rfl

end XTab

/-! ## Ratatouille: the event of a hit -/

namespace Rata

open VoleMole.Verifier VoleMole.Verifier.Bridge VoleMole.ZK.Sim VoleMole.ZK
open VoleMole.Privacy.Ratatouille VoleMole.Spec.Ratatouille VoleMole.Theft.Ratatouille
open VoleMole.Theft.Chain
open VoleMole.ROM.IC (muIn)

variable {R : Type} [CipherRow R] {L M : ℕ}

/-- The shared tables with the extra table `XTab L M`. -/
abbrev ShT (R : Type) (L M : ℕ) := ShX R pI (XTab L M)

/-- **The record the chain is computed with**: the base record `hbX x` with the `H₅` table. -/
noncomputable def recT (t : ShT R L M) : Hashes := rec5 (hbX t.2.2) t.2.1.1

/-- The PRG of the tables' cipher. -/
noncomputable abbrev prgT (t : ShT R L M) : HasPrg := icPrg (rowFn t.2.1.2)

variable (A : Thief Sizes.labelRows Tab3 (ShT R L M))

/-- **The forgery's statement** (the spend's with the adversary's key). -/
def fSt : Op Sizes.labelRows → Statement
  | .issue q t c => Privacy.Ratatouille.stI (opXI q t c)
  | .spend q c _ => Privacy.Ratatouille.stS (opXS A q c)

/-- The forgery's proof bytes. -/
def fPf : Op Sizes.labelRows → ByteArray
  | .issue q _ _ => bOf (issueReqProof q)
  | .spend q _ _ => bOf (SpendReq.parse q).proof

/-- **A simulation**: its statement and its output (none if no statement). -/
abbrev SimD := Option (Statement × Except String ByteArray)

/-- The issuance simulation. -/
noncomputable def sd₁ (x : Option IssueInstance) (c : SimCoins pI) : SimD :=
  x.map fun i => (Privacy.Ratatouille.stI i, simulate pI c)

/-- The spend simulation. -/
noncomputable def sd₂ (x : Option SpendInstance) (c : SimCoins pS) : SimD :=
  x.map fun i => (Privacy.Ratatouille.stS i, simulate pS c)

/-- The forgery's chain points: `H₂²`, `H₂¹`, `H₂⁰`. -/
noncomputable def fPt22 (op : Op Sizes.labelRows) (t : ShT R L M) : ByteArray :=
  @cin2 (prgT t) (recT t) CrtGen.tables (fSt A op) (fPf op)
noncomputable def fPt21 (op : Op Sizes.labelRows) (t : ShT R L M) : ByteArray :=
  @cin1 (prgT t) (recT t) (fSt A op) (fPf op)
def fPtMu (op : Op Sizes.labelRows) : ByteArray := muIn (fSt A op)

/-- A simulation's chain points. -/
noncomputable def sPt22 (d : SimD) (t : ShT R L M) : ByteArray :=
  match d with
  | some (st, o) => @sim2 (prgT t) (recT t) CrtGen.tables st o
  | none => ByteArray.empty
noncomputable def sPt21 (d : SimD) (t : ShT R L M) : ByteArray :=
  match d with
  | some (st, o) => @sim1 (prgT t) (recT t) st o
  | none => ByteArray.empty
def sPtMu (d : SimD) : ByteArray :=
  match d with
  | some (st, _) => muIn st
  | none => ByteArray.empty

/-- A simulation's targets: the first 56 bytes of its programmed block, and its `H₂¹`, `H₂⁰`
answers. -/
noncomputable def sTau22 (d : SimD) (t : ShT R L M) : ByteArray :=
  match d with
  | some (st, o) => (ba (blk (preLen pI) (@simPre (prgT t) (recT t) CrtGen.tables st o))).extract 0 56
  | none => ByteArray.empty
noncomputable def sTau21 (d : SimD) (t : ShT R L M) : ByteArray :=
  (recT t).hash .h21 (sPt21 d t)
noncomputable def sTauMu (d : SimD) (t : ShT R L M) : ByteArray :=
  (recT t).hash .mu (sPtMu d)

/-- **A hit at one level**: the forgery's point `Pf` is a short input other than the simulation's
`Ps`, and the table answers it with the target `τ`. -/
def Ev {n : ℕ} (Pf Ps τ : ByteArray) (G : KL L → ZK.Sim.Bytes n) : Prop :=
  ∃ k, encL k = Pf ∧ Pf ≠ Ps ∧ ba (G k) = τ

/-- **The weak freshness of the theft game with the adversary's key**: a spend is compared with
the simulated spend's statement with its key replaced by the adversary's. In the game the
Client's spend statement has the adversary's key (`stS`), so this is `FreshOp` there
(`freshOk_stS`); it never holds where `FreshOp` fails (`FreshOk.freshOp`). The Lean spend
statement does not hash the key (`Privacy.Ratatouille.stS`), so two spend statements that differ
only in the key have the same chain. -/
def FreshOk {Z : Sizes} {G S : Type} (A : Thief Z G S) (p₁ : Option (IssueInstance × IssueProof Z))
    (p₂ : Option (SpendInstance × SpendProof Z)) (op : Op Z) : Prop :=
  FreshOp A p₁ (p₂.map fun y => ({ y.1 with pk := A.pk }, y.2)) op

/-! ### Helpers -/

omit [CipherRow R] in
lemma recT_hash_ne (t : ShT R L M) {k : Kind} (hk : k ≠ .h5) :
    (recT t).hash k = (hbX t.2.2).hash k :=
  funext (Hashes.withTable_ne _ .h5 k hk enc5 t.2.1.1)

omit [CipherRow R] in
lemma recT_wf (t : ShT R L M) : HashesWF (recT t) := (hbX_wf t.2.2).withTable .h5 enc5 t.2.1.1

/-- The forger's verifier point is computed with the `H₅` record (`vPre` does not read `H₂³`). -/
lemma vPoint_eq {p : Params} (Hb : Hashes) (st : Statement) (pf : ByteArray) (s : ShG R p) :
    vPoint Hb st pf s =
      (@vPre (icPrg (rowFn s.2.2)) (rec5 Hb s.2.1) CrtGen.tables st pf ++ (pfOf st pf).ctr).push 11 := by
  unfold vPoint
  have hA : (recV p Hb s.1 s.2.1).AgreeOff .h23 (rec5 Hb s.2.1) :=
    agreeOff_withTable (fun k hk => funext (Hashes.withTable_ne Hb .h23 k hk _ _)) _ _
  rw [@vPre_agreeOff (icPrg (rowFn s.2.2)) _ _ _ unread_h23 hA]
  rfl

/-- The simulator's `outPre` is `simPre` with `recT`. -/
lemma outPre_eq (st : Statement) (o : Except String ByteArray) (t : ShT R L M) :
    @outPre (prgT t) (hbX t.2.2) CrtGen.tables st t.2.1.1 o =
      @simPre (prgT t) (recT t) CrtGen.tables st o := by
  cases o <;> rfl

lemma progRO_moved_at {p : Params} (st : Statement) (c : SimCoins p) (s : ShG R p) (u : ShT R L M)
    (hs : s.2 = u.2.1) (k : K2 p) (h : (progRO p (hbX u.2.2) st c s).1 k ≠ s.1 k) :
    k.1 = blk (preLen p) (@simPre (prgT u) (recT u) CrtGen.tables st (simulate p c)) := by
  obtain ⟨s1, s2⟩ := s
  simp only at hs
  subst hs
  rw [progRO_moved (hbX u.2.2) st c _ k h]
  exact congrArg _ (outPre_eq st _ u)

/-- **The keys both programmings change** are grinding keys of one of the two simulations'
prefixes. -/
lemma progT_moved (x₁ : Option IssueInstance) (c₁ : SimCoins pI) (x₂ : Option SpendInstance)
    (c₂ : SimCoins pS) (t : ShT R L M) (k : K2 pI)
    (h : (progT (leanProgIRX hbX) (leanProgSRX hbX) x₁ c₁ x₂ c₂ t).1 k ≠ t.1 k) :
    (∃ st o, sd₁ x₁ c₁ = some (st, o) ∧
        k.1 = blk (preLen pI) (@simPre (prgT t) (recT t) CrtGen.tables st o)) ∨
      (∃ st o, sd₂ x₂ c₂ = some (st, o) ∧
        k.1 = blk (preLen pI) (@simPre (prgT t) (recT t) CrtGen.tables st o)) := by
  -- the spend programming acts first, on `t`; the issuance programming on its output
  have h2 : (progO (leanProgSRX (R := R) hbX) x₂ c₂ t).2 = t.2 := by
    rcases x₂ with _ | i <;> rfl
  by_cases hk : (progO (leanProgSRX (R := R) hbX) x₂ c₂ t).1 k = t.1 k
  · left
    rcases x₁ with _ | i
    · exact absurd (by rw [← hk]; rfl) h
    · refine ⟨_, _, rfl, ?_⟩
      have hx : (progO (leanProgSRX (R := R) hbX) x₂ c₂ t).2.2 = t.2.2 := by rw [h2]
      have hm : (progRO pI (hbX t.2.2) (Privacy.Ratatouille.stI i) c₁
          (shOf (progO (leanProgSRX (R := R) hbX) x₂ c₂ t))).1 k ≠
          (shOf (progO (leanProgSRX (R := R) hbX) x₂ c₂ t)).1 k := by
        intro he
        apply h
        show (progRO pI (hbX (progO (leanProgSRX (R := R) hbX) x₂ c₂ t).2.2)
          (Privacy.Ratatouille.stI i) c₁ (shOf (progO (leanProgSRX (R := R) hbX) x₂ c₂ t))).1 k =
          t.1 k
        rw [hx, he, ← hk]
        rfl
      exact progRO_moved_at _ c₁ _ t (by simp only [shOf, h2]) k hm
  · right
    rcases x₂ with _ | i
    · exact absurd rfl hk
    · exact ⟨_, _, rfl, progRO_moved_at (p := pS) _ c₂ (shOf t) t rfl k hk⟩

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

/-! ### The cases of a hit -/

/-- **A hit on one simulation**, at one of the three levels. -/
def HitAt (op : Op Sizes.labelRows) (t : ShT R L M) (d : SimD) : Prop :=
  Ev (fPt22 A op t) (sPt22 d t) (sTau22 d t) (get22 t.2.2) ∨
    Ev (fPt21 A op t) (sPt21 d t) (sTau21 d t) (get21 t.2.2) ∨
    Ev (fPtMu A op) (sPtMu d) (sTauMu d t) (getMu t.2.2)

/-- The shortest table length that holds every chain input of the forgeries:
`H₂¹` inputs of the spend relation (`14357` bytes). -/
def Lmin : ℕ := 14357

omit [CipherRow R] in
lemma fSt_facts (op : Op Sizes.labelRows) :
    (fSt A op).delayed = false ∧ (fSt A op).binder1.size = 0 ∧ (fSt A op).binder2.size = 0 ∧
      64 + 16 * (fSt A op).params.correctionBytes +
        (fSt A op).params.nMask * (fSt A op).params.nMultBytes + 16 + 0 + 1 ≤ Lmin ∧
      264 + 0 + (fSt A op).params.witnessBytes + 1 ≤ Lmin ∧ (muIn (fSt A op)).size ≤ Lmin := by
  cases op with
  | issue q t c =>
    refine ⟨rfl, rfl, rfl, ?_, ?_, ?_⟩
    · show 64 + 16 * pI.correctionBytes + pI.nMask * pI.nMultBytes + 16 + 0 + 1 ≤ Lmin
      decide
    · show 264 + 0 + pI.witnessBytes + 1 ≤ Lmin
      decide
    · simp only [fSt, size_muIn_stI, Lmin]
      omega
  | spend q c x =>
    refine ⟨rfl, rfl, rfl, ?_, ?_, ?_⟩
    · show 64 + 16 * pS.correctionBytes + pS.nMask * pS.nMultBytes + 16 + 0 + 1 ≤ Lmin
      decide
    · show 264 + 0 + pS.witnessBytes + 1 ≤ Lmin
      decide
    · simp only [fSt, size_muIn_stS, Lmin]
      omega

omit [CipherRow R] in
lemma recT_22 (t : ShT R L M) (k : KL L) : (recT t).hash .h22 (encL k) = ba (get22 t.2.2 k) := by
  rw [recT_hash_ne t (by decide), hbX_22_eq, keyL_encL]
  rfl

omit [CipherRow R] in
lemma recT_21 (t : ShT R L M) (k : KL L) : (recT t).hash .h21 (encL k) = ba (get21 t.2.2 k) := by
  rw [recT_hash_ne t (by decide), hbX_21_eq, keyL_encL]
  rfl

omit [CipherRow R] in
lemma recT_mu (t : ShT R L M) (k : KL L) : (recT t).hash .mu (encL k) = ba (getMu t.2.2 k) := by
  rw [recT_hash_ne t (by decide), hbX_mu_eq, keyL_encL]
  rfl

/-- **A hit on one simulation's prefix** (`chain_hit` with the tables' record): one of the three
level events, unless the simulation produced a proof whose statement has the forgery's `H₂⁰`
input. -/
lemma hitAt_of (hL : Lmin ≤ L) {p : Params} (op : Op Sizes.labelRows) (t : ShT R L M)
    (st : Statement) (o : Except String ByteArray) (hds : st.delayed = false) (k : K2 p)
    (hk : enc2 p k = (@vPre (prgT t) (recT t) CrtGen.tables (fSt A op) (fPf op) ++
      (pfOf (fSt A op) (fPf op)).ctr).push 11)
    (hkp : ba (blk (preLen p) (@simPre (prgT t) (recT t) CrtGen.tables st o)) =
      ba (blk (preLen pI) (@simPre (prgT t) (recT t) CrtGen.tables st o)))
    (hkp' : k.1 = blk (preLen p) (@simPre (prgT t) (recT t) CrtGen.tables st o))
    (hne : (∃ b, o = .ok b) → muIn (fSt A op) ≠ muIn st) :
    HitAt A op t (some (st, o)) := by
  obtain ⟨hdf, hb1, hb2, hl1, hl2, hlm⟩ := fSt_facts A op
  obtain ⟨hv, hc⟩ := @chain_hit (prgT t) (recT t) CrtGen.tables (recT_wf t) p (fSt A op) st (fPf op)
    o hdf hds k hk hkp'
  rcases hc with ⟨h2, he⟩ | ⟨h1, he⟩ | ⟨hm, he⟩ | ⟨hok, hm⟩
  · left
    have hs := @size_cin2_le (prgT t) (recT t) CrtGen.tables (fSt A op) (fPf op) (recT_wf t) hdf
    obtain ⟨a, ha⟩ := exists_encL (L := L)
      (b := @cin2 (prgT t) (recT t) CrtGen.tables (fSt A op) (fPf op)) (by omega)
    refine ⟨a, ha, h2, ?_⟩
    rw [← recT_22, ha, he, hkp]
    rfl
  · right; left
    have hs := @size_cin1_le (prgT t) (recT t) (fSt A op) (fPf op) (recT_wf t)
    obtain ⟨a, ha⟩ := exists_encL (L := L)
      (b := @cin1 (prgT t) (recT t) (fSt A op) (fPf op)) (by omega)
    refine ⟨a, ha, h1, ?_⟩
    rw [← recT_21, ha]
    exact he
  · right; right
    obtain ⟨a, ha⟩ := exists_encL (L := L) (b := muIn (fSt A op)) (by omega)
    refine ⟨a, ha, hm, ?_⟩
    rw [← recT_mu, ha]
    exact he
  · exact absurd hm (hne hok)

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

/-- **The cases of a hit.** A fresh forgery (`FreshOk`) whose verifier's `H₂³` point is a point
the simulators programmed hits one of the two simulations at one of the three levels. -/
theorem hit_cases (hL : Lmin ≤ L) (x₁ : Option IssueInstance) (c₁ : SimCoins pI)
    (x₂ : Option SpendInstance) (c₂ : SimCoins pS) (op : Op Sizes.labelRows) (t : ShT R L M)
    (hfr : FreshOk A (pairO x₁ (simO leanSimIR x₁ c₁)) (pairO x₂ (simO leanSimSR x₂ c₂)) op)
    (hhit : HitOpX (Hb := hbX) A op (progT (leanProgIRX hbX) (leanProgSRX hbX) x₁ c₁ x₂ c₂ t) t) :
    HitAt A op t (sd₁ x₁ c₁) ∨ HitAt A op t (sd₂ x₂ c₂) := by
  cases op with
  | issue q tc c =>
    obtain ⟨k, hk, hmv⟩ := hhit
    rw [vPoint_eq] at hk
    rcases progT_moved x₁ c₁ x₂ c₂ t k hmv with ⟨st, o, hd, hkp⟩ | ⟨st, o, hd, hkp⟩
    · left
      rw [hd]
      rcases x₁ with _ | i
      · cases hd
      simp only [sd₁, Option.map_some, Option.some.injEq, Prod.mk.injEq] at hd
      obtain ⟨rfl, rfl⟩ := hd
      refine hitAt_of A hL (.issue q tc c) t _ _ rfl k hk rfl hkp ?_
      rintro ⟨b, hb⟩ hm
      obtain ⟨π, hπ⟩ := simO_some_I (i := i) hb
      refine hfr (i, π) (by rw [hπ]; rfl) ?_
      exact muIn_stI_inj hm
    · right
      rw [hd]
      rcases x₂ with _ | i
      · cases hd
      simp only [sd₂, Option.map_some, Option.some.injEq, Prod.mk.injEq] at hd
      obtain ⟨rfl, rfl⟩ := hd
      refine hitAt_of A hL (.issue q tc c) t _ _ rfl k hk rfl hkp ?_
      intro _ hm
      have := congrArg ByteArray.size hm
      simp only [fSt, size_muIn_stI, size_muIn_stS] at this
      omega
  | spend q c x =>
    obtain ⟨k, hk, hmv⟩ := hhit
    have hk := hk.trans (vPoint_eq (p := pS) _ _ _ (shOf t))
    rcases progT_moved x₁ c₁ x₂ c₂ t k hmv with ⟨st, o, hd, hkp⟩ | ⟨st, o, hd, hkp⟩
    · left
      rw [hd]
      rcases x₁ with _ | i
      · cases hd
      simp only [sd₁, Option.map_some, Option.some.injEq, Prod.mk.injEq] at hd
      obtain ⟨rfl, rfl⟩ := hd
      refine hitAt_of A hL (.spend q c x) t _ _ rfl k hk rfl hkp ?_
      intro _ hm
      have := congrArg ByteArray.size hm
      simp only [fSt, size_muIn_stI, size_muIn_stS] at this
      omega
    · right
      rw [hd]
      rcases x₂ with _ | i
      · cases hd
      simp only [sd₂, Option.map_some, Option.some.injEq, Prod.mk.injEq] at hd
      obtain ⟨rfl, rfl⟩ := hd
      refine hitAt_of A hL (.spend q c x) t _ _ rfl k hk rfl hkp ?_
      rintro ⟨b, hb⟩ hm
      obtain ⟨π, hπ⟩ := simO_some_S (i := i) hb
      refine hfr ({ i with pk := A.pk }, π) (by rw [hπ]; rfl) ?_
      have := muIn_stS_inj hm.symm
      rw [← this]
      rfl

end Rata

end VoleMole.Theft.Hit
