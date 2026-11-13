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

end VoleMole.Theft.Hit
