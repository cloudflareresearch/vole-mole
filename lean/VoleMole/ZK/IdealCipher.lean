import VoleMole.Privacy.Hybrid

/-!
# Puncturing a GGM tree in the ideal-cipher model (the counting core of hop H4)

An abstract GGM computation over a cipher table, and the hybrid that replaces the rows of the
secret nodes (the hidden paths) by independent uniform rows, one node at a time, in the counting
style of `Privacy/Hybrid.lean`.

**The model.** The cipher is a table `E : K → X → K`: for every key, a row `X → K` (a uniform
table is the ideal cipher with the rows uniform functions; the PRP/PRF switching term for
permutation rows is not part of this file). The tree is a heap: node `n + 1` has parent `n / 2`,
and its value is the parent's row at the input `x (n + 1)` (the node's CTR block). Node `0` is the
root seed. Every node `n` has a row, `rowAt rep E R seed n`: for the *replaced* nodes `n ∈ rep`
(with `n < N`) the independent row `R n`, otherwise `E` at the node's value `keyAt … n`. The real
computation is `rep = ∅`.

An output `Φ` of the rows is seen by a distinguisher `A` that also reads the table `E` at a set
`Q` of at most `q` keys (whole rows: a query at key `k` reveals `E k`).

* `hop`: replacing one more node `n` (whose parent is already replaced, or the root) costs
  `(N + q) / |K|`: the node's value is uniform and independent of everything else in the
  replaced experiment (`v ∉ T`, `pr_mem_reset_le`), and programming the table at it with a fresh
  row is perfect (`Privacy.pr_program_eq`); the two experiments differ only if the value is read
  as a key elsewhere (another node with the same value, or a query of `A`).
* `puncture`: for an upward-closed set of secret nodes, replacing all of them costs
  `|secret| · (N + q) / |K|` (the hybrid over the secret nodes in heap order).
* `rowAt_congr_points`: in the fully replaced experiment the rows off the secret nodes depend on
  the replaced rows only at the inputs of the non-secret children of secret nodes.
* `exper_empty`, `exper_eq_of_close`: the real experiment is `realPr` (a uniform seed and table),
  and a fully replaced experiment whose output has, for every table, the law of `F` of a uniform
  `h` is `idealPr F` (a uniform `h` and an independent table).

Side conditions: siblings have different inputs (`hsib`), and `Φ` does not read the row of a
secret node's parent at the secret node's input (`hΦ`), i.e. the value of a secret node is used
only as a key.
-/

open Finset

namespace VoleMole.ZK.IC

open VoleMole.Privacy

section Tree

variable {K X : Type} (x : ℕ → X) (N : ℕ)

/-- **The row of node `n`**: `R n` if `n` is replaced, else `E` at the node's value (the root seed,
or the parent's row at the node's input). -/
def rowAt (rep : Finset ℕ) (E : K → X → K) (R : Fin N → X → K) (seed : K) : ℕ → X → K
  | 0 => if h : 0 ∈ rep ∧ 0 < N then R ⟨0, h.2⟩ else E seed
  | n + 1 => if h : n + 1 ∈ rep ∧ n + 1 < N then R ⟨n + 1, h.2⟩
      else E (rowAt rep E R seed (n / 2) (x (n + 1)))
decreasing_by omega

/-- **The value of node `n`**: the root seed, or the parent's row at the node's input. -/
def keyAt (rep : Finset ℕ) (E : K → X → K) (R : Fin N → X → K) (seed : K) : ℕ → K
  | 0 => seed
  | n + 1 => rowAt x N rep E R seed (n / 2) (x (n + 1))

variable {x N}
variable {rep : Finset ℕ} {E : K → X → K} {R : Fin N → X → K} {seed : K}

lemma rowAt_eq (rep : Finset ℕ) (E : K → X → K) (R : Fin N → X → K) (seed : K) (n : ℕ) :
    rowAt x N rep E R seed n =
      if h : n ∈ rep ∧ n < N then R ⟨n, h.2⟩ else E (keyAt x N rep E R seed n) := by
  cases n with
  | zero => rw [rowAt]; rfl
  | succ n => rw [rowAt]; rfl

lemma rowAt_of_mem {n : ℕ} (h : n ∈ rep) (hn : n < N) : rowAt x N rep E R seed n = R ⟨n, hn⟩ := by
  rw [rowAt_eq, dite_eq_left_of_eq_true (eq_true ⟨h, hn⟩)]

lemma rowAt_of_not_mem {n : ℕ} (h : n ∉ rep) :
    rowAt x N rep E R seed n = E (keyAt x N rep E R seed n) := by
  rw [rowAt_eq, dite_eq_right_of_eq_false (eq_false fun h' => h h'.1)]

lemma keyAt_zero : keyAt x N rep E R seed 0 = seed := rfl

lemma keyAt_pos {n : ℕ} (hn : n ≠ 0) :
    keyAt x N rep E R seed n = rowAt x N rep E R seed ((n - 1) / 2) (x n) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rfl

/-- The value of a node whose parent is replaced: the parent's row at its input. -/
lemma keyAt_of_par {n : ℕ} (hn : n ≠ 0) (hp : (n - 1) / 2 ∈ rep) (hN : (n - 1) / 2 < N) :
    keyAt x N rep E R seed n = R ⟨(n - 1) / 2, hN⟩ (x n) := by
  rw [keyAt_pos hn, rowAt_of_mem hp hN]

end Tree

/-! ## Guessing a coordinate that the rest does not depend on -/

section Reset

variable {α K : Type*} [Fintype α] [Fintype K] [Nonempty K]

/-- **A coordinate the event's candidates do not depend on is guessed with probability
`≤ q / |K|`.** `f a` is the coordinate and `set a k` the point `a` with that coordinate set to
`k` (a lens); the candidates `T a` do not change under `set`. -/
theorem pr_mem_reset_le (f : α → K) (set : α → K → α) (hf : ∀ a k, f (set a k) = k)
    (hss : ∀ a k k', set (set a k) k' = set a k') (hsf : ∀ a, set a (f a) = a)
    (T : α → Finset K) (hT : ∀ a k, T (set a k) = T a) {q : ℕ} (hq : ∀ a, (T a).card ≤ q) :
    pr α (fun a => f a ∈ T a) ≤ q / Fintype.card K := by
  classical
  obtain ⟨k0⟩ := (inferInstance : Nonempty K)
  by_cases hα : Nonempty α
  swap
  · rw [not_nonempty_iff] at hα
    rw [pr_def]
    simp only [Finset.univ_eq_empty, Finset.filter_empty, Finset.card_empty, Nat.cast_zero,
      zero_div]
    positivity
  obtain ⟨a0⟩ := hα
  let β := {a : α // set a k0 = a}
  have : Nonempty β := ⟨⟨set a0 k0, hss _ _ _⟩⟩
  let e : α ≃ K × β :=
    { toFun := fun a => (f a, ⟨set a k0, hss _ _ _⟩)
      invFun := fun p => set p.2.1 p.1
      left_inv := fun a => by simp only [hss, hsf]
      right_inv := fun p => by
        obtain ⟨k, b, hb⟩ := p
        simp only [hf, Prod.mk.injEq, true_and]
        exact Subtype.ext (by simp only [hss]; exact hb) }
  have h1 : pr α (fun a => f a ∈ T a) = pr (K × β) (fun p => id p.1 ∈ T p.2.1) := by
    rw [← pr_equiv e.symm]
    refine pr_congr fun p => ?_
    show f (set p.2.1 p.1) ∈ T (set p.2.1 p.1) ↔ p.1 ∈ T p.2.1
    rw [hf, hT]
  rw [h1]
  exact pr_mem_indep_le id Function.injective_id (fun b : β => T b.1) fun b => hq _

end Reset

/-! ## One hop -/

section Hop

variable {K X : Type} [Fintype K] [DecidableEq K] [Nonempty K] [Fintype X] [DecidableEq X]
  {x : ℕ → X} {N : ℕ} {O : Type}

/-- The coins: the root seed and the replacement rows. -/
abbrev Coins (K X : Type) (N : ℕ) := K × (Fin N → X → K)

/-- The experiment with the replaced nodes `rep`: `A` sees `Φ` of the rows and reads the table. -/
noncomputable def exper (x : ℕ → X) (N : ℕ) (rep : Finset ℕ) (Φ : (ℕ → X → K) → O)
    (A : O → (K → X → K) → Prop) : ℝ :=
  pr (Coins K X N × (K → X → K)) (fun p => A (Φ (rowAt x N rep p.2 p.1.2 p.1.1)) p.2)

/-- The value of node `n` in an experiment where its parent is replaced (or it is the root): a
function of the coins. -/
def secretVal (n : ℕ) (hN : n < N) (c : Coins K X N) : K :=
  if n = 0 then c.1 else c.2 ⟨(n - 1) / 2, by omega⟩ (x n)

omit [Fintype K] [DecidableEq K] [Nonempty K] [Fintype X] [DecidableEq X] in
lemma keyAt_secret {rep : Finset ℕ} {n : ℕ} (hN : n < N) (hpar : n ≠ 0 → (n - 1) / 2 ∈ rep)
    (E : K → X → K) (c : Coins K X N) :
    keyAt x N rep E c.2 c.1 n = secretVal (x := x) n hN c := by
  unfold secretVal
  split_ifs with h0
  · subst h0; rfl
  · exact keyAt_of_par h0 (hpar h0) _

omit [Fintype K] [DecidableEq K] [Nonempty K] [Fintype X] [DecidableEq X] in
/-- **Identical until the secret value is read**: with the table programmed at node `n`'s value
by the row `u`, the experiment with `rep` is the one with `n` also replaced by `u`, unless another
non-replaced node below `N` has the same value. -/
lemma rowAt_program {rep : Finset ℕ} {n : ℕ} (hN : n < N) (hnr : n ∉ rep)
    (hpar : n ≠ 0 → (n - 1) / 2 ∈ rep) (E : K → X → K) (c : Coins K X N) (u : Unit → X → K)
    (hgood : ∀ m < N, m ∉ insert n rep →
      keyAt x N (insert n rep) E (Function.update c.2 ⟨n, hN⟩ (u ())) c.1 m ≠
        secretVal (x := x) n hN c) :
    ∀ m < N, rowAt x N rep (programAt (fun _ : Unit => secretVal (x := x) n hN c) u E) c.2 c.1 m =
        rowAt x N (insert n rep) E (Function.update c.2 ⟨n, hN⟩ (u ())) c.1 m ∧
      keyAt x N rep (programAt (fun _ : Unit => secretVal (x := x) n hN c) u E) c.2 c.1 m =
        keyAt x N (insert n rep) E (Function.update c.2 ⟨n, hN⟩ (u ())) c.1 m := by
  set v := secretVal (x := x) n hN c
  set E' := programAt (fun _ : Unit => v) u E
  set R' := Function.update c.2 ⟨n, hN⟩ (u ())
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro hm
    have hkey : keyAt x N rep E' c.2 c.1 m = keyAt x N (insert n rep) E R' c.1 m := by
      rcases Nat.eq_zero_or_pos m with rfl | hpos
      · rfl
      · rw [keyAt_pos (by omega), keyAt_pos (by omega), (ih _ (by omega) (by omega)).1]
    refine ⟨?_, hkey⟩
    by_cases hmr : m ∈ rep
    · have hmn : m ≠ n := fun h => hnr (h ▸ hmr)
      rw [rowAt_of_mem hmr hm, rowAt_of_mem (Finset.mem_insert_of_mem hmr) hm]
      exact (Function.update_of_ne (fun h => hmn (congrArg Fin.val h)) _ _).symm
    · by_cases hmn : m = n
      · subst hmn
        rw [rowAt_of_not_mem hmr, rowAt_of_mem (Finset.mem_insert_self _ _) hm,
          keyAt_secret hm hpar]
        simp only [R', Function.update_self]
        exact programAt_apply_pt (x := fun _ : Unit => v) (fun _ _ _ => rfl) u E ()
      · have hmi : m ∉ insert n rep := by simp [hmn, hmr]
        rw [rowAt_of_not_mem hmr, rowAt_of_not_mem hmi, hkey]
        exact programAt_apply_of_ne _ _ fun _ h => hgood m hm hmi h.symm

omit [Fintype K] [DecidableEq K] [Nonempty K] [Fintype X] [DecidableEq X] in
/-- With the root replaced, the root seed is not read. -/
lemma rowAt_seed_indep {rep : Finset ℕ} (h0 : 0 ∈ rep) (h0N : 0 < N) (E : K → X → K)
    (R : Fin N → X → K) (s s' : K) : ∀ m, rowAt x N rep E R s m = rowAt x N rep E R s' m ∧
      (m ≠ 0 → keyAt x N rep E R s m = keyAt x N rep E R s' m) := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    have hkey : m ≠ 0 → keyAt x N rep E R s m = keyAt x N rep E R s' m := fun hm => by
      rw [keyAt_pos hm, keyAt_pos hm, (ih _ (by omega)).1]
    refine ⟨?_, hkey⟩
    rw [rowAt_eq, rowAt_eq]
    split_ifs with h
    · rfl
    · have hm : m ≠ 0 := fun hm => h ⟨hm ▸ h0, hm ▸ h0N⟩
      rw [hkey hm]

omit [Fintype K] [DecidableEq K] [Nonempty K] [Fintype X] in
/-- With a node `n` and its parent `p` replaced, changing `p`'s row at `n`'s input changes no
other row and no other node's value. -/
lemma rowAt_point_indep {rep : Finset ℕ} {n : ℕ} (hnr : n ∈ rep) (hN : n < N)
    (hp : (n - 1) / 2 ∈ rep) (hsib : ∀ m, m ≠ 0 → m ≠ n → (m - 1) / 2 = (n - 1) / 2 → x m ≠ x n)
    (E : K → X → K) (R : Fin N → X → K) (seed : K) (k : K) :
    ∀ m, (m ≠ (n - 1) / 2 → rowAt x N rep E (Function.update R ⟨(n - 1) / 2, by omega⟩
        (Function.update (R ⟨(n - 1) / 2, by omega⟩) (x n) k)) seed m = rowAt x N rep E R seed m) ∧
      (m ≠ n → keyAt x N rep E (Function.update R ⟨(n - 1) / 2, by omega⟩
        (Function.update (R ⟨(n - 1) / 2, by omega⟩) (x n) k)) seed m = keyAt x N rep E R seed m) := by
  have hpN : (n - 1) / 2 < N := by omega
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    have hkey : m ≠ n → keyAt x N rep E (Function.update R ⟨(n - 1) / 2, hpN⟩
        (Function.update (R ⟨(n - 1) / 2, hpN⟩) (x n) k)) seed m = keyAt x N rep E R seed m := by
      intro hmn
      rcases Nat.eq_zero_or_pos m with rfl | hpos
      · rfl
      rw [keyAt_pos (by omega), keyAt_pos (by omega)]
      by_cases hq : (m - 1) / 2 = (n - 1) / 2
      · rw [hq, rowAt_of_mem hp hpN, rowAt_of_mem hp hpN, Function.update_self,
          Function.update_of_ne (hsib m (by omega) hmn hq)]
      · rw [(ih _ (by omega)).1 hq]
    refine ⟨fun hmp => ?_, hkey⟩
    rw [rowAt_eq, rowAt_eq]
    split_ifs with h
    · exact Function.update_of_ne (fun e => hmp (congrArg Fin.val e)) _ _
    · have hmn : m ≠ n := fun e => h ⟨e ▸ hnr, e ▸ hN⟩
      rw [hkey hmn]

omit [Fintype K] [DecidableEq K] [Nonempty K] [Fintype X] [DecidableEq X] in
lemma secretVal_update {n : ℕ} (hN : n < N) (c : Coins K X N) (u : X → K) :
    secretVal (x := x) n hN (c.1, Function.update c.2 ⟨n, hN⟩ u) = secretVal (x := x) n hN c := by
  unfold secretVal
  split_ifs with h0
  · rfl
  · exact congrFun (Function.update_of_ne (fun e => by
      have := congrArg Fin.val e; simp only at this; omega) _ _) _

/-- The coins with node `n`'s row taken from the answer `u`, and the old row moved to the answer
(an involution). -/
def swapRow {n : ℕ} (hN : n < N) :
    Coins K X N × ((K → X → K) × (Unit → X → K)) ≃ Coins K X N × ((K → X → K) × (Unit → X → K)) where
  toFun a := ((a.1.1, Function.update a.1.2 ⟨n, hN⟩ (a.2.2 ())), (a.2.1, fun _ => a.1.2 ⟨n, hN⟩))
  invFun a := ((a.1.1, Function.update a.1.2 ⟨n, hN⟩ (a.2.2 ())), (a.2.1, fun _ => a.1.2 ⟨n, hN⟩))
  left_inv a := by
    obtain ⟨⟨s, R⟩, g, u⟩ := a
    simp only [Function.update_self, Function.update_idem, Function.update_eq_self]
  right_inv a := by
    obtain ⟨⟨s, R⟩, g, u⟩ := a
    simp only [Function.update_self, Function.update_idem, Function.update_eq_self]

/-- The candidates for the secret value in the experiment with `ins` replaced: the values of the
non-replaced nodes below `N` and the keys `A` reads. -/
noncomputable def cands (x : ℕ → X) (N : ℕ) (ins : Finset ℕ) (Φ : (ℕ → X → K) → O)
    (Q : O → (K → X → K) → Finset K) (p : Coins K X N × (K → X → K)) : Finset K :=
  ((range N).filter (· ∉ ins)).image (fun m => keyAt x N ins p.2 p.1.2 p.1.1 m) ∪
    Q (Φ (rowAt x N ins p.2 p.1.2 p.1.1)) p.2

omit [Fintype K] [Nonempty K] [Fintype X] [DecidableEq X] in
lemma cands_card (ins : Finset ℕ) (Φ : (ℕ → X → K) → O) (Q : O → (K → X → K) → Finset K) {q : ℕ}
    (hq : ∀ o G, (Q o G).card ≤ q) (p : Coins K X N × (K → X → K)) :
    (cands x N ins Φ Q p).card ≤ N + q := by
  unfold cands
  refine (card_union_le _ _).trans (Nat.add_le_add ?_ (hq _ _))
  exact card_image_le.trans ((card_filter_le _ _).trans (card_range N).le)

/-- **The secret value is guessed with probability `≤ (N + q) / |K|`.** -/
lemma pr_secret_mem_cands {rep : Finset ℕ} {n : ℕ} (hN : n < N) (hpar : n ≠ 0 → (n - 1) / 2 ∈ rep)
    (hsib : n ≠ 0 → ∀ m, m ≠ 0 → m ≠ n → (m - 1) / 2 = (n - 1) / 2 → x m ≠ x n)
    (Φ : (ℕ → X → K) → O)
    (hΦ : n ≠ 0 → ∀ ρ y, Φ (Function.update ρ ((n - 1) / 2)
      (Function.update (ρ ((n - 1) / 2)) (x n) y)) = Φ ρ)
    (Q : O → (K → X → K) → Finset K) {q : ℕ} (hq : ∀ o G, (Q o G).card ≤ q) :
    pr (Coins K X N × (K → X → K)) (fun p => secretVal (x := x) n hN p.1 ∈
      cands x N (insert n rep) Φ Q p) ≤ (N + q : ℕ) / Fintype.card K := by
  have hin : n ∈ insert n rep := Finset.mem_insert_self _ _
  by_cases h0 : n = 0
  · subst h0
    refine pr_mem_reset_le (α := Coins K X N × (K → X → K)) (fun p => p.1.1)
      (fun p k => ((k, p.1.2), p.2)) (fun _ _ => rfl) (fun _ _ _ => rfl) (fun _ => rfl)
      (cands x N (insert 0 rep) Φ Q) (fun p k => ?_) (cands_card _ Φ Q hq)
    have hrow := fun m => (rowAt_seed_indep (x := x) hin hN p.2 p.1.2 k p.1.1 m)
    unfold cands
    congr 1
    · refine Finset.image_congr fun m hm => ?_
      have hm' : m ≠ 0 := fun e => (Finset.mem_filter.1 hm).2 (e ▸ hin)
      exact (hrow m).2 hm'
    · simp only
      rw [show rowAt x N (insert 0 rep) p.2 p.1.2 k = rowAt x N (insert 0 rep) p.2 p.1.2 p.1.1 from
        funext fun m => (hrow m).1]
  · have hp : (n - 1) / 2 ∈ insert n rep := Finset.mem_insert_of_mem (hpar h0)
    have hpN : (n - 1) / 2 < N := by omega
    have hpn : (n - 1) / 2 ≠ n := by omega
    let pf : Fin N := ⟨(n - 1) / 2, hpN⟩
    let st : Coins K X N × (K → X → K) → K → Coins K X N × (K → X → K) := fun p k =>
      ((p.1.1, Function.update p.1.2 pf (Function.update (p.1.2 pf) (x n) k)), p.2)
    have hf : ∀ p k, (st p k).1.2 pf (x n) = k := fun p k => by simp [st]
    have hss : ∀ p k k', st (st p k) k' = st p k' := fun p k k' => by simp [st]
    have hsf : ∀ p, st p (p.1.2 pf (x n)) = p := fun p => by simp [st]
    have hT : ∀ p k, cands x N (insert n rep) Φ Q (st p k) = cands x N (insert n rep) Φ Q p := by
      intro p k
      have hind := rowAt_point_indep (x := x) hin hN hp (hsib h0) p.2 p.1.2 p.1.1 k
      unfold cands
      congr 1
      · refine Finset.image_congr fun m hm => ?_
        have hm' : m ≠ n := fun e => (Finset.mem_filter.1 hm).2 (e ▸ hin)
        exact (hind m).2 hm'
      · simp only [st]
        have hρ : rowAt x N (insert n rep) p.2 (Function.update p.1.2 pf
            (Function.update (p.1.2 pf) (x n) k)) p.1.1 =
            Function.update (rowAt x N (insert n rep) p.2 p.1.2 p.1.1) ((n - 1) / 2)
              (Function.update (rowAt x N (insert n rep) p.2 p.1.2 p.1.1 ((n - 1) / 2)) (x n) k) := by
          funext m
          by_cases hm : m = (n - 1) / 2
          · subst hm
            rw [Function.update_self, rowAt_of_mem hp hpN, rowAt_of_mem hp hpN, Function.update_self]
          · rw [Function.update_of_ne hm, (hind m).1 hm]
        rw [hρ, hΦ h0]
    refine (le_of_eq (pr_congr fun p => ?_)).trans (pr_mem_reset_le (α := Coins K X N × (K → X → K))
      (fun p => p.1.2 pf (x n)) st hf hss hsf (cands x N (insert n rep) Φ Q) hT
      (cands_card _ Φ Q hq))
    simp only [secretVal, h0, ↓reduceIte]
    rfl

/-- **One hop**: replacing node `n` (its parent replaced, or the root) costs `(N + q) / |K|`. -/
theorem hop (rep : Finset ℕ) (n : ℕ) (hN : n < N) (hnr : n ∉ rep)
    (hpar : n ≠ 0 → (n - 1) / 2 ∈ rep)
    (hsib : n ≠ 0 → ∀ m, m ≠ 0 → m ≠ n → (m - 1) / 2 = (n - 1) / 2 → x m ≠ x n)
    (Φ : (ℕ → X → K) → O)
    (hΦ : n ≠ 0 → ∀ ρ y, Φ (Function.update ρ ((n - 1) / 2)
      (Function.update (ρ ((n - 1) / 2)) (x n) y)) = Φ ρ)
    (hΦN : ∀ ρ ρ', (∀ m < N, ρ m = ρ' m) → Φ ρ = Φ ρ')
    (A : O → (K → X → K) → Prop) (Q : O → (K → X → K) → Finset K)
    (hQ : ∀ o G G', (∀ k ∈ Q o G, G k = G' k) → (A o G ↔ A o G')) {q : ℕ}
    (hq : ∀ o G, (Q o G).card ≤ q) :
    |exper x N rep Φ A - exper x N (insert n rep) Φ A| ≤ (N + q : ℕ) / Fintype.card K := by
  classical
  let v : Coins K X N → K := secretVal (x := x) n hN
  let ins := insert n rep
  -- Programming the table at the secret value is perfect.
  have h1 : exper x N rep Φ A = pr (Coins K X N × ((K → X → K) × (Unit → X → K))) (fun p =>
      A (Φ (rowAt x N rep (programAt (fun _ : Unit => v p.1) p.2.2 p.2.1) p.1.2 p.1.1))
        (programAt (fun _ : Unit => v p.1) p.2.2 p.2.1)) :=
    pr_program_eq (ι := Unit) (x := fun c _ => v c) (fun _ _ _ _ => rfl)
      (fun c _ g => A (Φ (rowAt x N rep g c.2 c.1)) g)
  -- The experiment with `n` replaced by the answer.
  let B : Coins K X N × ((K → X → K) × (Unit → X → K)) → Prop := fun p =>
    A (Φ (rowAt x N ins p.2.1 (Function.update p.1.2 ⟨n, hN⟩ (p.2.2 ())) p.1.1)) p.2.1
  have h2 : pr _ B = exper x N ins Φ A := by
    have e := pr_equiv (swapRow (K := K) (X := X) hN)
      (fun p => A (Φ (rowAt x N ins p.2.1 p.1.2 p.1.1)) p.2.1)
    rw [pr_add_answers (fun p : Coins K X N × (K → X → K) =>
      A (Φ (rowAt x N ins p.2 p.1.2 p.1.1)) p.2)] at e
    exact e
  -- The bad event: the secret value is a candidate.
  let bad : Coins K X N × ((K → X → K) × (Unit → X → K)) → Prop := fun p =>
    v p.1 ∈ cands x N ins Φ Q ((p.1.1, Function.update p.1.2 ⟨n, hN⟩ (p.2.2 ())), p.2.1)
  have h3 : pr _ bad ≤ (N + q : ℕ) / Fintype.card K := by
    have e := pr_equiv (swapRow (K := K) (X := X) hN)
      (fun p => v p.1 ∈ cands x N ins Φ Q (p.1, p.2.1))
    rw [pr_add_answers (fun p : Coins K X N × (K → X → K) => v p.1 ∈ cands x N ins Φ Q p)] at e
    have e2 : pr _ bad = pr (Coins K X N × ((K → X → K) × (Unit → X → K)))
        (fun a => (fun p : Coins K X N × ((K → X → K) × (Unit → X → K)) =>
          v p.1 ∈ cands x N ins Φ Q (p.1, p.2.1)) (swapRow hN a)) :=
      pr_congr fun a => by
        show v a.1 ∈ _ ↔ v (a.1.1, Function.update a.1.2 ⟨n, hN⟩ (a.2.2 ())) ∈ _
        rw [show v (a.1.1, Function.update a.1.2 ⟨n, hN⟩ (a.2.2 ())) = v a.1 from
          secretVal_update hN a.1 _]
        rfl
    rw [e2, e]
    exact pr_secret_mem_cands hN hpar hsib Φ hΦ Q hq
  have h4 : ∀ p, ¬ bad p → ((A (Φ (rowAt x N rep (programAt (fun _ : Unit => v p.1) p.2.2 p.2.1)
      p.1.2 p.1.1)) (programAt (fun _ : Unit => v p.1) p.2.2 p.2.1)) ↔ B p) := by
    intro p hp
    have hgood : ∀ m < N, m ∉ ins → keyAt x N ins p.2.1 (Function.update p.1.2 ⟨n, hN⟩ (p.2.2 ()))
        p.1.1 m ≠ secretVal (x := x) n hN p.1 := fun m hm hmi e => hp (by
      show v p.1 ∈ cands x N ins Φ Q _
      unfold cands
      exact Finset.mem_union_left _ (Finset.mem_image.2 ⟨m, Finset.mem_filter.2
        ⟨Finset.mem_range.2 hm, hmi⟩, e⟩))
    have hrows := rowAt_program hN hnr hpar p.2.1 p.1 p.2.2 hgood
    rw [hΦN _ _ fun m hm => (hrows m hm).1]
    have hnq : v p.1 ∉ Q (Φ (rowAt x N ins p.2.1 (Function.update p.1.2 ⟨n, hN⟩ (p.2.2 ())) p.1.1))
        p.2.1 := fun h => hp (Finset.mem_union_right _ h)
    exact (hQ _ _ _ fun k hk => (programAt_apply_of_ne _ _ fun _ e => hnq (by rw [e]; exact hk)).symm).symm
  rw [h1, ← h2]
  exact (abs_pr_sub_le_of_agree _ _ bad h4).trans h3

/-- **The hybrid over the secret nodes**: for an upward-closed set `sec` of nodes (the hidden
paths; siblings with different inputs, and `Φ` not reading a secret node's value), replacing the
rows of all secret nodes below `N` by independent uniform rows costs `|sec| · (N + q) / |K|`
against a distinguisher that reads the table at `q` keys. -/
theorem puncture (sec : ℕ → Prop) [DecidablePred sec]
    (hup : ∀ n < N, sec n → n ≠ 0 → sec ((n - 1) / 2))
    (hsib : ∀ n < N, sec n → n ≠ 0 → ∀ m, m ≠ 0 → m ≠ n → (m - 1) / 2 = (n - 1) / 2 → x m ≠ x n)
    (Φ : (ℕ → X → K) → O)
    (hΦ : ∀ n < N, sec n → n ≠ 0 → ∀ ρ y, Φ (Function.update ρ ((n - 1) / 2)
      (Function.update (ρ ((n - 1) / 2)) (x n) y)) = Φ ρ)
    (hΦN : ∀ ρ ρ', (∀ m < N, ρ m = ρ' m) → Φ ρ = Φ ρ')
    (A : O → (K → X → K) → Prop) (Q : O → (K → X → K) → Finset K)
    (hQ : ∀ o G G', (∀ k ∈ Q o G, G k = G' k) → (A o G ↔ A o G')) {q : ℕ}
    (hq : ∀ o G, (Q o G).card ≤ q) :
    |exper x N ∅ Φ A - exper x N ((range N).filter sec) Φ A| ≤
      ((range N).filter sec).card * ((N + q : ℕ) / Fintype.card K) := by
  have key : ∀ j ≤ N, |exper x N ∅ Φ A - exper x N ((range j).filter sec) Φ A| ≤
      ((range j).filter sec).card * ((N + q : ℕ) / Fintype.card K) := by
    intro j
    induction j with
    | zero => intro _; simp
    | succ j ih =>
      intro hj
      have ih := ih (by omega)
      rw [Finset.range_add_one, Finset.filter_insert]
      split_ifs with hs
      · have hnot : j ∉ (range j).filter sec := by simp
        have h := hop ((range j).filter sec) j (by omega) hnot (fun h0 => Finset.mem_filter.2
            ⟨Finset.mem_range.2 (by omega), hup j (by omega) hs h0⟩) (hsib j (by omega) hs) Φ
          (hΦ j (by omega) hs) hΦN A Q hQ hq
        rw [Finset.card_insert_of_notMem hnot, Nat.cast_succ, add_mul, one_mul]
        have := abs_sub_le (exper x N ∅ Φ A) (exper x N ((range j).filter sec) Φ A)
          (exper x N (insert j ((range j).filter sec)) Φ A)
        linarith
      · exact ih
  exact key N le_rfl

omit [Fintype K] [DecidableEq K] [Nonempty K] [Fintype X] [DecidableEq X] in
/-- With nothing replaced, the replacement rows are not read. -/
lemma rowAt_empty (E : K → X → K) (R R' : Fin N → X → K) (s : K) :
    rowAt x N ∅ E R s = rowAt x N ∅ E R' s := by
  funext m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    rw [rowAt_of_not_mem (Finset.notMem_empty _), rowAt_of_not_mem (Finset.notMem_empty _)]
    rcases Nat.eq_zero_or_pos m with rfl | hpos
    · rfl
    · rw [keyAt_pos (by omega), keyAt_pos (by omega), ih _ (by omega)]

/-- `A`'s success on `G` of a uniform root seed and a uniform table (the real experiment). -/
noncomputable def realPr (G : K → (K → X → K) → O) (A : O → (K → X → K) → Prop) : ℝ :=
  pr (K × (K → X → K)) (fun p => A (G p.1 p.2) p.2)

/-- `A`'s success on `F` of a uniform `h` and an independent uniform table (the ideal experiment). -/
noncomputable def idealPr {H : Type} [Fintype H] (F : H → O) (A : O → (K → X → K) → Prop) : ℝ :=
  pr (H × (K → X → K)) (fun h => A (F h.1) h.2)

/-- **The real experiment** (nothing replaced) does not read the replacement rows. -/
theorem exper_empty (Φ : (ℕ → X → K) → O) (A : O → (K → X → K) → Prop) :
    exper x N ∅ Φ A = realPr (fun s E => Φ (rowAt x N ∅ E (fun _ _ => s) s)) A := by
  let e : Coins K X N × (K → X → K) ≃ (K × (K → X → K)) × (Fin N → X → K) :=
    { toFun := fun c => ((c.1.1, c.2), c.1.2)
      invFun := fun c => ((c.1.1, c.2), c.1.2)
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have h := pr_equiv e (fun c => A (Φ (rowAt x N ∅ c.1.2 (fun _ _ => c.1.1) c.1.1)) c.1.2)
  rw [pr_prod_fst (fun p : K × (K → X → K) => A (Φ (rowAt x N ∅ p.2 (fun _ _ => p.1) p.1)) p.2)] at h
  rw [realPr, ← h]
  refine pr_congr fun c => ?_
  show A (Φ (rowAt x N ∅ c.2 c.1.2 c.1.1)) c.2 ↔ _
  rw [rowAt_empty c.2 c.1.2 (fun _ _ => c.1.1) c.1.1]
  exact Iff.rfl

/-- An experiment whose output, for every table, has the law of `F` of a uniform `h`, is the
ideal experiment. -/
theorem exper_eq_of_close {H : Type} [Fintype H] (rep : Finset ℕ) (Φ : (ℕ → X → K) → O)
    (F : H → O) (hE : ∀ E : K → X → K, Close 0 (fun c : Coins K X N => Φ (rowAt x N rep E c.2 c.1)) F)
    (A : O → (K → X → K) → Prop) :
    exper x N rep Φ A = idealPr F A := by
  have h := Close.prod_left (X := fun (c : Coins K X N) (E : K → X → K) =>
      (Φ (rowAt x N rep E c.2 c.1), E)) (Y := fun (h : H) (E : K → X → K) => (F h, E))
    (fun E => (hE E).map fun o => (o, E)) (fun o => A o.1 o.2)
  exact sub_eq_zero.1 (abs_nonpos_iff.1 h)

omit [Fintype K] [DecidableEq K] [Nonempty K] [Fintype X] [DecidableEq X] in
/-- **In the fully replaced experiment the other rows read the replacement rows only at the
inputs of the non-secret children of replaced nodes** (and not the root seed). -/
lemma rowAt_congr_points {rep : Finset ℕ} (h0 : 0 ∈ rep) (E : K → X → K)
    (R R' : Fin N → X → K) (s s' : K)
    (hR : ∀ c < N, c ≠ 0 → c ∉ rep → ∀ hp : (c - 1) / 2 < N, (c - 1) / 2 ∈ rep →
      R ⟨(c - 1) / 2, hp⟩ (x c) = R' ⟨(c - 1) / 2, hp⟩ (x c)) :
    ∀ m < N, m ∉ rep → rowAt x N rep E R s m = rowAt x N rep E R' s' m ∧
      keyAt x N rep E R s m = keyAt x N rep E R' s' m := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro hm hmr
    have hm0 : m ≠ 0 := fun e => hmr (e ▸ h0)
    have hkey : keyAt x N rep E R s m = keyAt x N rep E R' s' m := by
      have hpN : (m - 1) / 2 < N := by omega
      by_cases hp : (m - 1) / 2 ∈ rep
      · rw [keyAt_of_par hm0 hp hpN, keyAt_of_par hm0 hp hpN]
        exact hR m hm hm0 hmr hpN hp
      · rw [keyAt_pos hm0, keyAt_pos hm0, (ih _ (by omega) hpN hp).1]
    exact ⟨by rw [rowAt_of_not_mem hmr, rowAt_of_not_mem hmr, hkey], hkey⟩

end Hop

end VoleMole.ZK.IC
