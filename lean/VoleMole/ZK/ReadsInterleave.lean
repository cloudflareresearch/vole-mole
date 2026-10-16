import VoleMole.ZK.AdaptRO

/-!
# Interleaved honest sessions are one consistent table reader

The adaptive many-session games (`Privacy/PomFRITAdaptive.lean`, `Privacy/MoussakaAdaptive.lean`,
`Privacy/RatatouilleAdaptive.lean`) run each further session to the end before the next starts,
so `SReads.bind` composes them. Here the sessions are **interleaved by an adaptive scheduler**: at
each step the scheduler, a function of everything it has seen, either starts a new honest session
with an input of its choice or delivers a message to a pending session, and sees the result. An
honest session's state is its own randomness (its index selects its tape) and the messages it has
received so far; its output after receiving `h` is `out j c h t` on the tables `t`.

* *The model* (`Act`, `Ev`, `sessSt`, `resO`, `stepT`, `runT`): a transcript is a list of the
  scheduler's actions with their results and of external events (the challenge's messages, which
  the games insert). The sessions' states are read off the actions (`sessSt`: at most `n`
  sessions; a start beyond `n`, or a message to a session that does not exist, is refused with
  `none`). `runT L` runs `L` steps.
* *The sessions' hypothesis* (`SessReads out Q`): each session's output after `h` is a consistent
  reader with read set `Q j c h t`, and the read set grows with the messages (`Q j c h ⊆
  Q j c (h ++ [m])`). This is what makes the count **per session**, not per step: a session that
  receives a message re-reads nothing new beyond its next step's keys.
* **The interleaving lemma** (`Good.run`, `Good.sreads`): a transcript-valued function built from
  constants, external events and steps (`Good.const`, `Good.ext`, `Good.step`) depends on the
  tables only through the union of the sessions' current read sets (`RQl`), consistently; so it is
  `SReads` with `n` times the per-session budget (`Good.sreads`), whatever the schedule, the fuel
  or the interleaving. The read sets themselves are available (`Good.cons`, `card_RQl`) for other
  counts (the prefix count of `Privacy/PomFRITAdaptivePfx.lean`).

The scheduler here reads no table (it is a function of the transcript), as the adaptive games'
interactions are; the sessions run inside it do.
-/

open Finset

set_option linter.unusedSectionVars false

namespace VoleMole.ZK.Sim

open VoleMole.Verifier VoleMole.Verifier.Bridge VoleMole.Arith VoleMole.ZK VoleMole.Privacy

section Interleave

/-- **A scheduler's action**: start the next session with input `c`, or deliver `m` to session
`j`. -/
inductive Act (C M : Type) where
  | start (c : C)
  | send (j : ℕ) (m : M)

/-- **A transcript entry**: an action and its result (`none` if refused), or an external event. -/
inductive Ev (C M O E : Type) where
  | act (a : Act C M) (o : Option O)
  | ext (e : E)

variable {R : Type} {p : Params} {C M O E : Type}

/-! ## The run -/

section Run

variable (n : ℕ)

/-- **The sessions' states after one more entry**: a start adds a session (if fewer than `n`), a
delivered message is appended to its session's messages. -/
def updS (S : List (C × List M)) : Ev C M O E → List (C × List M)
  | .act (.start c) _ => if S.length < n then S ++ [(c, [])] else S
  | .act (.send j m) _ => if h : j < S.length then S.set j (S[j].1, S[j].2 ++ [m]) else S
  | .ext _ => S

/-- **The sessions' states**: input and messages received, in the order they were started. -/
def sessSt (tr : List (Ev C M O E)) : List (C × List M) := tr.foldl (updS n) []

lemma sessSt_append (tr : List (Ev C M O E)) (e : Ev C M O E) :
    sessSt n (tr ++ [e]) = updS n (sessSt n tr) e := by
  simp [sessSt, List.foldl_append]

lemma updS_length_le {S : List (C × List M)} (hS : S.length ≤ n) (e : Ev C M O E) :
    (updS n S e).length ≤ n := by
  rcases e with ⟨a, o⟩ | e
  · rcases a with c | ⟨j, m⟩
    · simp only [updS]
      split_ifs with h
      · simp only [List.length_append, List.length_singleton]; omega
      · exact hS
    · simp only [updS]
      split_ifs with h
      · simpa using hS
      · exact hS
  · exact hS

lemma foldl_updS_length_le (tr : List (Ev C M O E)) :
    ∀ S : List (C × List M), S.length ≤ n → (tr.foldl (updS n) S).length ≤ n := by
  induction tr with
  | nil => exact fun S h => h
  | cons e tr ih => exact fun S h => ih _ (updS_length_le n h e)

/-- **At most `n` sessions.** -/
lemma sessSt_length_le (tr : List (Ev C M O E)) : (sessSt n tr).length ≤ n :=
  foldl_updS_length_le n tr [] (Nat.zero_le _)

variable (out : ℕ → C → List M → Tb R p → O)

/-- **The result of an action** on the tables `t`: a new session's first output, or a session's
output on its messages and the new one; `none` if refused. -/
def resO (S : List (C × List M)) (a : Act C M) (t : Tb R p) : Option O :=
  match a with
  | .start c => if S.length < n then some (out S.length c [] t) else none
  | .send j m => if h : j < S.length then some (out j S[j].1 (S[j].2 ++ [m]) t) else none

variable (next : List (Ev C M O E) → Act C M)

/-- **One step**: the scheduler's next action, chosen from the transcript, and its result. -/
def stepT (tr : List (Ev C M O E)) (t : Tb R p) : List (Ev C M O E) :=
  tr ++ [.act (next tr) (resO n out (sessSt n tr) (next tr) t)]

/-- **`L` steps.** -/
def runT : ℕ → List (Ev C M O E) → Tb R p → List (Ev C M O E)
  | 0, tr, _ => tr
  | L + 1, tr, t => runT L (stepT n out next tr t) t

variable {n out next}

/-- The run sees the tables only through the sessions' outputs. -/
lemma runT_congr_out {t t' : Tb R p} (h : ∀ j c hs, out j c hs t' = out j c hs t) :
    ∀ L tr, runT n out next L tr t' = runT n out next L tr t := by
  have hr : ∀ S a, resO n out S a t' = resO n out S a t := fun S a => by
    cases a <;> simp only [resO, h]
  intro L
  induction L with
  | zero => intro tr; rfl
  | succ L ih => intro tr; simp only [runT, stepT, hr, ih]

end Run

/-! ## Read sets -/

section RS

/-- `r` is contained in `r'`, table by table. -/
def RS.Le (r r' : RS p) : Prop :=
  r.1 ⊆ r'.1 ∧ r.2.1 ⊆ r'.2.1 ∧ r.2.2.1 ⊆ r'.2.2.1 ∧ r.2.2.2 ⊆ r'.2.2.2

lemma RS.Le.refl (r : RS p) : RS.Le r r := ⟨subset_rfl, subset_rfl, subset_rfl, subset_rfl⟩

lemma RS.Le.trans {r r' r'' : RS p} (h : RS.Le r r') (h' : RS.Le r' r'') : RS.Le r r'' :=
  ⟨h.1.trans h'.1, h.2.1.trans h'.2.1, h.2.2.1.trans h'.2.2.1, h.2.2.2.trans h'.2.2.2⟩

lemma RS.le_union_left (r r' : RS p) : RS.Le r (r.union r') :=
  ⟨subset_union_left, subset_union_left, subset_union_left, subset_union_left⟩

lemma RS.le_union_right (r r' : RS p) : RS.Le r' (r.union r') :=
  ⟨subset_union_right, subset_union_right, subset_union_right, subset_union_right⟩

lemma RS.union_le_union {r r' u u' : RS p} (h : RS.Le r u) (h' : RS.Le r' u') :
    RS.Le (r.union r') (u.union u') :=
  ⟨union_subset_union h.1 h'.1, union_subset_union h.2.1 h'.2.1, union_subset_union h.2.2.1 h'.2.2.1,
    union_subset_union h.2.2.2 h'.2.2.2⟩

lemma RS.empty_le (r : RS p) : RS.Le ((∅, ∅, ∅, ∅) : RS p) r :=
  ⟨empty_subset _, empty_subset _, empty_subset _, empty_subset _⟩

lemma AgT.mono {r r' : RS p} {t t' : Tb R p} (h : RS.Le r r') (ha : AgT r' t t') : AgT r t t' :=
  ⟨fun k hk => ha.1 k (h.1 hk), fun k hk => ha.2.1 k (h.2.1 hk), fun k hk => ha.2.2.1 k (h.2.2.1 hk),
    fun k hk => ha.2.2.2 k (h.2.2.2 hk)⟩

variable (Q : ℕ → C → List M → Tb R p → RS p)

/-- **The sessions' read sets**: the union of each session's current read set (session `k + i` at
position `i`). -/
def RQl (t : Tb R p) : ℕ → List (C × List M) → RS p
  | _, [] => (∅, ∅, ∅, ∅)
  | k, x :: S => (Q k x.1 x.2 t).union (RQl t (k + 1) S)

variable {Q}

lemma le_RQl (t : Tb R p) : ∀ (S : List (C × List M)) (k j : ℕ) (h : j < S.length),
    RS.Le (Q (k + j) S[j].1 S[j].2 t) (RQl Q t k S) := by
  intro S
  induction S with
  | nil => intro k j h; simp at h
  | cons x S ih =>
    intro k j h
    cases j with
    | zero => exact RS.le_union_left _ _
    | succ j =>
      have e : k + (j + 1) = k + 1 + j := by omega
      simp only [List.getElem_cons_succ, e]
      exact (ih (k + 1) j (by simpa using h)).trans (RS.le_union_right _ _)

lemma RQl_le_append (t : Tb R p) (x : C × List M) : ∀ (S : List (C × List M)) (k : ℕ),
    RS.Le (RQl Q t k S) (RQl Q t k (S ++ [x])) := by
  intro S
  induction S with
  | nil => intro k; exact RS.empty_le _
  | cons y S ih => intro k; exact RS.union_le_union (RS.Le.refl _) (ih (k + 1))

lemma RQl_le_set (t : Tb R p) (x : C × List M) : ∀ (S : List (C × List M)) (k j : ℕ)
    (h : j < S.length), RS.Le (Q (k + j) S[j].1 S[j].2 t) (Q (k + j) x.1 x.2 t) →
    RS.Le (RQl Q t k S) (RQl Q t k (S.set j x)) := by
  intro S
  induction S with
  | nil => intro k j h; simp at h
  | cons y S ih =>
    intro k j h hle
    cases j with
    | zero => exact RS.union_le_union hle (RS.Le.refl _)
    | succ j =>
      have e : k + (j + 1) = k + 1 + j := by omega
      simp only [List.getElem_cons_succ, e] at hle
      exact RS.union_le_union (RS.Le.refl _) (ih (k + 1) j (by simpa using h) hle)

lemma RQl_congr {t t' : Tb R p} : ∀ (S : List (C × List M)) (k : ℕ),
    (∀ j (h : j < S.length), Q (k + j) S[j].1 S[j].2 t' = Q (k + j) S[j].1 S[j].2 t) →
    RQl Q t' k S = RQl Q t k S := by
  intro S
  induction S with
  | nil => intro k _; rfl
  | cons y S ih =>
    intro k h
    have h0 := h 0 (by simp)
    simp only [Nat.add_zero, List.getElem_cons_zero] at h0
    have h1 := ih (k + 1) fun j hj => by
      have := h (j + 1) (by simpa using hj)
      simpa [show k + (j + 1) = k + 1 + j by omega] using this
    simp only [RQl, h0, h1]

/-- **The sessions' read sets count `|S|` times a session's**, for any measure that turns unions
into unions (a table's keys, or `H₂³`'s prefixes). -/
lemma card_RQl {κ : Type*} [DecidableEq κ] (f : RS p → Finset κ)
    (hf : ∀ r r', f (r.union r') = f r ∪ f r') (h0 : f ((∅, ∅, ∅, ∅) : RS p) = ∅) {b : ℕ}
    (t : Tb R p) (hb : ∀ j c h, (f (Q j c h t)).card ≤ b) :
    ∀ (S : List (C × List M)) (k : ℕ), (f (RQl Q t k S)).card ≤ S.length * b := by
  intro S
  induction S with
  | nil => intro k; simp [RQl, h0]
  | cons y S ih =>
    intro k
    simp only [RQl, hf, List.length_cons, Nat.succ_mul]
    exact (card_union_le _ _).trans (by have := ih (k + 1); have := hb k y.1 y.2; omega)

end RS

/-! ## The interleaving lemma -/

section Good

variable {n : ℕ} {out : ℕ → C → List M → Tb R p → O} {Q : ℕ → C → List M → Tb R p → RS p}
  {next : List (Ev C M O E) → Act C M}

/-- **The sessions are stateful consistent readers**: a session's output after the messages `h` is
read off its read set `Q j c h t` (consistently), and the read set grows with the messages. -/
structure SessReads (out : ℕ → C → List M → Tb R p → O) (Q : ℕ → C → List M → Tb R p → RS p) :
    Prop where
  cons : ∀ j c h (t t' : Tb R p), AgT (Q j c h t) t t' → Q j c h t' = Q j c h t ∧ out j c h t' = out j c h t
  mono : ∀ j c h m (t : Tb R p), RS.Le (Q j c h t) (Q j c (h ++ [m]) t)

variable (n Q) in
/-- **A transcript-valued function read off the sessions' read sets**: two tables that agree on
the union of the sessions' read sets at `t` (`RQl`, the sessions' states read off `F t`) give the
same transcript. -/
def Good (F : Tb R p → List (Ev C M O E)) : Prop :=
  ∀ t t', AgT (RQl Q t 0 (sessSt n (F t))) t t' → F t' = F t

lemma RQl_cons (hS : SessReads out Q) {t t' : Tb R p} (S : List (C × List M))
    (h : AgT (RQl Q t 0 S) t t') : RQl Q t' 0 S = RQl Q t 0 S :=
  RQl_congr S 0 fun j hj => (hS.cons _ _ _ t t' (AgT.mono (le_RQl t S 0 j hj) h)).1

lemma RQl_le_upd (hS : SessReads out Q) (t : Tb R p) (S : List (C × List M)) (a : Act C M)
    (o : Option O) : RS.Le (RQl Q t 0 S) (RQl Q t 0 (updS n S (.act a o : Ev C M O E))) := by
  cases a with
  | start c =>
    simp only [updS]
    split_ifs
    · exact RQl_le_append t _ S 0
    · exact RS.Le.refl _
  | send j m =>
    simp only [updS]
    split_ifs with hj
    · exact RQl_le_set t _ S 0 j hj (hS.mono _ _ _ _ _)
    · exact RS.Le.refl _

lemma resO_congr (hS : SessReads out Q) {t t' : Tb R p} (S : List (C × List M)) (a : Act C M)
    (o : Option O) (h : AgT (RQl Q t 0 (updS n S (.act a o : Ev C M O E))) t t') :
    resO n out S a t' = resO n out S a t := by
  cases a with
  | start c =>
    simp only [resO]
    by_cases hl : S.length < n
    · simp only [updS, hl, ↓reduceIte] at h
      have hm := le_RQl (Q := Q) t (S ++ [(c, [])]) 0 S.length (by simp)
      simp only [Nat.zero_add, List.getElem_append_right (Nat.le_refl _), Nat.sub_self,
        List.getElem_cons_zero] at hm
      simp only [hl, ↓reduceIte, (hS.cons _ _ _ t t' (AgT.mono hm h)).2]
    · simp only [hl, ↓reduceIte]
  | send j m =>
    simp only [resO]
    by_cases hj : j < S.length
    · simp only [updS, hj, dite_true] at h
      have hm := le_RQl (Q := Q) t (S.set j (S[j].1, S[j].2 ++ [m])) 0 j (by simpa using hj)
      simp only [Nat.zero_add, List.getElem_set_self] at hm
      simp only [hj, dite_true, (hS.cons _ _ _ t t' (AgT.mono hm h)).2]
    · simp only [hj, dite_false]

/-- A constant transcript is read off nothing. -/
lemma Good.const (tr : List (Ev C M O E)) : Good n Q (fun _ : Tb R p => tr) := fun _ _ _ => rfl

/-- **An external event** changes no session. -/
lemma Good.ext {F : Tb R p → List (Ev C M O E)} (hF : Good n Q F) (e : E) :
    Good n Q (fun t => F t ++ [.ext e]) := by
  intro t t' h
  rw [sessSt_append] at h
  show F t' ++ _ = F t ++ _
  rw [hF t t' h]

/-- **One step of the scheduler**: the step's session reads its new read set, which contains its
old one, so the transcript before the step is read off it as well. -/
lemma Good.step (hS : SessReads out Q) {F : Tb R p → List (Ev C M O E)} (hF : Good n Q F) :
    Good n Q (fun t => stepT n out next (F t) t) := by
  intro t t' h
  simp only [stepT, sessSt_append] at h ⊢
  have e := hF t t' (AgT.mono (RQl_le_upd hS t _ _ _) h)
  rw [e, resO_congr hS _ _ _ (by rw [← e] at h ⊢; exact h)]

/-- **The interleaving lemma**: any number of steps of any scheduler, after any good start. -/
lemma Good.run (hS : SessReads out Q) :
    ∀ (L : ℕ) {F : Tb R p → List (Ev C M O E)}, Good n Q F → Good n Q (fun t => runT n out next L (F t) t) := by
  intro L
  induction L with
  | zero => intro F hF; exact hF
  | succ L ih => intro F hF; exact ih (hF.step hS)

/-- **A good transcript is consistent, with the sessions' read sets** (for other counts than
`Good.sreads`'). -/
lemma Good.cons (hS : SessReads out Q) {F : Tb R p → List (Ev C M O E)} (hF : Good n Q F)
    (t t' : Tb R p) (h : AgT (RQl Q t 0 (sessSt n (F t))) t t') :
    RQl Q t' 0 (sessSt n (F t')) = RQl Q t 0 (sessSt n (F t)) ∧ F t' = F t := by
  have e := hF t t' h
  exact ⟨by rw [e]; exact RQl_cons hS _ h, e⟩

/-- **Interleaved sessions are a consistent reader with summed budgets**: `n` sessions of budget
`(b₃, b₂, b₅, b_E)` each, under any schedule. -/
theorem Good.sreads (hS : SessReads out Q) {F : Tb R p → List (Ev C M O E)} (hF : Good n Q F)
    {b3 b2 b5 bE : ℕ}
    (hb : ∀ j c h t, (Q j c h t).1.card ≤ b3 ∧ (Q j c h t).2.1.card ≤ b2 ∧ (Q j c h t).2.2.1.card ≤ b5 ∧
      (Q j c h t).2.2.2.card ≤ bE) :
    SReads p F (n * b3) (n * b2) (n * b5) (n * bE) := by
  classical
  refine ⟨fun t => RQl Q t 0 (sessSt n (F t)), fun t t' h => hF.cons hS t t' h, fun t => ?_⟩
  have hl := sessSt_length_le n (F t)
  have c1 := card_RQl (Q := Q) (fun r => r.1) (fun _ _ => rfl) rfl t (fun j c h => (hb j c h t).1)
    (sessSt n (F t)) 0
  have c2 := card_RQl (Q := Q) (fun r => r.2.1) (fun _ _ => rfl) rfl t (fun j c h => (hb j c h t).2.1)
    (sessSt n (F t)) 0
  have c3 := card_RQl (Q := Q) (fun r => r.2.2.1) (fun _ _ => rfl) rfl t
    (fun j c h => (hb j c h t).2.2.1) (sessSt n (F t)) 0
  have c4 := card_RQl (Q := Q) (fun r => r.2.2.2) (fun _ _ => rfl) rfl t
    (fun j c h => (hb j c h t).2.2.2) (sessSt n (F t)) 0
  exact ⟨c1.trans (Nat.mul_le_mul_right _ hl), c2.trans (Nat.mul_le_mul_right _ hl),
    c3.trans (Nat.mul_le_mul_right _ hl), c4.trans (Nat.mul_le_mul_right _ hl)⟩

end Good

/-! ## Sessions as chains of consistent readers -/

section Chain

variable {St : Type}

/-- The state of a chain after the messages `h`, from state `σ` at step `i`. -/
def chainGo (step : ℕ → M → St → Tb R p → St) (t : Tb R p) : ℕ → St → List M → St
  | _, σ, [] => σ
  | i, σ, m :: h => chainGo step t (i + 1) (step i m σ t) h

lemma chainGo_congr {step : ℕ → M → St → Tb R p → St} {t t' : Tb R p}
    (h : ∀ i m σ, step i m σ t' = step i m σ t) :
    ∀ (hs : List M) (i : ℕ) (σ : St), chainGo step t' i σ hs = chainGo step t i σ hs := by
  intro hs
  induction hs with
  | nil => intro i σ; rfl
  | cons m hs ih => intro i σ; simp only [chainGo, h, ih]

/-- The read sets of a chain after the messages `h`, accumulated onto `acc`. -/
def chainGoQ (step : ℕ → M → St → Tb R p → St) (Qs : ℕ → M → St → Tb R p → RS p) (t : Tb R p) :
    ℕ → St → RS p → List M → RS p
  | _, _, acc, [] => acc
  | i, σ, acc, m :: h => chainGoQ step Qs t (i + 1) (step i m σ t) (acc.union (Qs i m σ t)) h

lemma chainGo_append (step : ℕ → M → St → Tb R p → St) (t : Tb R p) (m : M) :
    ∀ (h : List M) (i : ℕ) (σ : St),
      chainGo step t i σ (h ++ [m]) = step (i + h.length) m (chainGo step t i σ h) t := by
  intro h
  induction h with
  | nil => intro i σ; simp [chainGo]
  | cons m' h ih =>
    intro i σ
    simp only [List.cons_append, chainGo, ih, List.length_cons]
    congr 1
    omega

lemma chainGoQ_append (step : ℕ → M → St → Tb R p → St) (Qs : ℕ → M → St → Tb R p → RS p)
    (t : Tb R p) (m : M) : ∀ (h : List M) (i : ℕ) (σ : St) (acc : RS p),
      chainGoQ step Qs t i σ acc (h ++ [m]) =
        (chainGoQ step Qs t i σ acc h).union (Qs (i + h.length) m (chainGo step t i σ h) t) := by
  intro h
  induction h with
  | nil => intro i σ acc; simp [chainGoQ, chainGo]
  | cons m' h ih =>
    intro i σ acc
    simp only [List.cons_append, chainGoQ, chainGo, ih, List.length_cons,
      show i + (h.length + 1) = i + 1 + h.length by omega]

/-- **A session as a chain**: its state starts at `init` (a consistent reader with read sets `Qi`)
and each message `m` moves it by `step i m` (a consistent reader with read sets `Qs i m σ` at each
state `σ`); its read set after `h` is the union of the steps' read sets along the run. -/
structure ChainCons (init : Tb R p → St) (step : ℕ → M → St → Tb R p → St) (Qi : Tb R p → RS p)
    (Qs : ℕ → M → St → Tb R p → RS p) : Prop where
  init : ∀ t t', AgT (Qi t) t t' → Qi t' = Qi t ∧ init t' = init t
  step : ∀ i m σ t t', AgT (Qs i m σ t) t t' → Qs i m σ t' = Qs i m σ t ∧ step i m σ t' = step i m σ t

/-- **A chain is read off its accumulated read sets.** -/
lemma ChainCons.cons {init : Tb R p → St} {step : ℕ → M → St → Tb R p → St} {Qi : Tb R p → RS p}
    {Qs : ℕ → M → St → Tb R p → RS p} (hC : ChainCons init step Qi Qs) (h : List M) :
    ∀ t t', AgT (chainGoQ step Qs t 0 (init t) (Qi t) h) t t' →
      chainGoQ step Qs t' 0 (init t') (Qi t') h = chainGoQ step Qs t 0 (init t) (Qi t) h ∧
        chainGo step t' 0 (init t') h = chainGo step t 0 (init t) h := by
  induction h using List.reverseRecOn with
  | nil =>
    intro t t' hA
    obtain ⟨e1, e2⟩ := hC.init t t' hA
    exact ⟨e1, by simp only [chainGo, e2]⟩
  | append_singleton h m ih =>
    intro t t' hA
    rw [chainGoQ_append] at hA
    obtain ⟨e1, e2⟩ := ih t t' hA.left
    obtain ⟨e3, e4⟩ := hC.step _ _ _ t t' hA.right
    refine ⟨?_, ?_⟩
    · rw [chainGoQ_append, chainGoQ_append, e1, e2, e3]
    · rw [chainGo_append, chainGo_append, e2, e4]

lemma chainGoQ_le_append (step : ℕ → M → St → Tb R p → St) (Qs : ℕ → M → St → Tb R p → RS p)
    (t : Tb R p) (σ : St) (acc : RS p) (h : List M) (m : M) :
    RS.Le (chainGoQ step Qs t 0 σ acc h) (chainGoQ step Qs t 0 σ acc (h ++ [m])) := by
  rw [chainGoQ_append]
  exact RS.le_union_left _ _

/-- **A chain's read sets count the initial reader once and each step once.** -/
lemma card_chainGoQ {κ : Type*} [DecidableEq κ] (f : RS p → Finset κ)
    (hf : ∀ r r', f (r.union r') = f r ∪ f r') (step : ℕ → M → St → Tb R p → St)
    (Qs : ℕ → M → St → Tb R p → RS p) (t : Tb R p) {a b : ℕ}
    (hs : ∀ i m σ, (f (Qs i m σ t)).card ≤ b) (σ : St) (acc : RS p) (ha : (f acc).card ≤ a) :
    ∀ h : List M, (f (chainGoQ step Qs t 0 σ acc h)).card ≤ a + h.length * b := by
  intro h
  induction h using List.reverseRecOn with
  | nil => simpa [chainGoQ] using ha
  | append_singleton h m ih =>
    rw [chainGoQ_append, hf]
    refine (card_union_le _ _).trans ?_
    have := hs (0 + h.length) m (chainGo step t 0 σ h)
    simp only [List.length_append, List.length_singleton, Nat.add_mul, Nat.one_mul]
    omega

/-- **A chain of at most `K` steps is a stateful consistent reader**: session `j` with input `c`
reads off the first `K` messages it received (later ones are ignored), its output is `outp` of its
state. -/
theorem ChainCons.sessReads {init : ℕ → C → Tb R p → St} {step : ℕ → C → ℕ → M → St → Tb R p → St}
    {Qi : ℕ → C → Tb R p → RS p} {Qs : ℕ → C → ℕ → M → St → Tb R p → RS p}
    (hC : ∀ j c, ChainCons (init j c) (step j c) (Qi j c) (Qs j c)) (outp : St → O) (K : ℕ) :
    SessReads (fun j c h t => outp (chainGo (step j c) t 0 (init j c t) (h.take K)))
      (fun j c h t => chainGoQ (step j c) (Qs j c) t 0 (init j c t) (Qi j c t) (h.take K)) where
  cons j c h t t' hA := by
    obtain ⟨e1, e2⟩ := (hC j c).cons (h.take K) t t' hA
    exact ⟨e1, by rw [e2]⟩
  mono j c h m t := by
    rw [List.take_append]
    by_cases hl : h.length < K
    · have e : [m].take (K - h.length) = [m] := List.take_of_length_le (by simp; omega)
      rw [e]
      exact chainGoQ_le_append _ _ t _ _ _ m
    · have e : K - h.length = 0 := by omega
      rw [e, List.take_zero, List.append_nil]
      exact RS.Le.refl _

/-- **A chain of at most `K` steps reads its initial reader's keys and `K` steps' keys.** -/
lemma chain_card (step : ℕ → M → St → Tb R p → St) (Qs : ℕ → M → St → Tb R p → RS p)
    (Qi : Tb R p → RS p) (t : Tb R p) (K : ℕ) {a3 a2 a5 aE b3 b2 b5 bE : ℕ}
    (hi : (Qi t).1.card ≤ a3 ∧ (Qi t).2.1.card ≤ a2 ∧ (Qi t).2.2.1.card ≤ a5 ∧ (Qi t).2.2.2.card ≤ aE)
    (hs : ∀ i m σ, (Qs i m σ t).1.card ≤ b3 ∧ (Qs i m σ t).2.1.card ≤ b2 ∧
      (Qs i m σ t).2.2.1.card ≤ b5 ∧ (Qs i m σ t).2.2.2.card ≤ bE) (σ : St) (h : List M) :
    (chainGoQ step Qs t 0 σ (Qi t) (h.take K)).1.card ≤ a3 + K * b3 ∧
      (chainGoQ step Qs t 0 σ (Qi t) (h.take K)).2.1.card ≤ a2 + K * b2 ∧
      (chainGoQ step Qs t 0 σ (Qi t) (h.take K)).2.2.1.card ≤ a5 + K * b5 ∧
      (chainGoQ step Qs t 0 σ (Qi t) (h.take K)).2.2.2.card ≤ aE + K * bE := by
  classical
  have hl : (h.take K).length ≤ K := List.length_take_le _ _
  have c1 := card_chainGoQ (fun r => r.1) (fun _ _ => rfl) step Qs t (fun i m σ => (hs i m σ).1) σ
    (Qi t) hi.1 (h.take K)
  have c2 := card_chainGoQ (fun r => r.2.1) (fun _ _ => rfl) step Qs t (fun i m σ => (hs i m σ).2.1)
    σ (Qi t) hi.2.1 (h.take K)
  have c3 := card_chainGoQ (fun r => r.2.2.1) (fun _ _ => rfl) step Qs t
    (fun i m σ => (hs i m σ).2.2.1) σ (Qi t) hi.2.2.1 (h.take K)
  have c4 := card_chainGoQ (fun r => r.2.2.2) (fun _ _ => rfl) step Qs t
    (fun i m σ => (hs i m σ).2.2.2) σ (Qi t) hi.2.2.2 (h.take K)
  exact ⟨c1.trans (by have := Nat.mul_le_mul_right b3 hl; omega),
    c2.trans (by have := Nat.mul_le_mul_right b2 hl; omega),
    c3.trans (by have := Nat.mul_le_mul_right b5 hl; omega),
    c4.trans (by have := Nat.mul_le_mul_right bE hl; omega)⟩

end Chain

end Interleave

end VoleMole.ZK.Sim
