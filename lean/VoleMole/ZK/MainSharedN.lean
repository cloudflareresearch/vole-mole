import VoleMole.ZK.MainSharedAll

/-!
# The joint hop on `main` for `n` proofs, all tables shared (`lean/docs/zk.md` §4.2)

`main_sharedAll_le` (`ZK/MainSharedAll.lean`) replaces **four** `main`-layout proofs that share all
tables (one `H₃`, one `H₂³` table, one `H₅` table, one cipher) by simulated ones. Its reduction
writes per-proof `H₃` slices into the columns of the one table at prefixes computed from the view;
it does not see the provers' `ρ`, so two proofs with one prefix cost a whole extra term. Here the
joint hop is done again, **for `n` proofs** and **directly on the shared tables**:

* **The game** (`NGame`, `runN`, `viewN`). Slot `i`'s statement and witness are a function of the
  secret and the outputs of the earlier slots. A slot is described by what it does on its
  statement (`SlotF`): its programming of `H₂³`, its output as a function of the `H₂³` table it
  reads, and the keys at which it reads `H₅` and the cipher. The slots run in sequence; slot `i`
  reads the raw `H₂³` table with the earlier slots' programmings applied, the earliest outermost
  (as in `ZK/MainShared23.lean`). The adversary's view (`NView`) is the secret, the shared `H₅`
  table and cipher, the programmed `H₂³` table, the one `H₃` table `T`, and the outputs. The real
  prover (`realF`) reads the column of `T` at its prefix `wPrefix ‖ μ₁` (`preOf`), the simulator
  (`simF`) programs `H₂³` and reads no `H₃`.
* **The hop** (`hopN`). In hybrid `j` (`hybN j`) the slots before `j` are simulated and the others
  real. Replacing slot `j` is `slot_zk_main` with the column of `T` at slot `j`'s prefix as the
  proof's `H₃` slice and the rest of the game as the distinguisher. **The later real proofs with
  the same prefix read that column at their own `ρ`** (`realROb_g3_congr'`): these are `n` more
  `H₃` reads of the distinguisher, so a prefix collision costs a `ρ` collision, `n·2⁻¹²⁸` per hop
  inside `εS`, instead of a separate term. The earlier simulations' programmings cost `Δ23N`
  (`pr_collide_main` with at most `n` earlier tails).
* **The bad event** (`bstarN`) is `bstar` of `ZK/MainSharedGame.lean` for `n` slots: some proof
  failed, or for some proof its label offset is zero or a key of the event's read set or of
  another proof is a gate input of the proof at its sibling offset.
* **The result** (`main_sharedAll_leN`): moving each hop's bad event to the all-simulated hybrid
  doubles it per later hop, as in `MainChain.fill_ideal_le`:

      |Pr[all real; F] − Pr[all simulated; F]|
          ≤ (2ⁿ − 1)·(εS(q₃ + n, q_E + 2n·4607) + Δ23N(d, n)) + (2ⁿ − 1)·Pr[all simulated; bstarN].

  For `n = 4` the factor is `15`, as in `main_sharedAll_le`, without its prefix-collision term
  (which is unbounded when one Client proves twice with one statement and witness).
-/

open Finset

-- (The coin types are large products: their `Fintype` instances exceed the default size.)
set_option synthInstance.maxSize 1024

namespace VoleMole.ZK.Sim

set_option linter.unusedSectionVars false
set_option linter.constructorNameAsVariable false

open VoleMole.Verifier VoleMole.Verifier.Bridge VoleMole.Arith VoleMole.ZK VoleMole.Privacy
  VoleMole.ZK.IC
open VoleMole.Privacy.MainChain

attribute [local instance] decEqW128
attribute [local irreducible] simulate realRO progRO realKeys5 realKeysE progKeys5 progKeysE

/-- Closes the goals of a step of `runN_rel` that `simp` left as `rfl`s or `True`. -/
local macro "rel_close" : tactic =>
  `(tactic| first | exact ⟨rfl, rfl⟩ | exact ⟨rfl, trivial⟩ | exact ⟨trivial, rfl⟩ |
    exact ⟨trivial, trivial⟩ | trivial | rfl)

/-! ## The game and its run -/

/-- **A game of `n` proofs in sequence**: slot `i`'s statement and witness from the secret and the
outputs (the run passes `none` for the slots not yet run). -/
structure NGame (S : Type) (n : ℕ) where
  σ : Fin n → S → (Fin n → Option Out) → Option SW

/-- **What a slot does on its statement**: its programming of `H₂³`, its output as a function of
the `H₂³` table it reads, and the keys at which it reads `H₅` and the cipher (at that table). -/
structure SlotF (p₀ : Params) where
  pg : Tab2G p₀ → Tab2G p₀
  out : Tab2G p₀ → Option Out
  k5 : Tab2G p₀ → Finset (Bytes 37)
  kE : Tab2G p₀ → Finset Blk

section Run

variable {S : Type} {n : ℕ} {p₀ : Params} (G : NGame S n) (s : S)
  (f : (i : Fin n) → Option SW → SlotF p₀) (G2 : Tab2G p₀)

/-- **The run of the first `k` slots** on the raw `H₂³` table `G2`: the outputs so far (`none` for
the later slots) and the composite of the programmings so far, the earliest outermost. -/
def runN : ℕ → (Fin n → Option Out) × (Tab2G p₀ → Tab2G p₀)
  | 0 => (fun _ => none, id)
  | k + 1 =>
    if h : k < n then
      ((Function.update (runN k).1 ⟨k, h⟩
        ((f ⟨k, h⟩ (G.σ ⟨k, h⟩ s (runN k).1)).out ((runN k).2 G2))),
        (runN k).2 ∘ (f ⟨k, h⟩ (G.σ ⟨k, h⟩ s (runN k).1)).pg)
    else runN k

/-- The statement of slot `i` in the run. -/
def stN (i : Fin n) : Option SW := G.σ i s (runN G s f G2 i).1

/-- The behaviour of slot `i` in the run. -/
def sfN (i : Fin n) : SlotF p₀ := f i (stN G s f G2 i)

/-- The `H₂³` table slot `i` reads in the run. -/
def tabN (i : Fin n) : Tab2G p₀ := (runN G s f G2 i).2 G2

lemma runN_succ {k : ℕ} (h : k < n) :
    runN G s f G2 (k + 1) = (Function.update (runN G s f G2 k).1 ⟨k, h⟩
      ((sfN G s f G2 ⟨k, h⟩).out (tabN G s f G2 ⟨k, h⟩)),
      (runN G s f G2 k).2 ∘ (sfN G s f G2 ⟨k, h⟩).pg) := by
  simp only [runN, h, ↓reduceDIte]; rfl

lemma runN_fst_none (k : ℕ) (j : Fin n) (hj : k ≤ j.val) : (runN G s f G2 k).1 j = none := by
  induction k with
  | zero => rfl
  | succ k ih =>
    have hk : k < n := by omega
    rw [runN_succ G s f G2 hk]
    dsimp only
    rw [Function.update_of_ne (fun h => by rw [h] at hj; simp at hj)]
    exact ih (by omega)

lemma runN_fst_stable (j : Fin n) (m : ℕ) (hm : j.val + 1 ≤ m) :
    (runN G s f G2 m).1 j = (runN G s f G2 (j.val + 1)).1 j := by
  induction m with
  | zero => omega
  | succ m ih =>
    rcases Nat.eq_or_lt_of_le hm with h | h
    · rw [h]
    · by_cases hmn : m < n
      · rw [runN_succ G s f G2 hmn]
        dsimp only
        rw [Function.update_of_ne (fun h' => by subst h'; simp at h)]
        exact ih (by omega)
      · simp only [runN, hmn, ↓reduceDIte]
        exact ih (by omega)

lemma runN_fst_self (j : Fin n) :
    (runN G s f G2 (j.val + 1)).1 j = (sfN G s f G2 j).out (tabN G s f G2 j) := by
  rw [runN_succ G s f G2 j.2]
  exact Function.update_self _ _ _

/-- The outputs of the first `k` slots, the later ones `none`. -/
def maskK (k : ℕ) (os : Fin n → Option Out) : Fin n → Option Out :=
  fun j => if j.val < k then os j else none

lemma runN_fst_mask (k : ℕ) :
    (runN G s f G2 k).1 = maskK k (runN G s f G2 n).1 := by
  funext j
  unfold maskK
  split
  · rename_i h
    rw [runN_fst_stable G s f G2 j k (by omega), runN_fst_stable G s f G2 j n (by omega)]
  · exact runN_fst_none G s f G2 k j (by omega)

/-- **Two runs related step by step.** If a relation `R` between the programming composites holds
at the start and is carried by each of the first `m` steps, with the outputs equal, then the two
runs have the same outputs after `m` steps and their composites are related. -/
theorem runN_rel (f f' : (i : Fin n) → Option SW → SlotF p₀) (G2 G2' : Tab2G p₀)
    (R : ℕ → (Tab2G p₀ → Tab2G p₀) → (Tab2G p₀ → Tab2G p₀) → Prop) (m : ℕ) (hm : m ≤ n)
    (h0 : R 0 id id)
    (hs : ∀ (k : ℕ) (hk : k < m) (L' : Tab2G p₀ → Tab2G p₀), R k (runN G s f G2 k).2 L' →
      (f' ⟨k, by omega⟩ (G.σ ⟨k, by omega⟩ s (runN G s f G2 k).1)).out (L' G2') =
          (f ⟨k, by omega⟩ (G.σ ⟨k, by omega⟩ s (runN G s f G2 k).1)).out
            ((runN G s f G2 k).2 G2) ∧
        R (k + 1) ((runN G s f G2 k).2 ∘ (f ⟨k, by omega⟩ (G.σ ⟨k, by omega⟩ s
            (runN G s f G2 k).1)).pg)
          (L' ∘ (f' ⟨k, by omega⟩ (G.σ ⟨k, by omega⟩ s (runN G s f G2 k).1)).pg)) :
    (runN G s f' G2' m).1 = (runN G s f G2 m).1 ∧
      R m (runN G s f G2 m).2 (runN G s f' G2' m).2 := by
  induction m with
  | zero => exact ⟨rfl, h0⟩
  | succ m ih =>
    have hmn : m < n := by omega
    obtain ⟨e1, e2⟩ := ih (by omega) fun k hk L' hR => hs k (by omega) L' hR
    obtain ⟨h1, h2⟩ := hs m (Nat.lt_succ_self m) _ e2
    rw [runN_succ G s f G2 hmn, runN_succ G s f' G2' hmn]
    simp only [sfN, tabN, stN, e1] at h1 h2 ⊢
    exact ⟨by rw [h1], h2⟩

end Run

/-! ## The view -/

/-- **The adversary's view of a game of `n` proofs on shared tables**: the secret, the shared
`H₅` table and cipher, the programmed `H₂³` table, the one `H₃` table, the outputs. -/
structure NView (S : Type) (n : ℕ) (p₀ : Params) where
  s : S
  u : USh
  M : Tab2G p₀
  T : H3T
  os : Fin n → Option Out

namespace NView

variable {S : Type} {n : ℕ} {p₀ : Params} (v : NView S n p₀)

/-- The view with other shared `H₅` table and cipher. -/
def withU (u : USh) : NView S n p₀ := { v with u := u }
/-- The view with another `H₃` table. -/
def withT (T : H3T) : NView S n p₀ := { v with T := T }

end NView

section View

variable {S : Type} {n : ℕ} {p₀ : Params} (G : NGame S n)

/-- **The view of the run.** -/
def viewN (s : S) (f : (i : Fin n) → Option SW → SlotF p₀) (G2 : Tab2G p₀) (u : USh) (T : H3T) :
    NView S n p₀ :=
  ⟨s, u, (runN G s f G2 n).2 G2, T, (runN G s f G2 n).1⟩

/-- The outputs of the slots before `i`. -/
def maskO (i : Fin n) (os : Fin n → Option Out) : Fin n → Option Out := maskK i.val os

/-- **Slot `i`'s statement on a view.** -/
def yN (i : Fin n) (v : NView S n p₀) : Option SW := G.σ i v.s (maskO i v.os)

lemma yN_viewN (s : S) (f : (i : Fin n) → Option SW → SlotF p₀) (G2 : Tab2G p₀) (u : USh)
    (T : H3T) (i : Fin n) : yN G i (viewN G s f G2 u T) = stN G s f G2 i := by
  unfold yN stN viewN maskO
  rw [runN_fst_mask G s f G2 i.val]

lemma os_viewN (s : S) (f : (i : Fin n) → Option SW → SlotF p₀) (G2 : Tab2G p₀) (u : USh)
    (T : H3T) (i : Fin n) :
    (viewN G s f G2 u T).os i = (sfN G s f G2 i).out (tabN G s f G2 i) := by
  show (runN G s f G2 n).1 i = _
  rw [runN_fst_stable G s f G2 i n i.2, runN_fst_self]

lemma yN_withU (i : Fin n) (v : NView S n p₀) (u : USh) : yN G i (v.withU u) = yN G i v := rfl
lemma yN_withT (i : Fin n) (v : NView S n p₀) (T : H3T) : yN G i (v.withT T) = yN G i v := rfl

end View

/-! ## The slots: simulated, real, given -/

section Modes

variable (Hb : Hashes) (p₀ : Params) {n : ℕ} (ns : Fin n → ℕ)

/-- **A simulated slot** with coins `c`: it programs `H₂³` at its proof's grinding points and reads
`H₅` and the cipher only for that (`progKeys5`, `progKeysE`, which do not depend on `H₂³`). -/
noncomputable def simF (i : Fin n) (c : SimCoins (pw p₀ (ns i))) (u : USh) (y : Option SW) :
    SlotF p₀ where
  pg G := match y with
    | some y => (progRO (pw p₀ (ns i)) Hb (withP y.1 (pw p₀ (ns i))) c
        (shOf (p := pw p₀ (ns i)) G u)).1
    | none => G
  out _ := y.map fun _ => simulate (pw p₀ (ns i)) c
  k5 _ := match y with
    | some y => progKeys5 Hb (withP y.1 (pw p₀ (ns i))) (simulate (pw p₀ (ns i)) c)
        (shOf (p := pw p₀ (ns i)) (Classical.arbitrary _) u)
    | none => ∅
  kE _ := match y with
    | some y => progKeysE Hb (withP y.1 (pw p₀ (ns i))) (simulate (pw p₀ (ns i)) c)
        (shOf (p := pw p₀ (ns i)) (Classical.arbitrary _) u)
    | none => ∅

/-- **A real slot** with randomness `ρ`: the executable prover reading the column of the one `H₃`
table `T` at its prefix (`preOf`), the `H₂³` table it is given and the shared tables. -/
noncomputable def realF (i : Fin n) (ρ : Bytes 16) (T : H3T) (u : USh) (y : Option SW) :
    SlotF p₀ where
  pg G := G
  out M := y.map fun sw => realRO (pw p₀ (ns i)) Hb (withP sw.1 (pw p₀ (ns i))) sw.2 ρ
    (T (preOf Hb (pw p₀ (ns i)) sw)) (shOf (p := pw p₀ (ns i)) M u)
  k5 M := match y with
    | some sw => realKeys5 (pw p₀ (ns i)) Hb (withP sw.1 (pw p₀ (ns i))) sw.2 (ba ρ)
        (T (preOf Hb (pw p₀ (ns i)) sw)) (shOf (p := pw p₀ (ns i)) M u)
    | none => ∅
  kE M := match y with
    | some sw => realKeysE (pw p₀ (ns i)) Hb (withP sw.1 (pw p₀ (ns i))) sw.2 (ba ρ)
        (T (preOf Hb (pw p₀ (ns i)) sw)) (shOf (p := pw p₀ (ns i)) M u)
    | none => ∅

/-- **A slot with a given output**, programming and reading nothing. -/
def givenF (o : Out) (y : Option SW) : SlotF p₀ where
  pg G := G
  out _ := y.map fun _ => o
  k5 _ := ∅
  kE _ := ∅

/-- The coins of the `n` slots: each prover's `ρ` and each simulator's coins. -/
abbrev CoinsN := (i : Fin n) → Bytes 16 × SimCoins (pw p₀ (ns i))

/-- **The tape**: the secret, the slots' coins, the one `H₃` table, the shared `H₅` table and
cipher, the raw `H₂³` table. -/
abbrev NTape (S : Type) := S × CoinsN p₀ ns × H3T × USh × Tab2G p₀

/-- **Slot `i` in hybrid `j`**: simulated iff `i < j`. -/
noncomputable def modeF (j : ℕ) (cs : CoinsN p₀ ns) (T : H3T) (u : USh) (i : Fin n)
    (y : Option SW) : SlotF p₀ :=
  if i.val < j then simF Hb p₀ ns i (cs i).2 u y else realF Hb p₀ ns i (cs i).1 T u y

variable {S : Type} (G : NGame S n)

/-- **The view in hybrid `j`.** -/
noncomputable def hybVN (j : ℕ) (x : NTape p₀ ns S) : NView S n p₀ :=
  viewN G x.1 (modeF Hb p₀ ns j x.2.1 x.2.2.1 x.2.2.2.1) x.2.2.2.2 x.2.2.2.1 x.2.2.1

/-- **The probability of an event of the view in hybrid `j`** (`j = 0`: all proofs real;
`j = n`: all simulated). -/
noncomputable def hybN [Fintype S] (j : ℕ) (Ψ : NView S n p₀ → Prop) : ℝ :=
  pr (NTape p₀ ns S) (fun x => Ψ (hybVN Hb p₀ ns G j x))

end Modes

/-! ## Events of the view and their read sets; the bad event -/

section Events

variable {S : Type} {n : ℕ} {p₀ : Params}

/-- **`f` reads the tables of a view within explicit sets**: the `H₅` table only at `R5`, the
cipher at `qE` keys, the one `H₃` at `q3` points `(prefix, ρ)` (the `H₂³` table, the secret and the
outputs freely). -/
structure RdN {X : Sort*} (f : NView S n p₀ → X) (R5 : NView S n p₀ → Finset (Bytes 37))
    (q3 qE : ℕ) : Prop where
  h5 : ∀ v (G5 : Tab5F), (∀ k ∈ R5 v, v.u.1 k = G5 k) → f (v.withU (G5, v.u.2)) = f v
  hE : ∃ Q : NView S n p₀ → Finset Blk, (∀ v, (Q v).card ≤ qE) ∧
    ∀ v (E : Cipher), (∀ k ∈ Q v, v.u.2 k = E k) → f (v.withU (v.u.1, E)) = f v
  hT : ∃ Q : NView S n p₀ → Finset (Pre × Bytes 16), (∀ v, (Q v).card ≤ q3) ∧
    ∀ v (T' : H3T), (∀ k ∈ Q v, v.T k.1 k.2 = T' k.1 k.2) → f (v.withT T') = f v

variable (Hb : Hashes) (G : NGame S n) (ps : Fin n → Params)

/-- **The bad event of the joint hop**, an event of the view: some proof failed, or for some proof
its label offset is zero, or a key of `R5` or of another proof is a gate input of the proof at its
sibling offset. -/
def bstarN (R5 : NView S n p₀ → Finset (Bytes 37)) (v : NView S n p₀) : Prop :=
  (∃ i, slotErr (v.os i)) ∨ ∃ j : Fin n, slotZero (ps j) (yN G j v) (v.os j) ∨
    ∃ k ∈ R5 v ∪ (univ.filter (· ≠ j)).biUnion
        (fun m => slotKeys Hb (ps m) (yN G m v) (v.os m) v.u.2),
      slotHit Hb (ps j) (yN G j v) (v.os j) v.u.2 k

/-- **The bad event reads what `R5` reads**, and the cipher at `n·4607` more keys (the
reconstructions of the `n` proofs). -/
theorem rd_bstarN {R5 : NView S n p₀ → Finset (Bytes 37)} {q3 qE : ℕ} (hR : RdN R5 R5 q3 qE) :
    RdN (bstarN Hb G ps R5) R5 q3 (qE + n * 4607) := by
  classical
  refine ⟨fun v G5 h => ?_, ?_, ?_⟩
  · show bstarN Hb G ps R5 (v.withU (G5, v.u.2)) = bstarN Hb G ps R5 v
    unfold bstarN
    rw [hR.h5 v G5 h]; rfl
  · obtain ⟨Q, hQc, hQ⟩ := hR.hE
    refine ⟨fun v => Q v ∪ univ.biUnion (fun i => slotRd Hb (ps i) (yN G i v) (v.os i) v.u.2),
      fun v => ?_, fun v E h => ?_⟩
    · have h1 := card_union_le (Q v)
        (univ.biUnion (fun i => slotRd Hb (ps i) (yN G i v) (v.os i) v.u.2))
      have h2 : (univ.biUnion (fun i => slotRd Hb (ps i) (yN G i v) (v.os i) v.u.2)).card ≤
          n * 4607 := by
        refine card_biUnion_le.trans ?_
        calc ∑ i : Fin n, (slotRd Hb (ps i) (yN G i v) (v.os i) v.u.2).card
            ≤ ∑ _i : Fin n, 4607 := sum_le_sum fun i _ => card_slotRd Hb _ _ _ _
          _ = n * 4607 := by simp
      have := hQc v
      beta_reduce
      omega
    · have e : ∀ i, slotKeys Hb (ps i) (yN G i v) (v.os i) E =
          slotKeys Hb (ps i) (yN G i v) (v.os i) v.u.2 := fun i =>
        slotKeys_congrE Hb (ps i) _ _ fun k hk =>
          h k (mem_union_right _ (mem_biUnion.2 ⟨i, mem_univ _, hk⟩))
      have e' : ∀ i, slotHit Hb (ps i) (yN G i v) (v.os i) E =
          slotHit Hb (ps i) (yN G i v) (v.os i) v.u.2 := fun i =>
        slotHit_congrE Hb (ps i) _ _ fun k hk =>
          h k (mem_union_right _ (mem_biUnion.2 ⟨i, mem_univ _, hk⟩))
      show bstarN Hb G ps R5 (v.withU (v.u.1, E)) = bstarN Hb G ps R5 v
      unfold bstarN
      rw [hQ v E fun k hk => h k (mem_union_left _ hk)]
      simp only [NView.withU, yN] at e e' ⊢
      simp only [e, e']
  · obtain ⟨Q, hQc, hQ⟩ := hR.hT
    refine ⟨Q, hQc, fun v T' h => ?_⟩
    show bstarN Hb G ps R5 (v.withT T') = bstarN Hb G ps R5 v
    unfold bstarN
    rw [hQ v T' h]; rfl

end Events

/-! ## Tools: a lens on the tape, the programming-collision bound, one proof in a context -/

section Tools

/-- **Resampling through a lens keeps the tape uniform**: writing a fresh value through a lens
`get`/`set` is measure-preserving (the map `(x, b) ↦ (set x b, get x)` is an involution). -/
theorem pr_lens {X B : Type*} [Fintype X] [Fintype B] [Nonempty B] (get : X → B)
    (set : X → B → X) (gs : ∀ x b, get (set x b) = b) (sg : ∀ x, set x (get x) = x)
    (ss : ∀ x b b', set (set x b) b' = set x b') (Φ : X → Prop) :
    pr (X × B) (fun z => Φ (set z.1 z.2)) = pr X Φ := by
  let e : X × B ≃ X × B :=
    { toFun := fun z => (set z.1 z.2, get z.1)
      invFun := fun z => (set z.1 z.2, get z.1)
      left_inv := fun z => by simp only [ss, sg, gs]
      right_inv := fun z => by simp only [ss, sg, gs] }
  calc pr (X × B) (fun z => Φ (set z.1 z.2)) = pr (X × B) (fun z => Φ (e z).1) := rfl
    _ = pr (X × B) (fun z => Φ z.1) := pr_equiv e (fun z => Φ z.1)
    _ = pr X Φ := pr_prod_fst Φ

/-- **The programming-collision bound of one hop with `m` earlier tails**: `pr_collide_main` with
`|T| ≤ m` (`Δ23 d = Δ23N d 3`). -/
noncomputable def Δ23N (d m : ℕ) : ℝ :=
  1 / 2 ^ 113 + εS 0 4607 + ((312 : ℕ) + 1) / 2 ^ 128 +
    (noHitProb + m / 2 ^ (8 * (16 * (d - 1))))

lemma Δ23N_nonneg (d m : ℕ) : 0 ≤ Δ23N d m := by
  have h1 := εS_nonneg 0 4607
  have h2 : 0 ≤ noHitProb := pr_nonneg _
  have h3 : (0 : ℝ) ≤ 1 / 2 ^ 113 := by positivity
  have h4 : (0 : ℝ) ≤ ((312 : ℕ) + 1) / 2 ^ 128 := by positivity
  have h5 : (0 : ℝ) ≤ (m : ℝ) / (2 : ℝ) ^ (8 * (16 * (d - 1))) :=
    div_nonneg (Nat.cast_nonneg _) (pow_nonneg (by norm_num) _)
  unfold Δ23N
  linarith

/-- `pr_collide_slot` with at most `m` earlier tails. -/
theorem pr_collide_slotN (Hb : Hashes) {p : Params} (hm : MainP p) (hp : SmallParams p)
    (hHb : HashesWF Hb) (y : SW) (hy : ValidZK CrtGen.tables p y) (L : USh → Tab2G p → Tab2G p)
    (T : Finset ByteArray) {m : ℕ} (hT : T.card ≤ m)
    (hL : ∀ u G2 (k : K2 p), preTail k.1 ∉ T → L u G2 k = G2 k) :
    pr (USh × KS p) (fun z => realRO p Hb (withP y.1 p) y.2 z.2.1.1 z.2.2.1
        ((L z.1 z.2.2.2, z.1) : Sh p) ≠
      realRO p Hb (withP y.1 p) y.2 z.2.1.1 z.2.2.1 (shOf z.2.2.2 z.1)) ≤ Δ23N p.qsDegree m := by
  classical
  obtain ⟨cs, hzk⟩ := hy
  have key := pr_collide_main (st := withP y.1 p) (w := y.2) (Hb := Hb) hm hzk hHb hp
    (L := fun t => (L t.2 t.1, t.2)) (B := fun _ => univ.filter fun b => preTail b ∈ T)
    ⟨fun _ => rfl, fun t k hk => hL t.2 t.1 k (by simpa using hk)⟩ T
    (fun _ b hb => by simpa using hb)
  let e : ((Bytes 16 × Tab3) × Sh p) × SimCoins p ≃ USh × KS p :=
    { toFun := fun a => (a.1.2.2, ((a.1.1.1, a.2), (a.1.1.2, a.1.2.1)))
      invFun := fun z => (((z.2.1.1, z.2.2.1), (z.2.2.2, z.1)), z.2.1.2)
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [← pr_equiv e]
  refine (le_of_eq (pr_prod_fst (β := SimCoins p) (fun a : (Bytes 16 × Tab3) × Sh p =>
    realRO p Hb (withP y.1 p) y.2 a.1.1 a.1.2 ((L a.2.2 a.2.1, a.2.2) : Sh p) ≠
      realRO p Hb (withP y.1 p) y.2 a.1.1 a.1.2 a.2))).trans (key.trans ?_)
  unfold Δ23N
  have h3 : (T.card : ℝ) ≤ m := by exact_mod_cast hT
  have : (T.card : ℝ) / 2 ^ (8 * (16 * (p.qsDegree - 1))) ≤
      m / 2 ^ (8 * (16 * (p.qsDegree - 1))) := by gcongr
  linarith

variable (Hb : Hashes) {V : Type}

/-- **One proof replaced, in a context that also reads its `H₃` slice.** `ctx_hop` of
`ZK/MainSharedGame.lean` where the rest of the game (`C`) may read the proof's slice `G3` at the
points `T3` (the later real proofs with the same prefix, at their own `ρ`): these count as
distinguisher reads of `H₃`. -/
theorem ctx_hopN {p : Params} (hm : MainP p) (hp : SmallParams p) (hHb : HashesWF Hb) (y : SW)
    (hy : ValidZK CrtGen.tables p y) (getU : V → USh) (withU : V → USh → V)
    (get3 : V → Tab3) (set3 : V → Tab3 → V) (Ψ : V → Prop) (R5 : V → Finset (Bytes 37))
    (C : Out → VP p → USh → V)
    (T5 : Out → VP p → USh → Finset (Bytes 37)) (TE : Out → VP p → USh → Finset Blk)
    (T3 : Finset (Bytes 16)) {tE : ℕ}
    (hCu : ∀ o V u, getU (C o V u) = u)
    (hC5 : ∀ o V u (G5 : Tab5F), (∀ k ∈ T5 o V u, u.1 k = G5 k) →
      C o V (G5, u.2) = withU (C o V u) (G5, u.2))
    (hCE : ∀ o V u (E : Cipher), (∀ k ∈ TE o V u, u.2 k = E k) →
      C o V (u.1, E) = withU (C o V u) (u.1, E))
    (hTE : ∀ o V u, (TE o V u).card ≤ tE)
    (hC3 : ∀ o (G3 G3' : Tab3) (G2 : Tab2G p) u, (∀ k ∈ T3, G3 k = G3' k) →
      C o (G3', G2) u = set3 (C o (G3, G2) u) G3')
    (hg3 : ∀ o (G3 : Tab3) (G2 : Tab2G p) u, get3 (C o (G3, G2) u) = G3)
    {q3 qE : ℕ}
    (hΨ5 : ∀ v (G5 : Tab5F), (∀ k ∈ R5 v, (getU v).1 k = G5 k) →
      Ψ (withU v (G5, (getU v).2)) = Ψ v)
    (hΨE : ∃ Q : V → Finset Blk, (∀ v, (Q v).card ≤ qE) ∧
      ∀ v (E : Cipher), (∀ k ∈ Q v, (getU v).2 k = E k) → Ψ (withU v ((getU v).1, E)) = Ψ v)
    (hΨ3 : ∃ Q : V → Finset (Bytes 16), (∀ v, (Q v).card ≤ q3) ∧
      ∀ v (G3 : Tab3), (∀ k ∈ Q v, get3 v k = G3 k) → Ψ (set3 v G3) = Ψ v) :
    |pr (USh × KS p) (fun z => Ψ (C (realRO p Hb (withP y.1 p) y.2 z.2.1.1 z.2.2.1
          (shOf z.2.2.2 z.1)) z.2.2 z.1)) -
      pr (USh × KS p) (fun z => Ψ (C (simulate p z.2.1.2)
          (z.2.2.1, (progRO p Hb (withP y.1 p) z.2.1.2 (shOf z.2.2.2 z.1)).1) z.1))| ≤
      εS (q3 + T3.card) (qE + tE) + pr (USh × KS p) (fun z => mainPredIC Hb (withP y.1 p) hm
        (fun o G3 G2 G5 E => R5 (C o (G3, G2) (G5, E)) ∪ T5 o (G3, G2) (G5, E)) (wPre y.2)
        ((z.2.1.2, (z.2.2.1, z.2.2.2, z.1.1)), z.1.2)) := by
  classical
  obtain ⟨cs, hzk⟩ := hy
  obtain ⟨QE, hQEc, hQE⟩ := hΨE
  obtain ⟨Q3, hQ3c, hQ3⟩ := hΨ3
  refine slot_zk_main Hb (withP y.1 p) y.2 hm hzk hHb hp
    (fun o G3 G2 G5 E => Ψ (C o (G3, G2) (G5, E)))
    (fun o G3 G2 G5 E => Q3 (C o (G3, G2) (G5, E)) ∪ T3) ?_
    (q3 := q3 + T3.card) (fun _ _ _ _ _ => (card_union_le _ _).trans (add_le_add (hQ3c _) le_rfl))
    (fun o G3 G2 G5 E => R5 (C o (G3, G2) (G5, E)) ∪ T5 o (G3, G2) (G5, E)) ?_
    (fun o G3 G2 G5 E => QE (C o (G3, G2) (G5, E)) ∪ TE o (G3, G2) (G5, E)) ?_ ?_
  · intro o G3 G3' G2 G5 E h
    show Ψ (C o (G3, G2) (G5, E)) ↔ Ψ (C o (G3', G2) (G5, E))
    rw [hC3 o G3 G3' G2 (G5, E) fun k hk => h k (mem_union_right _ hk),
      hQ3 _ G3' (by rw [hg3]; exact fun k hk => h k (mem_union_left _ hk))]
  · intro o G3 G2 G5 G5' E h
    have e := hC5 o (G3, G2) (G5, E) G5' fun k hk => h k (mem_union_right _ hk)
    have hu := hCu o (G3, G2) (G5, E)
    have := hΨ5 (C o (G3, G2) (G5, E)) G5' (by
      rw [hu]; exact fun k hk => h k (mem_union_left _ hk))
    rw [hu] at this
    show Ψ (C o (G3, G2) (G5, E)) ↔ Ψ (C o (G3, G2) (G5', E))
    rw [e, this]
  · intro o G3 G2 G5 E E' h
    have e := hCE o (G3, G2) (G5, E) E' fun k hk => h k (mem_union_right _ hk)
    have hu := hCu o (G3, G2) (G5, E)
    have := hQE (C o (G3, G2) (G5, E)) E' (by
      rw [hu]; exact fun k hk => h k (mem_union_left _ hk))
    rw [hu] at this
    show Ψ (C o (G3, G2) (G5, E)) ↔ Ψ (C o (G3, G2) (G5, E'))
    rw [e, this]
  · intro o G3 G2 G5 E
    exact (card_union_le _ _).trans (add_le_add (hQEc _) (hTE _ _ _))

end Tools

/-! ## What the slots read -/

section Cov

variable (Hb : Hashes) (p₀ : Params) {n : ℕ} (ns : Fin n → ℕ)

/-- **A slot's `H₅` keys are keys of its proof** (or it failed), at every table it may read. -/
def SlotF.Cov (p : Params) (sf : SlotF p₀) (y : Option SW) (E : Cipher) : Prop :=
  ∀ M, ∀ k ∈ sf.k5 M, slotErr (sf.out M) ∨ k ∈ slotKeys Hb p y (sf.out M) E

lemma givenF_cov (p : Params) (o : Out) (y : Option SW) (E : Cipher) :
    (givenF p₀ o y).Cov Hb p₀ p y E := fun _ k hk => by simp [givenF] at hk

lemma simF_cov (i : Fin n) (c : SimCoins (pw p₀ (ns i))) (u : USh) (y : Option SW)
    (hy : ∀ sw ∈ y, ValidZK CrtGen.tables (pw p₀ (ns i)) sw) :
    (simF Hb p₀ ns i c u y).Cov Hb p₀ (pw p₀ (ns i)) y u.2 := by
  intro M k hk
  rcases y with _ | y
  · simp [simF] at hk
  · have hk' : k ∈ simK5 Hb (pw p₀ (ns i)) c (Classical.arbitrary _, Classical.arbitrary _)
        (some y) u := hk
    exact simB_cov Hb c _ y (hy y rfl) u k hk'

lemma realF_cov (i : Fin n) (hm : MainP (pw p₀ (ns i))) (hHb : HashesWF Hb) (ρ : Bytes 16)
    (T : H3T) (u : USh) (y : Option SW)
    (hy : ∀ sw ∈ y, ValidZK CrtGen.tables (pw p₀ (ns i)) sw) :
    (realF Hb p₀ ns i ρ T u y).Cov Hb p₀ (pw p₀ (ns i)) y u.2 := by
  intro M k hk
  rcases y with _ | y
  · simp [realF] at hk
  · have hk' : k ∈ realK5 Hb (pw p₀ (ns i)) ρ (T (preOf Hb (pw p₀ (ns i)) y), M) (some y) u := hk
    exact realB_cov Hb hm hHb ρ _ y (hy y rfl) u k hk'

end Cov

/-! ## The first `j` slots of hybrid `j` -/

section Pre

variable (Hb : Hashes) (p₀ : Params) {n : ℕ} (ns : Fin n → ℕ) {S : Type} (G : NGame S n)

/-- **The first `j` slots of hybrid `j` are simulated**: their outputs depend only on the secret
and their simulator coins, their programmings also on the shared `H₅` table and cipher. -/
theorem preRun_eq (j j' m : ℕ) (hm : m ≤ n) (hmj : m ≤ j) (hmj' : m ≤ j') (s : S)
    (cs cs' : CoinsN p₀ ns) (T T' : H3T) (u : USh)
    (G2 G2' : Tab2G p₀) (hc : ∀ i : Fin n, i.val < m → (cs i).2 = (cs' i).2) :
    runN G s (modeF Hb p₀ ns j' cs' T' u) G2' m = runN G s (modeF Hb p₀ ns j cs T u) G2 m := by
  obtain ⟨e1, e2⟩ := runN_rel G s (modeF Hb p₀ ns j cs T u) (modeF Hb p₀ ns j' cs' T' u) G2 G2'
    (fun _ L L' => L = L') m hm rfl fun k hk L' hL => by
      subst hL
      have hk' : (⟨k, by omega⟩ : Fin n).val < j := by show k < j; omega
      have hk'' : (⟨k, by omega⟩ : Fin n).val < j' := by show k < j'; omega
      simp only [modeF, hk', hk'', ↓reduceIte, hc ⟨k, by omega⟩ hk]
      rel_close
  exact Prod.ext e1 e2.symm

/-- The outputs of the first `j` slots do not depend on the shared tables either. -/
theorem preRun_fst_eq (j j' m : ℕ) (hm : m ≤ n) (hmj : m ≤ j) (hmj' : m ≤ j') (s : S)
    (cs cs' : CoinsN p₀ ns) (T T' : H3T)
    (u u' : USh) (G2 G2' : Tab2G p₀) (hc : ∀ i : Fin n, i.val < m → (cs i).2 = (cs' i).2) :
    (runN G s (modeF Hb p₀ ns j' cs' T' u') G2' m).1 =
      (runN G s (modeF Hb p₀ ns j cs T u) G2 m).1 := by
  refine (runN_rel G s (modeF Hb p₀ ns j cs T u) (modeF Hb p₀ ns j' cs' T' u') G2 G2'
    (fun _ _ _ => True) m hm trivial fun k hk L' _ => ?_).1
  have hk' : (⟨k, by omega⟩ : Fin n).val < j := by show k < j; omega
  have hk'' : (⟨k, by omega⟩ : Fin n).val < j' := by show k < j'; omega
  simp only [modeF, hk', hk'', ↓reduceIte, hc ⟨k, by omega⟩ hk]
  exact ⟨rfl, trivial⟩

/-- **The earlier simulations' programmings change only blocks with their tails.** -/
theorem preRun_tl (hHb : HashesWF Hb) (j : ℕ) (hj : j ≤ n) (s : S) (cs : CoinsN p₀ ns)
    (T : H3T) (u : USh) (G2 H : Tab2G p₀) (k : K2 p₀)
    (hk : preTail k.1 ∉ (univ.filter fun i : Fin n => i.val < j).image
      (fun i => simTail (cs i).2)) :
    (runN G s (modeF Hb p₀ ns j cs T u) G2 j).2 H k = H k := by
  suffices h : ∀ m ≤ j, ∀ H : Tab2G p₀, (runN G s (modeF Hb p₀ ns j cs T u) G2 m).2 H k = H k from
    h j le_rfl H
  intro m hm
  induction m with
  | zero => intro H; rfl
  | succ m ih =>
    intro H
    have hmn : m < n := by omega
    rw [runN_succ G s _ G2 hmn]
    show (runN G s (modeF Hb p₀ ns j cs T u) G2 m).2 _ k = H k
    rw [ih (by omega)]
    have hmj : (⟨m, hmn⟩ : Fin n).val < j := by show m < j; omega
    simp only [sfN, modeF, hmj, ↓reduceIte, simF]
    rcases hy : stN G s (modeF Hb p₀ ns j cs T u) G2 ⟨m, hmn⟩ with _ | y
    · rfl
    · refine (progRO_progAt (R := Blk → Blk) Hb (withP y.1 (pw p₀ (ns ⟨m, hmn⟩)))
        (cs ⟨m, hmn⟩).2).2 (shOf (p := pw p₀ (ns ⟨m, hmn⟩)) H u) k fun hm' => hk ?_
      rw [Finset.mem_singleton] at hm'
      refine mem_image.2 ⟨⟨m, hmn⟩, mem_filter.2 ⟨mem_univ _, hmj⟩, ?_⟩
      rw [hm']
      exact (preTail_simBlk (st := withP y.1 (pw p₀ (ns ⟨m, hmn⟩))) hHb rfl _ _).symm

end Pre

/-! ## The hop for slot `j` -/

section Hop

variable (Hb : Hashes) (p₀ : Params) {n : ℕ} (ns : Fin n → ℕ) {S : Type} (G : NGame S n)

/-- **Slot `j`'s statement in hybrids `j` and `j + 1`**, a function of the secret and the earlier
simulators' coins. -/
noncomputable def yJ (j : ℕ) (hj : j < n) (x : NTape p₀ ns S) : Option SW :=
  G.σ ⟨j, hj⟩ x.1 (runN G x.1 (modeF Hb p₀ ns j x.2.1 x.2.2.1 x.2.2.2.1) x.2.2.2.2 j).1

/-- Its prefix (an arbitrary one without a statement). -/
noncomputable def preJ (j : ℕ) (hj : j < n) (x : NTape p₀ ns S) : Pre :=
  match yJ Hb p₀ ns G j hj x with
  | some y => preOf Hb (pw p₀ (ns ⟨j, hj⟩)) y
  | none => Classical.arbitrary _

/-- **The lens of slot `j`**: the shared `H₅` table and cipher, slot `j`'s coins, the column of
`H₃` at its prefix and the raw `H₂³` table, as the tape of `slot_zk_main`. -/
noncomputable def getJ (j : ℕ) (hj : j < n) (x : NTape p₀ ns S) :
    USh × KS (pw p₀ (ns ⟨j, hj⟩)) :=
  (x.2.2.2.1, (x.2.1 ⟨j, hj⟩, (x.2.2.1 (preJ Hb p₀ ns G j hj x), x.2.2.2.2)))

/-- Writing slot `j`'s experiment into the tape. -/
noncomputable def setJ (j : ℕ) (hj : j < n) (x : NTape p₀ ns S)
    (b : USh × KS (pw p₀ (ns ⟨j, hj⟩))) : NTape p₀ ns S :=
  (x.1, Function.update x.2.1 ⟨j, hj⟩ b.2.1,
    Function.update x.2.2.1 (preJ Hb p₀ ns G j hj x) b.2.2.1, b.1, b.2.2.2)

lemma upd_lt {j : ℕ} {hj : j < n} (cs : CoinsN p₀ ns) (b : Bytes 16 × SimCoins (pw p₀ (ns ⟨j, hj⟩)))
    (i : Fin n) (hi : i.val < j) : (Function.update cs ⟨j, hj⟩ b i).2 = (cs i).2 := by
  rw [Function.update_of_ne (fun h => by rw [h] at hi; exact lt_irrefl _ hi)]

lemma yJ_setJ (j : ℕ) (hj : j < n) (x : NTape p₀ ns S) (b : USh × KS (pw p₀ (ns ⟨j, hj⟩))) :
    yJ Hb p₀ ns G j hj (setJ Hb p₀ ns G j hj x b) = yJ Hb p₀ ns G j hj x := by
  unfold yJ
  congr 1
  exact preRun_fst_eq Hb p₀ ns G j j j hj.le le_rfl le_rfl x.1 _ _ _ _ _ _ _ _
    fun i hi => (upd_lt p₀ ns x.2.1 b.2.1 i hi).symm

lemma preJ_setJ (j : ℕ) (hj : j < n) (x : NTape p₀ ns S) (b : USh × KS (pw p₀ (ns ⟨j, hj⟩))) :
    preJ Hb p₀ ns G j hj (setJ Hb p₀ ns G j hj x b) = preJ Hb p₀ ns G j hj x := by
  unfold preJ
  rw [yJ_setJ]

/-- **A hybrid on the lens**: hybrid `j'` is hybrid `j'` with slot `j`'s experiment resampled. -/
theorem hybN_lens [Fintype S] (j : ℕ) (hj : j < n) (j' : ℕ) (Ψ : NView S n p₀ → Prop) :
    hybN Hb p₀ ns G j' Ψ = pr (NTape p₀ ns S × (USh × KS (pw p₀ (ns ⟨j, hj⟩)))) (fun z =>
      Ψ (hybVN Hb p₀ ns G j' (setJ Hb p₀ ns G j hj z.1 z.2))) := by
  unfold hybN
  refine (pr_lens (getJ Hb p₀ ns G j hj) (setJ Hb p₀ ns G j hj) (fun x b => ?_) (fun x => ?_)
    (fun x b b' => ?_) _).symm
  · unfold getJ
    rw [preJ_setJ]
    simp only [setJ, Function.update_self]
  · simp only [setJ, getJ, Function.update_eq_self]
  · have e := preJ_setJ Hb p₀ ns G j hj x b
    unfold setJ at e ⊢
    simp only [e, Function.update_idem]

/-- **The context of hop `j`**: the slots before `j` simulated, slot `j` given, the later ones
real (on the `H₃` table `T`). -/
noncomputable def ctxF (j : ℕ) (cs : CoinsN p₀ ns) (T : H3T) (u : USh) (o : Out) (i : Fin n)
    (y : Option SW) : SlotF p₀ :=
  if i.val < j then simF Hb p₀ ns i (cs i).2 u y
  else if i.val = j then givenF p₀ o y else realF Hb p₀ ns i (cs i).1 T u y

lemma card_ctxF_kE (j : ℕ) (cs : CoinsN p₀ ns) (T : H3T) (u : USh) (o : Out) (i : Fin n)
    (y : Option SW) (M : Tab2G p₀) : ((ctxF Hb p₀ ns j cs T u o i y).kE M).card ≤ 4607 := by
  unfold ctxF
  split
  · rcases y with _ | y
    · simp [simF]
    · exact card_progKeysE Hb _ _ _
  · split
    · simp [givenF]
    · rcases y with _ | y
      · simp [realF]
      · exact card_realKeysE _ Hb _ _ _ _ _

/-- All `H₅` keys a run reads. -/
def trace5 (s : S) (f : (i : Fin n) → Option SW → SlotF p₀) (G2 : Tab2G p₀) : Finset (Bytes 37) :=
  univ.biUnion fun i => (sfN G s f G2 i).k5 (tabN G s f G2 i)

/-- All cipher keys a run reads. -/
def traceE (s : S) (f : (i : Fin n) → Option SW → SlotF p₀) (G2 : Tab2G p₀) : Finset Blk :=
  univ.biUnion fun i => (sfN G s f G2 i).kE (tabN G s f G2 i)

end Hop

section HopFiber

variable (Hb : Hashes) (p₀ : Params) {n : ℕ} (ns : Fin n → ℕ) {S : Type} (G : NGame S n)

/-- The column of `H₃` that slot `j` reads, written into the tape's table. -/
noncomputable def TJ (j : ℕ) (hj : j < n) (x : NTape p₀ ns S) (G3 : Tab3) : H3T :=
  Function.update x.2.2.1 (preJ Hb p₀ ns G j hj x) G3

/-- **The view of the context of hop `j`** with slot `j`'s output `o`, its tables `V` (its `H₃`
column and the raw `H₂³` table) and the shared `H₅` table and cipher `u`. -/
noncomputable def ctxV (j : ℕ) (hj : j < n) (x : NTape p₀ ns S) (o : Out)
    (V : VP (pw p₀ (ns ⟨j, hj⟩))) (u : USh) : NView S n p₀ :=
  viewN G x.1 (ctxF Hb p₀ ns j x.2.1 (TJ Hb p₀ ns G j hj x V.1) u o) V.2 u
    (TJ Hb p₀ ns G j hj x V.1)

/-- The earlier simulations' programmings in hop `j` (on the tape `x`, at `u`). -/
noncomputable def LJ (j : ℕ) (x : NTape p₀ ns S) (u : USh) : Tab2G p₀ → Tab2G p₀ :=
  (runN G x.1 (modeF Hb p₀ ns j x.2.1 x.2.2.1 u) x.2.2.2.2 j).2

/-- The first `j` slots of the context are those of hybrid `j`. -/
lemma ctx_pre (j : ℕ) (hj : j ≤ n) (s : S) (cs : CoinsN p₀ ns) (T T' : H3T) (u : USh) (o : Out)
    (G2 G2' : Tab2G p₀) :
    runN G s (ctxF Hb p₀ ns j cs T u o) G2 j = runN G s (modeF Hb p₀ ns j cs T' u) G2' j := by
  obtain ⟨e1, e2⟩ := runN_rel G s (modeF Hb p₀ ns j cs T' u) (ctxF Hb p₀ ns j cs T u o) G2' G2
    (fun _ L L' => L = L') j hj rfl fun k hk L' hL => by
      subst hL
      have hk' : (⟨k, by omega⟩ : Fin n).val < j := hk
      simp only [modeF, ctxF, hk', ↓reduceIte]
      rel_close
  exact Prod.ext e1 e2.symm

lemma stN_ctx_j (j : ℕ) (hj : j < n) (x : NTape p₀ ns S) (T : H3T) (u : USh) (o : Out)
    (G2 : Tab2G p₀) :
    stN G x.1 (ctxF Hb p₀ ns j x.2.1 T u o) G2 ⟨j, hj⟩ = yJ Hb p₀ ns G j hj x := by
  unfold stN yJ
  rw [ctx_pre Hb p₀ ns G j hj.le x.1 x.2.1 T x.2.2.1 u o G2 x.2.2.2.2]
  congr 1
  exact preRun_fst_eq Hb p₀ ns G j j j hj.le le_rfl le_rfl x.1 _ _ _ _ _ _ _ _ fun _ _ => rfl

lemma TJ_at (j : ℕ) (hj : j < n) (x : NTape p₀ ns S) (y : SW)
    (hy : yJ Hb p₀ ns G j hj x = some y) (G3 : Tab3) :
    TJ Hb p₀ ns G j hj x G3 (preOf Hb (pw p₀ (ns ⟨j, hj⟩)) y) = G3 := by
  unfold TJ preJ
  rw [hy]
  exact Function.update_self _ _ _

/-- **The real side of hop `j` is the context with the real proof**, reading the table programmed
by the earlier simulations. -/
theorem hyb_real_eq (j : ℕ) (hj : j < n) (x : NTape p₀ ns S) (y : SW)
    (hy : yJ Hb p₀ ns G j hj x = some y) (u : USh) (ρ : Bytes 16)
    (c : SimCoins (pw p₀ (ns ⟨j, hj⟩))) (G3 : Tab3) (G2 : Tab2G p₀) :
    hybVN Hb p₀ ns G j (setJ Hb p₀ ns G j hj x (u, ((ρ, c), (G3, G2)))) =
      ctxV Hb p₀ ns G j hj x (realRO (pw p₀ (ns ⟨j, hj⟩)) Hb (withP y.1 (pw p₀ (ns ⟨j, hj⟩)))
        y.2 ρ G3 (shOf (p := pw p₀ (ns ⟨j, hj⟩)) (LJ Hb p₀ ns G j x u G2) u)) (G3, G2) u := by
  set cs' := Function.update x.2.1 ⟨j, hj⟩ (ρ, c) with hcs'
  set T' := TJ Hb p₀ ns G j hj x G3 with hT'
  have hc : ∀ i : Fin n, i.val < j → (x.2.1 i).2 = (cs' i).2 := fun i hi =>
    (upd_lt p₀ ns x.2.1 (ρ, c) i hi).symm
  have hpre : runN G x.1 (modeF Hb p₀ ns j cs' T' u) G2 j =
      runN G x.1 (modeF Hb p₀ ns j x.2.1 x.2.2.1 u) x.2.2.2.2 j :=
    preRun_eq Hb p₀ ns G j j j hj.le le_rfl le_rfl x.1 _ _ _ _ _ _ _ hc
  have hyj : G.σ ⟨j, hj⟩ x.1 (runN G x.1 (modeF Hb p₀ ns j cs' T' u) G2 j).1 = some y := by
    rw [← hy]
    unfold yJ
    congr 1
    exact preRun_fst_eq Hb p₀ ns G j j j hj.le le_rfl le_rfl x.1 _ _ _ _ _ _ _ _ hc
  show viewN G x.1 (modeF Hb p₀ ns j cs' T' u) G2 u T' = viewN G x.1 (ctxF Hb p₀ ns j x.2.1 T' u
    (realRO (pw p₀ (ns ⟨j, hj⟩)) Hb (withP y.1 (pw p₀ (ns ⟨j, hj⟩))) y.2 ρ G3
      (shOf (p := pw p₀ (ns ⟨j, hj⟩)) (LJ Hb p₀ ns G j x u G2) u))) G2 u T'
  unfold viewN
  obtain ⟨e1, e2⟩ := runN_rel G x.1 (modeF Hb p₀ ns j cs' T' u)
    (ctxF Hb p₀ ns j x.2.1 T' u
      (realRO (pw p₀ (ns ⟨j, hj⟩)) Hb (withP y.1 (pw p₀ (ns ⟨j, hj⟩))) y.2 ρ G3
        (shOf (p := pw p₀ (ns ⟨j, hj⟩)) (LJ Hb p₀ ns G j x u G2) u)))
    G2 G2 (fun _ L L' => L = L') n le_rfl rfl fun k hk L' hL => by
      subst hL
      rcases lt_trichotomy k j with hkj | rfl | hkj
      · have hk' : (⟨k, hk⟩ : Fin n).val < j := hkj
        simp only [modeF, ctxF, hk', ↓reduceIte, hcs', Function.update_of_ne
          (show (⟨k, hk⟩ : Fin n) ≠ ⟨j, hj⟩ from fun h => by
            rw [Fin.mk.injEq] at h; omega)]
        rel_close
      · have h1 : ¬ (⟨k, hk⟩ : Fin n).val < k := lt_irrefl _
        simp only [modeF, ctxF, h1, ↓reduceIte]
        refine ⟨?_, rfl⟩
        rw [hyj]
        have hρ : (cs' ⟨k, hk⟩).1 = ρ := by rw [hcs', Function.update_self]
        have hT : T' (preOf Hb (pw p₀ (ns ⟨k, hk⟩)) y) = G3 := TJ_at Hb p₀ ns G k hj x y hy G3
        simp only [realF, givenF, Option.map_some, hρ, hT]
        unfold LJ
        rw [← hpre]
      · have h1 : ¬ (⟨k, hk⟩ : Fin n).val < j := by show ¬ k < j; omega
        have h2 : ¬ (⟨k, hk⟩ : Fin n).val = j := by show ¬ k = j; omega
        simp only [modeF, ctxF, h1, h2, ↓reduceIte, hcs', Function.update_of_ne
          (show (⟨k, hk⟩ : Fin n) ≠ ⟨j, hj⟩ from fun h => by
            rw [Fin.mk.injEq] at h; omega)]
        rel_close
  rw [e1, e2]

/-- **The simulated side of hop `j` is the context with the simulated proof**, its programming
applied to the raw table first. -/
theorem hyb_sim_eq (j : ℕ) (hj : j < n) (x : NTape p₀ ns S) (y : SW)
    (hy : yJ Hb p₀ ns G j hj x = some y) (u : USh) (ρ : Bytes 16)
    (c : SimCoins (pw p₀ (ns ⟨j, hj⟩))) (G3 : Tab3) (G2 : Tab2G p₀) :
    hybVN Hb p₀ ns G (j + 1) (setJ Hb p₀ ns G j hj x (u, ((ρ, c), (G3, G2)))) =
      ctxV Hb p₀ ns G j hj x (simulate (pw p₀ (ns ⟨j, hj⟩)) c)
        (G3, (progRO (pw p₀ (ns ⟨j, hj⟩)) Hb (withP y.1 (pw p₀ (ns ⟨j, hj⟩))) c
          (shOf (p := pw p₀ (ns ⟨j, hj⟩)) G2 u)).1) u := by
  set cs' := Function.update x.2.1 ⟨j, hj⟩ (ρ, c) with hcs'
  set T' := TJ Hb p₀ ns G j hj x G3 with hT'
  set P : Tab2G p₀ → Tab2G p₀ := fun H => (progRO (pw p₀ (ns ⟨j, hj⟩)) Hb
    (withP y.1 (pw p₀ (ns ⟨j, hj⟩))) c (shOf (p := pw p₀ (ns ⟨j, hj⟩)) H u)).1 with hP
  have hc : ∀ i : Fin n, i.val < j → (x.2.1 i).2 = (cs' i).2 := fun i hi =>
    (upd_lt p₀ ns x.2.1 (ρ, c) i hi).symm
  have hyj : G.σ ⟨j, hj⟩ x.1 (runN G x.1 (modeF Hb p₀ ns (j + 1) cs' T' u) G2 j).1 = some y := by
    rw [← hy]
    unfold yJ
    congr 1
    exact preRun_fst_eq Hb p₀ ns G j (j + 1) j hj.le le_rfl (by omega) x.1 _ _ _ _ _ _ _ _ hc
  show viewN G x.1 (modeF Hb p₀ ns (j + 1) cs' T' u) G2 u T' =
    viewN G x.1 (ctxF Hb p₀ ns j x.2.1 T' u (simulate (pw p₀ (ns ⟨j, hj⟩)) c)) (P G2) u T'
  unfold viewN
  obtain ⟨e1, e2⟩ := runN_rel G x.1 (modeF Hb p₀ ns (j + 1) cs' T' u)
    (ctxF Hb p₀ ns j x.2.1 T' u (simulate (pw p₀ (ns ⟨j, hj⟩)) c))
    G2 (P G2) (fun k L L' => (k ≤ j → L' = L) ∧ (j < k → ∀ H, L' (P H) = L H)) n le_rfl
    ⟨fun _ => rfl, fun h => absurd h (Nat.not_lt_zero _)⟩ fun k hk L' hL => by
      rcases lt_trichotomy k j with hkj | rfl | hkj
      · have hk' : (⟨k, hk⟩ : Fin n).val < j := hkj
        have hk'' : (⟨k, hk⟩ : Fin n).val < j + 1 := by show k < j + 1; omega
        have hL' := hL.1 hkj.le
        subst hL'
        simp only [modeF, ctxF, hk', hk'', ↓reduceIte, hcs', Function.update_of_ne
          (show (⟨k, hk⟩ : Fin n) ≠ ⟨j, hj⟩ from fun h => by
            rw [Fin.mk.injEq] at h; omega)]
        refine ⟨by rel_close, fun _ => by rel_close, fun h => absurd h (by omega)⟩
      · have hL' := hL.1 le_rfl
        subst hL'
        have h1 : ¬ (⟨k, hk⟩ : Fin n).val < k := lt_irrefl _
        have h2 : (⟨k, hk⟩ : Fin n).val < k + 1 := Nat.lt_succ_self k
        have hcj : (cs' ⟨k, hk⟩).2 = c := by rw [hcs', Function.update_self]
        simp only [modeF, ctxF, h1, h2, ↓reduceIte, hcj, hyj]
        exact ⟨rfl, fun h => absurd h (by omega), fun _ H => rfl⟩
      · have h1 : ¬ (⟨k, hk⟩ : Fin n).val < j := by show ¬ k < j; omega
        have h1' : ¬ (⟨k, hk⟩ : Fin n).val < j + 1 := by show ¬ k < j + 1; omega
        have h2 : ¬ (⟨k, hk⟩ : Fin n).val = j := by show ¬ k = j; omega
        simp only [modeF, ctxF, h1, h1', h2, ↓reduceIte, hcs', Function.update_of_ne
          (show (⟨k, hk⟩ : Fin n) ≠ ⟨j, hj⟩ from fun h => by
            rw [Fin.mk.injEq] at h; omega)]
        refine ⟨?_, fun h => absurd h (by omega), fun _ H => hL.2 hkj H⟩
        simp only [realF]
        rw [hL.2 hkj G2]
  rw [e1, (e2.2 hj) G2]

/-- **Without a statement for slot `j`, hybrids `j` and `j + 1` coincide.** -/
theorem hyb_none (j : ℕ) (hj : j < n) (x : NTape p₀ ns S) (hy : yJ Hb p₀ ns G j hj x = none)
    (b : USh × KS (pw p₀ (ns ⟨j, hj⟩))) :
    hybVN Hb p₀ ns G j (setJ Hb p₀ ns G j hj x b) =
      hybVN Hb p₀ ns G (j + 1) (setJ Hb p₀ ns G j hj x b) := by
  set x' := setJ Hb p₀ ns G j hj x b with hx'
  have hyj : G.σ ⟨j, hj⟩ x'.1 (runN G x'.1 (modeF Hb p₀ ns j x'.2.1 x'.2.2.1 x'.2.2.2.1)
      x'.2.2.2.2 j).1 = none := by
    rw [← hy, ← yJ_setJ Hb p₀ ns G j hj x b]
    rfl
  unfold hybVN viewN
  obtain ⟨e1, e2⟩ := runN_rel G x'.1 (modeF Hb p₀ ns j x'.2.1 x'.2.2.1 x'.2.2.2.1)
    (modeF Hb p₀ ns (j + 1) x'.2.1 x'.2.2.1 x'.2.2.2.1) x'.2.2.2.2 x'.2.2.2.2
    (fun _ L L' => L = L') n le_rfl rfl fun k hk L' hL => by
      subst hL
      rcases lt_trichotomy k j with hkj | rfl | hkj
      · have hk' : (⟨k, hk⟩ : Fin n).val < j := hkj
        have hk'' : (⟨k, hk⟩ : Fin n).val < j + 1 := by show k < j + 1; omega
        simp only [modeF, hk', hk'', ↓reduceIte]
        rel_close
      · have h1 : ¬ (⟨k, hk⟩ : Fin n).val < k := lt_irrefl _
        have h2 : (⟨k, hk⟩ : Fin n).val < k + 1 := Nat.lt_succ_self k
        simp only [modeF, h1, h2, ↓reduceIte, hyj]
        rel_close
      · have h1 : ¬ (⟨k, hk⟩ : Fin n).val < j := by show ¬ k < j; omega
        have h1' : ¬ (⟨k, hk⟩ : Fin n).val < j + 1 := by show ¬ k < j + 1; omega
        simp only [modeF, h1, h1', ↓reduceIte]
        rel_close
  rw [e1, e2]

end HopFiber






/-! ## The context reads the tables only at its keys -/

section SlotReads

variable (Hb : Hashes)

lemma realRO_u5 (p : Params) (ρ : Bytes 16) (G3 : Tab3) (u : USh) (y : SW) (M : Tab2G p)
    (G5 : Tab5F)
    (h : ∀ k ∈ realKeys5 p Hb (withP y.1 p) y.2 (ba ρ) G3 (shOf (p := p) M u), u.1 k = G5 k) :
    realRO p Hb (withP y.1 p) y.2 ρ G3 (shOf (p := p) M (G5, u.2)) =
      realRO p Hb (withP y.1 p) y.2 ρ G3 (shOf (p := p) M u) :=
  realRO_congr5 p Hb (withP y.1 p) y.2 ρ G3 (shOf (p := p) M u) G5 h

lemma realRO_uE (hHb : HashesWF Hb) (p : Params) (ρ : Bytes 16) (G3 : Tab3) (u : USh) (y : SW)
    (M : Tab2G p) (E : Cipher)
    (h : ∀ k ∈ realKeysE p Hb (withP y.1 p) y.2 (ba ρ) G3 (shOf (p := p) M u), u.2 k = E k) :
    realRO p Hb (withP y.1 p) y.2 ρ G3 (shOf (p := p) M (u.1, E)) =
      realRO p Hb (withP y.1 p) y.2 ρ G3 (shOf (p := p) M u) :=
  realRO_congrE p Hb (withP y.1 p) y.2 hHb ρ G3 (shOf (p := p) M u) E h

lemma realRO_g3 (p : Params) (ρ : Bytes 16) (G3 G3' : Tab3) (y : SW) (t : Sh p)
    (h : G3 ρ = G3' ρ) :
    realRO p Hb (withP y.1 p) y.2 ρ G3' t = realRO p Hb (withP y.1 p) y.2 ρ G3 t := by
  unfold realRO
  refine (realROb_g3_congr' (p := p) (Hb := Hb) (st := withP y.1 p) (w := y.2) (ba ρ) t ?_).symm
  rw [blk_ba]
  exact h

lemma progRO_u5 (p : Params) (st : Statement) (c : SimCoins p) (u : USh) (H : Tab2G p)
    (G5 : Tab5F)
    (h : ∀ k ∈ progKeys5 Hb st (simulate p c) (shOf (p := p) (Classical.arbitrary _) u),
      u.1 k = G5 k) :
    (progRO p Hb st c (shOf (p := p) H (G5, u.2))).1 = (progRO p Hb st c (shOf (p := p) H u)).1 :=
  progRO_congr5 Hb st c (shOf (p := p) H u) G5 fun k hk => h k (by
    rw [progKeys5_snd Hb p st _ (Classical.arbitrary _) H]; exact hk)

lemma progRO_uE (p : Params) (st : Statement) (c : SimCoins p) (u : USh) (H : Tab2G p)
    (E : Cipher)
    (h : ∀ k ∈ progKeysE Hb st (simulate p c) (shOf (p := p) (Classical.arbitrary _) u),
      u.2 k = E k) :
    (progRO p Hb st c (shOf (p := p) H (u.1, E))).1 = (progRO p Hb st c (shOf (p := p) H u)).1 :=
  progRO_congrE Hb st c (shOf (p := p) H u) E fun k hk => h k (by
    rw [progKeysE_snd Hb p st _ (Classical.arbitrary _) H]; exact hk)

variable (p₀ : Params) {n : ℕ} (ns : Fin n → ℕ)

lemma simF_u5 (i : Fin n) (c : SimCoins (pw p₀ (ns i))) (u : USh) (y : Option SW) (M : Tab2G p₀)
    (G5 : Tab5F) (h : ∀ k ∈ (simF Hb p₀ ns i c u y).k5 M, u.1 k = G5 k) :
    (simF Hb p₀ ns i c (G5, u.2) y).out M = (simF Hb p₀ ns i c u y).out M ∧
      (simF Hb p₀ ns i c (G5, u.2) y).pg = (simF Hb p₀ ns i c u y).pg := by
  refine ⟨rfl, ?_⟩
  rcases y with _ | y
  · rfl
  · funext H
    exact progRO_u5 Hb (pw p₀ (ns i)) (withP y.1 (pw p₀ (ns i))) c u H G5 h

lemma simF_uE (i : Fin n) (c : SimCoins (pw p₀ (ns i))) (u : USh) (y : Option SW) (M : Tab2G p₀)
    (E : Cipher) (h : ∀ k ∈ (simF Hb p₀ ns i c u y).kE M, u.2 k = E k) :
    (simF Hb p₀ ns i c (u.1, E) y).out M = (simF Hb p₀ ns i c u y).out M ∧
      (simF Hb p₀ ns i c (u.1, E) y).pg = (simF Hb p₀ ns i c u y).pg := by
  refine ⟨rfl, ?_⟩
  rcases y with _ | y
  · rfl
  · funext H
    exact progRO_uE Hb (pw p₀ (ns i)) (withP y.1 (pw p₀ (ns i))) c u H E h

lemma realF_u5 (i : Fin n) (ρ : Bytes 16) (T : H3T) (u : USh) (y : Option SW) (M : Tab2G p₀)
    (G5 : Tab5F) (h : ∀ k ∈ (realF Hb p₀ ns i ρ T u y).k5 M, u.1 k = G5 k) :
    (realF Hb p₀ ns i ρ T (G5, u.2) y).out M = (realF Hb p₀ ns i ρ T u y).out M ∧
      (realF Hb p₀ ns i ρ T (G5, u.2) y).pg = (realF Hb p₀ ns i ρ T u y).pg := by
  refine ⟨?_, rfl⟩
  rcases y with _ | y
  · exact (rfl : (none : Option Out) = none)
  · have h' : ∀ k ∈ realKeys5 (pw p₀ (ns i)) Hb (withP y.1 (pw p₀ (ns i))) y.2 (ba ρ)
        (T (preOf Hb (pw p₀ (ns i)) y)) (shOf (p := pw p₀ (ns i)) M u), u.1 k = G5 k := h
    show some _ = some _
    exact congrArg some (realRO_u5 Hb (pw p₀ (ns i)) ρ (T (preOf Hb (pw p₀ (ns i)) y)) u y M G5 h')

lemma realF_uE (hHb : HashesWF Hb) (i : Fin n) (ρ : Bytes 16) (T : H3T) (u : USh)
    (y : Option SW) (M : Tab2G p₀) (E : Cipher)
    (h : ∀ k ∈ (realF Hb p₀ ns i ρ T u y).kE M, u.2 k = E k) :
    (realF Hb p₀ ns i ρ T (u.1, E) y).out M = (realF Hb p₀ ns i ρ T u y).out M ∧
      (realF Hb p₀ ns i ρ T (u.1, E) y).pg = (realF Hb p₀ ns i ρ T u y).pg := by
  refine ⟨?_, rfl⟩
  rcases y with _ | y
  · exact (rfl : (none : Option Out) = none)
  · have h' : ∀ k ∈ realKeysE (pw p₀ (ns i)) Hb (withP y.1 (pw p₀ (ns i))) y.2 (ba ρ)
        (T (preOf Hb (pw p₀ (ns i)) y)) (shOf (p := pw p₀ (ns i)) M u), u.2 k = E k := h
    show some _ = some _
    exact congrArg some
      (realRO_uE Hb hHb (pw p₀ (ns i)) ρ (T (preOf Hb (pw p₀ (ns i)) y)) u y M E h')

lemma realF_T (i : Fin n) (ρ : Bytes 16) (P : Pre) (T₀ : H3T) (G3 G3' : Tab3) (u : USh)
    (y : Option SW) (M : Tab2G p₀) (h : G3 ρ = G3' ρ) :
    (realF Hb p₀ ns i ρ (Function.update T₀ P G3') u y).out M =
      (realF Hb p₀ ns i ρ (Function.update T₀ P G3) u y).out M := by
  rcases y with _ | y
  · exact (rfl : (none : Option Out) = none)
  · have e : Function.update T₀ P G3' (preOf Hb (pw p₀ (ns i)) y) =
          Function.update T₀ P G3 (preOf Hb (pw p₀ (ns i)) y) ∨
        (preOf Hb (pw p₀ (ns i)) y = P) := by
      by_cases hP : preOf Hb (pw p₀ (ns i)) y = P
      · exact Or.inr hP
      · left; rw [Function.update_of_ne hP, Function.update_of_ne hP]
    show some (realRO (pw p₀ (ns i)) Hb (withP y.1 (pw p₀ (ns i))) y.2 ρ
        (Function.update T₀ P G3' (preOf Hb (pw p₀ (ns i)) y)) (shOf (p := pw p₀ (ns i)) M u)) =
      some (realRO (pw p₀ (ns i)) Hb (withP y.1 (pw p₀ (ns i))) y.2 ρ
        (Function.update T₀ P G3 (preOf Hb (pw p₀ (ns i)) y)) (shOf (p := pw p₀ (ns i)) M u))
    rcases e with e | hP
    · rw [e]
    · rw [hP, Function.update_self, Function.update_self]
      exact congrArg some (realRO_g3 Hb (pw p₀ (ns i)) ρ G3 G3' y _ h)

end SlotReads

section CtxReads

variable (Hb : Hashes) (p₀ : Params) {n : ℕ} (ns : Fin n → ℕ) {S : Type} (G : NGame S n)

lemma ctxF_u5 (j : ℕ) (cs : CoinsN p₀ ns) (T : H3T) (u : USh) (o : Out) (i : Fin n)
    (y : Option SW) (M : Tab2G p₀) (G5 : Tab5F)
    (h : ∀ k ∈ (ctxF Hb p₀ ns j cs T u o i y).k5 M, u.1 k = G5 k) :
    (ctxF Hb p₀ ns j cs T (G5, u.2) o i y).out M = (ctxF Hb p₀ ns j cs T u o i y).out M ∧
      (ctxF Hb p₀ ns j cs T (G5, u.2) o i y).pg = (ctxF Hb p₀ ns j cs T u o i y).pg := by
  by_cases hi : i.val < j
  · have e : ∀ u', ctxF Hb p₀ ns j cs T u' o i y = simF Hb p₀ ns i (cs i).2 u' y := fun u' => by
      simp only [ctxF, hi, ↓reduceIte]
    rw [e, e] at *
    exact simF_u5 Hb p₀ ns i _ u y M G5 h
  · by_cases hi' : i.val = j
    · have e : ∀ u', ctxF Hb p₀ ns j cs T u' o i y = givenF p₀ o y := fun u' => by
        simp only [ctxF, hi', lt_irrefl, ↓reduceIte]
      rw [e, e]
      exact ⟨rfl, rfl⟩
    · have e : ∀ u', ctxF Hb p₀ ns j cs T u' o i y = realF Hb p₀ ns i (cs i).1 T u' y :=
        fun u' => by simp only [ctxF, hi, hi', ↓reduceIte]
      rw [e, e] at *
      exact realF_u5 Hb p₀ ns i _ T u y M G5 h

lemma ctxF_uE (hHb : HashesWF Hb) (j : ℕ) (cs : CoinsN p₀ ns) (T : H3T) (u : USh) (o : Out)
    (i : Fin n) (y : Option SW) (M : Tab2G p₀) (E : Cipher)
    (h : ∀ k ∈ (ctxF Hb p₀ ns j cs T u o i y).kE M, u.2 k = E k) :
    (ctxF Hb p₀ ns j cs T (u.1, E) o i y).out M = (ctxF Hb p₀ ns j cs T u o i y).out M ∧
      (ctxF Hb p₀ ns j cs T (u.1, E) o i y).pg = (ctxF Hb p₀ ns j cs T u o i y).pg := by
  by_cases hi : i.val < j
  · have e : ∀ u', ctxF Hb p₀ ns j cs T u' o i y = simF Hb p₀ ns i (cs i).2 u' y := fun u' => by
      simp only [ctxF, hi, ↓reduceIte]
    rw [e, e] at *
    exact simF_uE Hb p₀ ns i _ u y M E h
  · by_cases hi' : i.val = j
    · have e : ∀ u', ctxF Hb p₀ ns j cs T u' o i y = givenF p₀ o y := fun u' => by
        simp only [ctxF, hi', lt_irrefl, ↓reduceIte]
      rw [e, e]
      exact ⟨rfl, rfl⟩
    · have e : ∀ u', ctxF Hb p₀ ns j cs T u' o i y = realF Hb p₀ ns i (cs i).1 T u' y :=
        fun u' => by simp only [ctxF, hi, hi', ↓reduceIte]
      rw [e, e] at *
      exact realF_uE Hb p₀ ns hHb i _ T u y M E h

lemma ctxF_T (j : ℕ) (cs : CoinsN p₀ ns) (P : Pre) (T₀ : H3T) (G3 G3' : Tab3) (u : USh)
    (o : Out) (i : Fin n) (y : Option SW) (M : Tab2G p₀) (h : G3 (cs i).1 = G3' (cs i).1) :
    (ctxF Hb p₀ ns j cs (Function.update T₀ P G3') u o i y).out M =
      (ctxF Hb p₀ ns j cs (Function.update T₀ P G3) u o i y).out M ∧
    (ctxF Hb p₀ ns j cs (Function.update T₀ P G3') u o i y).pg =
      (ctxF Hb p₀ ns j cs (Function.update T₀ P G3) u o i y).pg := by
  by_cases hi : i.val < j
  · simp only [ctxF, hi, ↓reduceIte]
    rel_close
  · by_cases hi' : i.val = j
    · simp only [ctxF, hi', lt_irrefl, ↓reduceIte]
      rel_close
    · have e : ∀ T, ctxF Hb p₀ ns j cs T u o i y = realF Hb p₀ ns i (cs i).1 T u y :=
        fun T => by simp only [ctxF, hi, hi', ↓reduceIte]
      rw [e, e]
      exact ⟨realF_T Hb p₀ ns i _ P T₀ G3 G3' u y M h, rfl⟩

lemma ctxF_cov (hHb : HashesWF Hb) (hm : ∀ i, MainP (pw p₀ (ns i))) (j : ℕ) (cs : CoinsN p₀ ns)
    (T : H3T) (u : USh) (o : Out) (i : Fin n) (y : Option SW)
    (hy : ∀ sw ∈ y, ValidZK CrtGen.tables (pw p₀ (ns i)) sw) :
    (ctxF Hb p₀ ns j cs T u o i y).Cov Hb p₀ (pw p₀ (ns i)) y u.2 := by
  unfold ctxF
  split
  · exact simF_cov Hb p₀ ns i _ u y hy
  · split
    · exact givenF_cov Hb p₀ _ o y u.2
    · exact realF_cov Hb p₀ ns i (hm i) hHb _ T u y hy

/-- `runN_rel` for a slot-wise congruence (same raw table, related composites equal). -/
lemma runN_congr (s : S) (f f' : (i : Fin n) → Option SW → SlotF p₀) (G2 : Tab2G p₀)
    (h : ∀ i : Fin n, (f' i (stN G s f G2 i)).out (tabN G s f G2 i) =
        (f i (stN G s f G2 i)).out (tabN G s f G2 i) ∧
      (f' i (stN G s f G2 i)).pg = (f i (stN G s f G2 i)).pg) :
    runN G s f' G2 n = runN G s f G2 n := by
  obtain ⟨e1, e2⟩ := runN_rel G s f f' G2 G2 (fun _ L L' => L = L') n le_rfl rfl
    fun k hk L' hL => by
      subst hL
      obtain ⟨h1, h2⟩ := h ⟨k, by omega⟩
      exact ⟨h1, congrArg _ h2.symm⟩
  exact Prod.ext e1 e2.symm

end CtxReads

/-! ## The bad event of hop `j` -/

section CtxBad

variable (Hb : Hashes) (p₀ : Params) {n : ℕ} (ns : Fin n → ℕ) {S : Type} (G : NGame S n)

/-- **Every statement of the game is valid**, and every slot's parameters are `main`'s with small
sizes. -/
structure NValid (G : NGame S n) (p₀ : Params) (ns : Fin n → ℕ) : Prop where
  v : ∀ i s os, ∀ y ∈ G.σ i s os, ValidZK CrtGen.tables (pw p₀ (ns i)) y
  m : ∀ i, MainP (pw p₀ (ns i))
  sm : ∀ i, SmallParams (pw p₀ (ns i))

set_option maxRecDepth 8000 in
/-- **The bad event of hop `j`, on the simulated proof, implies `bstarN`**: the predictor's
read set is the event's and the other slots' reads, which are keys of their proofs. -/
theorem ctx_bad (hHb : HashesWF Hb) (hv : NValid G p₀ ns) (j : ℕ) (hj : j < n)
    (x : NTape p₀ ns S) (y : SW) (hy : yJ Hb p₀ ns G j hj x = some y)
    (R5 : NView S n p₀ → Finset (Bytes 37)) (c : SimCoins (pw p₀ (ns ⟨j, hj⟩)))
    (V : VP (pw p₀ (ns ⟨j, hj⟩))) (u : USh)
    (hz : (letI : HasPrg := icPrg u.2
      wPre y.2 ∈ candidatesG Hb CrtGen.tables (withP y.1 (pw p₀ (ns ⟨j, hj⟩))) enc5 (hv.m _)
        (R5 (ctxV Hb p₀ ns G j hj x (simulate _ c) V u) ∪
          trace5 p₀ G x.1 (ctxF Hb p₀ ns j x.2.1 (TJ Hb p₀ ns G j hj x V.1) u (simulate _ c)) V.2)
        c.1 c.2)) :
    bstarN Hb G (fun i => pw p₀ (ns i)) R5 (ctxV Hb p₀ ns G j hj x (simulate _ c) V u) := by
  classical
  set f := ctxF Hb p₀ ns j x.2.1 (TJ Hb p₀ ns G j hj x V.1) u (simulate _ c) with hf
  set v := ctxV Hb p₀ ns G j hj x (simulate _ c) V u with hvdef
  have hyN : ∀ i, yN G i v = stN G x.1 f V.2 i := fun i => yN_viewN G x.1 f V.2 u _ i
  have hos : ∀ i, v.os i = (sfN G x.1 f V.2 i).out (tabN G x.1 f V.2 i) := fun i =>
    os_viewN G x.1 f V.2 u _ i
  have hst : stN G x.1 f V.2 ⟨j, hj⟩ = some y :=
    (stN_ctx_j Hb p₀ ns G j hj x (TJ Hb p₀ ns G j hj x V.1) u (simulate _ c) V.2).trans hy
  have hosj : v.os ⟨j, hj⟩ = some (simulate _ c) := by
    rw [hos]
    unfold sfN
    rw [hst]
    have e : f ⟨j, hj⟩ (some y) = givenF p₀ (simulate _ c) (some y) := by
      simp only [hf, ctxF, lt_irrefl, ↓reduceIte]
    rw [e]
    rfl
  have hvu : v.u = u := rfl
  rcases @pred_imp Hb (icPrg u.2) (pw p₀ (ns ⟨j, hj⟩)) (hv.m _) y c _ hz with h | h | h
  · exact Or.inl ⟨⟨j, hj⟩, by rw [hosj]; exact h⟩
  · refine Or.inr ⟨⟨j, hj⟩, Or.inl ?_⟩
    rw [hyN, hst, hosj]; exact h
  · obtain ⟨k, hk, hx⟩ := h
    have hhit : slotHit Hb (pw p₀ (ns ⟨j, hj⟩)) (yN G ⟨j, hj⟩ v) (v.os ⟨j, hj⟩) v.u.2 k := by
      rw [hyN, hst, hosj]
      exact slotHit_of (Hb := Hb) y _ _ k hx
    rcases mem_union.1 hk with hk | hk
    · exact Or.inr ⟨⟨j, hj⟩, Or.inr ⟨k, mem_union_left _ hk, hhit⟩⟩
    · obtain ⟨i, -, hki⟩ := mem_biUnion.1 hk
      by_cases hij : i = ⟨j, hj⟩
      · subst hij
        exfalso
        unfold sfN at hki
        rw [hst] at hki
        have e : f ⟨j, hj⟩ (some y) = givenF p₀ (simulate _ c) (some y) := by
          simp only [hf, ctxF, lt_irrefl, ↓reduceIte]
        rw [e] at hki
        exact absurd hki (Finset.notMem_empty k)
      · have hcov := ctxF_cov Hb p₀ ns hHb hv.m j x.2.1 (TJ Hb p₀ ns G j hj x V.1) u
          (simulate _ c) i (stN G x.1 f V.2 i) (hv.v i _ _) (tabN G x.1 f V.2 i) k hki
        rcases hcov with he | hk'
        · exact Or.inl ⟨i, by rw [hos]; exact he⟩
        · refine Or.inr ⟨⟨j, hj⟩, Or.inr ⟨k, mem_union_right _ (mem_biUnion.2 ⟨i,
            mem_filter.2 ⟨mem_univ _, hij⟩, ?_⟩), hhit⟩⟩
          rw [hyN, hos, hvu]
          exact hk'

end CtxBad

end VoleMole.ZK.Sim
