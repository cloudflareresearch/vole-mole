import VoleMole.Theft.Tables
import VoleMole.Theft.Many
import VoleMole.ZK.CollideRO

/-!
# The collision terms of the theft games: the generic bound with an extra table

The hybrids of the theft and non-malleability games (`Theft/Basic.lean`, `Theft/Many.lean`) carry
collision terms `δ` (`deltaG`, `deltaN`): the probability that a real proof, run on the tables the
earlier simulations programmed, differs from the proof on the original tables. In the privacy games
they are bounded by `pr_collide_zk` (`ZK/CollideRO.lean`). The theft games run on the tables with
one more component `x : X` (`ShX R p X`, `Theft/Tables.lean`), the base hash record `Hb x` read off
it. Here the bound is lifted to these tables.

* **`ProgTails L T`**: a programming of `ShX R p X` that changes only `H₂³`, and there only at the
  keys whose prefix block's tail (`preTail`, the field `ã`) is in the set `T`. The identity, the
  composition (`ProgTails.comp`, union of the sets), a simulator's programming `progX` with tail
  `simTail c` (`progTails_progRO`), and an optional statement's programming (`ProgTails.progO`).
* **`pr_collide_zkX`**: for a real proof whose statement does not depend on the tables, and a
  programming with `ProgTails L T`,

      Pr[ realRO(L t) ≠ realRO(t) ] ≤ 2⁻¹¹³ + εz(p; 0, 312, 4607) + noHitProb + |T|·2^(−8·16(d−1)).

  The proof conditions on the extra table and applies `pr_collide_zk` at every value of it.
* **`simPre_progTails`**: the programming of the first `j` simulated slots of `Theft/Many.lean`
  (`simPre`) has `ProgTails` with the union of the slots' tail sets; **`pr_deltaN_le`**: the
  collision term of hop `i` is bounded by a bound for every fixed rest of the tape.
-/

-- (The coin types are large products: their `Fintype` instances exceed the default size.)
set_option synthInstance.maxSize 1024

open Finset

namespace VoleMole.Theft

open VoleMole.Privacy VoleMole.ZK.Sim VoleMole.Verifier VoleMole.Verifier.Bridge VoleMole.Arith
  VoleMole.ZK

/-! ## Programmings at prefix tails -/

section ProgTails

variable {R : Type} {p : Params} {X : Type}

/-- **A programming of the tables at prefix tails in `T`**: it changes only `H₂³` (not `H₅`, the
cipher or the extra table), and there only the keys whose prefix block has its tail in `T`. -/
def ProgTails (L : ShX R p X → ShX R p X) (T : Finset ByteArray) : Prop :=
  (∀ t, (L t).2 = t.2) ∧ ∀ t (k : K2 p), preTail k.1 ∉ T → (L t).1 k = t.1 k

lemma ProgTails.id : ProgTails (fun t : ShX R p X => t) ∅ :=
  ⟨fun _ => rfl, fun _ _ _ => rfl⟩

lemma ProgTails.comp {L L' : ShX R p X → ShX R p X} {T T' : Finset ByteArray}
    (h : ProgTails L T) (h' : ProgTails L' T') : ProgTails (fun t => L (L' t)) (T ∪ T') := by
  refine ⟨fun t => (h.1 _).trans (h'.1 t), fun t k hk => ?_⟩
  rw [Finset.mem_union, not_or] at hk
  exact (h.2 _ k hk.1).trans (h'.2 t k hk.2)

lemma ProgTails.mono {L : ShX R p X → ShX R p X} {T T' : Finset ByteArray} (h : ProgTails L T)
    (hT : T ⊆ T') : ProgTails L T' :=
  ⟨h.1, fun t k hk => h.2 t k fun h' => hk (hT h')⟩

lemma ProgTails.congr {L L' : ShX R p X → ShX R p X} {T : Finset ByteArray} (h : ProgTails L T)
    (e : ∀ t, L' t = L t) : ProgTails L' T :=
  ⟨fun t => by rw [e]; exact h.1 t, fun t k hk => by rw [e]; exact h.2 t k hk⟩

/-- The extra table is not programmed. -/
lemma ProgTails.snd_snd {L : ShX R p X → ShX R p X} {T : Finset ByteArray} (h : ProgTails L T)
    (t : ShX R p X) : (L t).2.2 = t.2.2 :=
  congrArg Prod.snd (h.1 t)

/-- **An optional statement's programming**: none if there is no statement. -/
lemma ProgTails.progO {I C : Type*} {prog : I → C → ShX R p X → ShX R p X} {xo : Option I}
    {c : C} {T : Finset ByteArray} (h : ∀ i, xo = some i → ProgTails (prog i c) T) :
    ProgTails (fun t => Theft.progO prog xo c t) T := by
  rcases xo with _ | i
  · exact ProgTails.id.mono (Finset.empty_subset _)
  · exact h i rfl

/-- **A programming of the zero-knowledge tables at every value of the extra table** (`progX`)
whose programmed blocks have their tails in `T`. -/
lemma progTails_progX {I C : Type*} (prog : X → I → C → ShG R p → ShG R p) (i : I) (c : C)
    (B : X → ShG R p → Finset (ZK.Sim.Bytes (preLen p))) (h : ∀ x, ProgAt (prog x i c) (B x))
    (T : Finset ByteArray) (hT : ∀ x s, ∀ b ∈ B x s, preTail b ∈ T) :
    ProgTails (progX prog i c) T := by
  refine ⟨fun t => ?_, fun t k hk => ?_⟩
  · show ((prog t.2.2 i c (shOf t)).2, t.2.2) = t.2
    rw [(h t.2.2).1]
    rfl
  · show (prog t.2.2 i c (shOf t)).1 k = t.1 k
    exact (h t.2.2).2 _ k fun hb => hk (hT _ _ _ hb)

variable [CipherRow R]

/-- **A simulator's programming** (`progRO`, at every value of the extra table, the base record
`Hb x`) programs at prefix blocks with tail `simTail c`. -/
lemma progTails_progRO {I : Type*} {Hb : X → Hashes} (hHb : ∀ x, HashesWF (Hb x))
    (st : I → Statement) (hst : ∀ i, (st i).params = p) (i : I) (c : SimCoins p) :
    ProgTails (progX (fun x i c => progRO (R := R) p (Hb x) (st i) c) i c) {simTail c} :=
  progTails_progX _ i c _ (fun x => progRO_progAt (Hb x) (st i) c) _
    fun x s b hb => by
      rw [Finset.mem_singleton] at hb ⊢
      rw [hb]
      exact preTail_simBlk (hHb x) (hst i) c s

end ProgTails

/-! ## The collision bound with an extra table -/

section Collide

variable {R : Type} [Fintype R] [Nonempty R] [CipherRow R] {X : Type} [Fintype X] [Nonempty X]

/-- **The programming-collision bound with an extra table**: a real proof whose statement does
not depend on the tables, the base record read off the extra table, changes under a programming
at prefix tails in `T` with probability at most

    2⁻¹¹³ + εz(p; 0, 312, 4607) + noHitProb + |T|·2^(−8·16(d−1)). -/
theorem pr_collide_zkX [ZKRow R] {Hb : X → Hashes} (hHb : ∀ x, HashesWF (Hb x)) {st : Statement}
    {w : ByteArray} {cs : ByteArray → ByteArray → System GF128} (hlr : st.params.labelRows = true)
    (hzk : ZKHyp CrtGen.tables st w cs) (hp : SmallParams st.params)
    {L : ShX R st.params X → ShX R st.params X} {T : Finset ByteArray} (hL : ProgTails L T) :
    pr ((ZK.Sim.Bytes 16 × Tab3) × ShX R st.params X) (fun a =>
        realRO st.params (Hb a.2.2.2) st w a.1.1 a.1.2 (shOf (L a.2)) ≠
          realRO st.params (Hb a.2.2.2) st w a.1.1 a.1.2 (shOf a.2)) ≤
      1 / 2 ^ 113 + ZKRow.εz R st.params 0 312 4607 +
        (noHitProb + T.card / 2 ^ (8 * (16 * (st.params.qsDegree - 1)))) := by
  classical
  let e : X × ((ZK.Sim.Bytes 16 × Tab3) × ShG R st.params) ≃
      (ZK.Sim.Bytes 16 × Tab3) × ShX R st.params X :=
    { toFun := fun z => (z.2.1, atX z.2.2 z.1)
      invFun := fun a => (a.2.2.2, (a.1, shOf a.2))
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [← pr_equiv e]
  refine pr_le_of_fst fun x => ?_
  have hL' : ProgAt (fun s => shOf (L (atX s x)))
      (fun _ => Finset.univ.filter fun b : ZK.Sim.Bytes (preLen st.params) => preTail b ∈ T) := by
    refine ⟨fun s => ?_, fun s k hk => ?_⟩
    · show (L (atX s x)).2.1 = s.2
      rw [hL.1]
      rfl
    · show (L (atX s x)).1 k = s.1 k
      refine hL.2 _ k fun hm => hk ?_
      simpa using hm
  have hb := pr_collide_zk (R := R) (Hb := Hb x) hlr hzk (hHb x) hp hL' T
    fun s b hb => by simpa using hb
  have e2 : ∀ b : (ZK.Sim.Bytes 16 × Tab3) × ShG R st.params,
      (realRO st.params (Hb (e (x, b)).2.2.2) st w (e (x, b)).1.1 (e (x, b)).1.2
          (shOf (L (e (x, b)).2)) ≠
        realRO st.params (Hb (e (x, b)).2.2.2) st w (e (x, b)).1.1 (e (x, b)).1.2
          (shOf (e (x, b)).2)) ↔
      realRO st.params (Hb x) st w b.1.1 b.1.2 (shOf (L (atX b.2 x))) ≠
        realRO st.params (Hb x) st w b.1.1 b.1.2 b.2 := fun _ => Iff.rfl
  rw [pr_congr e2]
  exact hb

end Collide

/-! ## The programming of the simulated prefix of `N` slots -/

section Many

variable {R : Type} {p : Params} {X : Type} {Ω O C : Type*}
  (Sm : Ω → List O → C → O) (pg : Ω → List O → C → ShX R p X → ShX R p X)

/-- **The simulated prefix programs at the slots' tails**: if each slot's programming has
`ProgTails` with a set `F c` of its coins, the first `j` slots' programming has `ProgTails` with
the union over `k < j`. -/
lemma simPre_progTails (F : C → Finset ByteArray) (hpg : ∀ ω l c, ProgTails (pg ω l c) (F c))
    (ω : Ω) (cs : ℕ → C) :
    ∀ j, ProgTails (simPre Sm pg ω cs j).2 ((Finset.range j).biUnion fun k => F (cs k))
  | 0 => by
    simp only [simPre, Finset.range_zero, Finset.biUnion_empty]
    exact ProgTails.id.congr fun t => rfl
  | j + 1 => by
    have h := (simPre_progTails F hpg ω cs j).comp (hpg ω (simPre Sm pg ω cs j).1 (cs j))
    refine (h.congr fun t => rfl).mono ?_
    rw [Finset.range_add_one, Finset.biUnion_insert, Finset.union_comm]

/-- **The collision term of hop `i`, slot by slot**: a bound for every rest of the tape (the
secrets and the other slots fixed, so the history and the earlier programming are fixed) on the
probability that the real proof of slot `i` differs with and without the programming bounds
`Pr[deltaN i]`. -/
theorem pr_deltaN_le {Ω O ρ C G S : Type*} [Fintype Ω] [Nonempty Ω] [Fintype ρ] [Nonempty ρ]
    [Fintype C] [Nonempty C] [Fintype G] [Nonempty G] [Fintype S] {N : ℕ}
    (P : Ω → List O → ρ → G → S → O) (Sm : Ω → List O → C → O) (pg : Ω → List O → C → S → S)
    (i : Fin N) {ε : ℝ}
    (h : ∀ ω (τ : Fin N → Slot ρ C G), pr ((ρ × G) × S) (fun a =>
      P ω (simPre Sm pg ω (tapeC τ) i).1 a.1.1 a.1.2 ((simPre Sm pg ω (tapeC τ) i).2 a.2) ≠
        P ω (simPre Sm pg ω (tapeC τ) i).1 a.1.1 a.1.2 a.2) ≤ ε) :
    pr ((Ω × (Fin N → Slot ρ C G)) × S) (deltaN P Sm pg i) ≤ ε := by
  rw [← pr_slot i]
  refine pr_le_of_fst fun γ => ?_
  have e : ∀ b : Slot ρ C G × S, deltaN P Sm pg i ((γ.1, Function.update γ.2 i b.1), b.2) ↔
      (fun (r : ρ) (g : G) (s : S) =>
        P γ.1 (simPre Sm pg γ.1 (tapeC γ.2) i).1 r g ((simPre Sm pg γ.1 (tapeC γ.2) i).2 s) ≠
          P γ.1 (simPre Sm pg γ.1 (tapeC γ.2) i).1 r g s) b.1.1.1 b.1.2 b.2 := by
    intro b
    simp only [deltaN, simPre_update, tapeR_update_self]
  rw [pr_congr e, pr_slot_real (C := C) (fun (r : ρ) (g : G) (s : S) =>
    P γ.1 (simPre Sm pg γ.1 (tapeC γ.2) i).1 r g ((simPre Sm pg γ.1 (tapeC γ.2) i).2 s) ≠
      P γ.1 (simPre Sm pg γ.1 (tapeC γ.2) i).1 r g s)]
  exact h γ.1 γ.2

/-- The union of `j` sets of at most two elements has at most `2·j`. -/
lemma card_biUnion_le_two {C : Type*} (F : C → Finset ByteArray) (hF : ∀ c, (F c).card ≤ 2)
    (cs : ℕ → C) (j : ℕ) : ((Finset.range j).biUnion fun k => F (cs k)).card ≤ 2 * j := by
  refine (Finset.card_biUnion_le).trans ?_
  calc ∑ k ∈ Finset.range j, (F (cs k)).card ≤ ∑ _k ∈ Finset.range j, 2 :=
        Finset.sum_le_sum fun k _ => hF (cs k)
    _ = 2 * j := by rw [Finset.sum_const, Finset.card_range, smul_eq_mul, mul_comm]

end Many

end VoleMole.Theft
