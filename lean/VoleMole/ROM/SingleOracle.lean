import VoleMole.ROM.Accept
import VoleMole.ROM.DomainSep

/-!
# The soundness game against one SHAKE oracle

`ROM/DomainSep.lean` shows that one random oracle on byte strings, with a domain rule `κ`, gives
every event the probability of the per-domain oracles, for computations whose queries respect `κ`
(`prEvent_route_eq`), and that every single-oracle adversary is such a computation
(`unroute`, `prEvent_unroute_eq`). Here `κ` is L0's rule and the computation is the soundness game.

* `l0Kind`: L0 §2.1's domain of an input, read from its final byte (`1` `H₁`, `3` `H₃`, `4` `H₄`,
  `5` `H₅`, `8` `H₂⁰`, `9` `H₂¹`, `10` `H₂²`, `11` `H₂³`, `12` `H₂⁴`, `'0'` the combination of the
  45 UOV equations, which all three combined relations use).
* `allQueriesSatisfy_verifyQ`: **the verifier's own queries are in their L0 domains** (every input
  ends with its domain byte; the combination DST ends with `'0'`), for statements whose combination
  is 45 equations with such a DST (`CombOk`: true for all five relations, `combOk_*`).
* `game₁ T st A`: the game against the single oracle, for a prover `A` against it: `A`, then the
  verifier, every hash a query to the one oracle (`game₁_eq`).
* `prEvent_game₁_eq`: its event probabilities are those of `game T st (unroute l0Kind A)`, the
  per-domain game. So every bound of `ROM/Accept.lean` holds for single-oracle provers, with the
  per-domain counts of `A` (`isKindQueryBound_unroute`, `isTotalQueryBound_unroute`).
-/

open ENNReal OracleComp OracleSpec

namespace VoleMole.ROM

-- The statements hold for any CTR PRG (`HasPrg`, `Verifier/Prg.lean`), AES included.
variable [VoleMole.Verifier.HasPrg]

open VoleMole.Prob VoleMole.Verifier VoleMole.Verifier.Bridge

/-- L0's domain of a final byte. -/
def kindOfByte (b : UInt8) : Kind :=
  match b.toNat with
  | 1 => .h1
  | 3 => .h3
  | 4 => .h4
  | 5 => .h5
  | 8 => .mu
  | 9 => .h21
  | 10 => .h22
  | 11 => .h23
  | 12 => .muDelayed
  | 48 => .comb 45
  | _ => .h1

/-- **L0's domain rule**: the domain of an input is read from its final byte. -/
def l0Kind (x : ByteArray) : Kind := kindOfByte x[x.size - 1]!

omit [VoleMole.Verifier.HasPrg] in
@[simp] lemma l0Kind_push (a : ByteArray) (b : UInt8) : l0Kind (a.push b) = kindOfByte b := by
  simp [l0Kind, ByteArray.size_push]

omit [VoleMole.Verifier.HasPrg] in
lemma l0Kind_append {a c : ByteArray} (hc : 0 < c.size) : l0Kind (a ++ c) = l0Kind c := by
  have h1 : (a ++ c).size - 1 < (a ++ c).size := by simp [ByteArray.size_append]; omega
  have h2 : c.size - 1 < c.size := by omega
  simp only [l0Kind]
  rw [getElem!_pos (a ++ c) _ h1, getElem!_pos c _ h2,
    ByteArray.getElem_append_right (by simp [ByteArray.size_append]; omega)]
  congr 2
  simp [ByteArray.size_append]; omega

/-- The statement's combination (if any) is 45 equations, with a DST ending with `'0'`. -/
def CombOk (st : Statement) : Prop :=
  ∀ M dst, st.comb = some (M, dst) → M = 45 ∧ 0 < dst.size ∧ dst[dst.size - 1]! = 48

omit [VoleMole.Verifier.HasPrg] in
/-- `l.length` queries in their domains, then `f`. -/
lemma allQueriesSatisfy_mapM_hashQ_bind {α : Type} (k : Kind) (l : List ByteArray)
    {f : List ByteArray → OracleComp spec α} {P : Dom → Prop} (hl : ∀ x ∈ l, P (k, x))
    (hf : ∀ ans, AllQueriesSatisfy (f ans) P) : AllQueriesSatisfy (l.mapM (hashQ k) >>= f) P := by
  induction l generalizing f with
  | nil => simpa using hf []
  | cons x l ih =>
    simp only [List.mapM_cons, bind_assoc, pure_bind, hashQ_bind]
    exact (allQueriesSatisfy_query_bind_iff _ _ _).mpr ⟨hl x (by simp), fun u =>
      ih (fun y hy => hl y (by simp [hy])) fun ans => hf _⟩

omit [VoleMole.Verifier.HasPrg] in
lemma allQueriesSatisfy_hashQ_bind {α : Type} {k : Kind} {x : ByteArray}
    {f : ByteArray → OracleComp spec α} {P : Dom → Prop} (hx : P (k, x))
    (hf : ∀ u, AllQueriesSatisfy (f u) P) : AllQueriesSatisfy (hashQ k x >>= f) P := by
  rw [hashQ_bind]
  exact (allQueriesSatisfy_query_bind_iff _ _ _).mpr ⟨hx, fun u => hf _⟩

/-- **The verifier's queries are in their L0 domains.** -/
theorem allQueriesSatisfy_verifyQ (T : CrtTables) (st : Statement) (hst : CombOk st)
    (proof : ByteArray) :
    AllQueriesSatisfy (verifyQ T st proof) fun d => l0Kind d.2 = d.1 := by
  unfold verifyQ
  dsimp only
  split
  · exact allQueriesSatisfy_pure _ _
  have hmu : ∀ {f : ByteArray → OracleComp spec Transcript},
      (∀ u, AllQueriesSatisfy (f u) fun d => l0Kind d.2 = d.1) →
      AllQueriesSatisfy (mu1Q st >>= f) fun d => l0Kind d.2 = d.1 := by
    intro f hf
    unfold mu1Q
    split
    · exact allQueriesSatisfy_hashQ_bind (by simp [kindOfByte]) hf
    · exact allQueriesSatisfy_hashQ_bind (by simp [kindOfByte]) hf
  refine hmu fun mu1 => allQueriesSatisfy_hashQ_bind (by simp [kindOfByte]) fun iv => ?_
  split
  · exact allQueriesSatisfy_pure _ _
  refine allQueriesSatisfy_mapM_hashQ_bind _ _ (fun x hx => ?_) fun lh => ?_
  · obtain ⟨i, -, rfl⟩ := List.mem_map.1 hx
    simp [kindOfByte]
  refine allQueriesSatisfy_hashQ_bind (by simp [BAVC.comInput, kindOfByte]) fun com => ?_
  refine allQueriesSatisfy_hashQ_bind (by simp [chal1Input, kindOfByte]) fun c1 => ?_
  refine allQueriesSatisfy_mapM_hashQ_bind _ _ (fun x hx => ?_) fun gh => ?_
  · obtain ⟨i, -, rfl⟩ := List.mem_map.1 hx
    simp [kindOfByte]
  have hmuD : ∀ {f : ByteArray → OracleComp spec Transcript},
      (∀ u, AllQueriesSatisfy (f u) fun d => l0Kind d.2 = d.1) →
      AllQueriesSatisfy (muDelayedQ st c1 >>= f) fun d => l0Kind d.2 = d.1 := by
    intro f hf
    unfold muDelayedQ
    split
    · exact allQueriesSatisfy_hashQ_bind (by simp [kindOfByte]) hf
    · rw [pure_bind]; exact hf _
  refine hmuD fun muD => allQueriesSatisfy_hashQ_bind (by simp [chal2Input, kindOfByte])
    fun c2 => ?_
  split
  · exact allQueriesSatisfy_pure _ _
  have hcb : ∀ {f : ByteArray → OracleComp spec Transcript},
      (∀ u, AllQueriesSatisfy (f u) fun d => l0Kind d.2 = d.1) →
      AllQueriesSatisfy (combBytesQ st c2 >>= f) fun d => l0Kind d.2 = d.1 := by
    intro f hf
    unfold combBytesQ
    split
    · rw [pure_bind]; exact hf _
    · rename_i M dst hc
      obtain ⟨rfl, hsz, hlast⟩ := hst M dst hc
      refine allQueriesSatisfy_hashQ_bind ?_ hf
      simp only [l0Kind_append hsz]
      simp [l0Kind, hlast, kindOfByte]
  exact hcb fun lb => allQueriesSatisfy_hashQ_bind (by simp [chal3Input, kindOfByte])
    fun c3 => allQueriesSatisfy_pure _ _

omit [VoleMole.Verifier.HasPrg] in
lemma combOk_dst {M : ℕ} {dst : ByteArray} (hM : M = 45) (hsz : 0 < dst.size)
    (hlast : dst[dst.size - 1]! = 48) {st : Statement} (h : st.comb = some (M, dst)) :
    CombOk st := fun M' dst' h' => by
  rw [h] at h'
  cases h'
  exact ⟨hM, hsz, hlast⟩

omit [VoleMole.Verifier.HasPrg] in
theorem combOk_moussakaIssue (t ctxIss : ByteArray) (labelRows : Bool) :
    CombOk (moussakaIssue t ctxIss labelRows) := fun _ _ h => by cases h

omit [VoleMole.Verifier.HasPrg] in
theorem combOk_ratatouilleIssue (c : ByteArray) (tInit : ℕ) (ctxIss : ByteArray)
    (labelRows : Bool) : CombOk (ratatouilleIssue c tInit ctxIss labelRows) := fun _ _ h => by
  cases h

omit [VoleMole.Verifier.HasPrg] in
theorem combOk_moussakaRedeem (anchors : List UovPk) (nf ctxIss ctxRed challengeDigest : ByteArray)
    (labelRows : Bool) :
    CombOk (moussakaRedeem anchors nf ctxIss ctxRed challengeDigest labelRows) :=
  combOk_dst rfl (by decide) (by decide) rfl

omit [VoleMole.Verifier.HasPrg] in
theorem combOk_ratatouilleSpend (pk : UovPk) (nf : ByteArray) (d : ℕ) (cNext ctxIss : ByteArray)
    (labelRows : Bool) : CombOk (ratatouilleSpend pk nf d cNext ctxIss labelRows) :=
  combOk_dst rfl (by decide) (by decide) rfl

omit [VoleMole.Verifier.HasPrg] in
theorem combOk_pomfritRedeem (pk : UovPk) (sig msg : ByteArray) (labelRows : Bool) :
    CombOk (pomfritRedeem pk sig msg labelRows) :=
  combOk_dst rfl (by decide) (by decide) rfl

/-! ## The game against the single oracle -/

variable {β : Type}

/-- **The soundness game against one SHAKE oracle**: the prover `A` and the verifier both ask the
single oracle `spec₁ l0Kind` (`game₁_eq`). -/
def game₁ (T : CrtTables) (st : Statement)
    (A : OracleComp (spec₁ l0Kind) (ByteArray × ExtData β)) :
    OracleComp (spec₁ l0Kind) (ByteArray × ExtData β × Transcript) :=
  route l0Kind (game T st (unroute l0Kind A))

/-- `game₁` is the prover, then the verifier with its queries asked of the single oracle. -/
theorem game₁_eq (T : CrtTables) (st : Statement)
    (A : OracleComp (spec₁ l0Kind) (ByteArray × ExtData β)) :
    game₁ T st A = A >>= fun r =>
      (fun t => (r.1, r.2, t)) <$> route l0Kind (verifyQ T st r.1) := by
  rw [game₁, game, route, simulateQ_bind, ← route, route_unroute]
  simp only [route, simulateQ_map]

/-- **The single-oracle game has the event probabilities of the per-domain game**, for the
prover `unroute l0Kind A` (which asks `(l0Kind x, x)` where `A` asks `x`). -/
theorem prEvent_game₁_eq (T : CrtTables) (st : Statement) (hst : CombOk st)
    (A : OracleComp (spec₁ l0Kind) (ByteArray × ExtData β))
    (event : ByteArray × ExtData β × Transcript → Prop) :
    Pr{let r ← (simulateQ randomOracle (game₁ T st A)).run' ∅}[event r] =
      Pr{let r ← (simulateQ randomOracle (game T st (unroute l0Kind A))).run' ∅}[event r] := by
  refine prEvent_route_eq l0Kind _ ?_ event
  exact allQueriesSatisfy_bind (allQueriesSatisfy_unroute _ A) fun r =>
    (isQueryBound_map_iff _ _ _ _ _).2 (allQueriesSatisfy_verifyQ T st hst r.1)

end VoleMole.ROM
