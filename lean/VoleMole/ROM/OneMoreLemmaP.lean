import VoleMole.ROM.OneMorePomfrit
import VoleMole.ROM.ExtractReduce
import VoleMole.ROM.VerifyIC

/-!
# PomFRIT's one-more game against Lemma P: the game as a lazy random oracle, `E₁`, derived provers

`lean/docs/security/pomfrit.md` §5, §6.4 (gap G8). `ROM/OneMorePomfrit.lean` proves
`Pr[PomWin] ≤ Adv^{ompr}(B) + Pr[∃ i, PFail i]` for any first-phase rule. This file builds the
pieces that relate `PFail i` to the adaptive extraction game of `ROM/LemmaP.lean`, table by table.

* **The game as a lazy random oracle** (`realImpl_run_eq`): for a fixed key, cipher table and
  target stream, the one-more game's run is the lazy random oracle's run of one computation over the
  hashes (`htW`: the target oracle and the Issuer answered from a state, `tStep`). So the game's
  events can be compared, table by table, with events of other computations
  (`ROM/ExtractReduce.lean`, `prEvent_le_sum_of_table`).
* **Lemma P's `E₁`** (`e1P`): from the log at a target query, the first `H₂¹` preimage `x₁` of the
  input's `chal1`, the data committed there (`preCore`, `iv` read off the log: the reduction's own
  queries `auxSpec` put it there), the trees with no committed dead leaf, and the prefix of the
  widest group (`PomFRIT.majP`) of their candidates `u ⊕ d`.
* **The forger with the cipher as queries** (`wrapIC`, with a ghost of the hint logs; `wrapP`, with
  void hints): table by table the same forgeries, logs and target answers as the game's wrapped
  forger (`eval_forger`, `log_forger`, `eval_forgerP`); the target oracle's answers do not depend
  on the hints (`tStep_sameT`).
* **Verification, table by table** (`eval_verOne`, `eval_verPart`, `eval_verAll_split`,
  `eval_htW_persist`).
* **A failed forgery, table by table** (`pfail_table`): if forgery `i` of the game verifies and its
  claim is not a preimage of its programmed target, then in the adaptive game of the derived prover
  `proverI … i` (the forger and the reduction's verifications up to forgery `i`) the verifier accepts
  and no extracted candidate decodes to a preimage of the programmed target (`NoPick`).
* **Lemma P's extraction gives the claim** (`not_noPick`): if Lemma P's goal holds in that game
  (`MajorExtracted`), every alive tree is known, and the hint is the widest group's prefix, then
  some extracted candidate is a preimage of the programmed target.

**Not here** (`pomfrit.md` §6.4, G8): `proverI` reads the cipher table `E` directly (the
reduction's `chal1`, its `E₁` and the earlier forgeries' extraction use `icPrg E.cipher`), so the
adaptive bound `pomfritT_accept_le_major`, which is for provers that reach the cipher only through
queries, does not apply to it as it stands. An `E`-independent derived prover (the forger as
`wrapP`, `chal1` through `ROM/VerifyIC.lean`'s `verifyIC`) and the ordering step of Lemma P (`E₁`
at query time equals the widest group of the alive trees at the end, outside an `H₂¹` answer
hitting the `chal1` field of an earlier target query and the chain hits) remain.

No `sorry`, no `axiom`.
-/

open OracleComp OracleSpec
open scoped ENNReal

namespace VoleMole.ROM.OneMore

/-! ## The real game's world as a lazy random oracle -/

section Decomp

variable {DR : Type} [DecidableEq DR] {AR : DR → Type} [∀ d, SampleableType (AR d)]
  {X : Type} [DecidableEq X] {Hn G S : Type} [AddCommGroup G]

/-- The challenger's state without the random oracle's cache. -/
abbrev ChW (X Hn G : Type) := List G × (X → Option (G × Hn)) × ℕ

/-- The target oracle's step at `(x, h)` on the reduced state (as `realImpl`). -/
def tStep (φ : Hn → G ≃ G) (x : X) (h : Hn) (s : (X → Option (G × Hn)) × ChW X Hn G) :
    (G × Hn) × ((X → Option (G × Hn)) × ChW X Hn G) :=
  match s.1 x with
  | some a => (a, s)
  | none => match s.2.1 with
    | u :: r => ((u, h), (Function.update s.1 x (some (u, h)),
        (r, Function.update s.2.2.1 x (some (φ h u, h)), s.2.2.2)))
    | [] => (((0 : G), h), (Function.update s.1 x (some (0, h)), s.2))

/-- **The target oracle and the Issuer from a state, the world forwarded** (`realImpl` without the
world's cache). -/
def htW (φ : Hn → G ≃ G) (pre : G → S) :
    QueryImpl (specA AR X Hn G S) (StateT ((X → Option (G × Hn)) × ChW X Hn G)
      (OracleComp (specR AR)))
  | .inl d => StateT.mk fun s => (fun u => (u, s)) <$>
      (liftM ((specR AR).query d) : OracleComp (specR AR) (AR d))
  | .inr (.inl (x, h)) => StateT.mk fun s => pure (tStep φ x h s)
  | .inr (.inr t) => StateT.mk fun s => pure (pre t, (s.1, s.2.1, s.2.2.1, s.2.2.2 + 1))

/-- The challenger's state from the reduced one and a cache. -/
def chOf (w : ChW X Hn G) (ro : (specR AR).QueryCache) : Ch AR X Hn G := ⟨ro, w.1, w.2.1, w.2.2⟩

omit [DecidableEq X] [AddCommGroup G] in
lemma ro_run_query_map {β : Type} (d : DR) (f : AR d → β) (c : (specR AR).QueryCache) :
    (simulateQ randomOracle (f <$> (liftM ((specR AR).query d) : OracleComp (specR AR) (AR d)))).run
      c = (fun r => (f r.1, r.2)) <$> (randomOracle d).run c := by
  rw [simulateQ_map, simulateQ_spec_query, StateT.run_map]

/-- **The real game is the lazy random oracle's run of `htW`.** -/
theorem realImpl_run_eq (φ : Hn → G ≃ G) (pre : G → S) {α : Type}
    (oa : OracleComp (specA AR X Hn G S) α) :
    ∀ (s : X → Option (G × Hn)) (c : Ch AR X Hn G),
      (simulateQ (realImpl φ pre) oa).run (s, c) =
        (fun z => (z.1.1, (z.1.2.1, chOf z.1.2.2 z.2))) <$>
          (simulateQ randomOracle ((simulateQ (htW φ pre) oa).run (s, (c.rest, c.tg, c.iq)))).run
            c.ro := by
  induction oa using OracleComp.inductionOn with
  | pure x => intro s c; simp [chOf]
  | query_bind q k ih =>
    intro s c
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
    rcases q with d | ⟨x, h⟩ | t
    · simp only [realImpl, htW, StateT.run_mk, roStep, bind_map_left]
      erw [ro_run_query_map]
      rw [bind_map_left, map_bind]
      refine bind_congr fun r => ?_
      exact ih r.1 s { c with ro := r.2 }
    · cases hx : s x with
      | some a =>
        simp only [realImpl, htW, tStep, StateT.run_mk, hx, pure_bind]
        exact ih a s c
      | none =>
        cases hr : c.rest with
        | nil =>
          simp only [realImpl, htW, tStep, StateT.run_mk, hx, hr, pure_bind]
          have := ih ((0 : G), h) (Function.update s x (some (0, h))) c
          simpa [hr] using this
        | cons u r =>
          simp only [realImpl, htW, tStep, StateT.run_mk, hx, hr, pure_bind]
          exact ih (u, h) _ { c with rest := r, tg := Function.update c.tg x (some (φ h u, h)) }
    · simp only [realImpl, htW, StateT.run_mk, pure_bind, simulateQ_pure, StateT.run_pure]
      exact ih _ s { c with iq := c.iq + 1 }

end Decomp

end VoleMole.ROM.OneMore

/-! ## PomFRIT: the forger with the cipher as queries -/

namespace VoleMole.ROM.OneMore.Pomfrit

open VoleMole.Prob VoleMole.Arith VoleMole.Verifier VoleMole.ROM VoleMole.ROM.IC
open VoleMole.EndToEnd VoleMole.EndToEnd.SpecRel

/-- The reduced state of the target oracle (table, unused targets, programmed targets, Issuer
queries). -/
abbrev HTS := (ByteArray → Option (TG × TG)) × ChW ByteArray TG TG

/-- The ghost: the hint log of each target input's first query. -/
abbrev Gh := ByteArray → Option (QueryLog specIC)

/-- A hash query as a query to the hashes and the cipher. -/
def liftHIC : QueryImpl spec (OracleComp specIC) := fun d =>
  (liftM (specIC.query (.inl d)) : OracleComp specIC (Ans d))

/-- A computation against the hashes, as one against the hashes and the cipher. -/
def toHIC {α : Type} (oa : OracleComp spec α) : OracleComp specIC α := simulateQ liftHIC oa

/-- **The forger with its cipher queries as queries** (for the derived provers): its hash and cipher
queries go to `specIC`, logged; at its `H_T` query the reduction's own queries (`auxSpec`, logged)
and the target oracle's step on the state; its Issuer queries answered by `pre`. As `wrapImpl`
followed by `htW`, with the cipher answered by the oracle instead of the table. A ghost records,
for each target input, the log its hint was computed from at its first query. -/
noncomputable def wrapIC (lr : Bool) (hint : QueryLog specIC → ByteArray → TG) (pre : TG → SIss) :
    QueryImpl specU (StateT (QueryLog specIC × HTS × Gh) (OracleComp specIC))
  | .inl d => StateT.mk fun s => (fun u => (u, (s.1 ++ [⟨d, u⟩], s.2))) <$>
      (liftM (specIC.query d) : OracleComp specIC (AnsIC d))
  | .inr (.inl x) => StateT.mk fun s => toHIC (auxSpec lr s.1 x) >>= fun ax =>
      pure ((tStep addHint x (hint (s.1 ++ ax) x) s.2.1).1.1,
        (s.1 ++ ax, (tStep addHint x (hint (s.1 ++ ax) x) s.2.1).2,
          if s.2.1.1 x = none then Function.update s.2.2 x (some (s.1 ++ ax)) else s.2.2))
  | .inr (.inr t) => StateT.mk fun s =>
      pure (pre t, (s.1, (s.2.1.1, s.2.1.2.1, s.2.1.2.2.1, s.2.1.2.2.2 + 1), s.2.2))

section Eval

variable (g : Table) (E : CTable)

lemma eval_toHIC {α : Type} (oa : OracleComp spec α) :
    evalWithAnswerFn (QueryImpl.ofFn (join g E)) (toHIC oa) = evalWithAnswerFn (QueryImpl.ofFn g) oa := by
  unfold toHIC
  rw [evalWithAnswerFn_simulateQ]
  rfl

lemma log_toHIC {α : Type} (oa : OracleComp spec α) :
    tableQueryLog (toHIC oa) (join g E) =
      (tableQueryLog oa g).map fun e => (⟨.inl e.1, e.2⟩ : (t : DomIC) × AnsIC t) := by
  induction oa using OracleComp.inductionOn with
  | pure a => simp [toHIC]
  | query_bind t k ih =>
    simp only [toHIC, simulateQ_bind, simulateQ_spec_query, liftHIC] at ih ⊢
    erw [tableQueryLog_query_bind]
    rw [tableQueryLog_query_bind, List.map_cons]
    exact congrArg (List.cons _) (ih (g t))

lemma eval_htW_toC {Hn : Type} (φ : Hn → TG ≃ TG) (pre : TG → SIss) {α : Type}
    (oa : OracleComp spec α) (s : (ByteArray → Option (TG × Hn)) × ChW ByteArray Hn TG) :
    evalWithAnswerFn (QueryImpl.ofFn g)
      ((simulateQ (htW (AR := Ans) (S := SIss) φ pre) (toC (Hn := Hn) oa)).run s) =
      (evalWithAnswerFn (QueryImpl.ofFn g) oa, s) := by
  induction oa using OracleComp.inductionOn with
  | pure a => simp [toC]
  | query_bind t k ih =>
    simp only [toC, simulateQ_bind, simulateQ_spec_query, liftW] at ih ⊢
    simp only [StateT.run_bind, evalWithAnswerFn_bind]
    erw [evalWithAnswerFn_liftM_query]
    exact ih (g t)

/-- The reduction's own queries return their log. -/
lemma eval_auxSpec (lr : Bool) (L : QueryLog specIC) (x : ByteArray) :
    evalWithAnswerFn (QueryImpl.ofFn g) (auxSpec lr L x) =
      (tableQueryLog (auxSpec lr L x) g).map fun e => (⟨.inl e.1, e.2⟩ : (t : DomIC) × AnsIC t) := by
  unfold auxSpec
  cases x1Of L x <;> simp [tableQueryLog_bind, tableQueryLog_map']

variable (lr : Bool) (hint : QueryLog specIC → ByteArray → TG) (pre : TG → SIss)

lemma eval_htW_world {β : Type} (d : Dom) (f : Ans d → β) (hs : HTS) :
    evalWithAnswerFn (QueryImpl.ofFn g) ((simulateQ (htW (AR := Ans) (S := SIss) addHint pre)
      (f <$> (liftM ((specC TG).query (.inl d)) : OracleComp (specC TG) (Ans d)))).run hs) =
      (f (g d), hs) := by
  rw [simulateQ_map]
  erw [simulateQ_spec_query]
  rfl

lemma eval_htW_tgt {β : Type} (x : ByteArray) (h : TG) (f : TG × TG → β) (hs : HTS) :
    evalWithAnswerFn (QueryImpl.ofFn g) ((simulateQ (htW (AR := Ans) (S := SIss) addHint pre)
      (f <$> (liftM ((specC TG).query (.inr (.inl (x, h)))) : OracleComp (specC TG) (TG × TG)))).run
        hs) = (f (tStep addHint x h hs).1, (tStep addHint x h hs).2) := by
  rw [simulateQ_map]
  erw [simulateQ_spec_query]
  rfl

lemma eval_htW_iss {β : Type} (t : TG) (f : SIss → β) (hs : HTS) :
    evalWithAnswerFn (QueryImpl.ofFn g) ((simulateQ (htW (AR := Ans) (S := SIss) addHint pre)
      (f <$> (liftM ((specC TG).query (.inr (.inr t))) : OracleComp (specC TG) SIss))).run hs) =
      (f (pre t), (hs.1, hs.2.1, hs.2.2.1, hs.2.2.2 + 1)) := by
  rw [simulateQ_map]
  erw [simulateQ_spec_query]
  rfl

/-- **The forger's run, table by table**: the wrapped forger of the game (`wrapImpl`, the cipher
answered by `E`) with the target oracle and the Issuer on a state (`htW`), against the hash table
`g`, is the forger with the cipher as queries (`wrapIC`) against `g` and `E`: the same output, log
and state. -/
theorem eval_forger {α : Type} (oa : OracleComp specU α) :
    ∀ (L : QueryLog specIC) (hs : HTS) (gh : Gh),
      evalWithAnswerFn (QueryImpl.ofFn g)
        ((simulateQ (htW (AR := Ans) addHint pre) ((simulateQ (wrapImpl lr E hint) oa).run L)).run hs) =
      (fun b => ((b.1, b.2.1), b.2.2.1))
        (evalWithAnswerFn (QueryImpl.ofFn (join g E))
          ((simulateQ (wrapIC lr hint pre) oa).run (L, hs, gh))) := by
  induction oa using OracleComp.inductionOn with
  | pure a => intro L hs gh; simp
  | query_bind q k ih =>
    intro L hs gh
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
    rcases q with (d | x) | (x | t)
    · simp only [wrapImpl, wrapIC, StateT.run_mk, evalWithAnswerFn_bind]
      exact ih (g d) _ hs gh
    · simp only [wrapImpl, wrapIC, StateT.run_mk, simulateQ_pure, StateT.run_pure,
        evalWithAnswerFn_bind, pure_bind]
      exact ih (E x) _ hs gh
    · simp only [wrapImpl, wrapIC, auxC, StateT.run_mk, simulateQ_bind, StateT.run_bind,
        evalWithAnswerFn_bind, evalWithAnswerFn_pure, eval_htW_toC, eval_toHIC, eval_htW_tgt]
      exact ih _ _ _ _
    · simp only [wrapImpl, wrapIC, StateT.run_mk, evalWithAnswerFn_bind, evalWithAnswerFn_pure]
      exact ih _ _ _ _

/-- **The wrapper's log is the joint log of the run.** -/
theorem log_forger {α : Type} (oa : OracleComp specU α) :
    ∀ (L : QueryLog specIC) (hs : HTS) (gh : Gh),
      (evalWithAnswerFn (QueryImpl.ofFn (join g E))
        ((simulateQ (wrapIC lr hint pre) oa).run (L, hs, gh))).2.1 =
        L ++ tableQueryLog ((simulateQ (wrapIC lr hint pre) oa).run (L, hs, gh)) (join g E) := by
  induction oa using OracleComp.inductionOn with
  | pure a => intro L hs gh; simp
  | query_bind q k ih =>
    intro L hs gh
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
    rcases q with (d | x) | (x | t)
    · simp only [wrapIC, StateT.run_mk, evalWithAnswerFn_bind, tableQueryLog_bind]
      erw [tableQueryLog_query, evalWithAnswerFn_map, evalWithAnswerFn_liftM_query]
      rw [ih _ _ hs gh, List.append_assoc]
      rfl
    · simp only [wrapIC, StateT.run_mk, evalWithAnswerFn_bind, tableQueryLog_bind]
      erw [tableQueryLog_query, evalWithAnswerFn_map, evalWithAnswerFn_liftM_query]
      rw [ih _ _ hs gh, List.append_assoc]
      rfl
    · simp only [wrapIC, StateT.run_mk, evalWithAnswerFn_bind, evalWithAnswerFn_pure,
        tableQueryLog_bind, tableQueryLog_pure, eval_toHIC, log_toHIC, eval_auxSpec, List.append_nil]
      exact (ih _ _ _ _).trans (List.append_assoc _ _ _)
    · simp only [wrapIC, StateT.run_mk, evalWithAnswerFn_bind, evalWithAnswerFn_pure,
        tableQueryLog_bind, tableQueryLog_pure, List.nil_append]
      exact ih _ _ _ _

end Eval

/-! ## Lemma P's first-phase rule `E₁` -/

section E1

/-- The `d[0..M)` field of a `hash_to_target` input (bytes `239 … 284`). -/
def xDpre (x : ByteArray) : ByteArray := x.extract 239 284

/-- A table read off a log: the logged answer at each logged cell, arbitrary elsewhere. -/
noncomputable def tableOfLog (L : QueryLog spec) : Table := by
  classical
  exact fun d => if h : ∃ u, (⟨d, u⟩ : (t : Dom) × Ans t) ∈ L then h.choose
    else Classical.arbitrary _

/-- The reference statement of `E₁`: PomFRIT's parameters and DST, delayed binding. -/
def stE (lr : Bool) : Statement :=
  { params := pomfritParams lr
    dst := toBA (Spec.makeDst "pomf" 0 'p' '0')
    delayed := true
    instEnc := fun _ => ByteArray.empty
    values := fun _ _ _ => [] }

/-- 45 bytes as a target. -/
def toTG (b : Spec.Bytes) : TG := fun k => ⟨b.getD k.val 0⟩

/-- `n` zero bytes. -/
def zerosBA (n : ℕ) : ByteArray := ⟨Array.replicate n 0⟩

/-- **Lemma P's first-phase rule `E₁`** (`pomfrit.md` §5) on the log `L` at the target input `x`:
the first `H₂¹` preimage `x₁` of `x`'s `chal1` in `L` (`0` if none); the data committed at `x₁`
(`preCore`: the leaf keys from `L`'s cipher entries before `x₁`, `iv` read off `L`); the trees
with no committed dead leaf; their candidates' prefixes (`u ⊕ d` with `d[0..M)` from `x`); the
prefix of the widest group (`majP`). -/
noncomputable def e1P (lr : Bool) (E : CTable) (L : QueryLog specIC) (x : ByteArray) : TG :=
  match x1Of L x with
  | none => 0
  | some x1 =>
    letI : HasPrg := VoleMole.ZK.Sim.icPrg E.cipher
    let Gx := logBefore (.h21, x1) (hashEnt L)
    let Jx := logBefore (.inl (.h21, x1)) L
    let pc := preCore (stE lr) E Gx Jx x1 (tableOfLog (hashEnt L))
    let alive := Finset.univ.filter fun i => deadPre E Gx Jx pc.iv x1 i = ∅
    let pcd : Verifier.Bridge.Chain :=
      { pc with proof := pc.proof ++ zerosBA 64 ++ xDpre x ++ zerosBA 119 }
    toTG ((PomFRIT.majP alive fun i =>
      preB (EndToEnd.candidate (F := GF128) (pcd.u (stE lr)) (pcd.dc (stE lr)) i)).getD [])

end E1

/-! ## The derived prover of the `i`-th forgery -/

section Derived

/-- The target oracle and the Issuer on a state, the world as hash queries of `specIC`. -/
noncomputable def htIC (pre : TG → SIss) :
    QueryImpl (specC TG) (StateT HTS (OracleComp specIC))
  | .inl d => StateT.mk fun s => (fun u => (u, s)) <$>
      (liftM (specIC.query (.inl d)) : OracleComp specIC (Ans d))
  | .inr (.inl (x, h)) => StateT.mk fun s => pure (tStep addHint x h s)
  | .inr (.inr t) => StateT.mk fun s => pure (pre t, (s.1, s.2.1, s.2.2.1, s.2.2.2 + 1))

variable (g : Table) (E : CTable) (pre : TG → SIss)

/-- `htW` against `g` is `htIC` against `g` and `E`. -/
theorem eval_htW_htIC {α : Type} (m : OracleComp (specC TG) α) :
    ∀ hs : HTS, evalWithAnswerFn (QueryImpl.ofFn g)
        ((simulateQ (htW (AR := Ans) (S := SIss) addHint pre) m).run hs) =
      evalWithAnswerFn (QueryImpl.ofFn (join g E)) ((simulateQ (htIC pre) m).run hs) := by
  induction m using OracleComp.inductionOn with
  | pure a => intro hs; simp
  | query_bind q k ih =>
    intro hs
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, evalWithAnswerFn_bind]
    rcases q with d | ⟨x, h⟩ | t
    · exact ih (g d) hs
    · exact ih _ _
    · exact ih _ _

/-- `htIC`'s queries are hash queries: its log has no cipher entry. -/
theorem cipherLog_htIC {α : Type} (m : OracleComp (specC TG) α) :
    ∀ hs : HTS, cipherLog (tableQueryLog ((simulateQ (htIC pre) m).run hs) (join g E)) = [] := by
  induction m using OracleComp.inductionOn with
  | pure a => intro hs; simp
  | query_bind q k ih =>
    intro hs
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, tableQueryLog_bind]
    rcases q with d | ⟨x, h⟩ | t
    · simp only [htIC, StateT.run_mk]
      erw [tableQueryLog_query]
      simp only [List.singleton_append]
      exact ih _ _
    · exact ih _ _
    · exact ih _ _

end Derived

section Prover

variable (T : CrtTables) (lr : Bool) (E : CTable) (hint : QueryLog specIC → ByteArray → TG)
  (pk : UovPk) (pre : TG → SIss)

/-- The statements of the derived provers: the index `(a, b₁, b₂)` gives the target `a` (the
answer of `H_T`) and the binders. -/
def stG (s : TG × ByteArray × ByteArray) : Statement :=
  pomfritRedeemT pk (fun _ => encT s.1) s.2.1 s.2.2 lr

/-- **The `i`-th forgery's verification up to its target query**: the earlier forgeries verified
as in the game (`verAll`), then the `i`-th one's `chal1`, the reduction's queries and its target
query. Output: its proof, its statement index (the target oracle's answer, the binders) and the
hint of the target's first query. -/
noncomputable def verPart (i : ℕ) (L : QueryLog specIC) (outs : List (ByteArray × ByteArray)) :
    OracleComp (specC TG) (ByteArray × ((TG × ByteArray × ByteArray) × TG)) := do
  let _ ← verAll T lr E hint tgts1 pk L (outs.take i)
  let ms := outs.getD i (ByteArray.empty, ByteArray.empty)
  let n := (pomfritParams lr).proofBytes
  let proof := ms.2.extract 0 n
  let b1 := ms.2.extract n (n + 32)
  let b2 := ms.2.extract (n + 32) (n + 64)
  let oc1 ← toC (@chal1Pre (VoleMole.ZK.Sim.icPrg E.cipher)
    (pomfritRedeemT pk (fun _ => ByteArray.empty) b1 b2 lr) proof)
  match oc1 with
  | none => pure (proof, ((0, b1, b2), 0))
  | some c1 => do
    let x := tgtIn pk lr ms.2 ms.1 c1
    let ax ← auxC lr L x
    let ah ← tQ x (hint (L ++ ax) x)
    pure (proof, ((ah.1, b1, b2), ah.2))

/-- The initial reduced state: an empty table, the stream `Lst`, no programmed target, no Issuer
query. -/
def hs0 (Lst : List TG) : HTS := (fun _ => none, (Lst, fun _ => none, 0))

/-- **The derived prover of the `i`-th forgery**, for a target stream `Lst` and the Issuer `pre`:
the forger with the cipher as queries (`wrapIC`), then `verPart` with the target oracle and the
Issuer on the state. It outputs the `i`-th forgery's proof and statement index (`stG`). -/
noncomputable def proverI (A : Forger) (Lst : List TG) (i : ℕ) :
    OracleComp specIC (ByteArray × ((TG × ByteArray × ByteArray) × TG)) := do
  let r ← (simulateQ (wrapIC lr hint pre) (A pk)).run ([], hs0 Lst, fun _ => none)
  (fun z => z.1) <$> (simulateQ (htIC pre) (verPart T lr E hint pk i r.2.1 r.1)).run r.2.2.1

end Prover

lemma verAll_append (T : CrtTables) (lr : Bool) (E : CTable) {Hn : Type}
    (hint : QueryLog specIC → ByteArray → Hn) (tgts : TG × Hn → List TG) (pk : UovPk)
    (L : QueryLog specIC) :
    ∀ l₁ l₂ : List (ByteArray × ByteArray), verAll T lr E hint tgts pk L (l₁ ++ l₂) =
      (verAll T lr E hint tgts pk L l₁ >>= fun a =>
        verAll T lr E hint tgts pk L l₂ >>= fun b => pure (a ++ b))
  | [], l₂ => by simp [verAll]
  | (m, sg) :: l₁, l₂ => by
    simp only [List.cons_append, verAll, bind_assoc, pure_bind, verAll_append _ _ _ _ _ _ _ l₁ l₂]

/-! ## Table by table: the `i`-th verification -/

section TableVer

variable (g : Table) (T : CrtTables) (lr : Bool) (E : CTable)
  (hint : QueryLog specIC → ByteArray → TG) (pk : UovPk) (pre : TG → SIss)

/-- The forgery's fields: proof, binders. -/
def sProof (lr : Bool) (sg : ByteArray) : ByteArray := sg.extract 0 (pomfritParams lr).proofBytes
def sB1 (lr : Bool) (sg : ByteArray) : ByteArray :=
  sg.extract (pomfritParams lr).proofBytes ((pomfritParams lr).proofBytes + 32)
def sB2 (lr : Bool) (sg : ByteArray) : ByteArray :=
  sg.extract ((pomfritParams lr).proofBytes + 32) ((pomfritParams lr).proofBytes + 64)

/-- `chal1` of a forgery against `g` (with the ideal cipher `E`). -/
def c1T (sg : ByteArray) : Option ByteArray :=
  evalWithAnswerFn (QueryImpl.ofFn g) (@chal1Pre (VoleMole.ZK.Sim.icPrg E.cipher)
    (pomfritRedeemT pk (fun _ => ByteArray.empty) (sB1 lr sg) (sB2 lr sg) lr) (sProof lr sg))

/-- The reduction's queries at `x` against `g`, as log entries. -/
def axT (L : QueryLog specIC) (x : ByteArray) : QueryLog specIC :=
  evalWithAnswerFn (QueryImpl.ofFn g) (auxSpec lr L x)

lemma eval_htW_bind {α β : Type} (m : OracleComp (specC TG) α) (f : α → OracleComp (specC TG) β)
    (hs : HTS) :
    evalWithAnswerFn (QueryImpl.ofFn g) ((simulateQ (htW (AR := Ans) (S := SIss) addHint pre)
      (m >>= f)).run hs) =
    evalWithAnswerFn (QueryImpl.ofFn g) ((simulateQ (htW (AR := Ans) (S := SIss) addHint pre)
      (f (evalWithAnswerFn (QueryImpl.ofFn g) ((simulateQ (htW (AR := Ans) (S := SIss) addHint pre)
        m).run hs)).1)).run
      (evalWithAnswerFn (QueryImpl.ofFn g) ((simulateQ (htW (AR := Ans) (S := SIss) addHint pre)
        m).run hs)).2) := by
  simp only [simulateQ_bind, StateT.run_bind, evalWithAnswerFn_bind]

lemma eval_htW_tq (x : ByteArray) (h : TG) (hs : HTS) :
    evalWithAnswerFn (QueryImpl.ofFn g) ((simulateQ (htW (AR := Ans) (S := SIss) addHint pre)
      (liftM ((specC TG).query (.inr (.inl (x, h)))) : OracleComp (specC TG) (TG × TG))).run hs) =
      tStep addHint x h hs := by
  erw [simulateQ_spec_query]
  rfl

lemma eval_htW_toC' {α : Type} (oa : OracleComp spec α) (hs : HTS) :
    evalWithAnswerFn (QueryImpl.ofFn g)
      ((simulateQ (htW (AR := Ans) (S := SIss) addHint pre) (toC (Hn := TG) oa)).run hs) =
      (evalWithAnswerFn (QueryImpl.ofFn g) oa, hs) := eval_htW_toC g addHint pre oa hs

/-- **One verification, table by table.** -/
theorem eval_verOne (L : QueryLog specIC) (m sg : ByteArray) (hs : HTS) :
    evalWithAnswerFn (QueryImpl.ofFn g) ((simulateQ (htW (AR := Ans) (S := SIss) addHint pre)
      (verOne T lr E hint tgts1 pk L m sg)).run hs) =
    if toBA (Spec.PomFRIT.commitRefresher (toL (sB2 lr sg))) != sB1 lr sg then
      (((ByteArray.empty, none), false), hs)
    else match c1T g lr E pk sg with
      | none => (((ByteArray.empty, none), false), hs)
      | some c1 =>
        let x := tgtIn pk lr sg m c1
        let ah := tStep addHint x (hint (L ++ axT g lr L x) x) hs
        let st := pomfritRedeemT pk (fun _ => encT ah.1.1) (sB1 lr sg) (sB2 lr sg) lr
        let ex := evalWithAnswerFn (QueryImpl.ofFn g) (extractIC st E ((sProof lr sg, ()), L))
        let t := @verify (VoleMole.ZK.Sim.icPrg E.cipher) (Hashes.ofTable g) T st (sProof lr sg)
        (((x, pick pk (tgts1 ah.1) (candidates E st (ex.1, ex.2, t))), t.accept), ah.2) := by
  unfold verOne c1T sProof sB1 sB2 axT
  dsimp only
  split_ifs with hr
  · simp
  · rw [eval_htW_bind, eval_htW_toC]
    cases hc : evalWithAnswerFn (QueryImpl.ofFn g) (@chal1Pre (VoleMole.ZK.Sim.icPrg E.cipher)
      (pomfritRedeemT pk (fun _ => ByteArray.empty)
        (sg.extract (pomfritParams lr).proofBytes ((pomfritParams lr).proofBytes + 32))
        (sg.extract ((pomfritParams lr).proofBytes + 32) ((pomfritParams lr).proofBytes + 64)) lr)
      (sg.extract 0 (pomfritParams lr).proofBytes)) with
    | none => simp
    | some c1 =>
      simp only [auxC, eval_htW_bind, eval_htW_toC', tQ, verTail, eval_htW_tq, simulateQ_pure,
        StateT.run_pure, evalWithAnswerFn_pure, @evalWithAnswerFn_verifyQ (VoleMole.ZK.Sim.icPrg E.cipher)]

/-- **The `i`-th forgery's verification up to its target query, table by table.** -/
theorem eval_verPart (i : ℕ) (L : QueryLog specIC) (outs : List (ByteArray × ByteArray))
    (hs : HTS) :
    evalWithAnswerFn (QueryImpl.ofFn g) ((simulateQ (htW (AR := Ans) (S := SIss) addHint pre)
      (verPart T lr E hint pk i L outs)).run hs) =
    let hs' := (evalWithAnswerFn (QueryImpl.ofFn g) ((simulateQ (htW (AR := Ans) (S := SIss)
      addHint pre) (verAll T lr E hint tgts1 pk L (outs.take i))).run hs)).2
    let ms := outs.getD i (ByteArray.empty, ByteArray.empty)
    match c1T g lr E pk ms.2 with
    | none => ((sProof lr ms.2, ((0, sB1 lr ms.2, sB2 lr ms.2), 0)), hs')
    | some c1 =>
      let x := tgtIn pk lr ms.2 ms.1 c1
      let ah := tStep addHint x (hint (L ++ axT g lr L x) x) hs'
      ((sProof lr ms.2, ((ah.1.1, sB1 lr ms.2, sB2 lr ms.2), ah.1.2)), ah.2) := by
  unfold verPart c1T sProof sB1 sB2 axT
  dsimp only
  rw [eval_htW_bind, eval_htW_bind, eval_htW_toC']
  cases evalWithAnswerFn (QueryImpl.ofFn g) (@chal1Pre (VoleMole.ZK.Sim.icPrg E.cipher)
      (pomfritRedeemT pk (fun _ => ByteArray.empty)
        ((outs.getD i (ByteArray.empty, ByteArray.empty)).2.extract (pomfritParams lr).proofBytes
          ((pomfritParams lr).proofBytes + 32))
        ((outs.getD i (ByteArray.empty, ByteArray.empty)).2.extract
          ((pomfritParams lr).proofBytes + 32) ((pomfritParams lr).proofBytes + 64)) lr)
      ((outs.getD i (ByteArray.empty, ByteArray.empty)).2.extract 0 (pomfritParams lr).proofBytes)) with
  | none => simp
  | some c1 =>
    simp only [auxC, eval_htW_bind, eval_htW_toC', tQ, eval_htW_tq, simulateQ_pure,
      StateT.run_pure, evalWithAnswerFn_pure]

lemma eval_verAll_length (L : QueryLog specIC) :
    ∀ (l : List (ByteArray × ByteArray)) (s : HTS),
      (evalWithAnswerFn (QueryImpl.ofFn g) ((simulateQ (htW (AR := Ans) (S := SIss) addHint pre)
        (verAll T lr E hint tgts1 pk L l)).run s)).1.length = l.length
  | [], s => by simp [verAll]
  | (m, sg) :: l, s => by
    simp only [verAll, eval_htW_bind, simulateQ_pure, StateT.run_pure, evalWithAnswerFn_pure,
      List.length_cons, eval_verAll_length L l]

/-- `verAll` at a table, split at the `i`-th forgery. -/
theorem eval_verAll_split (L : QueryLog specIC) (outs : List (ByteArray × ByteArray)) (hs : HTS)
    (i : ℕ) (hi : i < outs.length) :
    let hs' := (evalWithAnswerFn (QueryImpl.ofFn g) ((simulateQ (htW (AR := Ans) (S := SIss)
      addHint pre) (verAll T lr E hint tgts1 pk L (outs.take i))).run hs)).2
    (evalWithAnswerFn (QueryImpl.ofFn g) ((simulateQ (htW (AR := Ans) (S := SIss) addHint pre)
      (verAll T lr E hint tgts1 pk L outs)).run hs)).1[i]? =
    some (evalWithAnswerFn (QueryImpl.ofFn g) ((simulateQ (htW (AR := Ans) (S := SIss) addHint pre)
      (verOne T lr E hint tgts1 pk L (outs[i]).1 (outs[i]).2)).run hs')).1 := by
  intro hs'
  have hsplit : outs = outs.take i ++ ((outs[i]).1, (outs[i]).2) :: outs.drop (i + 1) := by
    simp
  conv_lhs => rw [hsplit, verAll_append]
  simp only [eval_htW_bind, verAll, simulateQ_pure, StateT.run_pure, evalWithAnswerFn_pure]
  have hlen := eval_verAll_length g T lr E hint pk pre L
  rw [List.getElem?_append_right (by rw [hlen]; simp)]
  simp [hlen, Nat.min_eq_left hi.le, hs']

lemma eval_verAll_append_snd (L : QueryLog specIC) (l₁ l₂ : List (ByteArray × ByteArray))
    (hs : HTS) :
    (evalWithAnswerFn (QueryImpl.ofFn g) ((simulateQ (htW (AR := Ans) (S := SIss) addHint pre)
      (verAll T lr E hint tgts1 pk L (l₁ ++ l₂))).run hs)).2 =
    (evalWithAnswerFn (QueryImpl.ofFn g) ((simulateQ (htW (AR := Ans) (S := SIss) addHint pre)
      (verAll T lr E hint tgts1 pk L l₂)).run
      (evalWithAnswerFn (QueryImpl.ofFn g) ((simulateQ (htW (AR := Ans) (S := SIss) addHint pre)
        (verAll T lr E hint tgts1 pk L l₁)).run hs)).2)).2 := by
  rw [verAll_append]
  simp only [eval_htW_bind, simulateQ_pure, StateT.run_pure, evalWithAnswerFn_pure]

lemma eval_verAll_single_snd (L : QueryLog specIC) (m sg : ByteArray) (hs : HTS) :
    (evalWithAnswerFn (QueryImpl.ofFn g) ((simulateQ (htW (AR := Ans) (S := SIss) addHint pre)
      (verAll T lr E hint tgts1 pk L [(m, sg)])).run hs)).2 =
    (evalWithAnswerFn (QueryImpl.ofFn g) ((simulateQ (htW (AR := Ans) (S := SIss) addHint pre)
      (verOne T lr E hint tgts1 pk L m sg)).run hs)).2 := by
  simp only [verAll, eval_htW_bind, simulateQ_pure, StateT.run_pure, evalWithAnswerFn_pure]


lemma tStep_get {Hn : Type} (φ : Hn → TG ≃ TG) (x : ByteArray) (h : Hn)
    (s : (ByteArray → Option (TG × Hn)) × ChW ByteArray Hn TG) :
    (tStep φ x h s).2.1 x = some (tStep φ x h s).1 := by
  unfold tStep
  split
  · rename_i a ha; exact ha
  · split <;> simp

lemma tStep_keep {Hn : Type} (φ : Hn → TG ≃ TG) (x y : ByteArray) (h : Hn)
    (s : (ByteArray → Option (TG × Hn)) × ChW ByteArray Hn TG) {v : TG × Hn} (hy : s.1 y = some v) :
    (tStep φ x h s).2.1 y = some v := by
  unfold tStep
  split
  · exact hy
  · rename_i hx
    by_cases hyx : y = x
    · subst hyx; rw [hy] at hx; cases hx
    · split <;> simp [Function.update_of_ne hyx, hy]

/-- **Target-oracle entries persist.** -/
theorem eval_htW_persist {α : Type} (m : OracleComp (specC TG) α) :
    ∀ (hs : HTS) {y : ByteArray} {v : TG × TG}, hs.1 y = some v →
      (evalWithAnswerFn (QueryImpl.ofFn g) ((simulateQ (htW (AR := Ans) (S := SIss) addHint pre)
        m).run hs)).2.1 y = some v := by
  induction m using OracleComp.inductionOn with
  | pure a => intro hs y v h; simpa using h
  | query_bind q k ih =>
    intro hs y v h
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, evalWithAnswerFn_bind]
    rcases q with d | ⟨x, hh⟩ | t
    · exact ih _ _ h
    · exact ih _ _ (tStep_keep addHint x y hh hs h)
    · exact ih _ _ h

end TableVer

/-! ## A failed forgery, table by table -/

section Fail

variable (g : Table) (T : CrtTables) (lr : Bool) (E : CTable)
  (hint : QueryLog specIC → ByteArray → TG) (pk : UovPk) (pre : TG → SIss)

/-- Lemma P's failure for forgery `i` on the game's reduced output (`PFail`). -/
def PFailZ (i : ℕ) (z : (List (ByteArray × SIss) × Bool) × HTS) : Prop :=
  z.1.2 = true ∧ ∃ x σ, z.1.1[i]? = some (x, σ) ∧ ¬∃ a e, z.2.1 x = some (a, e) ∧ relP pk σ (a + e)

/-- **No extracted candidate of the derived game's output decodes to a preimage of its programmed
target** `a + e` (`a` the target oracle's answer, `e` the hint). -/
def NoPick (r : Out (((TG × ByteArray × ByteArray) × TG) × QueryLog specIC)) : Prop :=
  ∀ i' ∈ r.2.1.known,
    ¬((bytesOf (bitsOf (@candOut (VoleMole.ZK.Sim.icPrg E.cipher) _ (stG lr pk (stOut r)) r i'))
        45 119).length = 119 ∧
      pk.toSpec.eval (bytesOf (bitsOf (@candOut (VoleMole.ZK.Sim.icPrg E.cipher) _
        (stG lr pk (stOut r)) r i')) 45 119) = toL (encT ((stOut r).1 + r.2.1.aux.1.2)))

lemma not_rel_pick {t : TG} {cs : List Spec.Bytes} (h : ¬relP pk (pick pk [t] cs) t) :
    ∀ c ∈ cs, ¬(c.length = 119 ∧ pk.toSpec.eval c = toL (encT t)) := by
  intro c hc hct
  apply h
  unfold pick
  obtain ⟨c', hc'⟩ : ∃ c', cs.find? (fun σ => decide (σ.length = 119 ∧
      ∃ t' ∈ [t], pk.toSpec.eval σ = toL (encT t'))) = some c' :=
    Option.isSome_iff_exists.1 (List.find?_isSome.2 ⟨c, hc, by simpa using hct⟩)
  have hp := List.find?_some hc'
  simp only [List.mem_singleton, exists_eq_left, decide_eq_true_eq] at hp
  exact ⟨c', by rw [hc'], hp.1, hp.2⟩

lemma extractIC_congr (st : Statement) {β β' : Type} (a : ByteArray × β) (a' : ByteArray × β')
    (J J' : QueryLog specIC) (h1 : a.1 = a'.1) (hJ : cipherLog J = cipherLog J') :
    (evalWithAnswerFn (QueryImpl.ofFn g) (extractIC st E (a, J))).1 =
      (evalWithAnswerFn (QueryImpl.ofFn g) (extractIC st E (a', J'))).1 ∧
    (evalWithAnswerFn (QueryImpl.ofFn g) (extractIC st E (a, J))).2.keys =
      (evalWithAnswerFn (QueryImpl.ofFn g) (extractIC st E (a', J'))).2.keys ∧
    (evalWithAnswerFn (QueryImpl.ofFn g) (extractIC st E (a, J))).2.known =
      (evalWithAnswerFn (QueryImpl.ofFn g) (extractIC st E (a', J'))).2.known := by
  simp [extractIC, h1, hJ]

/-- The fixed game against `g` and `E`: the prover's output, its extractor on the joint log, the
verifier. -/
lemma eval_gameIC_eq {β : Type} (st : Statement) (P : OracleComp specIC (ByteArray × β)) :
    evalWithAnswerFn (QueryImpl.ofFn g) (gameIC T st P E) =
      ((evalWithAnswerFn (QueryImpl.ofFn g) (extractIC st E
          (evalWithAnswerFn (QueryImpl.ofFn (join g E)) P, tableQueryLog P (join g E)))).1,
        (evalWithAnswerFn (QueryImpl.ofFn g) (extractIC st E
          (evalWithAnswerFn (QueryImpl.ofFn (join g E)) P, tableQueryLog P (join g E)))).2,
        @verify (VoleMole.ZK.Sim.icPrg E.cipher) (Hashes.ofTable g) T st
          (evalWithAnswerFn (QueryImpl.ofFn (join g E)) P).1) := by
  unfold gameIC
  rw [@evalWithAnswerFn_game (VoleMole.ZK.Sim.icPrg E.cipher), proverIC_eq_bind,
    evalWithAnswerFn_bind, evalWithAnswerFn_runE]
  simp [extractIC]

lemma cipherLog_append (A B : QueryLog specIC) : cipherLog (A ++ B) = cipherLog A ++ cipherLog B :=
  List.filterMap_append

variable (A : Forger) (Lst : List TG) (ℓ : ℕ)

set_option maxHeartbeats 800000 in
/-- **A failed forgery is a failure of the derived prover's game, table by table**: if forgery `i`
of the game's run against `g` verifies and its claim is not a preimage of its programmed target,
then in the adaptive game of the derived prover `proverI … i` against `g` the verifier accepts and
no extracted candidate decodes to a preimage of the programmed target. -/
theorem pfail_table (i : ℕ)
    (h : PFailZ pk i (evalWithAnswerFn (QueryImpl.ofFn g)
      ((simulateQ (htW (AR := Ans) (S := SIss) addHint pre)
        (Acomp T lr E hint tgts1 pk ℓ A)).run (hs0 Lst)))) :
    let r := evalWithAnswerFn (QueryImpl.ofFn g)
      (gameA T (stG lr pk) (proverI T lr E hint pk pre A Lst i) E)
    r.2.2.accept = true ∧ NoPick lr E pk r := by
  intro r
  set b := evalWithAnswerFn (QueryImpl.ofFn (join g E))
    ((simulateQ (wrapIC lr hint pre) (A pk)).run ([], hs0 Lst, fun _ => none)) with hb
  have hF := eval_forger g E lr hint pre (A pk) [] (hs0 Lst) (fun _ => none)
  unfold Acomp at h
  rw [eval_htW_bind, hF] at h
  dsimp only at h
  split_ifs at h with hlen
  swap
  · simp [PFailZ] at h
  rw [eval_htW_bind] at h
  simp only [simulateQ_pure, StateT.run_pure, evalWithAnswerFn_pure] at h
  obtain ⟨hflag, x, σ, hcl, hnr⟩ := h
  rw [← hb] at hlen hflag hcl hnr
  set outs := b.1 with houts
  set L := b.2.1 with hL
  set hs := b.2.2.1 with hhs
  set vsS := evalWithAnswerFn (QueryImpl.ofFn g) ((simulateQ (htW (AR := Ans) (S := SIss)
    addHint pre) (verAll T lr E hint tgts1 pk L outs)).run hs) with hvsS
  simp only [decide_eq_true_eq] at hflag
  rw [List.getElem?_map] at hcl
  obtain ⟨v, hv, hvx⟩ : ∃ v, vsS.1[i]? = some v ∧ v.1 = (x, σ) := by
    cases hvi : vsS.1[i]? with
    | none => rw [hvi] at hcl; cases hcl
    | some v => rw [hvi] at hcl; exact ⟨v, rfl, Option.some.inj hcl⟩
  have hi : i < outs.length := by
    have := (List.getElem?_eq_some_iff.1 hv).1
    rwa [hvsS, eval_verAll_length] at this
  have hvacc : v.2 = true := hflag.1 v (List.mem_of_getElem? hv)
  have hsplit := eval_verAll_split g T lr E hint pk pre L outs hs i hi
  rw [← hvsS, hv] at hsplit
  set hsi := (evalWithAnswerFn (QueryImpl.ofFn g) ((simulateQ (htW (AR := Ans) (S := SIss)
    addHint pre) (verAll T lr E hint tgts1 pk L (outs.take i))).run hs)).2 with hhsi
  simp only [Option.some.injEq] at hsplit
  -- the final state extends the state after the `i`-th verification
  have hfin : vsS.2 = (evalWithAnswerFn (QueryImpl.ofFn g) ((simulateQ (htW (AR := Ans) (S := SIss)
      addHint pre) (verAll T lr E hint tgts1 pk L (outs.drop (i + 1)))).run
      (evalWithAnswerFn (QueryImpl.ofFn g) ((simulateQ (htW (AR := Ans) (S := SIss) addHint pre)
        (verOne T lr E hint tgts1 pk L (outs[i]).1 (outs[i]).2)).run hsi)).2)).2 := by
    have hsp : outs = (outs.take i ++ [((outs[i]).1, (outs[i]).2)]) ++ outs.drop (i + 1) := by simp
    rw [hvsS]
    conv_lhs => rw [hsp]
    rw [eval_verAll_append_snd, eval_verAll_append_snd, eval_verAll_single_snd]
  rw [eval_verOne] at hsplit hfin
  set ms := outs[i] with hms
  split_ifs at hsplit hfin with hrf
  · rw [hsplit] at hvacc; cases hvacc
  cases hc : c1T g lr E pk ms.2 with
  | none => rw [hc] at hsplit; rw [hsplit] at hvacc; cases hvacc
  | some c1 =>
    rw [hc] at hsplit hfin
    dsimp only at hsplit hfin
    set x0 := tgtIn pk lr ms.2 ms.1 c1 with hx0
    set ah := tStep addHint x0 (hint (L ++ axT g lr L x0) x0) hsi with hah
    set st := pomfritRedeemT pk (fun _ => encT ah.1.1) (sB1 lr ms.2) (sB2 lr ms.2) lr with hst
    set ex := evalWithAnswerFn (QueryImpl.ofFn g) (extractIC st E ((sProof lr ms.2, ()), L)) with hex
    set t := @verify (VoleMole.ZK.Sim.icPrg E.cipher) (Hashes.ofTable g) T st (sProof lr ms.2)
      with ht
    -- the derived prover's output
    have hgetD : outs.getD i (ByteArray.empty, ByteArray.empty) = ms := by
      rw [hms, List.getD_eq_getElem _ _ hi]
    have hP : evalWithAnswerFn (QueryImpl.ofFn (join g E)) (proverI T lr E hint pk pre A Lst i) =
        (sProof lr ms.2, ((ah.1.1, sB1 lr ms.2, sB2 lr ms.2), ah.1.2)) := by
      unfold proverI
      rw [evalWithAnswerFn_bind, evalWithAnswerFn_map, ← hb, ← eval_htW_htIC, eval_verPart, hgetD]
      dsimp only
      rw [hc]
    -- the derived prover's joint log has the forger's cipher entries
    have hJ : cipherLog (tableQueryLog (proverI T lr E hint pk pre A Lst i) (join g E)) =
        cipherLog L := by
      unfold proverI
      rw [tableQueryLog_bind, tableQueryLog_map', cipherLog_append, cipherLog_htIC, List.append_nil,
        hL, hb, log_forger, List.nil_append]
    have hsA : sA g (proverI T lr E hint pk pre A Lst i) E = (ah.1.1, sB1 lr ms.2, sB2 lr ms.2) := by
      unfold sA; rw [hP]
    have hr : r = evalWithAnswerFn (QueryImpl.ofFn g)
        (gameIC T (stG lr pk (ah.1.1, sB1 lr ms.2, sB2 lr ms.2)) (proverI T lr E hint pk pre A Lst i) E) := by
      show evalWithAnswerFn (QueryImpl.ofFn g)
        (gameA T (stG lr pk) (proverI T lr E hint pk pre A Lst i) E) = _
      rw [evalWithAnswerFn_gameA, hsA]
    have hstG : stG lr pk (ah.1.1, sB1 lr ms.2, sB2 lr ms.2) = st := rfl
    rw [hstG, eval_gameIC_eq, hP] at hr
    obtain ⟨e1, e2, e3⟩ := extractIC_congr g E st (sProof lr ms.2, ((ah.1.1, sB1 lr ms.2, sB2 lr ms.2), ah.1.2))
      (sProof lr ms.2, ()) (tableQueryLog (proverI T lr E hint pk pre A Lst i) (join g E)) L rfl hJ
    have hx : x = x0 ∧ σ = pick pk (tgts1 ah.1) (candidates E st (ex.1, ex.2, t)) := by
      rw [hsplit] at hvx
      exact ⟨(Prod.mk.inj hvx).1.symm, (Prod.mk.inj hvx).2.symm⟩
    have htacc : t.accept = true := by rw [hsplit] at hvacc; exact hvacc
    have hfinx : vsS.2.1 x0 = some ah.1 := by
      rw [hfin]
      exact eval_htW_persist g pre _ ah.2 (tStep_get addHint x0 _ hsi)
    have hnr' : ¬relP pk (pick pk [ah.1.1 + ah.1.2] (candidates E st (ex.1, ex.2, t)))
        (ah.1.1 + ah.1.2) := by
      intro hrel
      refine hnr ⟨ah.1.1, ah.1.2, ?_, ?_⟩
      · rw [hx.1, hfinx]
      · rw [hx.2]; exact hrel
    have hnone := not_rel_pick pk hnr'
    rw [hr]
    refine ⟨htacc, ?_⟩
    intro i' hi'
    simp only [stOut] at hi' ⊢
    have haux : (evalWithAnswerFn (QueryImpl.ofFn g) (extractIC st E
        ((sProof lr ms.2, ((ah.1.1, sB1 lr ms.2, sB2 lr ms.2), ah.1.2)),
          tableQueryLog (proverI T lr E hint pk pre A Lst i) (join g E)))).2.aux.1 =
        ((ah.1.1, sB1 lr ms.2, sB2 lr ms.2), ah.1.2) := by
      simp [extractIC]
    rw [haux]
    dsimp only
    have hcand : @candOut (VoleMole.ZK.Sim.icPrg E.cipher) _ st
        ((evalWithAnswerFn (QueryImpl.ofFn g) (extractIC st E
          ((sProof lr ms.2, ((ah.1.1, sB1 lr ms.2, sB2 lr ms.2), ah.1.2)),
            tableQueryLog (proverI T lr E hint pk pre A Lst i) (join g E)))).1,
          (evalWithAnswerFn (QueryImpl.ofFn g) (extractIC st E
          ((sProof lr ms.2, ((ah.1.1, sB1 lr ms.2, sB2 lr ms.2), ah.1.2)),
            tableQueryLog (proverI T lr E hint pk pre A Lst i) (join g E)))).2,
          @verify (VoleMole.ZK.Sim.icPrg E.cipher) (Hashes.ofTable g) T st
            (sProof lr ms.2, ((ah.1.1, sB1 lr ms.2, sB2 lr ms.2), ah.1.2)).1) i' =
        @candOut (VoleMole.ZK.Sim.icPrg E.cipher) _ st (ex.1, ex.2, t) i' := by
      unfold candOut outChain
      rw [e1, e2]
    rw [e3] at hi'
    rw [hstG, hcand]
    refine hnone _ ?_
    unfold candidates
    simp only [List.mem_map, List.mem_filter, List.mem_finRange, true_and, decide_eq_true_eq]
    exact ⟨i', hi', rfl⟩

end Fail

/-! ## Lemma P's extraction gives the claim -/

section Pick

variable (lr : Bool) (E : CTable) (pk : UovPk)

/-- The family of the derived provers' targets. -/
def hG : TG × ByteArray × ByteArray → ByteArray → ByteArray := fun s _ => encT s.1

lemma encT_size (a : TG) : (encT a).size = 45 := by
  simp [encT, VoleMole.Privacy.size_toBA]

lemma toL_encT_add_toTG (a : TG) (r : Spec.Bytes) (hr : r.length = 45) :
    toL (encT (a + toTG r)) = Spec.xorBytes (toL (encT a)) r := by
  simp only [encT, toL_toBA, Spec.xorBytes]
  refine List.ext_getElem (by simp [hr]) fun k h1 h2 => ?_
  simp only [List.getElem_ofFn, List.getElem_zipWith, Pi.add_apply, toTG]
  rw [List.getD_eq_getElem _ _ (by simp at h1; omega)]
  rfl

/-- **Lemma P's extraction, with `E₁` right, gives a claim**: if a fully alive tree of the widest
group has a candidate in the relation at the target `a`, every alive tree is known, and the hint
`e` is the widest group's prefix, then that tree's decoded `σ` satisfies `P(σ) = a + e`: the claim
is a preimage of the programmed target. -/
theorem not_noPick (r : Out (((TG × ByteArray × ByteArray) × TG) × QueryLog specIC))
    (hme : MajorExtracted E (stG lr pk (stOut r)) (witKT pk hG (some (stOut r))) r)
    (hsub : aliveR E r ⊆ r.2.1.known)
    (he : r.2.1.aux.1.2 = toTG ((PomFRIT.majP (aliveR E r) fun i =>
      preB (@candOut (VoleMole.ZK.Sim.icPrg E.cipher) _ (stG lr pk (stOut r)) r i)).getD [])) :
    ¬NoPick lr E pk r := by
  intro hnp
  obtain ⟨i', hi', hwit, hmaj⟩ := hme
  rw [hmaj, Option.getD_some] at he
  refine hnp i' (hsub hi') ?_
  set w := @candOut (VoleMole.ZK.Sim.icPrg E.cipher) _ (stG lr pk (stOut r)) r i'
  have hrel := pomRel_of_wit pk (encT (stOut r).1) (encT_size _) w hwit
  obtain ⟨hlr, -, hls, heval⟩ := hrel
  refine ⟨hls, ?_⟩
  rw [heval, he]
  exact (toL_encT_add_toTG _ _ hlr).symm

end Pick

/-! ## The derived provers, with the cipher only as queries -/

section ProverP

/-- **The forger for the derived provers**: its hash and cipher queries to `specIC`, its target
queries answered by the target oracle's step on the state with a void hint (the answers do not
depend on the hints), its Issuer queries by `pre`. It reads the cipher only through queries. -/
noncomputable def wrapP (pre : TG → SIss) : QueryImpl specU (StateT HTS (OracleComp specIC))
  | .inl d => StateT.mk fun s => (fun u => (u, s)) <$>
      (liftM (specIC.query d) : OracleComp specIC (AnsIC d))
  | .inr (.inl x) => StateT.mk fun s => pure ((tStep addHint x 0 s).1.1, (tStep addHint x 0 s).2)
  | .inr (.inr t) => StateT.mk fun s => pure (pre t, (s.1, s.2.1, s.2.2.1, s.2.2.2 + 1))

/-- Two reduced states with the same answers (first components), stream and Issuer count: they
differ only in the hints. -/
def SameT (s s' : HTS) : Prop :=
  (∀ x, (s.1 x).map Prod.fst = (s'.1 x).map Prod.fst) ∧ s.2.1 = s'.2.1 ∧ s.2.2.2 = s'.2.2.2

lemma SameT.refl (s : HTS) : SameT s s := ⟨fun _ => rfl, rfl, rfl⟩

/-- **The target oracle's answers do not depend on the hints.** -/
lemma tStep_sameT {s s' : HTS} (h : SameT s s') (x : ByteArray) (e e' : TG) :
    (tStep addHint x e s).1.1 = (tStep addHint x e' s').1.1 ∧
      SameT (tStep addHint x e s).2 (tStep addHint x e' s').2 := by
  obtain ⟨t, l, tg, n⟩ := s
  obtain ⟨t', l', tg', n'⟩ := s'
  obtain ⟨h1, h2, h3⟩ := h
  simp only at h1 h2 h3
  subst h2 h3
  have hx := h1 x
  unfold tStep
  simp only
  cases hs : t x with
  | some a =>
    cases hs' : t' x with
    | some a' =>
      rw [hs, hs'] at hx
      simp only [Option.map_some, Option.some.injEq] at hx
      exact ⟨hx, h1, rfl, rfl⟩
    | none => rw [hs, hs'] at hx; cases hx
  | none =>
    cases hs' : t' x with
    | some a' => rw [hs, hs'] at hx; cases hx
    | none =>
      cases l with
      | nil => exact ⟨rfl, fun y => by by_cases hy : y = x <;> simp [hy, h1 y], rfl, rfl⟩
      | cons u r => exact ⟨rfl, fun y => by by_cases hy : y = x <;> simp [hy, h1 y], rfl, rfl⟩

variable (g : Table) (T : CrtTables) (lr : Bool) (E : CTable)
  (hint : QueryLog specIC → ByteArray → TG) (pk : UovPk) (pre : TG → SIss)

lemma eval_htW_iq (t : TG) (hs : HTS) :
    evalWithAnswerFn (QueryImpl.ofFn g) ((simulateQ (htW (AR := Ans) (S := SIss) addHint pre)
      (liftM ((specC TG).query (.inr (.inr t))) : OracleComp (specC TG) SIss)).run hs) =
      (pre t, (hs.1, hs.2.1, hs.2.2.1, hs.2.2.2 + 1)) := by
  erw [simulateQ_spec_query]
  rfl

/-- **The game's forger and the derived provers' forger, table by table**: the same forgeries, and
states that differ only in the hints. -/
theorem eval_forgerP {α : Type} (oa : OracleComp specU α) :
    ∀ (L : QueryLog specIC) (hs hs' : HTS), SameT hs hs' →
      (evalWithAnswerFn (QueryImpl.ofFn g) ((simulateQ (htW (AR := Ans) (S := SIss) addHint pre)
        ((simulateQ (wrapImpl lr E hint) oa).run L)).run hs)).1.1 =
        (evalWithAnswerFn (QueryImpl.ofFn (join g E)) ((simulateQ (wrapP pre) oa).run hs')).1 ∧
      SameT (evalWithAnswerFn (QueryImpl.ofFn g) ((simulateQ (htW (AR := Ans) (S := SIss) addHint pre)
        ((simulateQ (wrapImpl lr E hint) oa).run L)).run hs)).2
        (evalWithAnswerFn (QueryImpl.ofFn (join g E)) ((simulateQ (wrapP pre) oa).run hs')).2 := by
  induction oa using OracleComp.inductionOn with
  | pure a => intro L hs hs' h; simpa using h
  | query_bind q k ih =>
    intro L hs hs' h
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
    rcases q with (d | x) | (x | t)
    · simp only [wrapImpl, wrapP, StateT.run_mk, evalWithAnswerFn_bind]
      exact ih (g d) _ hs hs' h
    · simp only [wrapImpl, wrapP, StateT.run_mk, simulateQ_pure, StateT.run_pure,
        evalWithAnswerFn_bind, pure_bind]
      exact ih (E x) _ hs hs' h
    · simp only [wrapImpl, wrapP, auxC, StateT.run_mk, simulateQ_bind, StateT.run_bind,
        evalWithAnswerFn_bind, evalWithAnswerFn_pure, eval_htW_toC, eval_htW_tgt]
      obtain ⟨e1, e2⟩ := tStep_sameT h x (hint (L ++ evalWithAnswerFn (QueryImpl.ofFn g)
        (auxSpec lr L x)) x) 0
      rw [e1]
      exact ih _ _ _ _ e2
    · simp only [wrapImpl, wrapP, StateT.run_mk, evalWithAnswerFn_bind, evalWithAnswerFn_pure]
      exact ih _ _ _ _ ⟨h.1, h.2.1, congrArg (· + 1) h.2.2⟩

end ProverP

end VoleMole.ROM.OneMore.Pomfrit
