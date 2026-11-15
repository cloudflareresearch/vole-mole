import VoleMole.Theft.PlainRom
import VoleMole.Theft.PlainRata

/-!
# Plain extraction for the theft game from `ROM/`'s bound (Ratatouille)

`noTheft_leanX_hitL` (`Theft/PlainRata.lean`) keeps plain extraction `PlainSEL` as a hypothesis.
Here it is proved from `ROM/`'s simultaneous extraction (`docs/security/ratatouille.md` §5,
item 4), for function rows (`R = Blk → Blk`, `ROM/`'s random-function cipher) and the combination
of `uovM` equations (`M = uovM`, the C++ value):

* `QBudT q qE nG`: `QBud q qE` and at most `nG` hash queries in all (`ROM/`'s bound charges the
  total number of hash queries; per-kind bounds do not bound it, `Kind.comb` has a parameter).
* **`eRom A`**: the straight-line extractor of `ROM/` on the theft tables: from the operation's
  statement and proof (`Hit.Rata.fd`), the cipher entries of the query list (`cLog`, answered by
  the cipher table), `mu₁` and `iv` from the extra table, it computes the leaf keys and known trees
  (`keysOf`, `knownOf`), and outputs a candidate (`candidate`) mapped to the spec witnesses
  (`issueWitOfR`, `spendWitOf`) that is a witness of the operation, if one is.
* `provI`, `provS`: the normalized adversary (`normT`) as `ROM/`'s provers of the two relations
  (the operation's statement and proof; a dummy for the other relation).
* **`plainSEL_rom`**: `PlainSEL` for `eRom A` against `QBudT q qE nG`, with error `ε_rom q qE nG`,
  `ratatouille_sim_joint_lean` with `m = 2` outputs: the tables are the lazy oracle on the table
  points (`pr_tables_eq_ro`), every query of the game is a table point (`gameA_onT`), and on the
  tables the bad event of `PlainSEL` implies the game's (`bad_imp`).
-/

-- (The coin types are large products: their `Fintype` instances exceed the default size.)
set_option synthInstance.maxSize 1024

open Finset OracleComp OracleSpec
open scoped ENNReal

namespace VoleMole.Theft

open VoleMole.Privacy VoleMole.ZK.Sim VoleMole.Verifier VoleMole.Verifier.Bridge
open VoleMole.ROM VoleMole.ROM.IC VoleMole.ROM.Reads

/-! ## Budgets with a total -/

section Budget

variable {α : Type}

/-- **The query budget with a total**: `QBud q qE` and at most `nG` hash queries in all. -/
def QBudT (q : Kind → ℕ) (qE nG : ℕ) (oa : OracleComp specIC α) : Prop :=
  QBud q qE oa ∧ IsQueryBoundP oa (fun t => t.isLeft = true) nG

end Budget

/-! ## Logs -/

section Logs

variable {α : Type}

/-- The log against a table is the queries with their answers. -/
lemma tableQueryLog_eq_qlog (f : (d : DomIC) → AnsIC d) (oa : OracleComp specIC α) :
    tableQueryLog oa f = (qlog f oa).map fun d => ⟨d, f d⟩ := by
  induction oa using OracleComp.inductionOn with
  | pure a => simp
  | query_bind t k ih =>
    rw [tableQueryLog_query_bind, qlog_query_bind, ih]
    rfl

/-- **The cipher entries of a query list**, answered by the cipher table. -/
def cLog (E : CTable) (l : List DomIC) : QueryLog cspec :=
  l.filterMap fun d => match d with
    | .inl _ => none
    | .inr c => some ⟨c, E c⟩

lemma cipherLog_map (f : (d : DomIC) → AnsIC d) (l : List DomIC) :
    cipherLog (l.map fun d => ⟨d, f d⟩) = cLog (fun c => f (.inr c)) l := by
  induction l with
  | nil => rfl
  | cons d l ih =>
    rcases d with d | c
    · exact ih
    · exact congrArg (List.cons _) ih

lemma cLog_filter (E : CTable) (P : DomIC → Bool) (hP : ∀ c, P (.inr c) = true) (l : List DomIC) :
    cLog E (l.filter P) = cLog E l := by
  induction l with
  | nil => rfl
  | cons d l ih =>
    rcases d with d | c
    · by_cases h : P (.inl d) = true
      · rw [List.filter_cons_of_pos h]; exact ih
      · rw [List.filter_cons_of_neg h]; exact ih
    · rw [List.filter_cons_of_pos (hP c)]
      exact congrArg (List.cons _) ih

/-- **A known tree's candidate** of an output, with the ideal-cipher PRG of `E`. -/
noncomputable def candOf (E : CTable) (st : Statement) {β : Type} (r : Out β) (i : Fin BAVC.tau) :
    ℕ → Arith.GF128 :=
  letI : HasPrg := icPrg E.cipher
  EndToEnd.candidate (F := Arith.GF128) ((outChain r).u st) ((outChain r).dc st) i

/-- The candidates of an output depend on the proof, the keys and `iv` only. -/
lemma candOf_congr {β β' : Type} {r : Out β} {r' : Out β'} (E : CTable) (st : Statement)
    (h1 : r.1 = r'.1) (h2 : r.2.1.keys = r'.2.1.keys) (h3 : r.2.2.iv = r'.2.2.iv)
    (i : Fin BAVC.tau) : candOf E st r i = candOf E st r' i := by
  simp only [candOf, outChain, h1, h2, h3]
  rfl

end Logs

/-! ## The game on a table -/

section GameEval

variable {ι β : Type}

/-- **`ROM/`'s adaptive game on a complete table**: the prover's proof, the extractor's keys and
known trees from the cipher entries of its log and `iv`, and the verifier's transcript. -/
lemma eval_gameA (T : CrtTables) (stF : ι → Statement) (P : OracleComp specIC (ByteArray × (ι × β)))
    (E : CTable) (g : Table) :
    evalWithAnswerFn (QueryImpl.ofFn g) (gameA T stF P E) =
      ((evalWithAnswerFn (QueryImpl.ofFn (join g E)) P).1,
        ⟨keysOf (cipherLog (tableQueryLog P (join g E))) E
            (ivOf (Hashes.ofTable g) ⟨(stF (evalWithAnswerFn (QueryImpl.ofFn (join g E)) P).2.1).params,
              (evalWithAnswerFn (QueryImpl.ofFn (join g E)) P).1⟩
              ((stF (evalWithAnswerFn (QueryImpl.ofFn (join g E)) P).2.1).mu1 (Hashes.ofTable g)))
            (Proof.opening ⟨(stF (evalWithAnswerFn (QueryImpl.ofFn (join g E)) P).2.1).params,
              (evalWithAnswerFn (QueryImpl.ofFn (join g E)) P).1⟩)
            (Proof.delta ⟨(stF (evalWithAnswerFn (QueryImpl.ofFn (join g E)) P).2.1).params,
              (evalWithAnswerFn (QueryImpl.ofFn (join g E)) P).1⟩),
          knownOf (cipherLog (tableQueryLog P (join g E))) E
            (ivOf (Hashes.ofTable g) ⟨(stF (evalWithAnswerFn (QueryImpl.ofFn (join g E)) P).2.1).params,
              (evalWithAnswerFn (QueryImpl.ofFn (join g E)) P).1⟩
              ((stF (evalWithAnswerFn (QueryImpl.ofFn (join g E)) P).2.1).mu1 (Hashes.ofTable g)))
            (Proof.opening ⟨(stF (evalWithAnswerFn (QueryImpl.ofFn (join g E)) P).2.1).params,
              (evalWithAnswerFn (QueryImpl.ofFn (join g E)) P).1⟩),
          ((evalWithAnswerFn (QueryImpl.ofFn (join g E)) P).2, tableQueryLog P (join g E))⟩,
        @verify (icPrg E.cipher) (Hashes.ofTable g) T
          (stF (evalWithAnswerFn (QueryImpl.ofFn (join g E)) P).2.1)
          (evalWithAnswerFn (QueryImpl.ofFn (join g E)) P).1) := by
  simp only [gameA, proverA, extractIC, evalWithAnswerFn_bind, evalWithAnswerFn_runE,
    evalWithAnswerFn_mu1Q, evalWithAnswerFn_hashQ, evalWithAnswerFn_pure, evalWithAnswerFn_map,
    evalWithAnswerFn_verifyQ, ivOf]

end GameEval

/-! ## The straight-line extractor on the theft tables -/

namespace Ratatouille

open VoleMole.Spec.Ratatouille VoleMole.EndToEnd
open VoleMole.Privacy.Ratatouille (stI stS bOf)

variable {L M : ℕ} {G S : Type}

/-- The spec witnesses of a candidate. -/
def witOfCand (w : ℕ → Arith.GF128) : Wit := (SpecRel.issueWitOfR w, SpecRel.spendWitOf w)

/-- **The output the extractor rebuilds**: the proof, the keys and known trees from the cipher
log (`keysOf`, `knownOf`), and `iv` (with `mu₁` from the record `Hs`). -/
def rOut (st : Statement) (proof : ByteArray) (Hs : Hashes) (E : CTable) (log : QueryLog cspec) :
    Out Unit :=
  (proof, ⟨keysOf log E (ivOf Hs ⟨st.params, proof⟩ (st.mu1 Hs)) (Proof.opening ⟨st.params, proof⟩)
      (Proof.delta ⟨st.params, proof⟩),
    knownOf log E (ivOf Hs ⟨st.params, proof⟩ (st.mu1 Hs)) (Proof.opening ⟨st.params, proof⟩), ()⟩,
    { iv := ivOf Hs ⟨st.params, proof⟩ (st.mu1 Hs) })

/-- The cipher table of function rows. -/
def ctOf (E : Blk → Blk → Blk) : CTable := fun c => E c.1 c.2

/-- **`ROM/`'s straight-line extractor on the theft tables**: a known tree's candidate that is a
witness of the operation, if there is one (the cipher entries of the query list answered by the
cipher rows, `mu₁` and `iv` read off the extra table). -/
noncomputable def eRom (A : Thief Sizes.labelRows G S) :
    Option (IssueInstance × IssueProof Sizes.labelRows) →
      Option (SpendInstance × SpendProof Sizes.labelRows) → Op Sizes.labelRows → List DomIC →
      Tab3 → Tab3 → (Tab5F × (Blk → Blk → Blk)) × XTab L M → Wit :=
  fun _ _ op qs _ _ b => by
    classical
    let f := Hit.Rata.fd A op
    let r := rOut f.1 f.2 (hbX b.2) (ctOf b.1.2) (cLog (ctOf b.1.2) qs)
    exact if h : ∃ i ∈ r.2.1.known, RelOp A op (witOfCand (candOf (ctOf b.1.2) f.1 r i)) then
      witOfCand (candOf (ctOf b.1.2) f.1 r h.choose)
    else witOfCand 0

/-- **`eRom` finds a witness when a known tree's candidate is one.** -/
lemma relOp_eRom (A : Thief Sizes.labelRows G S) (p₁ : Option (IssueInstance × IssueProof Sizes.labelRows))
    (p₂ : Option (SpendInstance × SpendProof Sizes.labelRows)) (op : Op Sizes.labelRows)
    (qs : List DomIC) (g₁ g₂ : Tab3) (b : (Tab5F × (Blk → Blk → Blk)) × XTab L M)
    (h : ∃ i ∈ (rOut (Hit.Rata.fd A op).1 (Hit.Rata.fd A op).2 (hbX b.2) (ctOf b.1.2)
        (cLog (ctOf b.1.2) qs)).2.1.known,
      RelOp A op (witOfCand (candOf (ctOf b.1.2) (Hit.Rata.fd A op).1
        (rOut (Hit.Rata.fd A op).1 (Hit.Rata.fd A op).2 (hbX b.2) (ctOf b.1.2)
          (cLog (ctOf b.1.2) qs)) i))) :
    RelOp A op (eRom A p₁ p₂ op qs g₁ g₂ b) := by
  classical
  unfold eRom
  dsimp only
  rw [dite_eq_left_of_eq_true (eq_true h)]
  exact h.choose_spec.2

/-! ## The adversary as `ROM/`'s provers -/

/-- The issuance relation's output of an operation (a dummy for a spend). -/
def outI : Op Sizes.labelRows → ByteArray × (IssueInstance × Unit)
  | .issue q t c => (bOf (issueReqProof q), (opXI q t c, ()))
  | .spend q c _ => (ByteArray.empty, (⟨(SpendReq.parse q).cNext, 0, c⟩, ()))

/-- The spend relation's output of an operation, with the key `pk` (a dummy for an issuance). -/
def outS (A : Thief Sizes.labelRows G S) : Op Sizes.labelRows → ByteArray × (SpendK A.pk × Unit)
  | .spend q c _ => (bOf (SpendReq.parse q).proof, (⟨opXS A q c, rfl⟩, ()))
  | .issue q _ c => (ByteArray.empty, (⟨⟨A.pk, Vector.replicate 24 0, 0, issueReqC q, c⟩,
      (rfl : A.pk = A.pk)⟩, ()))

end Ratatouille

/-! ## On the tables, the bad event is the game's -/

section Bad

open VoleMole.Spec.Ratatouille VoleMole.EndToEnd
open VoleMole.Privacy.Ratatouille (pI pS)

lemma ivOf_congr {Hs Hs' : Hashes} (h4 : Hs.hash .h4 = Hs'.hash .h4) (hmu : Hs.hash .mu = Hs'.hash .mu)
    (hmuD : Hs.hash .muDelayed = Hs'.hash .muDelayed) (pf : Proof) (st : Statement) :
    ivOf Hs pf (st.mu1 Hs) = ivOf Hs' pf (st.mu1 Hs') := by
  simp only [ivOf, Statement.mu1, mu, h4, hmu, hmuD]

lemma recV_hash_ne {p : Params} (Hb : Hashes) (G2 : Tab2G p) (G5 : Tab5F) {k : Kind} (h5 : k ≠ .h5)
    (h23 : k ≠ .h23) : (recV p Hb G2 G5).hash k = Hb.hash k :=
  funext fun b => (Hashes.withTable_ne _ .h5 k h5 _ _ b).trans (Hashes.withTable_ne _ .h23 k h23 _ _ b)

variable {L M : ℕ} {ι : Type}

lemma recP_hash_ne {p : Params} (g₁ g₂ : Tab3) (t : ShX (Blk → Blk) p (XTab L M)) {k : Kind}
    (h3 : k ≠ .h3) (h5 : k ≠ .h5) (h23 : k ≠ .h23) : (recP g₁ g₂ t).hash k = (hbX t.2.2).hash k :=
  funext fun b => recP_other g₁ g₂ t h3 h5 h23 b

variable (A : Ratatouille.Thief Sizes.labelRows Tab3 (ShX (Blk → Blk) pI (XTab L M)))

set_option maxHeartbeats 2000000 in
/-- **On the tables, a bad output of `PlainSEL` is a bad output of `ROM/`'s game**: if the
operation is accepted by the Lean verifier and `eRom` finds no witness, the game run on the
tables (the normalized adversary as the prover `out <$> normT`) accepts, and its extraction fails
(for a witness predicate `Wit` that gives the operation's relation). -/
theorem game_bad (stF : ι → Statement) (out : Op Sizes.labelRows → ByteArray × (ι × Unit))
    (Wit : ι → (ℕ → Arith.GF128) → Prop) (oa : OracleComp specIC (Op Sizes.labelRows))
    (g₁ g₂ : Tab3) (t : ShX (Blk → Blk) pI (XTab L M))
    (p₁ : Option (IssueInstance × IssueProof Sizes.labelRows))
    (p₂ : Option (SpendInstance × SpendProof Sizes.labelRows))
    (hfd : Hit.Rata.fd A (runT (ansP g₁ g₂ t) oa) =
      (stF (out (runT (ansP g₁ g₂ t) oa)).2.1, (out (runT (ansP g₁ g₂ t) oa)).1))
    (hacc : (verRO pI (hbX t.2.2) (stF (out (runT (ansP g₁ g₂ t) oa)).2.1)
      (out (runT (ansP g₁ g₂ t) oa)).1 (shOf t)).accept = true)
    (hW : ∀ w, Wit (out (runT (ansP g₁ g₂ t) oa)).2.1 w →
      Ratatouille.RelOp A (runT (ansP g₁ g₂ t) oa) (Ratatouille.witOfCand w))
    (hne : ¬ Ratatouille.RelOp A (runT (ansP g₁ g₂ t) oa)
      (Ratatouille.eRom A p₁ p₂ (runT (ansP g₁ g₂ t) oa) (qlog (ansP g₁ g₂ t) oa) g₁ g₂ t.2)) :
    (evalWithAnswerFn (QueryImpl.ofFn (tabP g₁ g₂ t)) (gameA CrtGen.tables stF
        (out <$> normT pI L M oa) (cellP t))).2.2.accept = true ∧
      ¬ @Extracted (icPrg (cellP t).cipher) _
        (stF (stOut (evalWithAnswerFn (QueryImpl.ofFn (tabP g₁ g₂ t)) (gameA CrtGen.tables stF
          (out <$> normT pI L M oa) (cellP t)))))
        (fun _ w => Wit (stOut (evalWithAnswerFn (QueryImpl.ofFn (tabP g₁ g₂ t))
          (gameA CrtGen.tables stF (out <$> normT pI L M oa) (cellP t)))) w)
        (evalWithAnswerFn (QueryImpl.ofFn (tabP g₁ g₂ t)) (gameA CrtGen.tables stF
          (out <$> normT pI L M oa) (cellP t))) := by
  classical
  set o := runT (ansP g₁ g₂ t) oa with ho
  obtain ⟨hrunN, hqN⟩ := normT_ansP g₁ g₂ t oa
  have hP : evalWithAnswerFn (QueryImpl.ofFn (join (tabP g₁ g₂ t) (cellP t)))
      (out <$> normT pI L M oa) = out o := by
    rw [← runT_eq_eval, runT_map]
    exact congrArg out hrunN
  have hJ : cipherLog (tableQueryLog (out <$> normT pI L M oa) (join (tabP g₁ g₂ t) (cellP t))) =
      cLog (Ratatouille.ctOf t.2.1.2) (qlog (ansP g₁ g₂ t) oa) := by
    rw [tableQueryLog_map', tableQueryLog_eq_qlog, cipherLog_map]
    show cLog (Ratatouille.ctOf t.2.1.2) (qlog (ansP g₁ g₂ t) (normT pI L M oa)) = _
    rw [hqN, cLog_filter _ _ fun c => decide_eq_true (show OnT pI L M (.inr c) from trivial)]
  have hivP : ivOf (Hashes.ofTable (tabP g₁ g₂ t)) ⟨(stF (out o).2.1).params, (out o).1⟩
      ((stF (out o).2.1).mu1 (Hashes.ofTable (tabP g₁ g₂ t))) =
      ivOf (hbX t.2.2) ⟨(stF (out o).2.1).params, (out o).1⟩ ((stF (out o).2.1).mu1 (hbX t.2.2)) := by
    rw [ofTable_tabP]
    exact ivOf_congr (recP_hash_ne _ _ _ (by decide) (by decide) (by decide))
      (recP_hash_ne _ _ _ (by decide) (by decide) (by decide))
      (recP_hash_ne _ _ _ (by decide) (by decide) (by decide)) _ _
  have hver : @verify (icPrg (cellP t).cipher) (Hashes.ofTable (tabP g₁ g₂ t)) CrtGen.tables
      (stF (out o).2.1) (out o).1 = verRO pI (hbX t.2.2) (stF (out o).2.1) (out o).1 (shOf t) := by
    rw [ofTable_tabP]
    exact congrFun (@verify_agreeOff_h3 (icPrg (rowFn t.2.1.2)) _ _
      (Hashes.agreeOff_withTable _ _ _ _).symm CrtGen.tables _) _
  have hivV : (verRO pI (hbX t.2.2) (stF (out o).2.1) (out o).1 (shOf t)).iv =
      ivOf (hbX t.2.2) ⟨(stF (out o).2.1).params, (out o).1⟩ ((stF (out o).2.1).mu1 (hbX t.2.2)) := by
    have hacc' : (@verify (icPrg (rowFn t.2.1.2)) (recV pI (hbX t.2.2) t.1 t.2.1.1) CrtGen.tables
        (stF (out o).2.1) (out o).1).accept = true := hacc
    obtain ⟨-, leaves, hrec, -⟩ := (@accept_iff (icPrg (rowFn t.2.1.2)) _ _ _ _).1 hacc'
    refine (@verify_iv_chal1 (icPrg (rowFn t.2.1.2)) _ _ _ _ hacc' leaves hrec).1.trans ?_
    exact ivOf_congr (recV_hash_ne _ _ _ (by decide) (by decide))
      (recV_hash_ne _ _ _ (by decide) (by decide)) (recV_hash_ne _ _ _ (by decide) (by decide)) _ _
  have hr := eval_gameA CrtGen.tables stF (out <$> normT pI L M oa) (cellP t) (tabP g₁ g₂ t)
  rw [hP, hJ, hver, hivP] at hr
  generalize evalWithAnswerFn (QueryImpl.ofFn (tabP g₁ g₂ t))
    (gameA CrtGen.tables stF (out <$> normT pI L M oa) (cellP t)) = R at hr ⊢
  have hS : stOut R = (out o).2.1 := by rw [hr]; rfl
  have hT : R.2.2 = verRO pI (hbX t.2.2) (stF (out o).2.1) (out o).1 (shOf t) := by rw [hr]
  have hKn : R.2.1.known = (Ratatouille.rOut (stF (out o).2.1) (out o).1 (hbX t.2.2)
      (Ratatouille.ctOf t.2.1.2) (cLog (Ratatouille.ctOf t.2.1.2) (qlog (ansP g₁ g₂ t) oa))).2.1.known := by
    rw [hr]; rfl
  have hK : R.2.1.keys = (Ratatouille.rOut (stF (out o).2.1) (out o).1 (hbX t.2.2)
      (Ratatouille.ctOf t.2.1.2) (cLog (Ratatouille.ctOf t.2.1.2) (qlog (ansP g₁ g₂ t) oa))).2.1.keys := by
    rw [hr]; rfl
  have h1 : R.1 = (out o).1 := by rw [hr]
  rw [hS, hT]
  refine ⟨hacc, fun he => hne ?_⟩
  obtain ⟨i, hi, hw⟩ := he
  apply Ratatouille.relOp_eRom
  rw [hfd]
  refine ⟨i, hKn ▸ hi, hW _ ?_⟩
  have hiv' : R.2.2.iv = (Ratatouille.rOut (stF (out o).2.1) (out o).1 (hbX t.2.2)
      (Ratatouille.ctOf t.2.1.2) (cLog (Ratatouille.ctOf t.2.1.2) (qlog (ansP g₁ g₂ t) oa))).2.2.iv := by
    rw [hT]; exact hivV
  have hc := candOf_congr (cellP t) (stF (out o).2.1) (r := R)
    (r' := Ratatouille.rOut (stF (out o).2.1) (out o).1 (hbX t.2.2) (Ratatouille.ctOf t.2.1.2)
      (cLog (Ratatouille.ctOf t.2.1.2) (qlog (ansP g₁ g₂ t) oa))) h1 hK hiv' i
  exact hc ▸ hw

end Bad

end VoleMole.Theft
