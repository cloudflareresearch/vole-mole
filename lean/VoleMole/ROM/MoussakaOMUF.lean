import VoleMole.ROM.VerifyIC
import VoleMole.Protocols.Moussaka
import VoleMole.Spec.MoussakaLabelRows

/-!
# Moussaka: one-more unforgeability (Theorem 1) in the random-oracle and ideal-cipher model

`lean/docs/security/moussaka.md` §4. The game OMUF of the note, on the executable spec, with the
Lean verifier as the honest Anchors' and the Moderator's check, and a reduction of a winning
adversary to

* the extraction failure of one of its accepted proofs, each bounded by the random-oracle and
  ideal-cipher soundness theorems for the spec relations (`ROM/SpecSound.lean`,
  `moussakaIssue_accept_le_adaptive_spec`, `moussakaRedeem_accept_le_adaptive_spec`);
* a collision of `Com` among the extracted openings (`Adv^bind_Com(B₁)`, an assumption);
* a CT-UF forgery on the honest Anchors' keys (`Adv^ct-uf(B₂)`, an assumption).

## The game

* The `K` honest Anchors have public keys `pk : Fin K → UovPk` and signers
  `sk : Fin K → Spec.Signer` (pqov's `derive_preimage` or any other; nothing is assumed of
  them). The adversary `A` (`Adversary`) is an interactive oracle computation over the hashes and
  the cipher (`specIC`): it starts (`init`), then makes `qI` Issue queries one after the other
  (`query`, which sees the answers to the earlier ones through its state, `absorb`), then outputs
  `qR` redemption requests (`final`), each with an Anchor Set of honest Anchors, `ctx_iss`,
  `ctx_red` and `challenge_digest`.
* **Issue** (`anchorIC`): the spec's `issue_response` (`Spec.Moussaka.issueResponseN`): a request
  of the wrong length or a context of the wrong length is malformed; otherwise the Anchor verifies
  `π_iss` for the instance `(t, ctx_iss)` with the **Lean verifier on the oracles** (`verifyIC`),
  and if it accepts, it puts `t` into the signed set and returns `derive_preimage(sk_k, t)`
  (`deriveFailed` if the signer fails). `anchorIC_eq_spec`: per table this is
  `issueResponseN` with the NIZK whose verifier is the executable verifier at those tables.
* **Redeem** (`moderatorIC`): `finalize_redeem` (`Spec.Moussaka.finalizeRedeemN`) with the Lean
  verifier, for a valid Anchor Set (non-empty, at most 64 distinct honest Anchors) and contexts of
  16 bytes (`std::array` in the C++ API). A redemption oracle is not needed: its answer is public,
  so the adversary computes it itself (`verifyIC`); it outputs its redemptions at the end.
* **Win** (`Win`): for some `ctx_iss`, the distinct accepted `(ctx_red, nf)` outnumber the distinct
  accepted `t` of that context (the note's `|L_{ctx_iss}|`); the Moderator's record is global,
  across all Anchor Sets.

The adversary is deterministic given the oracles (its coins fixed); every term of the bound is an
average over them, so the theorem holds for randomized adversaries as well.

## The reduction

`omuf_le`: for every adversary,

    Pr[Win] ≤ Σ_{j < qI} Pr[accept ∧ ¬Extracted](P^iss_j) + Σ_{j < qR} Pr[accept ∧ ¬Extracted](P^red_j)
              + AdvBind(B₁) + AdvCTUF(B₂),

where `P^iss_j` (`PI`) is the whole game with the `j`-th issuance proof as its output, and `P^red_j`
(`PR`) likewise; they query the cipher only through `specIC` (the honest verifications included,
`verifyIC`), so the soundness theorems apply to them as provers. `B₁`, `B₂` (`extAll`) run the game
and the straight-line extractor on every proof; `AdvBind` is the probability that two distinct
well-formed extracted openings collide under `Com`, `AdvCTUF` that some accepted redemption's
extracted opening, with an honest key of its Anchor Set and a preimage under it, commits to a
target that was never submitted to any Anchor's signer. Per table, a win with every accepted
proof extracted gives one of the two (`Protocols/Moussaka.lean`, `collision_or_forgery`).
-/

open Finset OracleComp OracleSpec
open scoped ENNReal

namespace VoleMole.ROM.IC.OMUF

open VoleMole.Prob VoleMole.Verifier VoleMole.Verifier.Bridge VoleMole.ZK.Sim VoleMole.ROM
  VoleMole.ROM.IC

/-! ## Messages and the adversary -/

/-- The issuance proof's length (`7272` on `main`, `7528` with label rows). -/
def pfLenI (lr : Bool) : ℕ := if lr then 7528 else 7272

/-- The redemption proof's length (`8751` on `main`, `9007` with label rows). -/
def pfLenR (lr : Bool) : ℕ := if lr then 9007 else 8751

variable {K : ℕ}

/-- An Issue query: the Anchor, the request `t ‖ π_iss`, `ctx_iss`. -/
structure IssQ (K : ℕ) where
  k : Fin K
  req : ByteArray
  ctx : ByteArray

/-- A redemption: the Anchor Set (honest Anchors), the request `nf ‖ π_red`, `ctx_iss`, `ctx_red`,
`challenge_digest`. -/
structure RedQ (K : ℕ) where
  S : List (Fin K)
  req : ByteArray
  ci : ByteArray
  cr : ByteArray
  cd : ByteArray

/-- The Anchor's answer (`issue_response`). -/
abbrev IssResp := Except Spec.Moussaka.Error (Option Spec.Bytes)

/-- **An OMUF adversary** with `qR` redemptions: an interactive oracle computation over the hashes
and the cipher. -/
structure Adversary (K qR : ℕ) where
  σ : Type
  init : OracleComp specIC σ
  query : σ → OracleComp specIC (σ × IssQ K)
  absorb : σ → IssResp → σ
  final : σ → OracleComp specIC (Fin qR → RedQ K)

/-! ## The honest parties -/

/-- `t` of an issuance request. -/
def IssQ.t (q : IssQ K) : ByteArray := q.req.extract 0 45

/-- `π_iss` of an issuance request. -/
def IssQ.pf (q : IssQ K) : ByteArray := q.req.extract 45 q.req.size

/-- The request is well-formed (`issue_response`'s length checks). -/
def IssQ.WF (lr : Bool) (q : IssQ K) : Prop := q.req.size = 45 + pfLenI lr ∧ q.ctx.size = 16

instance (lr : Bool) (q : IssQ K) : Decidable (q.WF lr) := by unfold IssQ.WF; infer_instance

/-- The issuance statement of a query. -/
def IssQ.stmt (lr : Bool) (q : IssQ K) : Statement := moussakaIssue q.t q.ctx lr

/-- **The honest Anchor** (`issue_response`, `moussaka.cpp:127`): the length checks, the Lean
verifier on the oracles, then `derive_preimage`. The second output is whether the proof was
accepted (then `t` is signed). -/
def anchorIC (lr : Bool) (sk : Fin K → Spec.Signer) (q : IssQ K) :
    OracleComp specIC (IssResp × Bool) :=
  if q.WF lr then
    (fun tr : Transcript => if tr.accept then
        ((match (sk q.k).derivePreimage (toL q.t) with
          | some s => .ok (some s)
          | none => .error .deriveFailed), true)
      else (.ok none, false)) <$> verifyIC CrtGen.tables (q.stmt lr) q.pf
  else pure (.error .malformed, false)

/-- `nf` of a redemption request. -/
def RedQ.nf (r : RedQ K) : ByteArray := r.req.extract 0 24

/-- `π_red` of a redemption request. -/
def RedQ.pf (r : RedQ K) : ByteArray := r.req.extract 24 r.req.size

/-- A valid redemption query: a valid Anchor Set of honest Anchors (`AnchorSet.mk?`: non-empty, at
most 64, no repeated key), a request of the right length, contexts of 16 bytes. -/
def RedQ.WF (lr : Bool) (r : RedQ K) : Prop :=
  r.S ≠ [] ∧ r.S.length ≤ 64 ∧ r.S.Nodup ∧ r.req.size = 24 + pfLenR lr ∧ r.ci.size = 16 ∧
    r.cr.size = 16

instance (lr : Bool) (r : RedQ K) : Decidable (r.WF lr) := by unfold RedQ.WF; infer_instance

/-- The redemption statement of a query. -/
def RedQ.stmt (lr : Bool) (pk : Fin K → UovPk) (r : RedQ K) : Statement :=
  moussakaRedeem (r.S.map pk) r.nf r.ci r.cr r.cd lr

/-- **The Moderator** (`finalize_redeem`, `moussaka.cpp:278-289`) with the Lean verifier on the
oracles. -/
def moderatorIC (lr : Bool) (pk : Fin K → UovPk) (r : RedQ K) : OracleComp specIC Bool :=
  if r.WF lr then (fun tr : Transcript => tr.accept) <$> verifyIC CrtGen.tables (r.stmt lr pk) r.pf
  else pure false

/-! ## The game -/

variable {qR : ℕ}

/-- The game's output: the Issue queries with their acceptance, the redemptions with theirs. -/
abbrev GOut (K : ℕ) := List (IssQ K × Bool) × List (RedQ K × Bool)

/-- `n` Issue rounds from the state `s`. -/
def runIss (lr : Bool) (sk : Fin K → Spec.Signer) (A : Adversary K qR) :
    ℕ → A.σ → OracleComp specIC (A.σ × List (IssQ K × Bool))
  | 0, s => pure (s, [])
  | n + 1, s => A.query s >>= fun sq => anchorIC lr sk sq.2 >>= fun ra =>
      runIss lr sk A n (A.absorb sq.1 ra.1) >>= fun rest => pure (rest.1, (sq.2, ra.2) :: rest.2)

/-- The redemptions, verified by the Moderator. -/
def runRed (lr : Bool) (pk : Fin K → UovPk) (R : Fin qR → RedQ K) :
    OracleComp specIC (List (RedQ K × Bool)) :=
  (List.finRange qR).mapM fun j => (fun b => (R j, b)) <$> moderatorIC lr pk (R j)

/-- **The OMUF game** with `qI` Issue queries. -/
def game (lr : Bool) (pk : Fin K → UovPk) (sk : Fin K → Spec.Signer) (qI : ℕ)
    (A : Adversary K qR) : OracleComp specIC (GOut K) :=
  A.init >>= fun s => runIss lr sk A qI s >>= fun r => A.final r.1 >>= fun R =>
    (fun red => (r.2, red)) <$> runRed lr pk R

/-- The accepted Issue queries, as `(t, ctx_iss)`. -/
def issL (o : GOut K) : List (Spec.Bytes × Spec.Bytes) :=
  (o.1.filter (·.2)).map fun p => (toL p.1.t, toL p.1.ctx)

/-- The accepted redemptions, as `(ctx_iss, (ctx_red, nf))`. -/
def redL (o : GOut K) : List (Spec.Bytes × (Spec.Bytes × Spec.Bytes)) :=
  (o.2.filter (·.2)).map fun p => (toL p.1.ci, (toL p.1.cr, toL p.1.nf))

/-- **The adversary wins**: for some `ctx_iss`, more distinct accepted `(ctx_red, nf)` than distinct
accepted (signed) `t`. -/
def Win (o : GOut K) : Prop :=
  ∃ c, (((issL o).filter (·.2 = c)).map (·.1)).toFinset.card <
    (((redL o).filter (·.1 = c)).map (·.2)).toFinset.card

/-! ## A union bound across computations, per table -/

/-- **A union bound across different games on the same oracles.** If, at every pair of complete
tables, the event of `m₀` implies the event of one of the games `m i`, `i ∈ s`, then its
probability is at most the sum of theirs. (For each cipher table the lazy hash oracle of every
game is the same uniform table on a finite set holding all their queries,
`prEvent_randomOracle_eq_eager`.) -/
theorem prEvent_le_sum_of_tables {X : Type} (m₀ : CTable → OracleComp spec X)
    (e₀ : CTable → X → Prop) {ι : Type} (s : Finset ι) {Y : ι → Type}
    (m : (i : ι) → CTable → OracleComp spec (Y i)) (e : (i : ι) → CTable → Y i → Prop)
    (h : ∀ (g : Table) (E : CTable), e₀ E (evalWithAnswerFn (QueryImpl.ofFn g) (m₀ E)) →
      ∃ i ∈ s, e i E (evalWithAnswerFn (QueryImpl.ofFn g) (m i E))) :
    Pr{let E ← $ᵗ CTable; let r ← (simulateQ randomOracle (m₀ E)).run' ∅}[e₀ E r] ≤
      ∑ i ∈ s, Pr{let E ← $ᵗ CTable; let r ← (simulateQ randomOracle (m i E)).run' ∅}[e i E r] := by
  classical
  let : MeasurableSpace CTable := ⊤
  have hint : ∀ {Z : Type} (n : CTable → OracleComp spec Z) (p : CTable → Z → Prop),
      Pr{let E ← $ᵗ CTable; let r ← (simulateQ randomOracle (n E)).run' ∅}[p E r] =
        ∫⁻ E, Pr{let r ← (simulateQ randomOracle (n E)).run' ∅}[p E r] ∂𝒟[$ᵗ CTable] :=
    fun n p => prEvent_bind_of_discrete _ _
  rw [hint]
  simp_rw [hint]
  rw [← MeasureTheory.lintegral_finsetSum _ fun _ _ => measurable_from_top]
  refine MeasureTheory.lintegral_mono fun E => ?_
  let S : Finset Dom := possibleQueryKeys (m₀ E) ∪ s.biUnion fun i => possibleQueryKeys (m i E)
  have hS₀ : AllQueriesSatisfy (m₀ E) (· ∈ S) :=
    (allQueriesSatisfy_possibleQueryKeys _).mono fun d hd => Finset.mem_union_left _ hd
  have hS : ∀ i ∈ s, AllQueriesSatisfy (m i E) (· ∈ S) := fun i hi =>
    (allQueriesSatisfy_possibleQueryKeys _).mono fun d hd =>
      Finset.mem_union_right _ (Finset.mem_biUnion.2 ⟨i, hi, hd⟩)
  let _ : SampleableType ((d : S) → Ans d.val) := SampleableType.ofFintype _
  rw [prEvent_randomOracle_eq_eager _ S hS₀]
  rw [Finset.sum_congr rfl fun i hi => prEvent_randomOracle_eq_eager _ S (hS i hi) (e i E)]
  refine (prEvent_mono _ _ _ fun G hG => h _ E hG).trans (prEvent_exists_finset_le s _ _)

/-- The same, for an event implying one of two indexed families of events or one of two events of a
further game. -/
theorem prEvent_le_sum4_of_tables {X Y₁ Y₂ Z : Type} (m₀ : CTable → OracleComp spec X)
    (e₀ : CTable → X → Prop) (s₁ s₂ : Finset ℕ)
    (m₁ : ℕ → CTable → OracleComp spec Y₁) (e₁ : CTable → Y₁ → Prop)
    (m₂ : ℕ → CTable → OracleComp spec Y₂) (e₂ : CTable → Y₂ → Prop)
    (n : CTable → OracleComp spec Z) (c d : CTable → Z → Prop)
    (h : ∀ (g : Table) (E : CTable), e₀ E (evalWithAnswerFn (QueryImpl.ofFn g) (m₀ E)) →
      (∃ i ∈ s₁, e₁ E (evalWithAnswerFn (QueryImpl.ofFn g) (m₁ i E))) ∨
      (∃ i ∈ s₂, e₂ E (evalWithAnswerFn (QueryImpl.ofFn g) (m₂ i E))) ∨
      c E (evalWithAnswerFn (QueryImpl.ofFn g) (n E)) ∨ d E (evalWithAnswerFn (QueryImpl.ofFn g) (n E))) :
    Pr{let E ← $ᵗ CTable; let r ← (simulateQ randomOracle (m₀ E)).run' ∅}[e₀ E r] ≤
      ∑ i ∈ s₁, Pr{let E ← $ᵗ CTable; let r ← (simulateQ randomOracle (m₁ i E)).run' ∅}[e₁ E r] +
      ∑ i ∈ s₂, Pr{let E ← $ᵗ CTable; let r ← (simulateQ randomOracle (m₂ i E)).run' ∅}[e₂ E r] +
      Pr{let E ← $ᵗ CTable; let r ← (simulateQ randomOracle (n E)).run' ∅}[c E r] +
      Pr{let E ← $ᵗ CTable; let r ← (simulateQ randomOracle (n E)).run' ∅}[d E r] := by
  classical
  let : MeasurableSpace CTable := ⊤
  have hint : ∀ {W : Type} (k : CTable → OracleComp spec W) (p : CTable → W → Prop),
      Pr{let E ← $ᵗ CTable; let r ← (simulateQ randomOracle (k E)).run' ∅}[p E r] =
        ∫⁻ E, Pr{let r ← (simulateQ randomOracle (k E)).run' ∅}[p E r] ∂𝒟[$ᵗ CTable] :=
    fun k p => prEvent_bind_of_discrete _ _
  rw [hint]
  simp_rw [hint]
  rw [← MeasureTheory.lintegral_finsetSum _ fun _ _ => measurable_from_top,
    ← MeasureTheory.lintegral_finsetSum _ fun _ _ => measurable_from_top,
    ← MeasureTheory.lintegral_add_left measurable_from_top,
    ← MeasureTheory.lintegral_add_left measurable_from_top,
    ← MeasureTheory.lintegral_add_left measurable_from_top]
  refine MeasureTheory.lintegral_mono fun E => ?_
  let S : Finset Dom := possibleQueryKeys (m₀ E) ∪ (s₁.biUnion fun i => possibleQueryKeys (m₁ i E)) ∪
    (s₂.biUnion fun i => possibleQueryKeys (m₂ i E)) ∪ possibleQueryKeys (n E)
  have hS₀ : AllQueriesSatisfy (m₀ E) (· ∈ S) :=
    (allQueriesSatisfy_possibleQueryKeys _).mono fun d hd => by simp [S, hd]
  have hS₁ : ∀ i ∈ s₁, AllQueriesSatisfy (m₁ i E) (· ∈ S) := fun i hi =>
    (allQueriesSatisfy_possibleQueryKeys _).mono fun d hd => by
      simp only [S, Finset.mem_union, Finset.mem_biUnion]; exact Or.inl (Or.inl (Or.inr ⟨i, hi, hd⟩))
  have hS₂ : ∀ i ∈ s₂, AllQueriesSatisfy (m₂ i E) (· ∈ S) := fun i hi =>
    (allQueriesSatisfy_possibleQueryKeys _).mono fun d hd => by
      simp only [S, Finset.mem_union, Finset.mem_biUnion]; exact Or.inl (Or.inr ⟨i, hi, hd⟩)
  have hSn : AllQueriesSatisfy (n E) (· ∈ S) :=
    (allQueriesSatisfy_possibleQueryKeys _).mono fun d hd => by simp [S, hd]
  let _ : SampleableType ((d : S) → Ans d.val) := SampleableType.ofFintype _
  rw [prEvent_randomOracle_eq_eager _ S hS₀,
    Finset.sum_congr rfl fun i hi => prEvent_randomOracle_eq_eager _ S (hS₁ i hi) (e₁ E),
    Finset.sum_congr rfl fun i hi => prEvent_randomOracle_eq_eager _ S (hS₂ i hi) (e₂ E),
    prEvent_randomOracle_eq_eager _ S hSn (c E), prEvent_randomOracle_eq_eager _ S hSn (d E)]
  refine (prEvent_mono _ _ _ fun G hG => h _ E hG).trans ?_
  refine (prEvent_or_le _ _ _).trans ?_
  refine (add_le_add_right ((prEvent_or_le _ _ _).trans (add_le_add_right (prEvent_or_le _ _ _) _))
    _).trans ?_
  refine (add_le_add (prEvent_exists_finset_le s₁ _ _)
    (add_le_add (prEvent_exists_finset_le s₂ _ _) le_rfl)).trans (le_of_eq ?_)
  ring

/-! ## Per table: the honest checks are the executable verifier -/

section PerTable

variable (g : Table) (E : CTable) (lr : Bool) (pk : Fin K → UovPk) (sk : Fin K → Spec.Signer)

/-- The executable verifier's verdict on an Issue query, at the tables `g`, `E`. -/
def verI (q : IssQ K) : Bool :=
  (@verify (icPrg E.cipher) (Hashes.ofTable g) CrtGen.tables (q.stmt lr) q.pf).accept

/-- The executable verifier's verdict on a redemption, at the tables `g`, `E`. -/
def verR (r : RedQ K) : Bool :=
  (@verify (icPrg E.cipher) (Hashes.ofTable g) CrtGen.tables (r.stmt lr pk) r.pf).accept

theorem evalWithAnswerFn_anchorIC (q : IssQ K) :
    (evalWithAnswerFn (QueryImpl.ofFn (join g E)) (anchorIC lr sk q)).2 =
      (decide (q.WF lr) && verI g E lr q) := by
  unfold anchorIC verI
  split_ifs with h
  · rw [evalWithAnswerFn_map, evalWithAnswerFn_verifyIC]
    simp only [h, decide_true, Bool.true_and]
    split_ifs with ha <;> simp [ha]
  · simp [h]

/-- **Per table, the honest Anchor is the spec's `issue_response`** (`issueResponseN` with the
request length of `lr`) for the NIZK whose verifier is the executable verifier at the tables. -/
def nizkI : Spec.Moussaka.NIZK Spec.Moussaka.IssueInstance :=
  ⟨fun _ _ _ => [], fun pf x =>
    (@verify (icPrg E.cipher) (Hashes.ofTable g) CrtGen.tables (moussakaIssue (toBA x.t) (toBA x.ctxIss) lr)
      (toBA pf)).accept⟩

theorem toBA_toL' (b : ByteArray) : toBA (toL b) = b := by
  rw [Privacy.toL_eq]; cases b; rfl

theorem toL_extract0 (b : ByteArray) (n : ℕ) : toL (b.extract 0 n) = (toL b).take n := by
  simp only [Privacy.toL_eq, ByteArray.data_extract, Array.toList_extract, List.extract]; simp

theorem toL_extract_size (b : ByteArray) (n : ℕ) : toL (b.extract n b.size) = (toL b).drop n := by
  simp only [Privacy.toL_eq, ByteArray.data_extract, Array.toList_extract, List.extract]; simp

theorem anchorIC_eq_spec (q : IssQ K) :
    (evalWithAnswerFn (QueryImpl.ofFn (join g E)) (anchorIC lr sk q)).1 =
      Spec.Moussaka.issueResponseN (45 + pfLenI lr) (nizkI g E lr) (sk q.k) (toL q.req)
        (toL q.ctx) := by
  have ht : (toL q.req).take 45 = toL q.t := (toL_extract0 _ _).symm
  have hp : (toL q.req).drop 45 = toL q.pf := (toL_extract_size _ _).symm
  unfold anchorIC Spec.Moussaka.issueResponseN
  by_cases h : q.WF lr
  · have h1 : ¬((toL q.req).length ≠ 45 + pfLenI lr ∨ (toL q.ctx).length ≠ Spec.Moussaka.ctxBytes) := by
      simp [Privacy.length_toL, h.1, h.2]
    simp only [h, h1, ↓reduceIte]
    rw [evalWithAnswerFn_map, evalWithAnswerFn_verifyIC]
    simp only [Spec.uovM, ht, hp, nizkI, toBA_toL', IssQ.stmt]
    by_cases ha : (@verify (icPrg E.cipher) (Hashes.ofTable g) CrtGen.tables
      (moussakaIssue q.t q.ctx lr) q.pf).accept = true
    · simp only [ha, ite_true]
      cases (sk q.k).derivePreimage (toL q.t) <;> rfl
    · simp only [ha, Bool.false_eq_true, ite_false]
  · have h1 : ((toL q.req).length ≠ 45 + pfLenI lr ∨ (toL q.ctx).length ≠ Spec.Moussaka.ctxBytes) := by
      simp only [IssQ.WF, not_and_or] at h
      simpa [Privacy.length_toL] using h
    simp only [h, h1, ↓reduceIte]
    rfl

theorem evalWithAnswerFn_moderatorIC (r : RedQ K) :
    evalWithAnswerFn (QueryImpl.ofFn (join g E)) (moderatorIC lr pk r) =
      (decide (r.WF lr) && verR g E lr pk r) := by
  unfold moderatorIC verR
  split_ifs with h
  · rw [evalWithAnswerFn_map, evalWithAnswerFn_verifyIC]; simp [h]
  · simp [h]

variable {qR : ℕ} (A : Adversary K qR)

/-- **Per table, every accepted Issue query is well-formed and verifies.** -/
theorem runIss_eval (n : ℕ) (s : A.σ) :
    (evalWithAnswerFn (QueryImpl.ofFn (join g E)) (runIss lr sk A n s)).2.length = n ∧
    ∀ p ∈ (evalWithAnswerFn (QueryImpl.ofFn (join g E)) (runIss lr sk A n s)).2,
      p.2 = true → p.1.WF lr ∧ verI g E lr p.1 = true := by
  induction n generalizing s with
  | zero => simp [runIss]
  | succ n ih =>
    simp only [runIss, evalWithAnswerFn_bind, evalWithAnswerFn_pure, List.length_cons,
      List.mem_cons]
    refine ⟨by rw [(ih _).1], ?_⟩
    rintro p (rfl | hp) hb
    · rw [evalWithAnswerFn_anchorIC] at hb
      simpa using hb
    · exact (ih _).2 p hp hb

theorem runRed_eval (R : Fin qR → RedQ K) :
    evalWithAnswerFn (QueryImpl.ofFn (join g E)) (runRed lr pk R) =
      (List.finRange qR).map fun j => (R j, decide ((R j).WF lr) && verR g E lr pk (R j)) := by
  unfold runRed
  rw [evalWithAnswerFn_mapM]
  simp only [evalWithAnswerFn_map, evalWithAnswerFn_moderatorIC]

/-- **Per table, the game's records**: `qI` Issue records, every accepted one well-formed and
verified; `qR` redemptions, every accepted one valid and verified. -/
theorem game_eval (qI : ℕ) :
    let o := evalWithAnswerFn (QueryImpl.ofFn (join g E)) (game lr pk sk qI A)
    o.1.length = qI ∧ (∀ p ∈ o.1, p.2 = true → p.1.WF lr ∧ verI g E lr p.1 = true) ∧
    o.2.length = qR ∧ (∀ p ∈ o.2, p.2 = true → p.1.WF lr ∧ verR g E lr pk p.1 = true) := by
  simp only [game, evalWithAnswerFn_bind, evalWithAnswerFn_map, runRed_eval]
  refine ⟨(runIss_eval g E lr sk A _ _).1, (runIss_eval g E lr sk A _ _).2, by simp, ?_⟩
  intro p hp hb
  obtain ⟨j, -, rfl⟩ := List.mem_map.1 hp
  simpa using hb

end PerTable

/-! ## The provers: the whole game, with one proof as output -/

/-- Issuance statements: `t` of 45 bytes, `ctx_iss` of 16. -/
abbrev ιI := {p : ByteArray × ByteArray // p.1.size = 45 ∧ p.2.size = 16}

/-- A fixed issuance statement (the output when the `j`-th query is malformed or missing). -/
def dummyI : ιI := ⟨(⟨Array.replicate 45 0⟩, ⟨Array.replicate 16 0⟩), by simp [ByteArray.size]⟩

/-- The issuance statement family. -/
abbrev stI (lr : Bool) (s : ιI) : Statement := moussakaIssue s.1.1 s.1.2 lr

/-- The `j`-th issuance proof of a game output, with its statement. -/
def projI (j : ℕ) (o : GOut K) : ByteArray × (ιI × GOut K) :=
  match o.1[j]? with
  | some p => if h : p.1.t.size = 45 ∧ p.1.ctx.size = 16 then (p.1.pf, (⟨(p.1.t, p.1.ctx), h⟩, o))
      else (ByteArray.empty, (dummyI, o))
  | none => (ByteArray.empty, (dummyI, o))

/-- **The prover `P^iss_j`**: the whole OMUF game (adversary, honest Anchors, Moderator), with the
`j`-th issuance proof and its statement as output. It reaches the cipher only through `specIC`. -/
def PI (lr : Bool) (pk : Fin K → UovPk) (sk : Fin K → Spec.Signer) (qI : ℕ) (A : Adversary K qR)
    (j : ℕ) : OracleComp specIC (ByteArray × (ιI × GOut K)) :=
  projI j <$> game lr pk sk qI A

/-- Redemption statements: at most 64 Anchors, `nf` of 24 bytes, contexts of 16. -/
abbrev ιR (K : ℕ) := {x : List (Fin K) × ByteArray × ByteArray × ByteArray × ByteArray //
  x.1.length ≤ 64 ∧ x.2.1.size = 24 ∧ x.2.2.1.size = 16 ∧ x.2.2.2.1.size = 16}

def dummyR : ιR K :=
  ⟨([], ⟨Array.replicate 24 0⟩, ⟨Array.replicate 16 0⟩, ⟨Array.replicate 16 0⟩, ByteArray.empty),
    by simp [ByteArray.size]⟩

/-- The Anchor Set of a redemption statement. -/
abbrev ancR (pk : Fin K → UovPk) (s : ιR K) : List UovPk := s.1.1.map pk

/-- The redemption statement family. -/
abbrev stR (lr : Bool) (pk : Fin K → UovPk) (s : ιR K) : Statement :=
  moussakaRedeem (ancR pk s) s.1.2.1 s.1.2.2.1 s.1.2.2.2.1 s.1.2.2.2.2 lr

/-- The `j`-th redemption proof of a game output, with its statement. -/
def projR (j : ℕ) (o : GOut K) : ByteArray × (ιR K × GOut K) :=
  match o.2[j]? with
  | some p => if h : p.1.S.length ≤ 64 ∧ p.1.nf.size = 24 ∧ p.1.ci.size = 16 ∧ p.1.cr.size = 16
      then (p.1.pf, (⟨(p.1.S, p.1.nf, p.1.ci, p.1.cr, p.1.cd), h⟩, o))
      else (ByteArray.empty, (dummyR, o))
  | none => (ByteArray.empty, (dummyR, o))

/-- **The prover `P^red_j`**: the whole game, with the `j`-th redemption proof as output. -/
def PR (lr : Bool) (pk : Fin K → UovPk) (sk : Fin K → Spec.Signer) (qI : ℕ) (A : Adversary K qR)
    (j : ℕ) : OracleComp specIC (ByteArray × (ιR K × GOut K)) :=
  projR j <$> game lr pk sk qI A

/-- The adaptive games' outputs. -/
abbrev OutI (K : ℕ) := Out ((ιI × GOut K) × QueryLog specIC)
abbrev OutR (K : ℕ) := Out ((ιR K × GOut K) × QueryLog specIC)

/-- **Per table, the adaptive game's transcript** is the executable verifier on `P`'s proof, at
`P`'s statement. -/
theorem gameA_transcript {ι β : Type} (g : Table) (E : CTable) (T : CrtTables)
    (stF : ι → Statement) (P : OracleComp specIC (ByteArray × (ι × β))) :
    (evalWithAnswerFn (QueryImpl.ofFn g) (gameA T stF P E)).2.2 =
      @verify (icPrg E.cipher) (Hashes.ofTable g) T (stF (sA g P E))
        (evalWithAnswerFn (QueryImpl.ofFn (join g E)) P).1 := by
  rw [evalWithAnswerFn_gameA]
  unfold gameIC
  rw [@evalWithAnswerFn_game (icPrg E.cipher), evalWithAnswerFn_proverIC]

lemma size_t {lr : Bool} {q : IssQ K} (h : q.WF lr) : q.t.size = 45 := by
  simp only [IssQ.t, ByteArray.size_extract, h.1]; omega

lemma size_nf {lr : Bool} {r : RedQ K} (h : r.WF lr) : r.nf.size = 24 := by
  simp only [RedQ.nf, ByteArray.size_extract, h.2.2.2.1]; omega

section Accepted

variable (g : Table) (E : CTable) (lr : Bool) (pk : Fin K → UovPk) (sk : Fin K → Spec.Signer)
  (qI : ℕ) (A : Adversary K qR)

/-- **An accepted Issue query is accepted by `P^iss_j`'s verifier, at its statement.** -/
theorem accepted_I {j : ℕ} {q : IssQ K}
    (hj : (evalWithAnswerFn (QueryImpl.ofFn (join g E)) (game lr pk sk qI A)).1[j]? = some (q, true)) :
    let r := evalWithAnswerFn (QueryImpl.ofFn g) (gameA CrtGen.tables (stI lr) (PI lr pk sk qI A j) E)
    r.2.2.accept = true ∧ (stOut r).1 = (q.t, q.ctx) := by
  obtain ⟨-, hrec, -⟩ := game_eval g E lr pk sk A qI
  obtain ⟨hwf, hv⟩ := hrec _ (List.mem_of_getElem? hj) rfl
  have hsz : q.t.size = 45 ∧ q.ctx.size = 16 := ⟨size_t hwf, hwf.2⟩
  have hP : evalWithAnswerFn (QueryImpl.ofFn (join g E)) (PI lr pk sk qI A j) =
      (q.pf, (⟨(q.t, q.ctx), hsz⟩, evalWithAnswerFn (QueryImpl.ofFn (join g E)) (game lr pk sk qI A))) := by
    simp only [PI, evalWithAnswerFn_map, projI, hj, hsz, and_self, dite_true]
  refine ⟨?_, ?_⟩
  · rw [gameA_transcript, sA, hP]; exact hv
  · rw [stOut_gameA, sA, hP]

/-- **An accepted redemption is accepted by `P^red_j`'s verifier, at its statement.** -/
theorem accepted_R {j : ℕ} {rq : RedQ K}
    (hj : (evalWithAnswerFn (QueryImpl.ofFn (join g E)) (game lr pk sk qI A)).2[j]? = some (rq, true)) :
    let r := evalWithAnswerFn (QueryImpl.ofFn g) (gameA CrtGen.tables (stR lr pk) (PR lr pk sk qI A j) E)
    r.2.2.accept = true ∧ (stOut r).1 = (rq.S, rq.nf, rq.ci, rq.cr, rq.cd) := by
  obtain ⟨-, -, -, hrec⟩ := game_eval g E lr pk sk A qI
  obtain ⟨hwf, hv⟩ := hrec _ (List.mem_of_getElem? hj) rfl
  have hsz : rq.S.length ≤ 64 ∧ rq.nf.size = 24 ∧ rq.ci.size = 16 ∧ rq.cr.size = 16 :=
    ⟨hwf.2.1, size_nf hwf, hwf.2.2.2.2.1, hwf.2.2.2.2.2⟩
  have hP : evalWithAnswerFn (QueryImpl.ofFn (join g E)) (PR lr pk sk qI A j) =
      (rq.pf, (⟨(rq.S, rq.nf, rq.ci, rq.cr, rq.cd), hsz⟩,
        evalWithAnswerFn (QueryImpl.ofFn (join g E)) (game lr pk sk qI A))) := by
    simp only [PR, evalWithAnswerFn_map, projR, hj, hsz, and_self, dite_true]
  refine ⟨?_, ?_⟩
  · rw [gameA_transcript, sA, hP]; exact hv
  · rw [stOut_gameA, sA, hP]

end Accepted

/-! ## Extraction and the extracted openings -/

/-- A commitment opening `(nf, ctx_iss, ctx_red, r)`. -/
abbrev Opening := Spec.Bytes × Spec.Bytes × Spec.Bytes × Spec.Bytes

/-- `Com` of an opening (`Spec.Moussaka.com`, Keccak-p[800]). -/
def comO (x : Opening) : Spec.Bytes := Spec.Moussaka.com x.1 x.2.1 x.2.2.1 x.2.2.2

/-- An opening in `Com`'s domain `D` (`nf` 24 bytes, contexts and `r` 16). -/
def WFO (x : Opening) : Prop :=
  x.1.length = 24 ∧ x.2.1.length = 16 ∧ x.2.2.1.length = 16 ∧ x.2.2.2.length = 16

section Ext

variable (E : CTable) (lr : Bool) (pk : Fin K → UovPk)

/-- **Extraction of an issuance proof succeeds** (the event of
`moussakaIssue_accept_le_adaptive_spec`): a known tree's candidate decodes to a witness of the
spec relation `IssueRelW` at the proof's statement. -/
def ExtI (r : OutI K) : Prop :=
  @Extracted (icPrg E.cipher) _ (stI lr (stOut r))
    (fun _ w => Privacy.Moussaka.IssueRelW ⟨toL (stOut r).1.1, toL (stOut r).1.2⟩
      (EndToEnd.SpecRel.issueWitOf (toL (stOut r).1.2) w)) r

/-- **Extraction of a redemption proof succeeds** (the event of
`moussakaRedeem_accept_le_adaptive_spec`). -/
def ExtR (r : OutR K) : Prop :=
  @Extracted (icPrg E.cipher) _ (stR lr pk (stOut r))
    (fun _ w => Privacy.Moussaka.RedeemRelW
      ⟨(ancR pk (stOut r)).map UovPk.toSpec, toL (stOut r).1.2.1, toL (stOut r).1.2.2.1,
        toL (stOut r).1.2.2.2.1, toL (stOut r).1.2.2.2.2⟩
      (EndToEnd.SpecRel.redeemWitOf (toL (stOut r).1.2.1) (toL (stOut r).1.2.2.1)
        (toL (stOut r).1.2.2.2.1) w)) r

/-- **The openings extracted from an issuance proof**: a known tree's candidate decodes to the
issuance witness of the opening, which commits to `t` in context `ctx_iss`. -/
def OpI (r : OutI K) : Set Opening := {x | WFO x ∧ x.2.1 = toL (stOut r).1.2 ∧
  comO x = toL (stOut r).1.1 ∧
  @Extracted (icPrg E.cipher) _ (stI lr (stOut r))
    (fun _ w => EndToEnd.SpecRel.issueWitOf (toL (stOut r).1.2) w =
      Spec.Moussaka.encodeIssueWitness x.1 x.2.1 x.2.2.1 x.2.2.2) r}

/-- **The openings extracted from a redemption proof, with a key and a preimage**: a known tree's
candidate decodes to the redemption witness of the opening (at `nf`, `ctx_iss`, `ctx_red`), a
preimage `s` and a selector `u`, and the Anchor at `u` is an honest Anchor `k` with
`P_k(s) = Com(opening)`. -/
def OpR (r : OutR K) : Set Opening := {x | WFO x ∧ x.1 = toL (stOut r).1.2.1 ∧
  x.2.1 = toL (stOut r).1.2.2.1 ∧ x.2.2.1 = toL (stOut r).1.2.2.2.1 ∧
  ∃ (s : Spec.Bytes) (u : ℕ) (k : Fin K), (stOut r).1.1[u]? = some k ∧
    (pk k).toSpec.eval s = comO x ∧
    @Extracted (icPrg E.cipher) _ (stR lr pk (stOut r))
      (fun _ w => EndToEnd.SpecRel.redeemWitOf (toL (stOut r).1.2.1) (toL (stOut r).1.2.2.1)
        (toL (stOut r).1.2.2.2.1) w =
        Spec.Moussaka.encodeRedeemWitness x.1 x.2.1 x.2.2.1 x.2.2.2 s u) r}

/-- **The extraction failure of an issuance proof**: accepted, and not extracted. -/
def BadI (r : OutI K) : Prop := r.2.2.accept = true ∧ ¬ExtI E lr r

/-- **The extraction failure of a redemption proof**. -/
def BadR (r : OutR K) : Prop := r.2.2.accept = true ∧ ¬ExtR E lr pk r

theorem opI_of_ext {r : OutI K} (h : ExtI E lr r) :
    ∃ x ∈ OpI E lr r, comO x = toL (stOut r).1.1 ∧ x.2.1 = toL (stOut r).1.2 := by
  obtain ⟨i, hi, ⟨nf, rr, cr, hnf, hr, hcr, hw, ht⟩, hci⟩ := h
  refine ⟨(nf, toL (stOut r).1.2, cr, rr), ⟨⟨hnf, hci, hcr, hr⟩, rfl, ht.symm, i, hi, hw⟩,
    ht.symm, rfl⟩

theorem opR_of_ext {r : OutR K} (h : ExtR E lr pk r) :
    ∃ x ∈ OpR E lr pk r, x.2.1 = toL (stOut r).1.2.2.1 ∧
      (x.2.2.1, x.1) = (toL (stOut r).1.2.2.2.1, toL (stOut r).1.2.1) := by
  obtain ⟨i, hi, ⟨rr, s, u, pk', hr, -, hu, hw, he⟩, -, hnf, hci, hcr⟩ := h
  simp only [ancR, List.map_map, List.getElem?_map, Option.map_eq_some_iff,
    Function.comp_apply] at hu
  obtain ⟨k, hk, rfl⟩ := hu
  exact ⟨(toL (stOut r).1.2.1, toL (stOut r).1.2.2.1, toL (stOut r).1.2.2.2.1, rr),
    ⟨⟨hnf, hci, hcr, hr⟩, rfl, rfl, rfl, s, u, k, hk, he, i, hi, hw⟩, rfl, rfl⟩

end Ext

/-! ## The reductions `B₁`, `B₂` and the per-table core -/

lemma evalWithAnswerFn_mapM_spec {β γ : Type} (g : Table) (l : List β) (h : β → OracleComp spec γ) :
    evalWithAnswerFn (QueryImpl.ofFn g) (l.mapM h) = l.map fun x => evalWithAnswerFn (QueryImpl.ofFn g) (h x) := by
  induction l with
  | nil => rfl
  | cons x l ih => simp [List.mapM_cons, ih]

section Red

variable (lr : Bool) (pk : Fin K → UovPk) (sk : Fin K → Spec.Signer) (qI : ℕ) (A : Adversary K qR)

/-- **The reductions' run** (`B₁` and `B₂`): the game, then every issuance and every redemption
proof's straight-line extraction and verification (`gameA` of `P^iss_j`, `P^red_j`; the adversary
is deterministic given the oracles, so each re-run is the same run). -/
def extAll (E : CTable) : OracleComp spec (GOut K × List (OutI K) × List (OutR K)) :=
  runE E (game lr pk sk qI A) >>= fun o =>
    (List.range qI).mapM (fun j => gameA CrtGen.tables (stI lr) (PI lr pk sk qI A j) E) >>= fun oi =>
      (List.range qR).mapM (fun j => gameA CrtGen.tables (stR lr pk) (PR lr pk sk qI A j) E) >>=
        fun orr => pure (o.1, oi, orr)

/-- The view of the reductions. -/
abbrev View (K : ℕ) := GOut K × List (OutI K) × List (OutR K)

/-- The openings extracted from the accepted issuance proofs. -/
def SI (E : CTable) (v : View K) : Set Opening :=
  {x | ∃ (j : ℕ) (q : IssQ K) (r : OutI K), v.1.1[j]? = some (q, true) ∧ v.2.1[j]? = some r ∧
    x ∈ OpI E lr r}

/-- The openings, with keys and preimages, extracted from the accepted redemption proofs. -/
def SR (E : CTable) (v : View K) : Set Opening :=
  {x | ∃ (j : ℕ) (rq : RedQ K) (r : OutR K), v.1.2[j]? = some (rq, true) ∧ v.2.2[j]? = some r ∧
    x ∈ OpR E lr pk r}

/-- **`B₁` wins the binding game**: two distinct extracted openings in `Com`'s domain with one
commitment. (`B₁` outputs such a pair if there is one: the candidates are polynomially many.) -/
def Coll (E : CTable) (v : View K) : Prop :=
  ∃ x ∈ SI lr E v ∪ SR lr pk E v, ∃ x' ∈ SI lr E v ∪ SR lr pk E v, x ≠ x' ∧ comO x = comO x'

/-- **`B₂` wins the CT-UF game**: an extracted redemption opening `x`, with an honest Anchor `k` and
`s` such that `P_k(s) = Com(x)`, whose commitment was never submitted to any Anchor's signer (the
signer is called exactly on the accepted Issue queries' `t`, `anchorIC`). -/
def Forge (E : CTable) (v : View K) : Prop :=
  ∃ x ∈ SR lr pk E v, comO x ∉ (issL v.1).map (·.1)

theorem extAll_eval (g : Table) (E : CTable) :
    evalWithAnswerFn (QueryImpl.ofFn g) (extAll lr pk sk qI A E) =
      (evalWithAnswerFn (QueryImpl.ofFn (join g E)) (game lr pk sk qI A),
        (List.range qI).map (fun j =>
          evalWithAnswerFn (QueryImpl.ofFn g) (gameA CrtGen.tables (stI lr) (PI lr pk sk qI A j) E)),
        (List.range qR).map (fun j =>
          evalWithAnswerFn (QueryImpl.ofFn g) (gameA CrtGen.tables (stR lr pk) (PR lr pk sk qI A j) E))) := by
  simp only [extAll, evalWithAnswerFn_bind, evalWithAnswerFn_runE, evalWithAnswerFn_mapM_spec,
    evalWithAnswerFn_pure]

/-- **The per-table core of Theorem 1**: a win means that some accepted proof is not extracted, or
`B₁` finds a `Com` collision, or `B₂` a CT-UF forgery. -/
theorem win_imp (g : Table) (E : CTable)
    (hwin : Win (evalWithAnswerFn (QueryImpl.ofFn (join g E)) (game lr pk sk qI A))) :
    (∃ j ∈ Finset.range qI, BadI E lr (evalWithAnswerFn (QueryImpl.ofFn g)
        (gameA CrtGen.tables (stI lr) (PI lr pk sk qI A j) E))) ∨
    (∃ j ∈ Finset.range qR, BadR E lr pk (evalWithAnswerFn (QueryImpl.ofFn g)
        (gameA CrtGen.tables (stR lr pk) (PR lr pk sk qI A j) E))) ∨
    Coll lr pk E (evalWithAnswerFn (QueryImpl.ofFn g) (extAll lr pk sk qI A E)) ∨
    Forge lr pk E (evalWithAnswerFn (QueryImpl.ofFn g) (extAll lr pk sk qI A E)) := by
  classical
  obtain ⟨hlI, -, hlR, -⟩ := game_eval g E lr pk sk A qI
  rw [extAll_eval]
  set o := evalWithAnswerFn (QueryImpl.ofFn (join g E)) (game lr pk sk qI A) with ho
  set oi := (List.range qI).map (fun j =>
    evalWithAnswerFn (QueryImpl.ofFn g) (gameA CrtGen.tables (stI lr) (PI lr pk sk qI A j) E))
    with hoi
  set orr := (List.range qR).map (fun j =>
    evalWithAnswerFn (QueryImpl.ofFn g) (gameA CrtGen.tables (stR lr pk) (PR lr pk sk qI A j) E))
    with horr
  by_contra hno
  simp only [BadI, BadR, not_or, not_exists, not_and, Finset.mem_range, not_not] at hno
  obtain ⟨hI, hR, hC, hF⟩ := hno
  obtain ⟨c, hc⟩ := hwin
  have key := Moussaka.collision_or_forgery comO (fun x => x.2.1) (fun x => (x.2.2.1, x.1))
    (SI lr E (o, oi, orr) ∪ SR lr pk E (o, oi, orr)) (SR lr pk E (o, oi, orr)) Set.subset_union_right
    (issL o) (redL o) ?_ ?_ c hc
  · rcases key with ⟨x, hx, x', hx', hne, he⟩ | ⟨x, hx, hn⟩
    · exact hC ⟨x, hx, x', hx', hne, he⟩
    · exact hF ⟨x, hx, hn⟩
  · intro q hq
    simp only [issL, List.mem_map, List.mem_filter] at hq
    obtain ⟨p, ⟨hp, hpb⟩, rfl⟩ := hq
    obtain ⟨j, hj⟩ := List.mem_iff_getElem?.1 hp
    have hjl : j < qI := by rw [← hlI]; exact (List.getElem?_eq_some_iff.1 hj).1
    have hj' : o.1[j]? = some (p.1, true) := by rw [hj]; cases p; simp_all
    obtain ⟨hacc, hst⟩ := accepted_I g E lr pk sk qI A hj'
    obtain ⟨x, hx, hxc, hxt⟩ := opI_of_ext E lr (hI j hjl hacc)
    refine ⟨x, Or.inl ⟨j, p.1, _, hj', by simp [oi, hjl], hx⟩, ?_, ?_⟩
    · rw [hxc, hst]
    · rw [hxt, hst]
  · intro q hq
    simp only [redL, List.mem_map, List.mem_filter] at hq
    obtain ⟨p, ⟨hp, hpb⟩, rfl⟩ := hq
    obtain ⟨j, hj⟩ := List.mem_iff_getElem?.1 hp
    have hjl : j < qR := by rw [← hlR]; exact (List.getElem?_eq_some_iff.1 hj).1
    have hj' : o.2[j]? = some (p.1, true) := by rw [hj]; cases p; simp_all
    obtain ⟨hacc, hst⟩ := accepted_R g E lr pk sk qI A hj'
    obtain ⟨x, hx, hxc, hxr⟩ := opR_of_ext E lr pk (hR j hjl hacc)
    refine ⟨x, ⟨j, p.1, _, hj', by simp [orr, hjl], hx⟩, ?_, ?_⟩
    · rw [hxc, hst]
    · rw [hxr, hst]

end Red

/-! ## Theorem 1 -/

/-- **Theorem 1 (one-more unforgeability), the reduction.** For every OMUF adversary, honest
Anchors with any public keys and signers, and either proof layout (`lr`): the probability that the
adversary wins is at most the extraction failures of the `qI` issuance and `qR` redemption provers
(each a prover of the soundness theorems), plus `B₁`'s binding advantage and `B₂`'s CT-UF
advantage. -/
theorem omuf_le (lr : Bool) (pk : Fin K → UovPk) (sk : Fin K → Spec.Signer) (qI : ℕ)
    (A : Adversary K qR) :
    Pr{let E ← $ᵗ CTable; let r ← (simulateQ randomOracle (runE E (game lr pk sk qI A))).run' ∅}[
        Win r.1] ≤
      ∑ j ∈ Finset.range qI, Pr{let E ← $ᵗ CTable; let r ← (simulateQ randomOracle
        (gameA CrtGen.tables (stI lr) (PI lr pk sk qI A j) E)).run' ∅}[BadI E lr r] +
      ∑ j ∈ Finset.range qR, Pr{let E ← $ᵗ CTable; let r ← (simulateQ randomOracle
        (gameA CrtGen.tables (stR lr pk) (PR lr pk sk qI A j) E)).run' ∅}[BadR E lr pk r] +
      Pr{let E ← $ᵗ CTable; let v ← (simulateQ randomOracle (extAll lr pk sk qI A E)).run' ∅}[
        Coll lr pk E v] +
      Pr{let E ← $ᵗ CTable; let v ← (simulateQ randomOracle (extAll lr pk sk qI A E)).run' ∅}[
        Forge lr pk E v] := by
  refine prEvent_le_sum4_of_tables (fun E => runE E (game lr pk sk qI A)) (fun _ r => Win r.1)
    (Finset.range qI) (Finset.range qR) _ _ _ _ _ _ _ fun g E hw => ?_
  rw [evalWithAnswerFn_runE] at hw
  exact win_imp lr pk sk qI A g E hw

end VoleMole.ROM.IC.OMUF
