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

end VoleMole.ROM.IC.OMUF
