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
* a CT-UF^open forgery on the honest Anchors' keys (`Adv^ct-uf(B₂)`, an assumption; as a standalone
  CT-UF^open advantage in `Assumptions/UOVLinks.lean`, `omuf_le_num_open`).

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

-- (`pfLenI_eq`, `pfLenR_eq` below: these are the executable verifier's proof sizes.)

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

/-- **`B₂` wins the CT-UF^open game**: an extracted redemption opening `x`, with an honest Anchor `k` and
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
  simp only [extAll, evalWithAnswerFn_bind, evalWithAnswerFn_runE, evalWithAnswerFn_mapM,
    evalWithAnswerFn_pure]

/-- **The per-table core of Theorem 1**: a win means that some accepted proof is not extracted, or
`B₁` finds a `Com` collision, or `B₂` a CT-UF^open forgery. -/
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
(each a prover of the soundness theorems), plus `B₁`'s binding advantage and `B₂`'s CT-UF^open
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
  refine prEvent_bind_le_sum4_of_table ($ᵗ CTable) (fun E => runE E (game lr pk sk qI A))
    (fun _ r => Win r.1) (Finset.range qI) (Finset.range qR) _ _ _ _ _ _ _ fun E g hw => ?_
  rw [evalWithAnswerFn_runE] at hw
  exact win_imp lr pk sk qI A g E hw

/-! ## Query bounds of the provers -/

/-- **The adversary's budget**: each of its stages makes at most `q k` hash queries of each kind,
`qE` cipher queries and `n` hash queries in all. -/
structure Adversary.Budget (A : Adversary K qR) (q : Kind → ℕ) (qE n : ℕ) : Prop where
  init_k : IsKindQueryBoundIC A.init q
  init_e : IsQueryBoundP A.init (fun t => t.isRight = true) qE
  init_h : IsQueryBoundP A.init (fun t => t.isLeft = true) n
  query_k : ∀ s, IsKindQueryBoundIC (A.query s) q
  query_e : ∀ s, IsQueryBoundP (A.query s) (fun t => t.isRight = true) qE
  query_h : ∀ s, IsQueryBoundP (A.query s) (fun t => t.isLeft = true) n
  final_k : ∀ s, IsKindQueryBoundIC (A.final s) q
  final_e : ∀ s, IsQueryBoundP (A.final s) (fun t => t.isRight = true) qE
  final_h : ∀ s, IsQueryBoundP (A.final s) (fun t => t.isLeft = true) n

/-- One verification's hash queries per kind. -/
def vK : Kind → ℕ := extractorQueries + verifierQueries

/-- The issuance proof parameters. -/
def parI (lr : Bool) : Params := { witnessBytes := 256, qsDegree := 9, labelRows := lr }

/-- The redemption proof parameters. -/
def parR (lr : Bool) : Params := { witnessBytes := 343, qsDegree := 9, labelRows := lr }

/-- **The game's hash queries per kind**: the adversary's `qI + 2` stages and the `qI + qR` honest
verifications. -/
def gameK (q : Kind → ℕ) (qI qR : ℕ) : Kind → ℕ := (qI + 2) • q + (qI + qR) • vK

/-- **The game's cipher queries.** -/
def gameE (lr : Bool) (qE qI qR : ℕ) : ℕ :=
  (qI + 2) * qE + qI * verifyCellBound (parI lr) + qR * verifyCellBound (parR lr)

/-- **The game's hash queries in all.** -/
def gameH (n qI qR : ℕ) : ℕ := (qI + 2) * n + (qI + qR) * (2 + verifierTotal)

section Bounds

variable (lr : Bool) (pk : Fin K → UovPk) (sk : Fin K → Spec.Signer)

theorem anchorIC_k (q : IssQ K) : IsKindQueryBoundIC (anchorIC lr sk q) vK := by
  unfold anchorIC
  split_ifs
  · exact isKindQueryBoundIC_map _ (isKindQueryBoundIC_verifyIC _ _ _)
  · trivial

theorem anchorIC_e (q : IssQ K) :
    IsQueryBoundP (anchorIC lr sk q) (fun t => t.isRight = true) (verifyCellBound (parI lr)) := by
  unfold anchorIC
  split_ifs
  · exact (isQueryBoundP_map_iff _ _ _).2 (isQueryBoundP_right_verifyIC _ _ _)
  · trivial

theorem anchorIC_h (q : IssQ K) :
    IsQueryBoundP (anchorIC lr sk q) (fun t => t.isLeft = true) (2 + verifierTotal) := by
  unfold anchorIC
  split_ifs
  · exact (isQueryBoundP_map_iff _ _ _).2 (isQueryBoundP_left_verifyIC _ _ _)
  · trivial

theorem moderatorIC_k (r : RedQ K) : IsKindQueryBoundIC (moderatorIC lr pk r) vK := by
  unfold moderatorIC
  split_ifs
  · exact isKindQueryBoundIC_map _ (isKindQueryBoundIC_verifyIC _ _ _)
  · trivial

theorem moderatorIC_e (r : RedQ K) :
    IsQueryBoundP (moderatorIC lr pk r) (fun t => t.isRight = true) (verifyCellBound (parR lr)) := by
  unfold moderatorIC
  split_ifs
  · exact (isQueryBoundP_map_iff _ _ _).2 (isQueryBoundP_right_verifyIC _ _ _)
  · trivial

theorem moderatorIC_h (r : RedQ K) :
    IsQueryBoundP (moderatorIC lr pk r) (fun t => t.isLeft = true) (2 + verifierTotal) := by
  unfold moderatorIC
  split_ifs
  · exact (isQueryBoundP_map_iff _ _ _).2 (isQueryBoundP_left_verifyIC _ _ _)
  · trivial

variable {A : Adversary K qR} {q : Kind → ℕ} {qE n : ℕ} (hA : A.Budget q qE n)
include hA

theorem runIss_k (m : ℕ) (s : A.σ) : IsKindQueryBoundIC (runIss lr sk A m s) (m • (q + vK)) := by
  induction m generalizing s with
  | zero => trivial
  | succ m ih =>
    refine (isKindQueryBoundIC_bind (hA.query_k s) fun sq =>
      isKindQueryBoundIC_bind (anchorIC_k lr sk sq.2) fun ra =>
        isKindQueryBoundIC_bind (q₂ := 0) (ob := fun rest => (pure (rest.1, (sq.2, ra.2) :: rest.2) :
          OracleComp specIC (A.σ × List (IssQ K × Bool)))) (ih _) fun _ => trivial).mono (le_of_eq ?_)
    rw [succ_nsmul]; abel

theorem runIss_e (m : ℕ) (s : A.σ) : IsQueryBoundP (runIss lr sk A m s)
    (fun t => t.isRight = true) (m * (qE + verifyCellBound (parI lr))) := by
  induction m generalizing s with
  | zero => trivial
  | succ m ih =>
    refine (isQueryBoundP_bind (hA.query_e s) fun sq _ =>
      isQueryBoundP_bind (anchorIC_e lr sk sq.2) fun ra _ =>
        isQueryBoundP_bind (m := 0) (ob := fun rest => (pure (rest.1, (sq.2, ra.2) :: rest.2) :
          OracleComp specIC (A.σ × List (IssQ K × Bool)))) (ih _) fun _ _ => trivial).mono
            (le_of_eq ?_)
    ring

theorem runIss_h (m : ℕ) (s : A.σ) : IsQueryBoundP (runIss lr sk A m s)
    (fun t => t.isLeft = true) (m * (n + (2 + verifierTotal))) := by
  induction m generalizing s with
  | zero => trivial
  | succ m ih =>
    refine (isQueryBoundP_bind (hA.query_h s) fun sq _ =>
      isQueryBoundP_bind (anchorIC_h lr sk sq.2) fun ra _ =>
        isQueryBoundP_bind (m := 0) (ob := fun rest => (pure (rest.1, (sq.2, ra.2) :: rest.2) :
          OracleComp specIC (A.σ × List (IssQ K × Bool)))) (ih _) fun _ _ => trivial).mono
            (le_of_eq ?_)
    ring

omit hA in
theorem runRed_k (R : Fin qR → RedQ K) : IsKindQueryBoundIC (runRed lr pk R) (qR • vK) := by
  unfold runRed
  simpa using isKindQueryBoundIC_mapM (List.finRange qR) _ fun j =>
    isKindQueryBoundIC_map _ (moderatorIC_k lr pk (R j))

omit hA in
theorem runRed_e (R : Fin qR → RedQ K) :
    IsQueryBoundP (runRed lr pk R) (fun t => t.isRight = true) (qR * verifyCellBound (parR lr)) := by
  unfold runRed
  simpa using isQueryBoundP_mapM _ (List.finRange qR) _ fun j =>
    (isQueryBoundP_map_iff _ _ _).2 (moderatorIC_e lr pk (R j))

omit hA in
theorem runRed_h (R : Fin qR → RedQ K) :
    IsQueryBoundP (runRed lr pk R) (fun t => t.isLeft = true) (qR * (2 + verifierTotal)) := by
  unfold runRed
  simpa using isQueryBoundP_mapM _ (List.finRange qR) _ fun j =>
    (isQueryBoundP_map_iff _ _ _).2 (moderatorIC_h lr pk (R j))

theorem game_k (qI : ℕ) : IsKindQueryBoundIC (game lr pk sk qI A) (gameK q qI qR) := by
  unfold game
  refine (isKindQueryBoundIC_bind hA.init_k fun s =>
    isKindQueryBoundIC_bind (runIss_k lr sk hA qI s) fun r =>
      isKindQueryBoundIC_bind (hA.final_k r.1) fun R =>
        isKindQueryBoundIC_map _ (runRed_k lr pk R)).mono (le_of_eq ?_)
  simp only [gameK, smul_add, add_smul]
  abel

theorem game_e (qI : ℕ) :
    IsQueryBoundP (game lr pk sk qI A) (fun t => t.isRight = true) (gameE lr qE qI qR) := by
  unfold game
  refine (isQueryBoundP_bind hA.init_e fun s _ =>
    isQueryBoundP_bind (runIss_e lr sk hA qI s) fun r _ =>
      isQueryBoundP_bind (hA.final_e r.1) fun R _ =>
        (isQueryBoundP_map_iff _ _ _).2 (runRed_e lr pk R)).mono (le_of_eq ?_)
  simp only [gameE]; ring

theorem game_h (qI : ℕ) :
    IsQueryBoundP (game lr pk sk qI A) (fun t => t.isLeft = true) (gameH n qI qR) := by
  unfold game
  refine (isQueryBoundP_bind hA.init_h fun s _ =>
    isQueryBoundP_bind (runIss_h lr sk hA qI s) fun r _ =>
      isQueryBoundP_bind (hA.final_h r.1) fun R _ =>
        (isQueryBoundP_map_iff _ _ _).2 (runRed_h lr pk R)).mono (le_of_eq ?_)
  simp only [gameH]; ring

end Bounds

/-! ## Theorem 1 with the extraction terms of the soundness theorems -/

/-- **The extraction failure of one issuance proof** (`moussakaIssue_accept_le_adaptive_spec`), for
a prover with `q k` hash queries of kind `k` and `qE` cipher queries. -/
noncomputable def epsI (q : Kind → ℕ) (qE : ℕ) : ℝ≥0∞ :=
  (q .h21 + 1) * (2 ^ 150 : ℝ≥0∞)⁻¹ +
    (q .h22 + 1) * ENNReal.ofReal (Seed.epsQS (2 ^ 128) (2 ^ 64) 4008) +
    (q .h23 + 1) * ((9 : ℝ≥0∞) / 2 ^ 128) +
    (2 * qE ^ 2 * (2 ^ 256)⁻¹ + (openHashEps q + q .h1 * (2 ^ 256 : ℝ≥0∞)⁻¹)) +
    (openHashEps q + q .h1 * (2 ^ 256 : ℝ≥0∞)⁻¹) +
    ((qE * 2 : ℕ) : ℝ≥0∞) * (((512 * q .h1 : ℕ) : ℝ≥0∞) * (2 ^ 256 : ℝ≥0∞)⁻¹) +
    chainHitEps q + stmtBindEps q

/-- **The extraction failure of one redemption proof** (`moussakaRedeem_accept_le_adaptive_spec`),
`n` the prover's hash queries in all. -/
noncomputable def epsR (q : Kind → ℕ) (qE n : ℕ) : ℝ≥0∞ :=
  (q .h21 + 1) * (2 ^ 150 : ℝ≥0∞)⁻¹ +
    (q .h22 + 1) * (ENNReal.ofReal (Seed.epsQS (2 ^ 128) (2 ^ 64) 4409) +
      (2 ^ 128 : ℝ≥0∞)⁻¹ + ((n + 2 + verifierTotal : ℕ) : ℝ≥0∞) / 2 ^ 448) +
    (q .h23 + 1) * ((9 : ℝ≥0∞) / 2 ^ 128) +
    (2 * qE ^ 2 * (2 ^ 256)⁻¹ + (openHashEps q + q .h1 * (2 ^ 256 : ℝ≥0∞)⁻¹)) +
    (openHashEps q + q .h1 * (2 ^ 256 : ℝ≥0∞)⁻¹) +
    ((qE * 2 : ℕ) : ℝ≥0∞) * (((512 * q .h1 : ℕ) : ℝ≥0∞) * (2 ^ 256 : ℝ≥0∞)⁻¹) +
    chainHitEpsComb q Arith.Moussaka.M + stmtBindEps q

section Num

variable (lr : Bool) (pk : Fin K → UovPk) (sk : Fin K → Spec.Signer) (qI : ℕ) {A : Adversary K qR}
  {q : Kind → ℕ} {qE n : ℕ}

theorem hinjI : Function.Injective fun s : ιI =>
    (moussakaIssue s.1.1 s.1.2 lr).instEnc ByteArray.empty :=
  EndToEnd.SpecRel.hinj_moussakaIssue_of (fun s : ιI => s.1) lr 45 (fun s => s.2.1)
    Subtype.val_injective

theorem hinjR (hdig : ∀ k, (pk k).digest.size = 32)
    (hdinj : Function.Injective fun k => (pk k).digest) :
    Function.Injective fun s : ιR K =>
      (moussakaRedeem (ancR pk s) s.1.2.1 s.1.2.2.1 s.1.2.2.2.1 s.1.2.2.2.2 lr).instEnc
        ByteArray.empty := by
  refine EndToEnd.SpecRel.hinj_moussakaRedeem (fun s : ιR K => ancR pk s) (fun s => s.1.2.1)
    (fun s => s.1.2.2.1) (fun s => s.1.2.2.2.1) (fun s => s.1.2.2.2.2) lr ?_ ?_ 24 16 16
    (fun s => s.2.2.1) (fun s => s.2.2.2.1) (fun s => s.2.2.2.2) ?_
  · intro s p hp
    obtain ⟨k, -, rfl⟩ := List.mem_map.1 hp
    exact hdig k
  · intro s; simp only [ancR, List.length_map]; have := s.2.1; omega
  · intro s s' h
    simp only [ancR, List.map_map, Prod.mk.injEq] at h
    obtain ⟨h1, h2, h3, h4, h5⟩ := h
    have hl : s.1.1 = s'.1.1 := (List.map_injective_iff.2 hdinj) h1
    exact Subtype.ext (Prod.ext hl (Prod.ext h2 (Prod.ext h3 (Prod.ext h4 h5))))

/-- **Theorem 1 (one-more unforgeability per issuance context), with the extraction terms of the
soundness theorems.** For an adversary within its budget (`A.Budget q qE n`, per stage) and honest
Anchors whose 32-byte key digests are distinct (`hdig`, `hdinj`: the note's `ε_dig` event, here a
condition on the keys):

    Pr[Win] ≤ qI·εI(q', q'_E) + qR·εR(q', q'_E, n') + AdvBind(B₁) + AdvCTUF(B₂),

with the provers' budgets `q' = gameK q qI qR` (the adversary's `qI + 2` stages and the `qI + qR`
honest verifications, `extractorQueries + verifierQueries` each), `q'_E = gameE lr qE qI qR`,
`n' = gameH n qI qR`. `εI`, `εR` are the bounds of `moussakaIssue_accept_le_adaptive_spec` and
`moussakaRedeem_accept_le_adaptive_spec`. -/
theorem omuf_le_num (hA : A.Budget q qE n) (hdig : ∀ k, (pk k).digest.size = 32)
    (hdinj : Function.Injective fun k => (pk k).digest) :
    Pr{let E ← $ᵗ CTable; let r ← (simulateQ randomOracle (runE E (game lr pk sk qI A))).run' ∅}[
        Win r.1] ≤
      qI * epsI (gameK q qI qR) (gameE lr qE qI qR) +
      qR * epsR (gameK q qI qR) (gameE lr qE qI qR) (gameH n qI qR) +
      Pr{let E ← $ᵗ CTable; let v ← (simulateQ randomOracle (extAll lr pk sk qI A E)).run' ∅}[
        Coll lr pk E v] +
      Pr{let E ← $ᵗ CTable; let v ← (simulateQ randomOracle (extAll lr pk sk qI A E)).run' ∅}[
        Forge lr pk E v] := by
  refine (omuf_le lr pk sk qI A).trans (add_le_add (add_le_add (add_le_add ?_ ?_) le_rfl) le_rfl)
  · refine (Finset.sum_le_card_nsmul _ _ (epsI (gameK q qI qR) (gameE lr qE qI qR))
      fun j _ => ?_).trans (by simp)
    exact moussakaIssue_accept_le_adaptive_spec (ι := ιI) (β := GOut K) (fun s => s.1)
      (fun s => s.2.1) (fun s => s.2.2) lr (hinjI lr) (PI lr pk sk qI A j) _
      ((isQueryBoundP_map_iff _ _ _).2 (game_e lr pk sk hA qI)) _
      (isKindQueryBoundIC_map _ (game_k lr pk sk hA qI))
  · refine (Finset.sum_le_card_nsmul _ _
      (epsR (gameK q qI qR) (gameE lr qE qI qR) (gameH n qI qR)) fun j _ => ?_).trans (by simp)
    exact moussakaRedeem_accept_le_adaptive_spec (ι := ιR K) (β := GOut K) (fun s => ancR pk s)
      (fun s => by simpa using s.2.1) (fun s => s.1.2.1) (fun s => s.1.2.2.1)
      (fun s => s.1.2.2.2.1) (fun s => s.1.2.2.2.2) (fun s => s.2.2.1) (fun s => s.2.2.2.1)
      (fun s => s.2.2.2.2) lr (hinjR lr pk hdig hdinj) (PR lr pk sk qI A j) _
      ((isQueryBoundP_map_iff _ _ _).2 (game_e lr pk sk hA qI)) _
      ((isQueryBoundP_map_iff _ _ _).2 (game_h lr pk sk hA qI)) _
      (isKindQueryBoundIC_map _ (game_k lr pk sk hA qI))

end Num

/-! ## Liveness: the honest checks' lengths are the verifier's proof sizes -/

/-- The issuance request length the Anchor expects is `45` plus the executable verifier's issuance
proof size, on `main` and with label rows (so honest requests are not refused as malformed; the
privacy games had this hazard, `Audit/Liveness.lean`). -/
theorem pfLenI_eq (lr : Bool) : pfLenI lr = (parI lr).proofBytes := by
  cases lr <;> decide

/-- The same for the Moderator's redemption request length. -/
theorem pfLenR_eq (lr : Bool) : pfLenR lr = (parR lr).proofBytes := by
  cases lr <;> decide

/-- The Anchor's statement has the issuance parameters. -/
theorem stmt_params (lr : Bool) (q : IssQ K) : (q.stmt lr).params = parI lr := rfl

/-- The Moderator's statement has the redemption parameters. -/
theorem stmtR_params (lr : Bool) (pk : Fin K → UovPk) (r : RedQ K) :
    (r.stmt lr pk).params = parR lr := rfl

end VoleMole.ROM.IC.OMUF
