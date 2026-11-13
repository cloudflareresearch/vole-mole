import VoleMole.ROM.MoussakaOMUF
import VoleMole.ROM.MoussakaUnboundSpec
import VoleMole.Protocols.MoussakaUnbound
import VoleMole.Privacy.MoussakaUnboundNC

/-!
# Unbound Moussaka: unforgeability per redemption context (Theorem U1) in the random-oracle and
ideal-cipher model

`lean/docs/security/moussaka-unbound.md` §4. The game OMUF-U of the note on the executable spec,
with the Lean verifier as the honest Anchors' and the Moderator's check, and a reduction of a
winning adversary to

* the extraction failure of one of its accepted proofs, of three relation families: bound
  issuance (`ε_ext^{iss}`, `moussakaIssue_accept_le_adaptive_spec`), unbound issuance
  (`ε_ext^{u-iss}`, `moussakaUnboundIssue_accept_le_adaptive_spec`) and unbound redemption
  (`ε_ext^{u-red}`, `moussakaUnboundRedeem_accept_le_adaptive_spec`);
* a collision among the extracted inputs of `Com ∪ UCom` (`Adv^bind_{Com∪UCom}(B₁)`, an
  assumption);
* a CT-UF^open forgery on the honest Anchors' keys over the union domain (`Adv^ct-uf-open(B₂)`,
  an assumption; as a standalone CT-UF^open advantage in `Assumptions/UnboundLinks.lean`).

## The game

It is `ROM/MoussakaOMUF.lean`'s game with a second issuance oracle and the unbound Moderator.

* The `K` honest Anchors have public keys `pk` and signers `sk` (nothing is assumed of them). Each
  Anchor runs **both** variants with one key (§7 of the note): an Issue query (`IQ`) is either a
  bound one (`inl`, the bound Anchor `OMUF.anchorIC`, `issue_response`) or an unbound one (`inr`,
  `uanchorIC`, `unbound_issue_response`: request `t ‖ π_iss` of `45 + 6864` bytes on `main`, the
  unbound issuance proof verified for `(t, ctx_iss)`, then `derive_preimage(sk_k, t)`; per table
  it is `Privacy.MoussakaUnbound.issueResponse` with the executable verifier,
  `uanchorIC_eq_spec`). An accepted proof of either variant puts `t` into the signed set.
* The adversary makes `qI` Issue queries one after the other (each seeing the earlier answers),
  then outputs `qR` unbound redemptions with Anchor Sets of honest Anchors. The Moderator
  (`umoderatorIC`) is `unbound_finalize_redeem` with the Lean verifier (`moussakaUnboundRedeem`),
  for a valid Anchor Set (non-empty, at most 64 distinct honest Anchors) and contexts of 16 bytes.
  A redemption oracle is not needed: its answer is public.
* **Win** (`Win`): for some `(ctx_iss, ctx_red)`, the distinct accepted nullifiers outnumber the
  distinct `t` accepted through **unbound** issuance for `ctx_iss`; the Moderator's record is
  global across all Anchor Sets. Bound issuances do not count (the note's remark "bound tokens
  are not counted").

The adversary is deterministic given the oracles; every term averages over its coins.

## The reduction

`omufU_le`: for every adversary,

    Pr[Win] ≤ Σ_{j<qI} Pr[BadBI_j] + Σ_{j<qI} Pr[BadUI_j] + Σ_{j<qR} Pr[BadUR_j]
              + AdvBind(B₁) + AdvCTUF(B₂),

where `BadBI_j` (`BadUI_j`) is the extraction failure of the `j`-th Issue query's proof if that
query is bound (unbound), and `BadUR_j` that of the `j`-th redemption proof. Each position `j < qI`
is charged in both issuance families, since the adversary chooses the variant adaptively; the
prover of the other variant outputs a fixed dummy statement. `B₁`, `B₂` (`extAll`) run the game
and the straight-line extractor on every proof. `AdvBind` is the probability that two distinct
extracted inputs of `Com ∪ UCom` (`XOp = Opening ⊕ UOpening`: the input spaces are disjoint, byte
4 of the Keccak state, `Arith.MoussakaUnbound.encodeUnboundComState_ne_encodeComState`) have one
commitment. `AdvCTUF` is the probability that some accepted redemption's extracted `UCom` input,
with an honest key of its Anchor Set and a preimage under it, commits to a target that no Anchor's
signer was called on, through either variant. Per table, a win with every accepted proof
extracted gives one of the two (`Protocols/MoussakaUnbound.lean`,
`collision_or_forgery_unbound`).

`omufU_le_num`: the extraction terms bounded by the soundness theorems at the game's budget.
-/

open Finset OracleComp OracleSpec
open scoped ENNReal

namespace VoleMole.ROM.IC.OMUFU

open VoleMole.Prob VoleMole.Verifier VoleMole.Verifier.Bridge VoleMole.ZK.Sim VoleMole.ROM
  VoleMole.ROM.IC VoleMole.ROM.IC.OMUF

-- `Com`, `UCom` and `Derive` evaluate Keccak-p[800]; nothing below needs to unfold them.
attribute [local irreducible] Spec.Moussaka.com Spec.MoussakaUnbound.ucom
  Spec.MoussakaUnbound.derive

/-! ## Messages and the adversary -/

/-- The unbound issuance proof's length (`6864` on `main`, `7120` with label rows;
`UNBOUND_ISSUE_PROOF_BYTES`). -/
def upfLenI (lr : Bool) : ℕ := if lr then 7120 else 6864

/-- The unbound redemption proof's length (`12423` on `main`, `12679` with label rows;
`UNBOUND_REDEEM_PROOF_BYTES`). -/
def upfLenR (lr : Bool) : ℕ := if lr then 12679 else 12423

variable {K : ℕ}

/-- **An Issue query of either variant**: `inl` a bound one (`issue_response`), `inr` an unbound
one (`unbound_issue_response`), each with the Anchor, the request `t ‖ π_iss` and `ctx_iss`. -/
abbrev IQ (K : ℕ) := IssQ K ⊕ IssQ K

/-- The query of either variant. -/
def IQ.q : IQ K → IssQ K := Sum.elim id id

/-- An unbound request is well-formed (`45 + UNBOUND_ISSUE_PROOF_BYTES` bytes, `ctx_iss` of 16). -/
def uWFI (lr : Bool) (q : IssQ K) : Prop := q.req.size = 45 + upfLenI lr ∧ q.ctx.size = 16

instance (lr : Bool) (q : IssQ K) : Decidable (uWFI lr q) := by unfold uWFI; infer_instance

/-- The unbound issuance statement of a query. -/
def ustmtI (lr : Bool) (q : IssQ K) : Statement := moussakaUnboundIssue q.t q.ctx lr

/-- **The honest Anchor's unbound issuance** (`unbound_issue_response`, `src/ihat/ihat.cpp:369-380`):
the length checks, the Lean verifier on the oracles for the unbound issuance relation, then
`derive_preimage`. The second output is whether the proof was accepted (then `t` is signed). -/
def uanchorIC (lr : Bool) (sk : Fin K → Spec.Signer) (q : IssQ K) :
    OracleComp specIC (IssResp × Bool) :=
  if uWFI lr q then
    (fun tr : Transcript => if tr.accept then
        ((match (sk q.k).derivePreimage (toL q.t) with
          | some s => .ok (some s)
          | none => .error .deriveFailed), true)
      else (.ok none, false)) <$> verifyIC CrtGen.tables (ustmtI lr q) q.pf
  else pure (.error .malformed, false)

/-- **The honest Anchor, both variants with one key.** -/
def anchorU (lr : Bool) (sk : Fin K → Spec.Signer) : IQ K → OracleComp specIC (IssResp × Bool)
  | .inl q => anchorIC lr sk q
  | .inr q => uanchorIC lr sk q

/-- A valid unbound redemption query: a valid Anchor Set of honest Anchors, a request
`nf ‖ π_red` of `24 + UNBOUND_REDEEM_PROOF_BYTES` bytes, contexts of 16 bytes. -/
def uWFR (lr : Bool) (r : RedQ K) : Prop :=
  r.S ≠ [] ∧ r.S.length ≤ 64 ∧ r.S.Nodup ∧ r.req.size = 24 + upfLenR lr ∧ r.ci.size = 16 ∧
    r.cr.size = 16

instance (lr : Bool) (r : RedQ K) : Decidable (uWFR lr r) := by unfold uWFR; infer_instance

/-- The unbound redemption statement of a query. -/
def ustmtR (lr : Bool) (pk : Fin K → UovPk) (r : RedQ K) : Statement :=
  moussakaUnboundRedeem (r.S.map pk) r.nf r.ci r.cr r.cd lr

/-- **The Moderator** (`unbound_finalize_redeem`) with the Lean verifier on the oracles. -/
def umoderatorIC (lr : Bool) (pk : Fin K → UovPk) (r : RedQ K) : OracleComp specIC Bool :=
  if uWFR lr r then
    (fun tr : Transcript => tr.accept) <$> verifyIC CrtGen.tables (ustmtR lr pk r) r.pf
  else pure false

/-- **An OMUF-U adversary** with `qR` unbound redemptions: an interactive oracle computation over
the hashes and the cipher, whose Issue queries are of either variant. -/
structure Adversary (K qR : ℕ) where
  σ : Type
  init : OracleComp specIC σ
  query : σ → OracleComp specIC (σ × IQ K)
  absorb : σ → IssResp → σ
  final : σ → OracleComp specIC (Fin qR → RedQ K)

/-! ## The game -/

variable {qR : ℕ}

/-- The game's output: the Issue queries with their acceptance, the redemptions with theirs. -/
abbrev GOut (K : ℕ) := List (IQ K × Bool) × List (RedQ K × Bool)

/-- `n` Issue rounds from the state `s`. -/
def runIss (lr : Bool) (sk : Fin K → Spec.Signer) (A : Adversary K qR) :
    ℕ → A.σ → OracleComp specIC (A.σ × List (IQ K × Bool))
  | 0, s => pure (s, [])
  | n + 1, s => A.query s >>= fun sq => anchorU lr sk sq.2 >>= fun ra =>
      runIss lr sk A n (A.absorb sq.1 ra.1) >>= fun rest => pure (rest.1, (sq.2, ra.2) :: rest.2)

/-- The redemptions, verified by the Moderator. -/
def runRed (lr : Bool) (pk : Fin K → UovPk) (R : Fin qR → RedQ K) :
    OracleComp specIC (List (RedQ K × Bool)) :=
  (List.finRange qR).mapM fun j => (fun b => (R j, b)) <$> umoderatorIC lr pk (R j)

/-- **The OMUF-U game** with `qI` Issue queries. -/
def game (lr : Bool) (pk : Fin K → UovPk) (sk : Fin K → Spec.Signer) (qI : ℕ)
    (A : Adversary K qR) : OracleComp specIC (GOut K) :=
  A.init >>= fun s => runIss lr sk A qI s >>= fun r => A.final r.1 >>= fun R =>
    (fun red => (r.2, red)) <$> runRed lr pk R

/-- The accepted **unbound** Issue queries, as `(t, ctx_iss)` (the note's `L^u`). -/
def uissL (o : GOut K) : List (Spec.Bytes × Spec.Bytes) :=
  (o.1.filter fun p => p.2 && p.1.isRight).map fun p => (toL p.1.q.t, toL p.1.q.ctx)

/-- The accepted **bound** Issue queries' `t` (the note's `L^b`, any context). -/
def bissL (o : GOut K) : List Spec.Bytes :=
  (o.1.filter fun p => p.2 && p.1.isLeft).map fun p => toL p.1.q.t

/-- The signed targets: every accepted Issue query's `t`, of either variant. -/
def sigT (o : GOut K) : List Spec.Bytes := (o.1.filter (·.2)).map fun p => toL p.1.q.t

/-- The accepted redemptions, as `((ctx_iss, ctx_red), nf)` (the Moderator's record `R`). -/
def uredL (o : GOut K) : List ((Spec.Bytes × Spec.Bytes) × Spec.Bytes) :=
  (o.2.filter (·.2)).map fun p => ((toL p.1.ci, toL p.1.cr), toL p.1.nf)

/-- **The adversary wins**: for some `(ctx_iss, ctx_red)`, more distinct accepted nullifiers than
distinct `t` accepted through unbound issuance for `ctx_iss`. -/
def Win (o : GOut K) : Prop :=
  ∃ c cr, (((uissL o).filter (·.2 = c)).map (·.1)).toFinset.card <
    (((uredL o).filter (·.1 = (c, cr))).map (·.2)).toFinset.card

theorem mem_sigT {o : GOut K} {t : Spec.Bytes} (h : t ∈ sigT o) :
    t ∈ (uissL o).map (·.1) ∨ t ∈ bissL o := by
  obtain ⟨p, hp, rfl⟩ := List.mem_map.1 h
  obtain ⟨hp, hb⟩ := List.mem_filter.1 hp
  rcases p with ⟨q | q, b⟩
  · refine Or.inr (List.mem_map.2 ⟨_, List.mem_filter.2 ⟨hp, by simpa using hb⟩, rfl⟩)
  · refine Or.inl (List.mem_map.2 ⟨(toL q.t, toL q.ctx), List.mem_map.2
      ⟨_, List.mem_filter.2 ⟨hp, by simpa using hb⟩, rfl⟩, rfl⟩)

/-! ## Per table: the honest checks are the executable verifier -/

section PerTable

variable (g : Table) (E : CTable) (lr : Bool) (pk : Fin K → UovPk) (sk : Fin K → Spec.Signer)

/-- The executable verifier's verdict on an unbound Issue query, at the tables `g`, `E`. -/
def verUI (q : IssQ K) : Bool :=
  (@verify (icPrg E.cipher) (Hashes.ofTable g) CrtGen.tables (ustmtI lr q) q.pf).accept

/-- The executable verifier's verdict on an unbound redemption. -/
def verUR (r : RedQ K) : Bool :=
  (@verify (icPrg E.cipher) (Hashes.ofTable g) CrtGen.tables (ustmtR lr pk r) r.pf).accept

/-- **An accepted Issue query of either variant**: well-formed for its variant and verified by the
executable verifier for its relation. -/
def Acc : IQ K → Prop
  | .inl q => q.WF lr ∧ verI g E lr q = true
  | .inr q => uWFI lr q ∧ verUI g E lr q = true

theorem evalWithAnswerFn_uanchorIC (q : IssQ K) :
    (evalWithAnswerFn (QueryImpl.ofFn (join g E)) (uanchorIC lr sk q)).2 =
      (decide (uWFI lr q) && verUI g E lr q) := by
  unfold uanchorIC verUI
  split_ifs with h
  · rw [evalWithAnswerFn_map, evalWithAnswerFn_verifyIC]
    simp only [h, decide_true, Bool.true_and]
    split_ifs with ha <;> simp [ha]
  · simp [h]

/-- Per table, the NIZK whose verifier is the executable verifier for unbound issuance. -/
def nizkUI : Spec.Moussaka.NIZK Spec.MoussakaUnbound.IssueInstance :=
  ⟨fun _ _ _ => [], fun pf x =>
    (@verify (icPrg E.cipher) (Hashes.ofTable g) CrtGen.tables
      (moussakaUnboundIssue (toBA x.t) (toBA x.ctxIss) lr) (toBA pf)).accept⟩

set_option maxRecDepth 20000 in
/-- **Per table, the unbound Anchor on a well-formed request is `unbound_issue_response`**
(`Privacy.MoussakaUnbound.issueResponse`, which folds `std::nullopt` and a failed
`derive_preimage` into `none`) for the NIZK whose verifier is the executable verifier. -/
theorem uanchorIC_eq_spec (q : IssQ K) (hq : uWFI lr q) :
    (match (evalWithAnswerFn (QueryImpl.ofFn (join g E)) (uanchorIC lr sk q)).1 with
      | .ok (some s) => some s
      | _ => none) =
      Privacy.MoussakaUnbound.issueResponse (nizkUI g E lr) (sk q.k) (toL q.req) (toL q.ctx) := by
  have ht : (toL q.req).take 45 = toL q.t := (toL_extract0 _ _).symm
  have hp : (toL q.req).drop 45 = toL q.pf := (toL_extract_size _ _).symm
  unfold uanchorIC Privacy.MoussakaUnbound.issueResponse
  simp only [hq, ↓reduceIte]
  rw [evalWithAnswerFn_map, evalWithAnswerFn_verifyIC]
  simp only [Spec.uovM, ht, hp, nizkUI, toBA_toL', ustmtI]
  by_cases ha : (@verify (icPrg E.cipher) (Hashes.ofTable g) CrtGen.tables
    (moussakaUnboundIssue q.t q.ctx lr) q.pf).accept = true
  · simp only [ha, ite_true]
    cases (sk q.k).derivePreimage (toL q.t) <;> simp
  · simp only [ha, Bool.false_eq_true, ite_false]

theorem acc_of_anchorU (q : IQ K)
    (h : (evalWithAnswerFn (QueryImpl.ofFn (join g E)) (anchorU lr sk q)).2 = true) :
    Acc g E lr q := by
  rcases q with q | q
  · rw [anchorU, evalWithAnswerFn_anchorIC] at h
    simpa [Acc] using h
  · rw [anchorU, evalWithAnswerFn_uanchorIC] at h
    simpa [Acc] using h

theorem evalWithAnswerFn_umoderatorIC (r : RedQ K) :
    evalWithAnswerFn (QueryImpl.ofFn (join g E)) (umoderatorIC lr pk r) =
      (decide (uWFR lr r) && verUR g E lr pk r) := by
  unfold umoderatorIC verUR
  split_ifs with h
  · rw [evalWithAnswerFn_map, evalWithAnswerFn_verifyIC]; simp [h]
  · simp [h]

variable {qR : ℕ} (A : Adversary K qR)

theorem runIss_eval (n : ℕ) (s : A.σ) :
    (evalWithAnswerFn (QueryImpl.ofFn (join g E)) (runIss lr sk A n s)).2.length = n ∧
    ∀ p ∈ (evalWithAnswerFn (QueryImpl.ofFn (join g E)) (runIss lr sk A n s)).2,
      p.2 = true → Acc g E lr p.1 := by
  induction n generalizing s with
  | zero => simp [runIss]
  | succ n ih =>
    simp only [runIss, evalWithAnswerFn_bind, evalWithAnswerFn_pure, List.length_cons,
      List.mem_cons]
    refine ⟨by rw [(ih _).1], ?_⟩
    rintro p (rfl | hp) hb
    · exact acc_of_anchorU g E lr sk _ hb
    · exact (ih _).2 p hp hb

theorem runRed_eval (R : Fin qR → RedQ K) :
    evalWithAnswerFn (QueryImpl.ofFn (join g E)) (runRed lr pk R) =
      (List.finRange qR).map fun j => (R j, decide (uWFR lr (R j)) && verUR g E lr pk (R j)) := by
  unfold runRed
  rw [evalWithAnswerFn_mapM]
  simp only [evalWithAnswerFn_map, evalWithAnswerFn_umoderatorIC]

/-- **Per table, the game's records**: `qI` Issue records, every accepted one well-formed and
verified for its variant; `qR` redemptions, every accepted one valid and verified. -/
theorem game_eval (qI : ℕ) :
    let o := evalWithAnswerFn (QueryImpl.ofFn (join g E)) (game lr pk sk qI A)
    o.1.length = qI ∧ (∀ p ∈ o.1, p.2 = true → Acc g E lr p.1) ∧
    o.2.length = qR ∧ (∀ p ∈ o.2, p.2 = true → uWFR lr p.1 ∧ verUR g E lr pk p.1 = true) := by
  simp only [game, evalWithAnswerFn_bind, evalWithAnswerFn_map, runRed_eval]
  refine ⟨(runIss_eval g E lr sk A _ _).1, (runIss_eval g E lr sk A _ _).2, by simp, ?_⟩
  intro p hp hb
  obtain ⟨j, -, rfl⟩ := List.mem_map.1 hp
  simpa using hb

end PerTable

/-! ## The provers: the whole game, with one proof as output -/

/-- The unbound issuance statement family (`t` of 45 bytes, `ctx_iss` of 16). -/
abbrev stUI (lr : Bool) (s : ιI) : Statement := moussakaUnboundIssue s.1.1 s.1.2 lr

/-- The unbound redemption statement family (at most 64 Anchors, `nf` of 24 bytes, contexts of
16). -/
abbrev stUR (lr : Bool) (pk : Fin K → UovPk) (s : ιR K) : Statement :=
  moussakaUnboundRedeem (ancR pk s) s.1.2.1 s.1.2.2.1 s.1.2.2.2.1 s.1.2.2.2.2 lr

/-- The `j`-th Issue query's proof, with its statement, **if it is a bound query** (otherwise a
fixed dummy statement and the empty proof). -/
def projBI (j : ℕ) (o : GOut K) : ByteArray × (ιI × GOut K) :=
  match o.1[j]? with
  | some (.inl q, _) => if h : q.t.size = 45 ∧ q.ctx.size = 16 then (q.pf, (⟨(q.t, q.ctx), h⟩, o))
      else (ByteArray.empty, (dummyI, o))
  | _ => (ByteArray.empty, (dummyI, o))

/-- The `j`-th Issue query's proof, with its statement, **if it is an unbound query**. -/
def projUI (j : ℕ) (o : GOut K) : ByteArray × (ιI × GOut K) :=
  match o.1[j]? with
  | some (.inr q, _) => if h : q.t.size = 45 ∧ q.ctx.size = 16 then (q.pf, (⟨(q.t, q.ctx), h⟩, o))
      else (ByteArray.empty, (dummyI, o))
  | _ => (ByteArray.empty, (dummyI, o))

/-- The `j`-th redemption proof, with its statement. -/
def projUR (j : ℕ) (o : GOut K) : ByteArray × (ιR K × GOut K) :=
  match o.2[j]? with
  | some p => if h : p.1.S.length ≤ 64 ∧ p.1.nf.size = 24 ∧ p.1.ci.size = 16 ∧ p.1.cr.size = 16
      then (p.1.pf, (⟨(p.1.S, p.1.nf, p.1.ci, p.1.cr, p.1.cd), h⟩, o))
      else (ByteArray.empty, (dummyR, o))
  | none => (ByteArray.empty, (dummyR, o))

section Provers

variable (lr : Bool) (pk : Fin K → UovPk) (sk : Fin K → Spec.Signer) (qI : ℕ) (A : Adversary K qR)

/-- **The prover `P^iss_j`** (bound issuance): the whole OMUF-U game, with the `j`-th Issue
query's proof as output if that query is bound. -/
def PBI (j : ℕ) : OracleComp specIC (ByteArray × (ιI × GOut K)) := projBI j <$> game lr pk sk qI A

/-- **The prover `P^u-iss_j`** (unbound issuance). -/
def PUI (j : ℕ) : OracleComp specIC (ByteArray × (ιI × GOut K)) := projUI j <$> game lr pk sk qI A

/-- **The prover `P^u-red_j`** (unbound redemption). -/
def PUR (j : ℕ) : OracleComp specIC (ByteArray × (ιR K × GOut K)) :=
  projUR j <$> game lr pk sk qI A

end Provers

/-- The adaptive games' outputs. -/
abbrev OutI (K : ℕ) := Out ((ιI × GOut K) × QueryLog specIC)
abbrev OutR (K : ℕ) := Out ((ιR K × GOut K) × QueryLog specIC)

lemma size_t_u {lr : Bool} {q : IssQ K} (h : uWFI lr q) : q.t.size = 45 := by
  simp only [IssQ.t, ByteArray.size_extract, h.1]; omega

lemma size_nf_u {lr : Bool} {r : RedQ K} (h : uWFR lr r) : r.nf.size = 24 := by
  simp only [RedQ.nf, ByteArray.size_extract, h.2.2.2.1]; omega

section Accepted

variable (g : Table) (E : CTable) (lr : Bool) (pk : Fin K → UovPk) (sk : Fin K → Spec.Signer)
  (qI : ℕ) (A : Adversary K qR)

/-- **An accepted bound Issue query is accepted by `P^iss_j`'s verifier, at its statement.** -/
theorem accepted_BI {j : ℕ} {q : IssQ K}
    (hj : (evalWithAnswerFn (QueryImpl.ofFn (join g E)) (game lr pk sk qI A)).1[j]? =
      some (.inl q, true)) :
    let r := evalWithAnswerFn (QueryImpl.ofFn g) (gameA CrtGen.tables (stI lr) (PBI lr pk sk qI A j) E)
    r.2.2.accept = true ∧ (stOut r).1 = (q.t, q.ctx) := by
  obtain ⟨-, hrec, -⟩ := game_eval g E lr pk sk A qI
  obtain ⟨hwf, hv⟩ := hrec _ (List.mem_of_getElem? hj) rfl
  have hsz : q.t.size = 45 ∧ q.ctx.size = 16 := ⟨size_t hwf, hwf.2⟩
  have hP : evalWithAnswerFn (QueryImpl.ofFn (join g E)) (PBI lr pk sk qI A j) =
      (q.pf, (⟨(q.t, q.ctx), hsz⟩, evalWithAnswerFn (QueryImpl.ofFn (join g E)) (game lr pk sk qI A))) := by
    simp only [PBI, evalWithAnswerFn_map, projBI, hj, hsz, and_self, dite_true]
  refine ⟨?_, ?_⟩
  · rw [gameA_transcript, sA, hP]; exact hv
  · rw [stOut_gameA, sA, hP]

/-- **An accepted unbound Issue query is accepted by `P^u-iss_j`'s verifier, at its statement.** -/
theorem accepted_UI {j : ℕ} {q : IssQ K}
    (hj : (evalWithAnswerFn (QueryImpl.ofFn (join g E)) (game lr pk sk qI A)).1[j]? =
      some (.inr q, true)) :
    let r := evalWithAnswerFn (QueryImpl.ofFn g) (gameA CrtGen.tables (stUI lr) (PUI lr pk sk qI A j) E)
    r.2.2.accept = true ∧ (stOut r).1 = (q.t, q.ctx) := by
  obtain ⟨-, hrec, -⟩ := game_eval g E lr pk sk A qI
  obtain ⟨hwf, hv⟩ := hrec _ (List.mem_of_getElem? hj) rfl
  have hsz : q.t.size = 45 ∧ q.ctx.size = 16 := ⟨size_t_u hwf, hwf.2⟩
  have hP : evalWithAnswerFn (QueryImpl.ofFn (join g E)) (PUI lr pk sk qI A j) =
      (q.pf, (⟨(q.t, q.ctx), hsz⟩, evalWithAnswerFn (QueryImpl.ofFn (join g E)) (game lr pk sk qI A))) := by
    simp only [PUI, evalWithAnswerFn_map, projUI, hj, hsz, and_self, dite_true]
  refine ⟨?_, ?_⟩
  · rw [gameA_transcript, sA, hP]; exact hv
  · rw [stOut_gameA, sA, hP]

/-- **An accepted redemption is accepted by `P^u-red_j`'s verifier, at its statement.** -/
theorem accepted_UR {j : ℕ} {rq : RedQ K}
    (hj : (evalWithAnswerFn (QueryImpl.ofFn (join g E)) (game lr pk sk qI A)).2[j]? = some (rq, true)) :
    let r := evalWithAnswerFn (QueryImpl.ofFn g) (gameA CrtGen.tables (stUR lr pk) (PUR lr pk sk qI A j) E)
    r.2.2.accept = true ∧ (stOut r).1 = (rq.S, rq.nf, rq.ci, rq.cr, rq.cd) := by
  obtain ⟨-, -, -, hrec⟩ := game_eval g E lr pk sk A qI
  obtain ⟨hwf, hv⟩ := hrec _ (List.mem_of_getElem? hj) rfl
  have hsz : rq.S.length ≤ 64 ∧ rq.nf.size = 24 ∧ rq.ci.size = 16 ∧ rq.cr.size = 16 :=
    ⟨hwf.2.1, size_nf_u hwf, hwf.2.2.2.2.1, hwf.2.2.2.2.2⟩
  have hP : evalWithAnswerFn (QueryImpl.ofFn (join g E)) (PUR lr pk sk qI A j) =
      (rq.pf, (⟨(rq.S, rq.nf, rq.ci, rq.cr, rq.cd), hsz⟩,
        evalWithAnswerFn (QueryImpl.ofFn (join g E)) (game lr pk sk qI A))) := by
    simp only [PUR, evalWithAnswerFn_map, projUR, hj, hsz, and_self, dite_true]
  refine ⟨?_, ?_⟩
  · rw [gameA_transcript, sA, hP]; exact hv
  · rw [stOut_gameA, sA, hP]

end Accepted

/-! ## Extraction and the extracted inputs -/

/-- A `UCom` input `(nf_key, ctx_iss, r)`. -/
abbrev UOpening := Spec.Bytes × Spec.Bytes × Spec.Bytes

/-- `UCom` of an input (`Spec.MoussakaUnbound.ucom`, Keccak-p[800]). -/
def ucomO (y : UOpening) : Spec.Bytes := Spec.MoussakaUnbound.ucom y.1 y.2.1 y.2.2

/-- A `UCom` input in its domain `D_u` (`nf_key`, `ctx_iss`, `r` of 16 bytes each). -/
def WFU (y : UOpening) : Prop := y.1.length = 16 ∧ y.2.1.length = 16 ∧ y.2.2.length = 16

/-- **An input of `Com ∪ UCom`**: a bound `Com` input or a `UCom` input. The two input spaces are
disjoint as Keccak states (`Arith.MoussakaUnbound.encodeUnboundComState_ne_encodeComState`), so
distinct inputs here are distinct Keccak inputs. -/
abbrev XOp := Opening ⊕ UOpening

/-- The commitment of an input: `Com` or `UCom`, both `KP800(·)[0..45)`. -/
def comX : XOp → Spec.Bytes := Sum.elim comO ucomO

/-- An input in the union domain `D ∪ D_u`. -/
def WFX : XOp → Prop := Sum.elim WFO WFU

/-- The issuance context field of an input. -/
def ctxX : XOp → Spec.Bytes := Sum.elim (fun x => x.2.1) (fun y => y.2.1)

/-- The nullifier key of a `UCom` input (unused for bound inputs). -/
def keyX : XOp → Spec.Bytes := Sum.elim (fun _ => []) (fun y => y.1)

section Ext

variable (E : CTable) (lr : Bool) (pk : Fin K → UovPk)

/-- **Extraction of a bound issuance proof succeeds** (`OMUF.ExtI` for this game's provers). -/
def ExtBI (r : OutI K) : Prop :=
  @Extracted (icPrg E.cipher) _ (stI lr (stOut r))
    (fun _ w => Privacy.Moussaka.IssueRelW ⟨toL (stOut r).1.1, toL (stOut r).1.2⟩
      (EndToEnd.SpecRel.issueWitOf (toL (stOut r).1.2) w)) r

/-- **Extraction of an unbound issuance proof succeeds** (the event of
`moussakaUnboundIssue_accept_le_adaptive_spec`): a known tree's candidate decodes to a witness of
`Spec.MoussakaUnbound.IssueRel` at the proof's statement. -/
def ExtUI (r : OutI K) : Prop :=
  @Extracted (icPrg E.cipher) _ (stUI lr (stOut r))
    (fun _ w => Spec.MoussakaUnbound.IssueRel ⟨toL (stOut r).1.1, toL (stOut r).1.2⟩
      (EndToEnd.SpecRel.uIssueWitOf (toL (stOut r).1.2) w)) r

/-- **Extraction of an unbound redemption proof succeeds** (the event of
`moussakaUnboundRedeem_accept_le_adaptive_spec`). -/
def ExtUR (r : OutR K) : Prop :=
  @Extracted (icPrg E.cipher) _ (stUR lr pk (stOut r))
    (fun _ w => Spec.MoussakaUnbound.RedeemRel
      ⟨(ancR pk (stOut r)).map UovPk.toSpec, toL (stOut r).1.2.1, toL (stOut r).1.2.2.1,
        toL (stOut r).1.2.2.2.1, toL (stOut r).1.2.2.2.2⟩
      (EndToEnd.SpecRel.uRedeemWitOf (toL (stOut r).1.2.2.1) (toL (stOut r).1.2.2.2.1) w)) r

/-- **The inputs extracted from a bound issuance proof** (`OMUF.OpI`). -/
def OpBI (r : OutI K) : Set Opening := {x | WFO x ∧ x.2.1 = toL (stOut r).1.2 ∧
  comO x = toL (stOut r).1.1 ∧
  @Extracted (icPrg E.cipher) _ (stI lr (stOut r))
    (fun _ w => EndToEnd.SpecRel.issueWitOf (toL (stOut r).1.2) w =
      Spec.Moussaka.encodeIssueWitness x.1 x.2.1 x.2.2.1 x.2.2.2) r}

/-- **The inputs extracted from an unbound issuance proof**: a known tree's candidate decodes to
the unbound issuance witness of the input, which commits to `t` in context `ctx_iss`. -/
def OpUI (r : OutI K) : Set UOpening := {y | WFU y ∧ y.2.1 = toL (stOut r).1.2 ∧
  ucomO y = toL (stOut r).1.1 ∧
  @Extracted (icPrg E.cipher) _ (stUI lr (stOut r))
    (fun _ w => EndToEnd.SpecRel.uIssueWitOf (toL (stOut r).1.2) w =
      Spec.MoussakaUnbound.encodeIssueWitness y.1 y.2.1 y.2.2) r}

/-- **The inputs extracted from an unbound redemption proof, with a key and a preimage**: a known
tree's candidate decodes to the redemption witness of the input (at `ctx_iss`, `ctx_red`), a
preimage `s` and a selector `u`; the Anchor at `u` is an honest Anchor `k` with
`P_k(s) = UCom(input)`, and the input's key gives the nullifier, `Derive(nf_key, ctx_red) = nf`. -/
def OpUR (r : OutR K) : Set UOpening := {y | WFU y ∧ y.2.1 = toL (stOut r).1.2.2.1 ∧
  Spec.MoussakaUnbound.derive y.1 (toL (stOut r).1.2.2.2.1) = toL (stOut r).1.2.1 ∧
  ∃ (s : Spec.Bytes) (u : ℕ) (k : Fin K), (stOut r).1.1[u]? = some k ∧
    (pk k).toSpec.eval s = ucomO y ∧
    @Extracted (icPrg E.cipher) _ (stUR lr pk (stOut r))
      (fun _ w => EndToEnd.SpecRel.uRedeemWitOf (toL (stOut r).1.2.2.1) (toL (stOut r).1.2.2.2.1) w =
        Spec.MoussakaUnbound.encodeRedeemWitness y.1 y.2.1 (toL (stOut r).1.2.2.2.1) y.2.2 s u) r}

/-- **The extraction failure of a bound issuance proof**: accepted, and not extracted. -/
def BadBI (r : OutI K) : Prop := r.2.2.accept = true ∧ ¬ExtBI E lr r

/-- **The extraction failure of an unbound issuance proof.** -/
def BadUI (r : OutI K) : Prop := r.2.2.accept = true ∧ ¬ExtUI E lr r

/-- **The extraction failure of an unbound redemption proof.** -/
def BadUR (r : OutR K) : Prop := r.2.2.accept = true ∧ ¬ExtUR E lr pk r

theorem opBI_of_ext {r : OutI K} (h : ExtBI E lr r) :
    ∃ x ∈ OpBI E lr r, comO x = toL (stOut r).1.1 ∧ x.2.1 = toL (stOut r).1.2 := by
  obtain ⟨i, hi, ⟨nf, rr, cr, hnf, hr, hcr, hw, ht⟩, hci⟩ := h
  refine ⟨(nf, toL (stOut r).1.2, cr, rr), ⟨⟨hnf, hci, hcr, hr⟩, rfl, ht.symm, i, hi, hw⟩,
    ht.symm, rfl⟩

theorem opUI_of_ext {r : OutI K} (h : ExtUI E lr r) :
    ∃ y ∈ OpUI E lr r, ucomO y = toL (stOut r).1.1 ∧ y.2.1 = toL (stOut r).1.2 := by
  obtain ⟨i, hi, ⟨k, rr, hk, hr, hw, ht⟩⟩ := h
  have hci : (toL (stOut r).1.2).length = 16 := by
    rw [Privacy.length_toL]; exact (stOut r).2.2
  exact ⟨(k, toL (stOut r).1.2, rr), ⟨⟨hk, hci, hr⟩, rfl, ht.symm, i, hi, hw⟩, ht.symm, rfl⟩

theorem opUR_of_ext {r : OutR K} (h : ExtUR E lr pk r) :
    ∃ y ∈ OpUR E lr pk r, y.2.1 = toL (stOut r).1.2.2.1 ∧
      Spec.MoussakaUnbound.derive y.1 (toL (stOut r).1.2.2.2.1) = toL (stOut r).1.2.1 := by
  obtain ⟨i, hi, ⟨k, rr, s, u, pk', hk, hr, -, hu, hw, he, hnf⟩⟩ := h
  simp only [ancR, List.map_map, List.getElem?_map, Option.map_eq_some_iff,
    Function.comp_apply] at hu
  obtain ⟨a, ha, rfl⟩ := hu
  have hci : (toL (stOut r).1.2.2.1).length = 16 := by
    rw [Privacy.length_toL]; exact (stOut r).2.2.2.1
  exact ⟨(k, toL (stOut r).1.2.2.1, rr), ⟨⟨hk, hci, hr⟩, rfl, hnf.symm, s, u, a, ha, he, i, hi, hw⟩,
    rfl, hnf.symm⟩

end Ext

/-! ## The reductions `B₁`, `B₂` and the per-table core -/

section Red

variable (lr : Bool) (pk : Fin K → UovPk) (sk : Fin K → Spec.Signer) (qI : ℕ) (A : Adversary K qR)

/-- **The reductions' run** (`B₁` and `B₂`): the game, then every proof's straight-line extraction
and verification, for the three families. -/
def extAll (E : CTable) :
    OracleComp spec (GOut K × List (OutI K) × List (OutI K) × List (OutR K)) :=
  runE E (game lr pk sk qI A) >>= fun o =>
    (List.range qI).mapM (fun j => gameA CrtGen.tables (stI lr) (PBI lr pk sk qI A j) E) >>= fun ob =>
      (List.range qI).mapM (fun j => gameA CrtGen.tables (stUI lr) (PUI lr pk sk qI A j) E) >>=
        fun ou =>
          (List.range qR).mapM (fun j => gameA CrtGen.tables (stUR lr pk) (PUR lr pk sk qI A j) E) >>=
            fun orr => pure (o.1, ob, ou, orr)

/-- The view of the reductions. -/
abbrev View (K : ℕ) := GOut K × List (OutI K) × List (OutI K) × List (OutR K)

/-- The inputs extracted from the accepted bound issuance proofs. -/
def SBI (E : CTable) (v : View K) : Set Opening :=
  {x | ∃ (j : ℕ) (q : IssQ K) (r : OutI K), v.1.1[j]? = some (.inl q, true) ∧ v.2.1[j]? = some r ∧
    x ∈ OpBI E lr r}

/-- The inputs extracted from the accepted unbound issuance proofs. -/
def SUI (E : CTable) (v : View K) : Set UOpening :=
  {y | ∃ (j : ℕ) (q : IssQ K) (r : OutI K), v.1.1[j]? = some (.inr q, true) ∧
    v.2.2.1[j]? = some r ∧ y ∈ OpUI E lr r}

/-- The inputs, with keys and preimages, extracted from the accepted unbound redemption proofs. -/
def SUR (E : CTable) (v : View K) : Set UOpening :=
  {y | ∃ (j : ℕ) (rq : RedQ K) (r : OutR K), v.1.2[j]? = some (rq, true) ∧ v.2.2.2[j]? = some r ∧
    y ∈ OpUR E lr pk r}

/-- All extracted inputs of `Com ∪ UCom`. -/
def SX (E : CTable) (v : View K) : Set XOp :=
  Sum.inl '' SBI lr E v ∪ Sum.inr '' (SUI lr E v ∪ SUR lr pk E v)

/-- **`B₁` wins the joint binding game**: two distinct extracted inputs of `Com ∪ UCom` with one
commitment (within one variant or **across** the variants). -/
def Coll (E : CTable) (v : View K) : Prop :=
  ∃ x ∈ SX lr pk E v, ∃ x' ∈ SX lr pk E v, x ≠ x' ∧ comX x = comX x'

/-- **`B₂` wins the CT-UF^open game**: an extracted redemption input `y`, with an honest Anchor
`k` and `s` such that `P_k(s) = UCom(y)`, whose commitment was never submitted to any Anchor's
signer, through either variant. -/
def Forge (E : CTable) (v : View K) : Prop :=
  ∃ y ∈ SUR lr pk E v, ucomO y ∉ sigT v.1

theorem extAll_eval (g : Table) (E : CTable) :
    evalWithAnswerFn (QueryImpl.ofFn g) (extAll lr pk sk qI A E) =
      (evalWithAnswerFn (QueryImpl.ofFn (join g E)) (game lr pk sk qI A),
        (List.range qI).map (fun j =>
          evalWithAnswerFn (QueryImpl.ofFn g) (gameA CrtGen.tables (stI lr) (PBI lr pk sk qI A j) E)),
        (List.range qI).map (fun j =>
          evalWithAnswerFn (QueryImpl.ofFn g) (gameA CrtGen.tables (stUI lr) (PUI lr pk sk qI A j) E)),
        (List.range qR).map (fun j =>
          evalWithAnswerFn (QueryImpl.ofFn g)
            (gameA CrtGen.tables (stUR lr pk) (PUR lr pk sk qI A j) E))) := by
  simp only [extAll, evalWithAnswerFn_bind, evalWithAnswerFn_runE, evalWithAnswerFn_mapM,
    evalWithAnswerFn_pure]

/-- **The per-table core of Theorem U1**: a win means that some accepted proof (of one of the
three families) is not extracted, or `B₁` finds a collision of `Com ∪ UCom`, or `B₂` a CT-UF^open
forgery. -/
theorem win_imp (g : Table) (E : CTable)
    (hwin : Win (evalWithAnswerFn (QueryImpl.ofFn (join g E)) (game lr pk sk qI A))) :
    (∃ j ∈ Finset.range qI, BadBI E lr (evalWithAnswerFn (QueryImpl.ofFn g)
        (gameA CrtGen.tables (stI lr) (PBI lr pk sk qI A j) E))) ∨
    (∃ j ∈ Finset.range qI, BadUI E lr (evalWithAnswerFn (QueryImpl.ofFn g)
        (gameA CrtGen.tables (stUI lr) (PUI lr pk sk qI A j) E))) ∨
    (∃ j ∈ Finset.range qR, BadUR E lr pk (evalWithAnswerFn (QueryImpl.ofFn g)
        (gameA CrtGen.tables (stUR lr pk) (PUR lr pk sk qI A j) E))) ∨
    Coll lr pk E (evalWithAnswerFn (QueryImpl.ofFn g) (extAll lr pk sk qI A E)) ∨
    Forge lr pk E (evalWithAnswerFn (QueryImpl.ofFn g) (extAll lr pk sk qI A E)) := by
  classical
  obtain ⟨hlI, -, hlR, -⟩ := game_eval g E lr pk sk A qI
  rw [extAll_eval]
  set o := evalWithAnswerFn (QueryImpl.ofFn (join g E)) (game lr pk sk qI A) with ho
  set ob := (List.range qI).map (fun j =>
    evalWithAnswerFn (QueryImpl.ofFn g) (gameA CrtGen.tables (stI lr) (PBI lr pk sk qI A j) E))
    with hob
  set ou := (List.range qI).map (fun j =>
    evalWithAnswerFn (QueryImpl.ofFn g) (gameA CrtGen.tables (stUI lr) (PUI lr pk sk qI A j) E))
    with hou
  set orr := (List.range qR).map (fun j =>
    evalWithAnswerFn (QueryImpl.ofFn g) (gameA CrtGen.tables (stUR lr pk) (PUR lr pk sk qI A j) E))
    with horr
  by_contra hno
  simp only [BadBI, BadUI, BadUR, not_or, not_exists, not_and, Finset.mem_range, not_not] at hno
  obtain ⟨hB, hU, hR, hC, hF⟩ := hno
  obtain ⟨c, cr, hc⟩ := hwin
  have key := _root_.VoleMole.MoussakaUnbound.collision_or_forgery_unbound comX (fun x => x.isRight = true) ctxX
    keyX Spec.MoussakaUnbound.derive (SX lr pk E (o, ob, ou, orr))
    (Sum.inr '' SUR lr pk E (o, ob, ou, orr))
    (fun x hx => Or.inr (Set.image_mono Set.subset_union_right hx))
    (uissL o) (bissL o) (uredL o) ?_ ?_ ?_ c cr hc
  · rcases key with ⟨x, hx, x', hx', hne, he⟩ | ⟨x, hx, hn1, hn2⟩
    · exact hC ⟨x, hx, x', hx', hne, he⟩
    · obtain ⟨y, hy, rfl⟩ := hx
      have e : comX (Sum.inr y) = ucomO y := by simp only [comX, Sum.elim_inr]
      rw [e] at hn1 hn2
      exact hF ⟨y, hy, fun hs => (mem_sigT hs).elim hn1 hn2⟩
  · -- every accepted unbound issuance has an extracted `UCom` input
    intro q hq
    simp only [uissL, List.mem_map, List.mem_filter, Bool.and_eq_true] at hq
    obtain ⟨⟨p, b⟩, ⟨hp, hpb, hpr⟩, rfl⟩ := hq
    rcases p with p | p
    · simp at hpr
    obtain ⟨j, hj⟩ := List.mem_iff_getElem?.1 hp
    have hjl : j < qI := by rw [← hlI]; exact (List.getElem?_eq_some_iff.1 hj).1
    have hj' : o.1[j]? = some (.inr p, true) := by rw [hj]; simp_all
    obtain ⟨hacc, hst⟩ := accepted_UI g E lr pk sk qI A hj'
    obtain ⟨y, hy, hyc, hyt⟩ := opUI_of_ext E lr (hU j hjl hacc)
    refine ⟨.inr y, Or.inr ⟨y, Or.inl ⟨j, p, _, hj', by simp [ou, hjl], hy⟩, rfl⟩, rfl, ?_, ?_⟩
    · simp only [comX, Sum.elim_inr, IQ.q]; rw [hyc, hst]; rfl
    · simp only [ctxX, Sum.elim_inr, IQ.q]; rw [hyt, hst]; rfl
  · -- every accepted bound issuance has an extracted `Com` input
    intro t ht
    simp only [bissL, List.mem_map, List.mem_filter, Bool.and_eq_true] at ht
    obtain ⟨⟨p, b⟩, ⟨hp, hpb, hpl⟩, rfl⟩ := ht
    rcases p with p | p
    swap
    · simp at hpl
    obtain ⟨j, hj⟩ := List.mem_iff_getElem?.1 hp
    have hjl : j < qI := by rw [← hlI]; exact (List.getElem?_eq_some_iff.1 hj).1
    have hj' : o.1[j]? = some (.inl p, true) := by rw [hj]; simp_all
    obtain ⟨hacc, hst⟩ := accepted_BI g E lr pk sk qI A hj'
    obtain ⟨x, hx, hxc, -⟩ := opBI_of_ext E lr (hB j hjl hacc)
    refine ⟨.inl x, Or.inl ⟨x, ⟨j, p, _, hj', by simp [ob, hjl], hx⟩, rfl⟩, by simp, ?_⟩
    simp only [comX, Sum.elim_inl, IQ.q]; rw [hxc, hst]; rfl
  · -- every accepted redemption has an extracted `UCom` input, with a key and a preimage
    intro q hq
    simp only [uredL, List.mem_map, List.mem_filter] at hq
    obtain ⟨p, ⟨hp, hpb⟩, rfl⟩ := hq
    obtain ⟨j, hj⟩ := List.mem_iff_getElem?.1 hp
    have hjl : j < qR := by rw [← hlR]; exact (List.getElem?_eq_some_iff.1 hj).1
    have hj' : o.2[j]? = some (p.1, true) := by rw [hj]; cases p; simp_all
    obtain ⟨hacc, hst⟩ := accepted_UR g E lr pk sk qI A hj'
    obtain ⟨y, hy, hyc, hyd⟩ := opUR_of_ext E lr pk (hR j hjl hacc)
    refine ⟨.inr y, ⟨y, ⟨j, p.1, _, hj', by simp [orr, hjl], hy⟩, rfl⟩, rfl, ?_, ?_⟩
    · simp only [ctxX, Sum.elim_inr]; rw [hyc, hst]
    · simp only [keyX, Sum.elim_inr]; rw [hst] at hyd; exact hyd

end Red

/-! ## Theorem U1 -/

section Union

variable {D : Type} [DecidableEq D] {R : D → Type} [∀ d, Fintype (R d)] [∀ d, Nonempty (R d)]
  [∀ d, SampleableType (R d)]

/-- **Three indexed families and two events of a further computation**
(`prEvent_bind_le_sum4_of_table` with a third family). -/
theorem prEvent_bind_le_sum5_of_table {T X Y₁ Y₂ Y₃ Z : Type} (mT : ProbComp T)
    (m₀ : T → OracleComp (OracleSpec.ofFn R) X) (e₀ : T → X → Prop) (s₁ s₂ s₃ : Finset ℕ)
    (m₁ : ℕ → T → OracleComp (OracleSpec.ofFn R) Y₁) (e₁ : T → Y₁ → Prop)
    (m₂ : ℕ → T → OracleComp (OracleSpec.ofFn R) Y₂) (e₂ : T → Y₂ → Prop)
    (m₃ : ℕ → T → OracleComp (OracleSpec.ofFn R) Y₃) (e₃ : T → Y₃ → Prop)
    (n : T → OracleComp (OracleSpec.ofFn R) Z) (c d : T → Z → Prop)
    (h : ∀ E (g : (d : D) → R d), e₀ E (evalWithAnswerFn (QueryImpl.ofFn g) (m₀ E)) →
      (∃ i ∈ s₁, e₁ E (evalWithAnswerFn (QueryImpl.ofFn g) (m₁ i E))) ∨
      (∃ i ∈ s₂, e₂ E (evalWithAnswerFn (QueryImpl.ofFn g) (m₂ i E))) ∨
      (∃ i ∈ s₃, e₃ E (evalWithAnswerFn (QueryImpl.ofFn g) (m₃ i E))) ∨
      c E (evalWithAnswerFn (QueryImpl.ofFn g) (n E)) ∨
      d E (evalWithAnswerFn (QueryImpl.ofFn g) (n E))) :
    Pr{let E ← mT; let r ← (simulateQ randomOracle (m₀ E)).run' ∅}[e₀ E r] ≤
      ∑ i ∈ s₁, Pr{let E ← mT; let r ← (simulateQ randomOracle (m₁ i E)).run' ∅}[e₁ E r] +
      ∑ i ∈ s₂, Pr{let E ← mT; let r ← (simulateQ randomOracle (m₂ i E)).run' ∅}[e₂ E r] +
      ∑ i ∈ s₃, Pr{let E ← mT; let r ← (simulateQ randomOracle (m₃ i E)).run' ∅}[e₃ E r] +
      Pr{let E ← mT; let r ← (simulateQ randomOracle (n E)).run' ∅}[c E r] +
      Pr{let E ← mT; let r ← (simulateQ randomOracle (n E)).run' ∅}[d E r] := by
  classical
  let Y : ((ℕ ⊕ ℕ) ⊕ ℕ) ⊕ Bool → Type := fun
    | .inl (.inl (.inl _)) => Y₁
    | .inl (.inl (.inr _)) => Y₂
    | .inl (.inr _) => Y₃
    | .inr _ => Z
  let ob : (i : ((ℕ ⊕ ℕ) ⊕ ℕ) ⊕ Bool) → T → OracleComp (OracleSpec.ofFn R) (Y i) := fun
    | .inl (.inl (.inl i)) => m₁ i
    | .inl (.inl (.inr i)) => m₂ i
    | .inl (.inr i) => m₃ i
    | .inr _ => n
  let Q : (i : ((ℕ ⊕ ℕ) ⊕ ℕ) ⊕ Bool) → T → Y i → Prop := fun
    | .inl (.inl (.inl _)) => e₁
    | .inl (.inl (.inr _)) => e₂
    | .inl (.inr _) => e₃
    | .inr true => c
    | .inr false => d
  have key := prEvent_bind_le_sum_of_table mT m₀
    (((s₁.disjSum s₂).disjSum s₃).disjSum Finset.univ) ob e₀ Q fun E g hw => by
      rcases h E g hw with ⟨i, hi, he⟩ | ⟨i, hi, he⟩ | ⟨i, hi, he⟩ | hc | hd
      · exact ⟨.inl (.inl (.inl i)), by simp [hi], he⟩
      · exact ⟨.inl (.inl (.inr i)), by simp [hi], he⟩
      · exact ⟨.inl (.inr i), by simp [hi], he⟩
      · exact ⟨.inr true, by simp, hc⟩
      · exact ⟨.inr false, by simp, hd⟩
  rw [Finset.sum_disjSum, Finset.sum_disjSum, Finset.sum_disjSum, Fintype.sum_bool] at key
  refine key.trans (le_of_eq ?_)
  simp only [ob, Q]
  ring

end Union

/-- **Theorem U1 (unforgeability per redemption context), the reduction.** For every OMUF-U
adversary, honest Anchors with any public keys and signers (each running both variants with one
key), and either proof layout (`lr`): the probability that the adversary wins is at most the
extraction failures of the `qI` bound issuance, `qI` unbound issuance and `qR` unbound redemption
provers (each a prover of the soundness theorems), plus `B₁`'s joint binding advantage and `B₂`'s
CT-UF^open advantage. -/
theorem omufU_le (lr : Bool) (pk : Fin K → UovPk) (sk : Fin K → Spec.Signer) (qI : ℕ)
    (A : Adversary K qR) :
    Pr{let E ← $ᵗ CTable; let r ← (simulateQ randomOracle (runE E (game lr pk sk qI A))).run' ∅}[
        Win r.1] ≤
      ∑ j ∈ Finset.range qI, Pr{let E ← $ᵗ CTable; let r ← (simulateQ randomOracle
        (gameA CrtGen.tables (stI lr) (PBI lr pk sk qI A j) E)).run' ∅}[BadBI E lr r] +
      ∑ j ∈ Finset.range qI, Pr{let E ← $ᵗ CTable; let r ← (simulateQ randomOracle
        (gameA CrtGen.tables (stUI lr) (PUI lr pk sk qI A j) E)).run' ∅}[BadUI E lr r] +
      ∑ j ∈ Finset.range qR, Pr{let E ← $ᵗ CTable; let r ← (simulateQ randomOracle
        (gameA CrtGen.tables (stUR lr pk) (PUR lr pk sk qI A j) E)).run' ∅}[BadUR E lr pk r] +
      Pr{let E ← $ᵗ CTable; let v ← (simulateQ randomOracle (extAll lr pk sk qI A E)).run' ∅}[
        Coll lr pk E v] +
      Pr{let E ← $ᵗ CTable; let v ← (simulateQ randomOracle (extAll lr pk sk qI A E)).run' ∅}[
        Forge lr pk E v] := by
  refine prEvent_bind_le_sum5_of_table ($ᵗ CTable) (fun E => runE E (game lr pk sk qI A))
    (fun _ r => Win r.1) (Finset.range qI) (Finset.range qI) (Finset.range qR) _ _ _ _ _ _ _ _ _
    fun E g hw => ?_
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

/-- One honest issuance verification's cipher queries, either variant. -/
def cellI (lr : Bool) : ℕ :=
  max (verifyCellBound (parI lr)) (verifyCellBound (Unbound.issueParams lr))

/-- **The game's hash queries per kind**: the adversary's `qI + 2` stages and the `qI + qR`
honest verifications (as `OMUF.gameK`). -/
abbrev gameK (q : Kind → ℕ) (qI qR : ℕ) : Kind → ℕ := OMUF.gameK q qI qR

/-- **The game's cipher queries.** -/
def gameE (lr : Bool) (qE qI qR : ℕ) : ℕ :=
  (qI + 2) * qE + qI * cellI lr + qR * verifyCellBound (Unbound.redeemParams lr)

/-- **The game's hash queries in all** (as `OMUF.gameH`). -/
abbrev gameH (n qI qR : ℕ) : ℕ := OMUF.gameH n qI qR

section Bounds

variable (lr : Bool) (pk : Fin K → UovPk) (sk : Fin K → Spec.Signer)

theorem anchorU_k (q : IQ K) : IsKindQueryBoundIC (anchorU lr sk q) vK := by
  rcases q with q | q
  · exact anchorIC_k lr sk q
  · show IsKindQueryBoundIC (uanchorIC lr sk q) vK
    unfold uanchorIC
    split_ifs
    · exact isKindQueryBoundIC_map _ (isKindQueryBoundIC_verifyIC _ _ _)
    · trivial

theorem anchorU_e (q : IQ K) :
    IsQueryBoundP (anchorU lr sk q) (fun t => t.isRight = true) (cellI lr) := by
  rcases q with q | q
  · exact (anchorIC_e lr sk q).mono (le_max_left _ _)
  · show IsQueryBoundP (uanchorIC lr sk q) _ _
    unfold uanchorIC
    split_ifs
    · exact ((isQueryBoundP_map_iff _ _ _).2 (isQueryBoundP_right_verifyIC _ _ _)).mono
        (le_max_right _ _)
    · trivial

theorem anchorU_h (q : IQ K) :
    IsQueryBoundP (anchorU lr sk q) (fun t => t.isLeft = true) (2 + verifierTotal) := by
  rcases q with q | q
  · exact anchorIC_h lr sk q
  · show IsQueryBoundP (uanchorIC lr sk q) _ _
    unfold uanchorIC
    split_ifs
    · exact (isQueryBoundP_map_iff _ _ _).2 (isQueryBoundP_left_verifyIC _ _ _)
    · trivial

theorem umoderatorIC_k (r : RedQ K) : IsKindQueryBoundIC (umoderatorIC lr pk r) vK := by
  unfold umoderatorIC
  split_ifs
  · exact isKindQueryBoundIC_map _ (isKindQueryBoundIC_verifyIC _ _ _)
  · trivial

theorem umoderatorIC_e (r : RedQ K) :
    IsQueryBoundP (umoderatorIC lr pk r) (fun t => t.isRight = true)
      (verifyCellBound (Unbound.redeemParams lr)) := by
  unfold umoderatorIC
  split_ifs
  · exact (isQueryBoundP_map_iff _ _ _).2 (isQueryBoundP_right_verifyIC _ _ _)
  · trivial

theorem umoderatorIC_h (r : RedQ K) :
    IsQueryBoundP (umoderatorIC lr pk r) (fun t => t.isLeft = true) (2 + verifierTotal) := by
  unfold umoderatorIC
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
      isKindQueryBoundIC_bind (anchorU_k lr sk sq.2) fun ra =>
        isKindQueryBoundIC_bind (q₂ := 0) (ob := fun rest => (pure (rest.1, (sq.2, ra.2) :: rest.2) :
          OracleComp specIC (A.σ × List (IQ K × Bool)))) (ih _) fun _ => trivial).mono (le_of_eq ?_)
    rw [succ_nsmul]; abel

theorem runIss_e (m : ℕ) (s : A.σ) : IsQueryBoundP (runIss lr sk A m s)
    (fun t => t.isRight = true) (m * (qE + cellI lr)) := by
  induction m generalizing s with
  | zero => trivial
  | succ m ih =>
    refine (isQueryBoundP_bind (hA.query_e s) fun sq _ =>
      isQueryBoundP_bind (anchorU_e lr sk sq.2) fun ra _ =>
        isQueryBoundP_bind (m := 0) (ob := fun rest => (pure (rest.1, (sq.2, ra.2) :: rest.2) :
          OracleComp specIC (A.σ × List (IQ K × Bool)))) (ih _) fun _ _ => trivial).mono
            (le_of_eq ?_)
    ring

theorem runIss_h (m : ℕ) (s : A.σ) : IsQueryBoundP (runIss lr sk A m s)
    (fun t => t.isLeft = true) (m * (n + (2 + verifierTotal))) := by
  induction m generalizing s with
  | zero => trivial
  | succ m ih =>
    refine (isQueryBoundP_bind (hA.query_h s) fun sq _ =>
      isQueryBoundP_bind (anchorU_h lr sk sq.2) fun ra _ =>
        isQueryBoundP_bind (m := 0) (ob := fun rest => (pure (rest.1, (sq.2, ra.2) :: rest.2) :
          OracleComp specIC (A.σ × List (IQ K × Bool)))) (ih _) fun _ _ => trivial).mono
            (le_of_eq ?_)
    ring

omit hA in
theorem runRed_k (R : Fin qR → RedQ K) : IsKindQueryBoundIC (runRed lr pk R) (qR • vK) := by
  unfold runRed
  simpa using isKindQueryBoundIC_mapM (List.finRange qR) _ fun j =>
    isKindQueryBoundIC_map _ (umoderatorIC_k lr pk (R j))

omit hA in
theorem runRed_e (R : Fin qR → RedQ K) :
    IsQueryBoundP (runRed lr pk R) (fun t => t.isRight = true)
      (qR * verifyCellBound (Unbound.redeemParams lr)) := by
  unfold runRed
  simpa using isQueryBoundP_mapM _ (List.finRange qR) _ fun j =>
    (isQueryBoundP_map_iff _ _ _).2 (umoderatorIC_e lr pk (R j))

omit hA in
theorem runRed_h (R : Fin qR → RedQ K) :
    IsQueryBoundP (runRed lr pk R) (fun t => t.isLeft = true) (qR * (2 + verifierTotal)) := by
  unfold runRed
  simpa using isQueryBoundP_mapM _ (List.finRange qR) _ fun j =>
    (isQueryBoundP_map_iff _ _ _).2 (umoderatorIC_h lr pk (R j))

theorem game_k (qI : ℕ) : IsKindQueryBoundIC (game lr pk sk qI A) (gameK q qI qR) := by
  unfold game
  refine (isKindQueryBoundIC_bind hA.init_k fun s =>
    isKindQueryBoundIC_bind (runIss_k lr sk hA qI s) fun r =>
      isKindQueryBoundIC_bind (hA.final_k r.1) fun R =>
        isKindQueryBoundIC_map _ (runRed_k lr pk R)).mono (le_of_eq ?_)
  simp only [gameK, OMUF.gameK, smul_add, add_smul]
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
  simp only [gameH, OMUF.gameH]; ring

end Bounds

/-! ## Theorem U1 with the extraction terms of the soundness theorems -/

/-- **The extraction failure of one unbound issuance proof**
(`moussakaUnboundIssue_accept_le_adaptive_spec`). -/
noncomputable def epsUI (q : Kind → ℕ) (qE : ℕ) : ℝ≥0∞ :=
  (q .h21 + 1) * (2 ^ 150 : ℝ≥0∞)⁻¹ +
    (q .h22 + 1) * ENNReal.ofReal (Seed.epsQS (2 ^ 128) (2 ^ 64) 3816) +
    (q .h23 + 1) * ((9 : ℝ≥0∞) / 2 ^ 128) +
    (2 * qE ^ 2 * (2 ^ 256)⁻¹ + (openHashEps q + q .h1 * (2 ^ 256 : ℝ≥0∞)⁻¹)) +
    (openHashEps q + q .h1 * (2 ^ 256 : ℝ≥0∞)⁻¹) +
    ((qE * 2 : ℕ) : ℝ≥0∞) * (((512 * q .h1 : ℕ) : ℝ≥0∞) * (2 ^ 256 : ℝ≥0∞)⁻¹) +
    chainHitEps q + stmtBindEps q

/-- **The extraction failure of one unbound redemption proof**
(`moussakaUnboundRedeem_accept_le_adaptive_spec`), `n` the prover's hash queries in all. -/
noncomputable def epsUR (q : Kind → ℕ) (qE n : ℕ) : ℝ≥0∞ :=
  (q .h21 + 1) * (2 ^ 150 : ℝ≥0∞)⁻¹ +
    (q .h22 + 1) * (ENNReal.ofReal (Seed.epsQS (2 ^ 128) (2 ^ 64) 7929) +
      (2 ^ 128 : ℝ≥0∞)⁻¹ + ((n + 2 + verifierTotal : ℕ) : ℝ≥0∞) / 2 ^ 448) +
    (q .h23 + 1) * ((9 : ℝ≥0∞) / 2 ^ 128) +
    (2 * qE ^ 2 * (2 ^ 256)⁻¹ + (openHashEps q + q .h1 * (2 ^ 256 : ℝ≥0∞)⁻¹)) +
    (openHashEps q + q .h1 * (2 ^ 256 : ℝ≥0∞)⁻¹) +
    ((qE * 2 : ℕ) : ℝ≥0∞) * (((512 * q .h1 : ℕ) : ℝ≥0∞) * (2 ^ 256 : ℝ≥0∞)⁻¹) +
    chainHitEpsComb q Arith.Moussaka.M + stmtBindEps q

section Num

variable (lr : Bool) (pk : Fin K → UovPk) (sk : Fin K → Spec.Signer) (qI : ℕ) {A : Adversary K qR}
  {q : Kind → ℕ} {qE n : ℕ}

theorem hinjUI : Function.Injective fun s : ιI =>
    (moussakaUnboundIssue s.1.1 s.1.2 lr).instEnc ByteArray.empty :=
  EndToEnd.SpecRel.hinj_moussakaUnboundIssue lr (fun s : ιI => s.1) 45 (fun s => s.2.1)
    Subtype.val_injective

theorem hinjUR (hdig : ∀ k, (pk k).digest.size = 32)
    (hdinj : Function.Injective fun k => (pk k).digest) :
    Function.Injective fun s : ιR K =>
      (moussakaUnboundRedeem (ancR pk s) s.1.2.1 s.1.2.2.1 s.1.2.2.2.1 s.1.2.2.2.2 lr).instEnc
        ByteArray.empty := by
  refine EndToEnd.SpecRel.hinj_moussakaUnboundRedeem lr (fun s : ιR K => ancR pk s)
    (fun s => s.1.2.1) (fun s => s.1.2.2.1) (fun s => s.1.2.2.2.1) (fun s => s.1.2.2.2.2) ?_ ?_
    24 16 16 (fun s => s.2.2.1) (fun s => s.2.2.2.1) (fun s => s.2.2.2.2) ?_
  · intro s p hp
    obtain ⟨k, -, rfl⟩ := List.mem_map.1 hp
    exact hdig k
  · intro s; simp only [ancR, List.length_map]; have := s.2.1; omega
  · intro s s' h
    simp only [ancR, List.map_map, Prod.mk.injEq] at h
    obtain ⟨h1, h2, h3, h4, h5⟩ := h
    have hl : s.1.1 = s'.1.1 := (List.map_injective_iff.2 hdinj) h1
    exact Subtype.ext (Prod.ext hl (Prod.ext h2 (Prod.ext h3 (Prod.ext h4 h5))))

/-- **Theorem U1 (unforgeability per redemption context), with the extraction terms of the
soundness theorems.** For an adversary within its budget (`A.Budget q qE n`, per stage) and honest
Anchors whose 32-byte key digests are distinct (`hdig`, `hdinj`: the note's `ε_dig` event, a
condition on the keys):

    Pr[Win] ≤ qI·εI(q', q'_E) + qI·εUI(q', q'_E) + qR·εUR(q', q'_E, n')
              + AdvBind(B₁) + AdvCTUF(B₂),

with the provers' budgets `q' = gameK q qI qR`, `q'_E = gameE lr qE qI qR`, `n' = gameH n qI qR`.
`εI` (`OMUF.epsI`, `ε_ext^{iss}`), `εUI` (`ε_ext^{u-iss}`) and `εUR` (`ε_ext^{u-red}`) are the
single-proof bounds of the three relations. -/
theorem omufU_le_num (hA : A.Budget q qE n) (hdig : ∀ k, (pk k).digest.size = 32)
    (hdinj : Function.Injective fun k => (pk k).digest) :
    Pr{let E ← $ᵗ CTable; let r ← (simulateQ randomOracle (runE E (game lr pk sk qI A))).run' ∅}[
        Win r.1] ≤
      qI * epsI (gameK q qI qR) (gameE lr qE qI qR) +
      qI * epsUI (gameK q qI qR) (gameE lr qE qI qR) +
      qR * epsUR (gameK q qI qR) (gameE lr qE qI qR) (gameH n qI qR) +
      Pr{let E ← $ᵗ CTable; let v ← (simulateQ randomOracle (extAll lr pk sk qI A E)).run' ∅}[
        Coll lr pk E v] +
      Pr{let E ← $ᵗ CTable; let v ← (simulateQ randomOracle (extAll lr pk sk qI A E)).run' ∅}[
        Forge lr pk E v] := by
  refine (omufU_le lr pk sk qI A).trans
    (add_le_add (add_le_add (add_le_add (add_le_add ?_ ?_) ?_) le_rfl) le_rfl)
  · refine (Finset.sum_le_card_nsmul _ _ (epsI (gameK q qI qR) (gameE lr qE qI qR))
      fun j _ => ?_).trans (by simp)
    exact moussakaIssue_accept_le_adaptive_spec (ι := ιI) (β := GOut K) (fun s => s.1)
      (fun s => s.2.1) (fun s => s.2.2) lr (hinjI lr) (PBI lr pk sk qI A j) _
      ((isQueryBoundP_map_iff _ _ _).2 (game_e lr pk sk hA qI)) _
      (isKindQueryBoundIC_map _ (game_k lr pk sk hA qI))
  · refine (Finset.sum_le_card_nsmul _ _ (epsUI (gameK q qI qR) (gameE lr qE qI qR))
      fun j _ => ?_).trans (by simp)
    exact moussakaUnboundIssue_accept_le_adaptive_spec (ι := ιI) (β := GOut K) (stUI lr) lr
      (fun s => s.1) (fun s => Unbound.moussakaUnboundIssue_stmt _ _ lr) (fun s => s.2.1)
      (hinjUI lr) (PUI lr pk sk qI A j) _
      ((isQueryBoundP_map_iff _ _ _).2 (game_e lr pk sk hA qI)) _
      (isKindQueryBoundIC_map _ (game_k lr pk sk hA qI))
  · refine (Finset.sum_le_card_nsmul _ _
      (epsUR (gameK q qI qR) (gameE lr qE qI qR) (gameH n qI qR)) fun j _ => ?_).trans (by simp)
    exact moussakaUnboundRedeem_accept_le_adaptive_spec (ι := ιR K) (β := GOut K) (stUR lr pk) lr
      (fun s => ancR pk s) (fun s => by simpa using s.2.1) (fun s => s.1.2.1) (fun s => s.1.2.2.1)
      (fun s => s.1.2.2.2.1) (fun s => s.1.2.2.2.2)
      (fun s => Unbound.moussakaUnboundRedeem_stmt _ _ _ _ _ lr) (fun s => s.2.2.1)
      (hinjUR lr pk hdig hdinj) (PUR lr pk sk qI A j) _
      ((isQueryBoundP_map_iff _ _ _).2 (game_e lr pk sk hA qI)) _
      ((isQueryBoundP_map_iff _ _ _).2 (game_h lr pk sk hA qI)) _
      (isKindQueryBoundIC_map _ (game_k lr pk sk hA qI))

end Num

/-! ## Liveness: the honest checks' lengths are the verifier's proof sizes -/

/-- The unbound issuance request length the Anchor expects is `45` plus the executable verifier's
unbound issuance proof size, on `main` and with label rows. -/
theorem upfLenI_eq (lr : Bool) : upfLenI lr = (Unbound.issueParams lr).proofBytes := by
  cases lr <;> decide

/-- The same for the Moderator's unbound redemption request length. -/
theorem upfLenR_eq (lr : Bool) : upfLenR lr = (Unbound.redeemParams lr).proofBytes := by
  cases lr <;> decide

/-- On `main`, the request lengths are the C++ constants (`UNBOUND_ISSUE_PROOF_BYTES`,
`UNBOUND_REDEEM_PROOF_BYTES`). -/
theorem upfLen_main :
    upfLenI false = Spec.MoussakaUnbound.issueProofBytes ∧
      upfLenR false = Spec.MoussakaUnbound.redeemProofBytes := ⟨rfl, rfl⟩

/-- The Anchor's unbound statement has the unbound issuance parameters. -/
theorem ustmtI_params (lr : Bool) (q : IssQ K) : (ustmtI lr q).params = Unbound.issueParams lr :=
  rfl

/-- The Moderator's statement has the unbound redemption parameters. -/
theorem ustmtR_params (lr : Bool) (pk : Fin K → UovPk) (r : RedQ K) :
    (ustmtR lr pk r).params = Unbound.redeemParams lr := rfl

end VoleMole.ROM.IC.OMUFU
