import VoleMole.Assumptions.Blind
import VoleMole.Assumptions.UOVLinks

/-!
# Theorem 6 at PomFRIT: OMPR is at most PomFRIT one-more unforgeability plus completeness

`lean/docs/security/uov-assumptions.md` §5.6 (T6), `lean/docs/security/pomfrit.md` §6.4, G9. The
generic core `Blind.ompr_le_blind` instantiated at PomFRIT's real one-more forgery game.

**The game for a forger with coins** (`gameB`). `Pomfrit.Forger` has no randomness. A `ForgerB`
has coins (a `ProbComp` layer) and its own random oracle `AR` (coins on demand), besides
`Pomfrit.Forger`'s oracles (the hashes and the cipher, `H_T`, the Issuer). `gameB` is
`Pomfrit.game` for it: the composed adversary `AcompB` runs the forger wrapped by `wrapImplB` (its
own oracle forwarded, everything else as `Pomfrit.wrapImpl`), then `Pomfrit.verAll`. The world of
the `OneMore.omuf` instance is the forger's oracle and the hashes (`WB`). For a forger without
coins it is `Pomfrit.game` (`gameB_liftF`: the same win probability).

**The client** (`PomClient`). A PomFRIT client against the hashes and the cipher (`specIC`): coins,
step 1 of session `k` for the message `msgOf k` (the step-1 signature bytes, `chal1`, a state), and
the final signature from the state, the `H_T` answer and the Issuer's response. Session `k`'s
label is `hash_to_target`'s input `tgtIn` for its message (`label`); labels of distinct sessions
are distinct (`label_ne`, from `tgtIn_inj`). The blinding is `0`: the forger is not an honest
client and need not blind, and PomFRIT's relation holds for every witness prefix `r`
(`P(s) = H_T(x) ⊕ r` with `r = 0`).

**The forger** (`blindForger`). From an OMPR adversary `B`: `B`'s coins and the client's; `B`'s
world goes to the forger's random oracle; `B`'s `k`-th target request (`k < n`) is answered by
step 1 of session `k` and the `H_T` answer at its label; `B`'s preimage queries go to the Issuer;
then the claimed sessions are finished with `B`'s preimages. It makes at most as many `H_T`
queries as `B` makes target requests (`blindForger_bound`).

**The reduction to `ompr_le_blind`.** The client as a `Blind.Client` (`toClient`): coins are the
cipher table and the client's coins; its state carried across sessions is the game wrapper's log;
`start` is step 1 with the cipher answered by the table and every query logged (`logImpl`, as
`Pomfrit.wrapImpl` does), followed by the reduction's own queries at the label (`auxSpec`,
logged); `post` finishes the claimed sessions (logged, `finLog`) and runs PomFRIT's verification
of the signatures at the final log (`flagV`: `Pomfrit.verOne`'s decision, `verOneV`). Its labels
are distinct for all keys, coins and logs (`distinct_toClient`). The blind game of
`ompr_le_blind` and `gameB` with the blinding forger have the same key, flag and final state
(`projF_eqd`), because the two composed adversaries have the same flag as oracle computations
(`star`): the forger's handler under the wrapper is `Blind.blindImpl` of `toClient`, with the
wrapper's log as the client's carried state (`collapseU`, `blindB_step`, `fS`), the client's
queries under the wrapper are its logged queries (`wrapB_liftU`, `wrapB_finU`), and the
verifier's decision does not depend on the claim rule (`verOne_snd`).

**Theorems.**
* `pomfrit_T6`: for every OMPR adversary `B`, every client `cl`, every `n`, `ℓ`,

      Adv^{ompr}(B; n, ℓ) ≤ Pr[PomWin(blindForger cl n B)] + compFail,

  `PomWin` in `gameB` (programmed target the `H_T` answer: `addHint` with hint `0`), `compFail`
  the probability that `B`'s claims are `ℓ + 1` preimages of distinct sessions' targets within
  `ℓ` Issuer queries but the client's signatures are not all accepted.
* `pomfrit_T6_bound`: for `B` with at most `Q` target requests, the same with `Adv^{ompr}(B; Q, ℓ)`
  and the game with `Q + ℓ + 1` targets (U1's convention `n = Q_T + ℓ + 1`; `advOMPR_pad`: unused
  targets do not matter).

**Not here.** A bound on `compFail` for the Lean client. It needs the Lean prover's step 1 and
step 2 (`Prover.voleGen`, `Prover.proveCommit`) as oracle computations over `specIC`, equal per
table to the executable prover (hash queries as for `verifyQ`; cipher queries for the full GGM
tree, the leaf commitments, the VOLE expansion and `u_mask`, as `ROM/VerifyIC.lean` does for the
verifier), and completeness in this lazy model: per claimed session, outside `GrindBad` of the
`H₂³` answers at its grinding prefix the verifier accepts (`ZK.Sim.realRun2_complete`), and that
prefix is a function of the run without the `H₂³` answers (`B` never sees them, step 1 does not
read them, and a session's prefix does not depend on the other sessions' grinding), so
`compFail ≤ (ℓ + 1)·2⁻¹¹³`. On paper (`pomfrit.md` G9).

No `sorry`, no `axiom`.
-/

open OracleComp OracleSpec VoleMole.ROM VoleMole.ROM.IC VoleMole.ROM.OneMore
  VoleMole.ROM.OneMore.Pomfrit VoleMole.Assumptions.UOV VoleMole.Assumptions.Blind VoleMole.Verifier
open scoped ENNReal

namespace VoleMole.Assumptions.BlindPomfrit

/-! ## The PomFRIT game for a forger with coins -/

section Game

variable {DR : Type} (AR : DR → Type)

/-- **A forger's oracles with its own random oracle** `AR` (its coins on demand), then those of
`Pomfrit.Forger`: the hashes and the cipher, `hash_to_target`, the Issuer. -/
abbrev specUB : OracleSpec (DR ⊕ (DomIC ⊕ (ByteArray ⊕ TG))) := OracleSpec.ofFn (Sum.elim AR AnsU)

/-- The world of the game: the forger's random oracle and the hashes. -/
abbrev WB : DR ⊕ Dom → Type := WA AR Ans

/-- The composed adversary's oracles. -/
abbrev specCB (Hn : Type) := specA (WB AR) ByteArray Hn TG SIss

/-- **A forger with coins**: from the Issuer's key, coins (`ProbComp`), then an oracle computation
with its own random oracle, the hashes and the cipher, `H_T` and the Issuer, returning
message–signature pairs. `Pomfrit.Forger` is the case without coins (`liftF`). -/
abbrev ForgerB := UovPk → ProbComp (OracleComp (specUB AR) (List (ByteArray × ByteArray)))

variable {AR} {Hn : Type}

/-- The composed adversary of `Pomfrit` (world: the hashes) inside this one. -/
def liftWB : QueryImpl (specC Hn) (OracleComp (specCB AR Hn))
  | .inl d => liftM ((specCB AR Hn).query (.inl (.inr d)))
  | .inr q => liftM ((specCB AR Hn).query (.inr q))

/-- **The wrapper**: the forger's own random oracle forwarded to the world, everything else as
`Pomfrit.wrapImpl` (hashes to the world, the cipher by `E`, both logged; `H_T` with the hint;
the Issuer). -/
def wrapImplB (lr : Bool) (E : CTable) (hint : QueryLog specIC → ByteArray → Hn) :
    QueryImpl (specUB AR) (StateT (QueryLog specIC) (OracleComp (specCB AR Hn)))
  | .inl d => StateT.mk fun L => (fun a => (a, L)) <$>
      (liftM ((specCB AR Hn).query (.inl (.inl d))) : OracleComp (specCB AR Hn) (AR d))
  | .inr q => StateT.mk fun L => simulateQ liftWB ((wrapImpl lr E hint q).run L)

variable (T : CrtTables) (lr : Bool) (E : CTable) (hint : QueryLog specIC → ByteArray → Hn)
  (tgts : TG × Hn → List TG) (pk : UovPk) (ℓ : ℕ)

/-- **The composed adversary** (`Pomfrit.Acomp` for a forger with coins): the forger's run
(wrapped), then, if it output `ℓ + 1` forgeries, their verification and extraction. -/
noncomputable def AcompB (f : OracleComp (specUB AR) (List (ByteArray × ByteArray))) :
    OracleComp (specCB AR Hn) (List (ByteArray × SIss) × Bool) := do
  let r ← (simulateQ (wrapImplB lr E hint) f).run []
  if r.1.length = ℓ + 1 then
    let vs ← simulateQ liftWB (verAll T lr E hint tgts pk r.2 r.1)
    pure (vs.map Prod.fst, decide ((∀ v ∈ vs, v.2 = true) ∧ (r.1.map Prod.fst).Nodup))
  else pure ([], false)

/-- The composed adversary with the cipher table drawn uniformly, then the forger's coins. -/
noncomputable def advCB (F : ForgerB AR) (hint : CTable → QueryLog specIC → ByteArray → Hn)
    (pk : UovPk) : ProbComp (OracleComp (specCB AR Hn) (List (ByteArray × SIss) × Bool)) := do
  let E ← $ᵗ CTable
  let f ← F pk
  pure (AcompB T lr E (hint E) tgts pk ℓ f)

variable [DecidableEq DR] [∀ d, SampleableType (AR d)] {K : Type}
  (KG : ProbComp (UovPk × K)) (pre : K → TG → SIss) (n : ℕ)

/-- **The one-more forgery game for PomFRIT, for a forger with coins** (`Pomfrit.game` with
`ForgerB`): an instance of `OneMore.omuf`, whose world is the forger's random oracle and the
hashes. -/
noncomputable def gameB (F : ForgerB AR) (φ : Hn → TG ≃ TG)
    (hint : CTable → QueryLog specIC → ByteArray → Hn) :=
  omuf KG pre n φ (advCB T lr tgts ℓ F hint)

omit [DecidableEq DR] [∀ d, SampleableType (AR d)] in
/-- **The forger wins** (`Pomfrit.PomWin`): its `ℓ + 1` forgeries verify, on pairwise distinct
messages, after at most `ℓ` Issuer queries. -/
def PomWinB (r : UovPk × (List (ByteArray × SIss) × Bool) × (ByteArray → Option (TG × Hn)) ×
    Ch (WB AR) ByteArray Hn TG) : Prop :=
  r.2.1.2 = true ∧ r.2.2.2.iq ≤ ℓ

end Game

/-! ## A PomFRIT client as an oracle computation -/

section Client

/-- The message of session `k` (pairwise distinct by length). -/
def msgOf (k : ℕ) : ByteArray := ⟨Array.replicate k 0⟩

lemma msgOf_injective : Function.Injective msgOf := by
  intro a b h
  have := congrArg ByteArray.size h
  simpa [msgOf, ByteArray.size] using this

/-- **A PomFRIT client** (signature requester) against the hashes and the cipher: coins, step 1
of session `k` for the message `msgOf k` (the step-1 signature bytes, `chal1`, and a state), and
the final signature from the state, the `H_T` answer and the Issuer's response. The Lean
client is `issue_request` / `finalize_issue` with the prover's hashes and PRG as queries. -/
structure PomClient (Cn St : Type) where
  coins : ProbComp Cn
  start : UovPk → Cn → ℕ → OracleComp specIC (ByteArray × ByteArray × St)
  finish : UovPk → Cn → ℕ → St → TG → SIss → OracleComp specIC ByteArray

/-- **The label of session `k`**: `hash_to_target`'s input (`tgtIn`) for the message `msgOf k`,
the step-1 signature bytes `sig₁` and `chal1` (normalized to their lengths, which the honest
client's already have; this makes labels of distinct sessions distinct, `label_ne`). -/
def label (pk : UovPk) (lr : Bool) (k : ℕ) (sig1 c1 : ByteArray) : ByteArray :=
  tgtIn pk lr (Prover.fit sig1 (pomfritParams lr).proofBytes) (msgOf k) (Prover.fit c1 136)

lemma size_fit (b : ByteArray) (n : ℕ) : (Prover.fit b n).size = n := by
  simp only [Prover.fit, ByteArray.size_extract, ByteArray.size_append, Prover.zeros]
  simp only [ByteArray.size, Array.size_replicate]
  omega

lemma label_ne {pk : UovPk} {lr : Bool} {i j : ℕ} (hij : i ≠ j) (s c s' c' : ByteArray) :
    label pk lr i s c ≠ label pk lr j s' c' := fun h =>
  hij (msgOf_injective (tgtIn_inj (size_fit _ _) (size_fit _ _)
    (by rw [ByteArray.size_extract, size_fit]; omega)
    (by rw [ByteArray.size_extract, size_fit]; omega) h))

/-- The cipher answered by the table `E`. -/
def cellImpl (E : CTable) : QueryImpl specIC (OracleComp spec)
  | .inl d => liftM (spec.query d)
  | .inr x => pure (E x)

/-- A computation against the hashes and the cipher with the cipher answered by `E`. -/
def cellsBy {α : Type} (E : CTable) (oc : OracleComp specIC α) : OracleComp spec α :=
  simulateQ (cellImpl E) oc

end Client

/-! ## The client as a blind-preimage client (`Blind.Client`), and the blinding forger -/

section Inst

variable (T : CrtTables) (lr : Bool) (ℓ : ℕ) {Cn St : Type} (cl : PomClient Cn St)

/-- A hash query of the client's finishing phase (`Blind.specV`). -/
def liftVW : QueryImpl spec (OracleComp (specV Ans ByteArray TG)) := fun d =>
  liftM ((specV Ans ByteArray TG).query (.inl d))

/-- A hash computation in the client's finishing phase. -/
def toV {α : Type} (oa : OracleComp spec α) : OracleComp (specV Ans ByteArray TG) α :=
  simulateQ liftVW oa

/-- The hint `0`. -/
def hint0 : QueryLog specIC → ByteArray → TG := fun _ _ => 0

/-- **The client's queries as the game's wrapper treats them**: the cipher answered by the table
`E`, every hash and cipher query logged (`Pomfrit.wrapImpl`'s first two cases). -/
def logImpl (E : CTable) : QueryImpl specIC (StateT (QueryLog specIC) (OracleComp spec))
  | .inl d => StateT.mk fun L => (fun u => (u, L ++ [⟨.inl d, u⟩])) <$>
      (liftM (spec.query d) : OracleComp spec (Ans d))
  | .inr x => StateT.mk fun L => pure (E x, L ++ [⟨.inr x, E x⟩])

/-- **The verifier's decision on one forgery** (`Pomfrit.verOne`'s flag, with the hint `0`, at the
log `L`; the reduction's queries `auxSpec` and the extractor's queries kept), against the hashes
and `H_T`. -/
noncomputable def verOneV (E : CTable) (pk : UovPk) (L : QueryLog specIC) (msg sig : ByteArray) :
    OracleComp (specV Ans ByteArray TG) Bool := do
  let n := (pomfritParams lr).proofBytes
  let proof := sig.extract 0 n
  let b1 := sig.extract n (n + 32)
  let b2 := sig.extract (n + 32) (n + 64)
  if toBA (Spec.PomFRIT.commitRefresher (toL b2)) != b1 then return false
  let oc1 ← toV (@chal1Pre (VoleMole.ZK.Sim.icPrg E.cipher)
    (pomfritRedeemT pk (fun _ => ByteArray.empty) b1 b2 lr) proof)
  match oc1 with
  | none => return false
  | some c1 =>
    let x := tgtIn pk lr sig msg c1
    let ax ← toV (auxSpec lr L x)
    let ah ← (liftM ((specV Ans ByteArray TG).query (.inr (x, hint0 (L ++ ax) x))) :
      OracleComp (specV Ans ByteArray TG) (TG × TG))
    let _ ← toV (extractIC (pomfritRedeemT pk (fun _ => encT ah.1) b1 b2 lr) E ((proof, ()), L))
    let t ← toV (@verifyQ (VoleMole.ZK.Sim.icPrg E.cipher) T
      (pomfritRedeemT pk (fun _ => encT ah.1) b1 b2 lr) proof)
    pure t.accept

/-- Every forgery's decision, in order. -/
noncomputable def verAllV (E : CTable) (pk : UovPk) (L : QueryLog specIC) :
    List (ByteArray × ByteArray) → OracleComp (specV Ans ByteArray TG) (List Bool)
  | [] => pure []
  | (m, sg) :: rest => do
    let v ← verOneV T lr E pk L m sg
    let vs ← verAllV E pk L rest
    pure (v :: vs)

/-- **The acceptance flag of `Pomfrit.Acomp`** on the signatures `sigs` at the log `L`: there are
`ℓ + 1`, every one verifies, and their messages are pairwise distinct. -/
noncomputable def flagV (E : CTable) (pk : UovPk) (L : QueryLog specIC)
    (sigs : List (ByteArray × ByteArray)) : OracleComp (specV Ans ByteArray TG) Bool :=
  if sigs.length = ℓ + 1 then
    (fun vs => decide ((∀ v ∈ vs, v = true) ∧ (sigs.map Prod.fst).Nodup)) <$>
      verAllV T lr E pk L sigs
  else pure false

/-- The claimed sessions' signatures with the client's queries logged. -/
def finLog (pk : UovPk) (κ : CTable × Cn) (cs : List (ByteArray × TG × (ℕ × St) × TG × SIss)) :
    StateT (QueryLog specIC) (OracleComp spec) (List (ByteArray × ByteArray)) :=
  cs.mapM fun e => (fun sg => (msgOf e.2.2.1.1, sg)) <$>
    simulateQ (logImpl κ.1) (cl.finish pk κ.2 e.2.2.1.1 e.2.2.1.2 e.2.2.2.1 e.2.2.2.2)

/-- **The PomFRIT client as a blind-preimage client** (`Blind.Client`), with the blinding `0`: its
coins are the cipher table and the client's coins; its carried state is the game wrapper's log
(the client's queries and the reduction's own); session `k` is step 1 for `msgOf k` (the cipher
answered by the table, queries logged), labelled by `hash_to_target`'s input, followed by the
reduction's queries at the label (`auxSpec`, logged); the finishing phase makes the signatures of
the claimed sessions (logged) and runs PomFRIT's verification on them at the final log
(`flagV`). -/
noncomputable def toClient :
    Client Ans ByteArray TG SIss (ℕ × St) (CTable × Cn) UovPk (QueryLog specIC) where
  coins := do
    let E ← $ᵗ CTable
    let κ ← cl.coins
    pure (E, κ)
  init := []
  start pk κ L k := do
    let r ← (simulateQ (logImpl κ.1) (cl.start pk κ.2 k)).run L
    let ax ← auxSpec lr r.2 (label pk lr k r.1.1 r.1.2.1)
    pure ((label pk lr k r.1.1 r.1.2.1, (0 : TG), (k, r.1.2.2)), r.2 ++ ax)
  post pk κ L cs := do
    let r ← toV ((finLog cl pk κ cs).run L)
    flagV T lr ℓ κ.1 pk r.2 r.1

/-- **Labels of distinct sessions are distinct** (`Blind.Distinct`), for every key and coins. -/
theorem distinct_toClient (pk : UovPk) (κ : CTable × Cn) :
    Distinct (toClient T lr ℓ cl) pk κ := by
  intro i j hij g a ha g' b hb
  simp only [toClient, mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at ha hb
  obtain ⟨r, -, ax, -, rfl⟩ := ha
  obtain ⟨r', -, ax', -, rfl⟩ := hb
  exact label_ne hij _ _ _ _

variable {DR : Type} {AR : DR → Type}

/-- A client query inside the forger. -/
def liftU : QueryImpl specIC (OracleComp (specUB AR)) := fun d =>
  liftM ((specUB AR).query (.inr (.inl d)))

variable {X' Hn' : Type} [DecidableEq X'] (n : ℕ)

/-- **The blinding forger's handler** of `B`'s queries (as `Blind.blindImpl`, against the
forger's oracles): `B`'s world to the forger's random oracle; `B`'s `k`-th target request
(`k < n`) by step 1 of session `k` and an `H_T` query at its label, whose answer `B` gets; `B`'s
preimage queries to the Issuer. (No carried state: the log is the game's.) -/
def blindImplU (pk : UovPk) (κ : Cn) : QueryImpl (specB AR X' Hn' TG SIss)
    (StateT (BSt ByteArray TG Hn' (ℕ × St) X' Unit) (OracleComp (specUB AR)))
  | .inl d => StateT.mk fun s => (fun a => (a, s)) <$>
      (liftM ((specUB AR).query (.inl d)) : OracleComp (specUB AR) (AR d))
  | .inr (.inl (x', hB)) => StateT.mk fun s =>
      if s.k < n then do
        let o ← (fun o => (label pk lr s.k o.1 o.2.1, (0 : TG), (s.k, o.2.2))) <$>
          simulateQ liftU (cl.start pk κ s.k)
        let a ← (liftM ((specUB AR).query (.inr (.inr (.inl o.1)))) : OracleComp (specUB AR) TG)
        pure (some (a + o.2.1),
          ⟨s.k + 1, Function.update s.ses x' (some ⟨s.k, o.1, o.2.1, o.2.2, a, hB⟩), s.cs⟩)
      else pure (none, s)
  | .inr (.inr t) => StateT.mk fun s => (fun a => (a, s)) <$>
      (liftM ((specUB AR).query (.inr (.inr (.inr t)))) : OracleComp (specUB AR) SIss)

/-- The signatures of the claimed sessions. -/
def finU (pk : UovPk) (κ : Cn) (cs : List (ByteArray × TG × (ℕ × St) × TG × SIss)) :
    OracleComp (specUB AR) (List (ByteArray × ByteArray)) :=
  cs.mapM fun e => (fun sg => (msgOf e.2.2.1.1, sg)) <$>
    simulateQ liftU (cl.finish pk κ e.2.2.1.1 e.2.2.1.2 e.2.2.2.1 e.2.2.2.2)

/-- **The blinding forger** (a `ForgerB`) of an OMPR adversary `B` and the client `cl`: `B`'s
coins and the client's, then `B` with its target requests answered by fresh sessions' `H_T`
answers and its preimage queries by the Issuer, then the claimed sessions' signatures on their
messages. -/
def blindForger (B : UovPk → ProbComp (OracleComp (specB AR X' Hn' TG SIss) (List (X' × SIss)))) :
    ForgerB AR := fun pk => do
  let b ← B pk
  let κ ← cl.coins
  pure do
    let z ← (simulateQ (blindImplU lr cl n pk κ) b).run (bs0 ())
    finU cl pk κ (claimed z)

end Inst

/-! ## The forger in the game is the blind client's forger -/

section Same

/-- A stateless simulation of a stateful handler's run is the run of the simulated handler. -/
theorem simulateQ_run_comm {ι ι' ι'' σ : Type} {sp : OracleSpec ι} {sp' : OracleSpec ι'}
    {sp'' : OracleSpec ι''} (h : QueryImpl sp' (OracleComp sp''))
    (i : QueryImpl sp (StateT σ (OracleComp sp'))) (j : QueryImpl sp (StateT σ (OracleComp sp'')))
    (hij : ∀ q s, simulateQ h ((i q).run s) = (j q).run s) {α : Type} (oa : OracleComp sp α) :
    ∀ s, simulateQ h ((simulateQ i oa).run s) = (simulateQ j oa).run s := by
  induction oa using OracleComp.inductionOn with
  | pure x => intro s; simp
  | query_bind q k ih =>
    intro s
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, hij]
    exact bind_congr fun p => ih p.1 p.2

/-- Two stateful handlers related by a map of states run the same, up to that map. -/
theorem simulateQ_run_fmap {ι ι' σ₁ σ₂ : Type} {sp : OracleSpec ι} {sp' : OracleSpec ι'}
    (i₁ : QueryImpl sp (StateT σ₁ (OracleComp sp'))) (i₂ : QueryImpl sp (StateT σ₂ (OracleComp sp')))
    (f : σ₁ → σ₂) (h : ∀ q s, (i₂ q).run (f s) = (fun r => (r.1, f r.2)) <$> (i₁ q).run s)
    {α : Type} (oa : OracleComp sp α) :
    ∀ s, (simulateQ i₂ oa).run (f s) = (fun r => (r.1, f r.2)) <$> (simulateQ i₁ oa).run s := by
  induction oa using OracleComp.inductionOn with
  | pure x => intro s; simp
  | query_bind q k ih =>
    intro s
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, h, bind_map_left, map_bind]
    exact bind_congr fun p => ih p.1 p.2

variable {DR : Type} {AR : DR → Type} (lr : Bool) (E : CTable)

/-- A hash computation in the composed world. -/
def hashB : QueryImpl spec (OracleComp (specCB AR TG)) := fun d =>
  liftM ((specCB AR TG).query (.inl (.inr d)))

theorem liftWB_toC {α : Type} (oa : OracleComp spec α) :
    simulateQ (liftWB (AR := AR) (Hn := TG)) (toC oa) = simulateQ hashB oa := by
  rw [toC, ← QueryImpl.simulateQ_compose]
  congr 1

theorem liftV_toV {α : Type} (oa : OracleComp spec α) :
    simulateQ (liftV (AR := AR) (S := SIss)) (toV oa) = simulateQ hashB oa := by
  rw [toV, ← QueryImpl.simulateQ_compose]
  congr 1

theorem liftC_eq {α : Type} (oa : OracleComp spec α) :
    simulateQ (liftC (AR := AR) (X := ByteArray) (G := TG) (S := SIss)) oa =
      simulateQ hashB oa := rfl

/-- **The client's queries under the game's wrapper** are its logged queries (`logImpl`). -/
theorem wrapB_liftU {α : Type} (oc : OracleComp specIC α) (L : QueryLog specIC) :
    (simulateQ (wrapImplB (AR := AR) lr E hint0) (simulateQ liftU oc)).run L =
      simulateQ hashB ((simulateQ (logImpl E) oc).run L) := by
  rw [← QueryImpl.simulateQ_compose]
  refine (simulateQ_run_comm hashB (logImpl E) _ (fun q s => ?_) oc L).symm
  rw [QueryImpl.apply_compose]
  simp only [liftU]
  erw [simulateQ_spec_query]
  rcases q with d | x
  · simp only [logImpl, wrapImplB, wrapImpl, StateT.run_mk]
    rfl
  · simp [logImpl, wrapImplB, wrapImpl]

variable {Cn St : Type} (cl : PomClient Cn St) (pk : UovPk) (κ : Cn)

theorem wrapB_finU (cs : List (ByteArray × TG × (ℕ × St) × TG × SIss)) (L : QueryLog specIC) :
    (simulateQ (wrapImplB (AR := AR) lr E hint0) (finU cl pk κ cs)).run L =
      simulateQ hashB ((finLog cl pk (E, κ) cs).run L) := by
  induction cs generalizing L with
  | nil => simp [finU, finLog]
  | cons e cs ih =>
    simp only [finU, finLog, List.mapM_cons, simulateQ_bind, simulateQ_pure,
      StateT.run_bind, StateT.run_pure, bind_map_left]
    rw [wrapB_liftU]
    refine bind_congr fun p => ?_
    have := ih p.2
    simp only [finU, finLog] at this
    rw [this]

end Same

section Ver

variable {DR : Type} {AR : DR → Type} (T : CrtTables) (lr : Bool) (E : CTable)
  (tgts : TG × TG → List TG) (pk : UovPk)

/-- **The verifier's decision on one forgery does not depend on the claim rule.** -/
theorem verOne_snd (L : QueryLog specIC) (m sg : ByteArray) :
    Prod.snd <$> simulateQ (liftWB (AR := AR)) (verOne T lr E hint0 tgts pk L m sg) =
      simulateQ (liftV (AR := AR) (S := SIss)) (verOneV T lr E pk L m sg) := by
  unfold verOne verOneV
  dsimp only
  split_ifs with hc
  · simp
  · simp only [simulateQ_bind, map_bind, liftWB_toC, liftV_toV]
    refine bind_congr fun oc1 => ?_
    cases oc1 with
    | none => simp
    | some c1 =>
      simp only [simulateQ_bind, map_bind, liftWB_toC, liftV_toV, verTail, tQ, auxC]
      refine bind_congr fun ax => ?_
      erw [simulateQ_spec_query]
      refine bind_congr fun a => ?_
      simp only [simulateQ_pure, map_pure]

theorem verAll_snd (L : QueryLog specIC) :
    ∀ outs : List (ByteArray × ByteArray),
      List.map Prod.snd <$> simulateQ (liftWB (AR := AR)) (verAll T lr E hint0 tgts pk L outs) =
        simulateQ (liftV (AR := AR) (S := SIss)) (verAllV T lr E pk L outs)
  | [] => by simp [verAll, verAllV]
  | (m, sg) :: rest => by
    simp only [verAll, verAllV, simulateQ_bind, simulateQ_pure, map_bind, map_pure]
    rw [← verOne_snd T lr E tgts pk L m sg, bind_map_left]
    refine bind_congr fun v => ?_
    rw [← verAll_snd L rest, bind_map_left]
    simp

variable (ℓ : ℕ)

/-- **The composed adversary's flag after the forger's run** is the client's `flagV`. -/
theorem acomp_flag (r : List (ByteArray × ByteArray) × QueryLog specIC) :
    Prod.snd <$> (if r.1.length = ℓ + 1 then do
        let vs ← simulateQ (liftWB (AR := AR)) (verAll T lr E hint0 tgts pk r.2 r.1)
        pure (vs.map Prod.fst, decide ((∀ v ∈ vs, v.2 = true) ∧ (r.1.map Prod.fst).Nodup))
      else pure ([], false)) =
      simulateQ (liftV (AR := AR) (S := SIss)) (flagV T lr ℓ E pk r.2 r.1) := by
  unfold flagV
  split_ifs with h
  · rw [simulateQ_map, ← verAll_snd T lr E tgts pk r.2 r.1, map_bind, Functor.map_map]
    simp only [map_pure]
    rw [← bind_pure_comp]
    refine bind_congr fun vs => ?_
    simp only [pure_inj]
    congr 1
    simp
  · simp

end Ver

/-! ## The two games agree on the forger's flag -/

section Star

variable {DR : Type} {AR : DR → Type} (T : CrtTables) (lr : Bool) (ℓ : ℕ) {Cn St : Type}
  (cl : PomClient Cn St) {X' Hn' : Type} [DecidableEq X'] (n : ℕ) (pk : UovPk) (E : CTable)
  (κ : Cn)

/-- The blinding forger's handler and the game's wrapper as one handler. -/
def combU : QueryImpl (specB AR X' Hn' TG SIss)
    (StateT (BSt ByteArray TG Hn' (ℕ × St) X' Unit × QueryLog specIC) (OracleComp (specCB AR TG))) :=
  fun q => StateT.mk fun p => (fun r => (r.1.1, (r.1.2, r.2))) <$>
    (simulateQ (wrapImplB lr E hint0) ((blindImplU lr cl n pk κ q).run p.1)).run p.2

theorem collapseU {α : Type} (oa : OracleComp (specB AR X' Hn' TG SIss) α)
    (s : BSt ByteArray TG Hn' (ℕ × St) X' Unit) (L : QueryLog specIC) :
    (simulateQ (wrapImplB lr E hint0) ((simulateQ (blindImplU lr cl n pk κ) oa).run s)).run L =
      (fun r => ((r.1, r.2.1), r.2.2)) <$> (simulateQ (combU lr cl n pk E κ) oa).run (s, L) := by
  refine simulateQ_StateT_StateT_compose _ _ _ (fun q s c => ?_) oa s L
  show _ = _ <$> ((fun r : (_ × _) × _ => (r.1.1, (r.1.2, r.2))) <$> _)
  rw [Functor.map_map]
  exact (id_map _).symm

omit [DecidableEq X'] in
lemma wrapB_ht (x : ByteArray) (L : QueryLog specIC) :
    (wrapImplB (AR := AR) lr E hint0 (.inr (.inr (.inl x)))).run L = (do
      let ax ← simulateQ hashB (auxSpec lr L x)
      (fun a => (a.1, L ++ ax)) <$>
        (liftM ((specCB AR TG).query (.inr (.inl (x, 0)))) : OracleComp (specCB AR TG) (TG × TG))) := by
  simp only [wrapImplB, wrapImpl, auxC, StateT.run_mk, hint0]
  erw [simulateQ_bind, liftWB_toC]
  refine bind_congr fun ax => ?_
  erw [simulateQ_map, simulateQ_spec_query]
  rfl

omit [DecidableEq X'] in
lemma assoc_aux {ι α β γ δ : Type} {sp : OracleSpec ι} (X : OracleComp sp α) (Q : OracleComp sp β)
    (F : α → β → γ) (f : α → β → δ) (G : δ → OracleComp sp γ) (h : ∀ x a, G (f x a) = pure (F x a)) :
    (X >>= fun x => Q >>= fun a => pure (F x a)) = (X >>= fun x => f x <$> Q) >>= G := by
  simp [bind_assoc, bind_map_left, h]

/-- The blind client's forger state: the game's log as the carried state. -/
def fS (p : BSt ByteArray TG Hn' (ℕ × St) X' Unit × QueryLog specIC) :
    BSt ByteArray TG Hn' (ℕ × St) X' (QueryLog specIC) :=
  ⟨p.1.k, p.1.ses, p.2⟩

theorem blindB_step (q : DR ⊕ ((X' × Hn') ⊕ TG))
    (p : BSt ByteArray TG Hn' (ℕ × St) X' Unit × QueryLog specIC) :
    (blindImpl (AR := AR) (toClient T lr ℓ cl) n pk (E, κ) q).run (fS p) =
      (fun r => (r.1, fS r.2)) <$> (combU lr cl n pk E κ q).run p := by
  rcases q with d | ⟨x', hB⟩ | t
  · simp only [combU, blindImplU, blindImpl, StateT.run_mk, Functor.map_map]
    erw [simulateQ_map, StateT.run_map, Functor.map_map]
  · by_cases hk : p.1.k < n
    · have hk' : (fS p).k < n := hk
      simp only [combU, blindImplU, blindImpl, hk, hk', ite_true, StateT.run_mk, simulateQ_bind,
        StateT.run_bind, wrapB_liftU, toClient, liftC_eq,
        map_bind, bind_map_left, bind_assoc, Functor.map_map]
      simp only [fS, simulateQ_pure, pure_bind]
      refine bind_congr fun r => ?_
      erw [simulateQ_spec_query, wrapB_ht]
      exact assoc_aux _ _ _ _ _ fun _ _ => rfl
    · have hk' : ¬ (fS p).k < n := hk
      simp [combU, blindImplU, blindImpl, hk, hk']
  · simp only [combU, blindImplU, blindImpl, StateT.run_mk, Functor.map_map]
    erw [simulateQ_map, StateT.run_map, Functor.map_map]

variable (tgts : TG × TG → List TG)

/-- **(★) The forger's flag in the PomFRIT game is the blind client's**: for every cipher table
`E`, client coins `κ` and run `b` of `B`, the composed adversary of the blinding forger and the
blinding forger of `Blind` (with the client `toClient`) have the same flag, as oracle
computations. -/
theorem star (b : OracleComp (specB AR X' Hn' TG SIss) (List (X' × SIss))) :
    Prod.snd <$> AcompB T lr E hint0 tgts pk ℓ (do
        let z ← (simulateQ (blindImplU lr cl n pk κ) b).run (bs0 ())
        finU cl pk κ (claimed z)) =
      Prod.snd <$> (do
        let z ← (simulateQ (blindImpl (toClient T lr ℓ cl) n pk (E, κ)) b).run
          (bs0 (toClient T lr ℓ cl).init)
        let f ← simulateQ liftV ((toClient T lr ℓ cl).post pk (E, κ) z.2.cs (claimed z))
        pure ((claimed z).map fun e => (e.1, e.2.2.2.2), f)) := by
  rw [AcompB, map_bind]
  simp only [acomp_flag]
  have e0 : (bs0 (toClient T lr ℓ cl).init : BSt ByteArray TG Hn' (ℕ × St) X' _) =
      fS (bs0 (), []) := rfl
  rw [e0, simulateQ_run_fmap _ _ fS (fun q s => blindB_step T lr ℓ cl n pk E κ q s) b,
    simulateQ_bind, StateT.run_bind, collapseU, bind_map_left, bind_assoc]
  simp only [map_bind, bind_map_left, map_pure, bind_pure]
  refine bind_congr fun r => ?_
  rw [wrapB_finU]
  simp only [toClient, simulateQ_bind, liftV_toV]
  rfl

end Star

/-! ## Theorem 6 at PomFRIT -/

section T6

variable {DR : Type} [DecidableEq DR] {AR : DR → Type} [∀ d, SampleableType (AR d)]
  (T : CrtTables) (lr : Bool) (ℓ : ℕ) {Cn St : Type} (cl : PomClient Cn St) {X' Hn' : Type}
  [DecidableEq X'] (n : ℕ) {K : Type} (KG : ProbComp (UovPk × K)) (pre : K → TG → SIss)
  (tgts : TG × TG → List TG)
  (B : UovPk → ProbComp (OracleComp (specB AR X' Hn' TG SIss) (List (X' × SIss))))

/-- The one-more game's key, flag and final state. -/
def projF {α Y : Type} (r : UovPk × (α × Bool) × Y) : UovPk × Bool × Y := (r.1, r.2.1.2, r.2.2)

lemma omuf_projF
    (A : UovPk → ProbComp (OracleComp (specCB AR TG) (List (ByteArray × SIss) × Bool))) :
    projF <$> omuf KG pre n addHint A = (do
      let kp ← KG
      let a ← (fun a => Prod.snd <$> a) <$> A kp.1
      let L ← unifList TG n
      let r ← (simulateQ (realImpl addHint (pre kp.2)) a).run (fun _ => none, ch0 L)
      pure (kp.1, r.1, r.2)) := by
  simp only [omuf, map_bind, map_pure, bind_map_left, simulateQ_map, StateT.run_map, projF]

/-- **The blind client's game and the PomFRIT game of the blinding forger have the same key, flag
and final state.** -/
theorem projF_eqd :
    projF <$> omuf KG pre n addHint (blindAdv (toClient T lr ℓ cl) n B) =ᵈ
      projF <$> gameB T lr tgts ℓ KG pre n (blindForger lr cl n B) addHint (fun _ => hint0) := by
  rw [gameB, omuf_projF, omuf_projF]
  refine EvalDistEq.bind_right _ fun kp => ?_
  refine EvalDistEq.bind_left ?_ _
  simp only [blindAdv, advCB, blindForger, map_bind, map_pure, bind_assoc, pure_bind,
    star T lr ℓ cl n kp.1 _ _ tgts]
  have hc : (toClient T lr ℓ cl).coins = (do
      let E ← $ᵗ CTable
      let κ ← cl.coins
      pure (E, κ)) := rfl
  simp only [hc, bind_assoc, pure_bind]
  exact eqd_swap _ _ _

/-- **The completeness failure** (`Blind.ompr_le_blind`'s `CompFail` for the client `cl`): `B`'s
`ℓ + 1` claims are preimages (`relP`) of the targets of distinct sessions' labels after at most
`ℓ` Issuer queries, but the client's signatures on those sessions' messages do not all pass
PomFRIT's verification (`flagV`). -/
noncomputable def compFail : ℝ≥0∞ :=
  Pr{let r ← omuf KG pre n addHint (blindAdv (toClient T lr ℓ cl) n B)}[
    Wins ℓ (goodPre relP) r.1 r.2.1.1 r.2.2.2 ∧ r.2.1.2 = false]

/-- **Theorem 6 at PomFRIT** (`uov-assumptions.md` §5.6, `pomfrit.md` G9): for every OMPR
adversary `B` (`n` targets, `ℓ` preimage queries) and every PomFRIT client `cl`, the blinding
forger `blindForger lr cl n B` wins PomFRIT's one-more forgery game (`gameB`, programmed target
the `H_T` answer) with

    Adv^{ompr}(B; n, ℓ) ≤ Pr[PomWin] + Pr[CompFail],

`CompFail` (`compFail`) the client's completeness failure on `B`'s winning runs. -/
theorem pomfrit_T6 :
    advOMPR (Links.pomTrap KG pre) n ℓ B ≤
      Pr{let r ← gameB T lr tgts ℓ KG pre n (blindForger lr cl n B) addHint (fun _ => hint0)}[
        PomWinB ℓ r] + compFail T lr ℓ cl n KG pre B := by
  refine (ompr_le_blind (Links.pomTrap KG pre) (toClient T lr ℓ cl) n ℓ B
    fun pk κ _ => distinct_toClient T lr ℓ cl pk κ).trans (add_le_add ?_ le_rfl)
  refine (prEvent_mono _ _ (fun r => r.2.1.2 = true ∧ r.2.2.2.iq ≤ ℓ)
    fun r h => ⟨h.1, h.2.2.2⟩).trans (le_of_eq ?_)
  have h := (projF_eqd T lr ℓ cl n KG pre tgts B).prEvent_eq
    (fun t => t.2.1 = true ∧ t.2.2.2.iq ≤ ℓ)
  rw [prEvent_map, prEvent_map] at h
  exact h

end T6

/-! ## `gameB` extends `Pomfrit.game`: a forger without coins -/

section Lift

variable {DR : Type} [DecidableEq DR] {AR : DR → Type} [∀ d, SampleableType (AR d)] {Hn : Type}

/-- A query of a `Pomfrit.Forger` as one of a `ForgerB`. -/
def liftUB : QueryImpl specU (OracleComp (specUB AR)) := fun q =>
  liftM ((specUB AR).query (.inr q))

/-- **A forger without coins** (`Pomfrit.Forger`) as a `ForgerB` that ignores its random oracle. -/
def liftF (A : Forger) : ForgerB AR := fun pk => pure (simulateQ liftUB (A pk))

variable (T : CrtTables) (lr : Bool) (E : CTable) (hint : QueryLog specIC → ByteArray → Hn)
  (tgts : TG × Hn → List TG) (pk : UovPk) (ℓ : ℕ)

omit [DecidableEq DR] [∀ d, SampleableType (AR d)] in
theorem acompB_liftF (A : Forger) :
    AcompB (AR := AR) T lr E hint tgts pk ℓ (simulateQ liftUB (A pk)) =
      simulateQ liftWB (Acomp T lr E hint tgts pk ℓ A) := by
  have h : ∀ L, (simulateQ (wrapImplB (AR := AR) lr E hint) (simulateQ liftUB (A pk))).run L =
      simulateQ liftWB ((simulateQ (wrapImpl lr E hint) (A pk)).run L) := fun L => by
    rw [← QueryImpl.simulateQ_compose]
    refine (simulateQ_run_comm liftWB (wrapImpl lr E hint) _ (fun q s => ?_) (A pk) L).symm
    rw [QueryImpl.apply_compose]
    simp only [liftUB]
    erw [simulateQ_spec_query]
    rfl
  rw [AcompB, Acomp, h, simulateQ_bind]
  refine bind_congr fun r => ?_
  split_ifs <;> simp

/-- The hashes' part of the composed world's cache. -/
def resR (c : (specR (WB AR)).QueryCache) : (specR Ans).QueryCache :=
  QueryCache.ofFn fun d => c (.inr d)

omit [∀ d, SampleableType (AR d)] in
lemma resR_cacheQuery_inr (c : (specR (WB AR)).QueryCache) (d : Dom) (u : Ans d) :
    resR (c.cacheQuery (.inr d) u) = (resR c).cacheQuery d u := by
  refine QueryCache.ext fun d' => ?_
  show (c.cacheQuery (.inr d) u) (.inr d') = ((resR c).cacheQuery d u) d'
  by_cases h : d' = d
  · subst h
    erw [QueryCache.cacheQuery_self, QueryCache.cacheQuery_self]
    rfl
  · show Function.update c.toFn (.inr d) (some u) (.inr d') =
      Function.update (resR c).toFn d (some u) d'
    rw [Function.update_of_ne (by simpa using h), Function.update_of_ne h]
    rfl

/-- **The hashes in the composed world are the hashes**: a query at `inr d`, restricted to the
hashes' part of the cache. -/
lemma roR (c : (specR (WB AR)).QueryCache) (d : Dom) :
    (fun r => (r.1, resR r.2)) <$> ((specR (WB AR)).randomOracle (.inr d)).run c =
      (((specR Ans).randomOracle d).run (resR c) : ProbComp (Ans d × (specR Ans).QueryCache)) := by
  rw [randomOracle.run_eq, randomOracle.run_eq]
  have h' : (resR c) d = c (.inr d) := rfl
  rw [h']
  cases h : c (.inr d) with
  | some u => simp
  | none =>
    simp only [map_bind, map_pure]
    show ($ᵗ (Ans d)) >>= (fun a => pure (a, resR (c.cacheQuery (Sum.inr d) a))) = _
    congr 1
    funext a
    rw [resR_cacheQuery_inr]

/-- The projection of the composed world's game state onto `Pomfrit.game`'s. -/
def piR (s : (ByteArray → Option (TG × Hn)) × Ch (WB AR) ByteArray Hn TG) :
    (ByteArray → Option (TG × Hn)) × Ch Ans ByteArray Hn TG :=
  (s.1, ⟨resR s.2.ro, s.2.rest, s.2.tg, s.2.iq⟩)

theorem liftWB_step (φ : Hn → TG ≃ TG) (pre : TG → SIss) (q : Dom ⊕ ((ByteArray × Hn) ⊕ TG))
    (s : (ByteArray → Option (TG × Hn)) × Ch (WB AR) ByteArray Hn TG) :
    (fun z => (z.1, piR z.2)) <$> ((realImpl φ pre ∘ₛ liftWB (AR := AR) (Hn := Hn)) q).run s =ᵈ
      (realImpl φ pre q).run (piR s) := by
  rw [QueryImpl.apply_compose]
  rcases q with d | ⟨x, h⟩ | t
  · simp only [liftWB]
    erw [simulateQ_spec_query]
    show (fun z => (z.1, piR z.2)) <$> ((fun r => (r.1, (s.1, r.2))) <$>
        roStep (AR := WB AR) (X := ByteArray) (Hn := Hn) (G := TG) (Sum.inr d) s.2) =ᵈ
      (fun r => (r.1, ((piR s).1, r.2))) <$> roStep d (piR s).2
    simp only [roStep, Functor.map_map]
    erw [← roR (AR := AR) s.2.ro d, Functor.map_map]
    exact EvalDistEq.rfl
  · simp only [liftWB]
    erw [simulateQ_spec_query]
    simp only [realImpl, StateT.run_mk, piR]
    cases hx : s.1 x with
    | some a => simp [hx]
    | none => cases hr : s.2.rest <;> simp [hx, hr]
  · simp only [liftWB]
    erw [simulateQ_spec_query]
    simp [realImpl, piR]

variable {K : Type} (KG : ProbComp (UovPk × K)) (pre : K → TG → SIss) (n : ℕ)

/-- **For a forger without coins, `gameB` is `Pomfrit.game`**: the same win probability. -/
theorem gameB_liftF (A : Forger) (φ : Hn → TG ≃ TG)
    (hint : CTable → QueryLog specIC → ByteArray → Hn) :
    Pr{let r ← gameB (AR := AR) T lr tgts ℓ KG pre n (liftF A) φ hint}[PomWinB ℓ r] =
      Pr{let r ← Pomfrit.game KG pre n ℓ T lr A φ hint tgts}[PomWin ℓ r] := by
  have hE : (fun r => (r.1, r.2.1, piR r.2.2)) <$>
      gameB (AR := AR) T lr tgts ℓ KG pre n (liftF A) φ hint =ᵈ
        Pomfrit.game KG pre n ℓ T lr A φ hint tgts := by
    simp only [gameB, Pomfrit.game, omuf, advCB, advC, liftF, map_bind, map_pure, bind_assoc, pure_bind,
      acompB_liftF]
    refine EvalDistEq.bind_right _ fun kp => EvalDistEq.bind_right _ fun E =>
      EvalDistEq.bind_right _ fun L => ?_
    have h0 : piR (AR := AR) ((fun _ => none : ByteArray → Option (TG × Hn)), ch0 L) =
        ((fun _ => none), ch0 L) := by
      simp only [piR, ch0]
      congr 2
    have := (LazyIdeal.simulateQ_proj_eqd_inv (realImpl φ (pre kp.2) ∘ₛ liftWB (AR := AR))
      (realImpl φ (pre kp.2)) piR (fun _ => True) (fun _ _ _ _ _ => trivial)
      (fun q s _ => liftWB_step φ (pre kp.2) q s) (Acomp T lr E (hint E) tgts kp.1 ℓ A)
      ((fun _ => none), ch0 L) trivial).bind_left (fun z => pure (kp.1, z.1, z.2))
    rw [h0, QueryImpl.simulateQ_compose] at this
    simpa only [bind_map_left] using this
  rw [← hE.prEvent_eq, prEvent_map]
  rfl

end Lift

/-! ## Padding the target stream of the experiment -/

section Pad

variable {DR : Type} [DecidableEq DR] {AR : DR → Type} [∀ d, SampleableType (AR d)]
  {X : Type} [DecidableEq X] {Hn G S : Type} [AddCommGroup G] [SampleableType G]

omit [AddCommGroup G] in
lemma unifList_add (m : ℕ) : ∀ Q : ℕ,
    unifList G (Q + m) = (do
      let L ← unifList G Q
      let L' ← unifList G m
      pure (L ++ L'))
  | 0 => by simp [unifList]
  | Q + 1 => by
    rw [show Q + 1 + m = (Q + m) + 1 by omega]
    simp only [unifList, unifList_add m Q, bind_assoc, pure_bind, List.cons_append]

omit [AddCommGroup G] [SampleableType G] in
/-- **Unused targets do not matter**: an adversary with at most `k ≤ |stream|` target requests
runs the same on a longer stream, the extra targets left over. -/
theorem chImpl_pad (pre : G → S) (L' : List G) {α : Type}
    (b : OracleComp (specB AR X Hn G S) α) :
    ∀ (k : ℕ) (c : Ch AR X Hn G), IsQueryBoundP b (fun q => isTgt q = true) k →
      k ≤ c.rest.length →
      (simulateQ (chImpl pre) b).run { c with rest := c.rest ++ L' } =
        (fun z => (z.1, { z.2 with rest := z.2.rest ++ L' })) <$> (simulateQ (chImpl pre) b).run c := by
  induction b using OracleComp.inductionOn with
  | pure x => intro k c _ _; simp
  | query_bind q cont ih =>
    intro k c hq hk
    rw [isQueryBoundP_query_bind_iff] at hq
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, map_bind]
    rcases q with d | ⟨x, h⟩ | t
    · have e : ∀ c' : Ch AR X Hn G, (chImpl (S := S) pre (.inl d)).run c' = roStep d c' :=
        fun _ => rfl
      rw [e, e]
      simp only [roStep]
      erw [bind_map_left, bind_map_left]
      refine bind_congr fun r => ?_
      exact ih r.1 k { c with ro := r.2 } (hq.2 r.1) hk
    · have hk0 : 0 < k := hq.1.resolve_left (by simp [isTgt])
      cases hr : c.rest with
      | nil => rw [hr] at hk; simp at hk; omega
      | cons u r =>
        simp only [chImpl, StateT.run_mk, hr, List.cons_append, pure_bind]
        have := ih (some u) (k - 1) { c with rest := r, tg := Function.update c.tg x (some (u, h)) }
          (hq.2 (some u)) (by rw [hr] at hk; simp at hk ⊢; omega)
        exact this
    · simp only [chImpl, StateT.run_mk, pure_bind]
      exact ih _ k { c with iq := c.iq + 1 } (hq.2 _) hk

variable {PK K : Type} (KG : ProbComp (PK × K)) (pre : K → G → S)

omit [AddCommGroup G] in
/-- **Padding the stream**: for an adversary making at most `Q` target requests, the experiment
with `Q + m` targets has the same distribution of key, claims, labelled targets and preimage
count as with `Q`. -/
theorem omExp_pad (Q m : ℕ) (B : PK → ProbComp (OracleComp (specB AR X Hn G S) (List (X × S))))
    (hB : ∀ pk, ∀ b ∈ support (B pk), IsQueryBoundP b (fun q => isTgt q = true) Q) :
    (fun r => (r.1, r.2.1, r.2.2.tg, r.2.2.iq)) <$> omExp KG pre (Q + m) B =ᵈ
      (fun r => (r.1, r.2.1, r.2.2.tg, r.2.2.iq)) <$> omExp KG pre Q B := by
  simp only [omExp, map_bind, map_pure, unifList_add m Q, bind_assoc, pure_bind]
  refine EvalDistEq.bind_right _ fun kp => EvalDistEq.bind_congr_of_support _ fun b hb => ?_
  refine EvalDistEq.bind_congr_of_support _ fun L hL => ?_
  have hlen := length_of_mem_unifList Q L hL
  have hpad : ∀ L', (simulateQ (chImpl (pre kp.2)) b).run (ch0 (L ++ L')) =
      (fun z => (z.1, { z.2 with rest := z.2.rest ++ L' })) <$>
        (simulateQ (chImpl (pre kp.2)) b).run (ch0 L) := fun L' =>
    chImpl_pad (pre kp.2) L' b Q (ch0 L) (hB kp.1 b hb) (by simp [ch0, hlen])
  simp only [hpad, bind_map_left]
  exact UOV.bind_unused _ _

omit [DecidableEq DR] [∀ d, SampleableType (AR d)] [DecidableEq X] [AddCommGroup G]
  [SampleableType G] in
lemma wins_congr (ℓ : ℕ) (good : PK → S → Option (G × Hn) → Prop) (pk : PK) (cl : List (X × S))
    (c c' : Ch AR X Hn G) (h1 : c.tg = c'.tg) (h2 : c.iq = c'.iq) :
    Wins ℓ good pk cl c ↔ Wins ℓ good pk cl c' := by
  simp only [Wins, h1, h2]

omit [AddCommGroup G] in
/-- **`Adv^{ompr}` does not depend on unused targets.** -/
theorem advOMPR_pad {SK : Type} (tr : Trapdoor PK SK G S) (Q m ℓ : ℕ)
    (B : PK → ProbComp (OracleComp (specB AR X Hn G S) (List (X × S))))
    (hB : ∀ pk, ∀ b ∈ support (B pk), IsQueryBoundP b (fun q => isTgt q = true) Q) :
    advOMPR tr (Q + m) ℓ B = advOMPR tr Q ℓ B := by
  have h := (omExp_pad tr.keyGen tr.D Q m B hB).prEvent_eq
    (fun t => t.2.1.length = ℓ + 1 ∧ (t.2.1.map Prod.fst).Nodup ∧ t.2.2.2 ≤ ℓ ∧
      ∀ p ∈ t.2.1, goodPre tr.IsPre t.1 p.2 (t.2.2.1 p.1))
  rw [prEvent_map, prEvent_map] at h
  exact h

end Pad

/-! ## The blinding forger's `H_T` queries -/

section Bound

variable {DR : Type} {AR : DR → Type}

/-- An `H_T` query of a `ForgerB`. -/
def isHTB : DR ⊕ (DomIC ⊕ (ByteArray ⊕ TG)) → Bool
  | .inr (.inr (.inl _)) => true
  | _ => false

lemma liftU_bound {α : Type} (oc : OracleComp specIC α) :
    IsQueryBoundP (simulateQ (liftU (AR := AR)) oc) (fun q => isHTB q = true) 0 := by
  induction oc using OracleComp.inductionOn with
  | pure x => trivial
  | query_bind t k ih =>
    simp only [simulateQ_bind, simulateQ_spec_query, liftU]
    erw [isQueryBoundP_query_bind_iff]
    exact ⟨Or.inl (by simp [isHTB]), fun u => ih u⟩

lemma mapM_bound {β γ : Type} (f : β → OracleComp (specUB AR) γ)
    (hf : ∀ b, IsQueryBoundP (f b) (fun q => isHTB q = true) 0) :
    ∀ l : List β, IsQueryBoundP (l.mapM f) (fun q => isHTB q = true) 0
  | [] => trivial
  | b :: l => by
    rw [List.mapM_cons]
    exact isQueryBoundP_bind (n := 0) (m := 0) (hf b) fun _ _ =>
      isQueryBoundP_bind (n := 0) (m := 0) (mapM_bound f hf l) fun _ _ => isQueryBoundP_pure _ _ _

variable (lr : Bool) {Cn St : Type} (cl : PomClient Cn St) {X' Hn' : Type} [DecidableEq X'] (n : ℕ)
  (pk : UovPk) (κ : Cn)

lemma blindU_bound {α : Type} (b : OracleComp (specB AR X' Hn' TG SIss) α) :
    ∀ (k : ℕ) (s : BSt ByteArray TG Hn' (ℕ × St) X' Unit),
      IsQueryBoundP b (fun q => isTgt q = true) k →
        IsQueryBoundP ((simulateQ (blindImplU lr cl n pk κ) b).run s) (fun q => isHTB q = true) k := by
  induction b using OracleComp.inductionOn with
  | pure x => intro k s _; trivial
  | query_bind q cont ih =>
    intro k s hq
    rw [isQueryBoundP_query_bind_iff] at hq
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
    rcases q with d | ⟨x', hB⟩ | t
    · have h2 : ∀ u, IsQueryBoundP (cont u) (fun q => isTgt q = true) k := hq.2
      refine (isQueryBoundP_bind (n := 0) (m := k) ?_ fun p _ => ih p.1 k p.2 (h2 p.1)).mono
        (by omega)
      exact (isQueryBoundP_map_iff _ _ _).2 ((isQueryBoundP_query_iff _ _ _).2 (by simp [isHTB]))
    · have h2 : ∀ u, IsQueryBoundP (cont u) (fun q => isTgt q = true) (k - 1) := hq.2
      have hk : 0 < k := hq.1.resolve_left (by simp [isTgt])
      refine (isQueryBoundP_bind (n := 1) (m := k - 1) ?_ fun p _ =>
        ih p.1 (k - 1) p.2 (h2 p.1)).mono (by omega)
      simp only [blindImplU, StateT.run_mk]
      split_ifs
      · refine (isQueryBoundP_bind (n := 0) (m := 1)
          ((isQueryBoundP_map_iff _ _ _).2 (liftU_bound _)) fun o _ => ?_).mono (by omega)
        refine (isQueryBoundP_bind (n := 1) (m := 0) ?_ fun _ _ => isQueryBoundP_pure _ _ _)
        exact (isQueryBoundP_query_iff _ _ _).2 fun _ => Nat.one_pos
      · exact isQueryBoundP_pure _ _ _
    · have h2 : ∀ u, IsQueryBoundP (cont u) (fun q => isTgt q = true) k := hq.2
      refine (isQueryBoundP_bind (n := 0) (m := k) ?_ fun p _ => ih p.1 k p.2 (h2 p.1)).mono
        (by omega)
      exact (isQueryBoundP_map_iff _ _ _).2 ((isQueryBoundP_query_iff _ _ _).2 (by simp [isHTB]))

/-- **The blinding forger makes at most `Q` `H_T` queries** if `B` makes at most `Q` target
requests: one per served request; the client's steps make none. -/
theorem blindForger_bound (Q : ℕ)
    (B : UovPk → ProbComp (OracleComp (specB AR X' Hn' TG SIss) (List (X' × SIss))))
    (hB : ∀ pk, ∀ b ∈ support (B pk), IsQueryBoundP b (fun q => isTgt q = true) Q) :
    ∀ f ∈ support (blindForger lr cl n B pk), IsQueryBoundP f (fun q => isHTB q = true) Q := by
  intro f hf
  simp only [blindForger, mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hf
  obtain ⟨b, hb, κ, -, rfl⟩ := hf
  refine (isQueryBoundP_bind (n := Q) (m := 0) (blindU_bound lr cl n pk κ b Q (bs0 ()) (hB pk b hb))
    fun z _ => ?_).mono (by omega)
  exact mapM_bound _ (fun e => (isQueryBoundP_map_iff _ _ _).2 (liftU_bound _)) _

end Bound

/-! ## Theorem 6 at PomFRIT with `B`'s target budget -/

section T6Bound

variable {DR : Type} [DecidableEq DR] {AR : DR → Type} [∀ d, SampleableType (AR d)]
  (T : CrtTables) (lr : Bool) (ℓ Q : ℕ) {Cn St : Type} (cl : PomClient Cn St) {X' Hn' : Type}
  [DecidableEq X'] {K : Type} (KG : ProbComp (UovPk × K)) (pre : K → TG → SIss)
  (tgts : TG × TG → List TG)
  (B : UovPk → ProbComp (OracleComp (specB AR X' Hn' TG SIss) (List (X' × SIss))))

/-- **Theorem 6 at PomFRIT, with `B`'s target budget**: for an OMPR adversary `B` with at most
`Q` target requests, `Adv^{ompr}(B; Q, ℓ)` is at most the win probability of the blinding forger
(which makes at most `Q` `H_T` queries, `blindForger_bound`) in PomFRIT's one-more forgery game
with `Q + ℓ + 1` targets (U1's `n = Q_T + ℓ + 1`: the game's target oracle is a random oracle,
`OneMore.noFall_of_bound`) plus the client's completeness failure. -/
theorem pomfrit_T6_bound
    (hB : ∀ pk, ∀ b ∈ support (B pk), IsQueryBoundP b (fun q => isTgt q = true) Q) :
    advOMPR (Links.pomTrap KG pre) Q ℓ B ≤
      Pr{let r ← gameB T lr tgts ℓ KG pre (Q + (ℓ + 1)) (blindForger lr cl (Q + (ℓ + 1)) B)
          addHint (fun _ => hint0)}[PomWinB ℓ r] +
        compFail T lr ℓ cl (Q + (ℓ + 1)) KG pre B := by
  rw [← advOMPR_pad (Links.pomTrap KG pre) Q (ℓ + 1) ℓ B hB]
  exact pomfrit_T6 T lr ℓ cl (Q + (ℓ + 1)) KG pre tgts B

end T6Bound

end VoleMole.Assumptions.BlindPomfrit
