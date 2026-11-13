import VoleMole.Assumptions.Blind
import VoleMole.Assumptions.UOVLinks

/-!
# Theorem 6 at PomFRIT: OMPR is at most PomFRIT one-more unforgeability plus completeness

WIP.
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
def wrapImplB (E : CTable) (hint : QueryLog specIC → ByteArray → Hn) :
    QueryImpl (specUB AR) (StateT (QueryLog specIC) (OracleComp (specCB AR Hn)))
  | .inl d => StateT.mk fun L => (fun a => (a, L)) <$>
      (liftM ((specCB AR Hn).query (.inl (.inl d))) : OracleComp (specCB AR Hn) (AR d))
  | .inr q => StateT.mk fun L => simulateQ liftWB ((wrapImpl E hint q).run L)

variable (T : CrtTables) (lr : Bool) (E : CTable) (hint : QueryLog specIC → ByteArray → Hn)
  (tgts : TG × Hn → List TG) (pk : UovPk) (ℓ : ℕ)

/-- **The composed adversary** (`Pomfrit.Acomp` for a forger with coins): the forger's run
(wrapped), then, if it output `ℓ + 1` forgeries, their verification and extraction. -/
noncomputable def AcompB (f : OracleComp (specUB AR) (List (ByteArray × ByteArray))) :
    OracleComp (specCB AR Hn) (List (ByteArray × SIss) × Bool) := do
  let r ← (simulateQ (wrapImplB E hint) f).run []
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

lemma bind_const_congr {α β γ : Type} {ι : Type} {sp : OracleSpec ι} (X : OracleComp sp α)
    (Y : OracleComp sp β) (K : OracleComp sp γ)
    (h : (fun _ => ()) <$> X = (fun _ => ()) <$> Y) : (X >>= fun _ => K) = (Y >>= fun _ => K) := by
  have h1 : (X >>= fun _ => K) = ((fun _ => ()) <$> X) >>= fun _ => K := by rw [bind_map_left]
  rw [h1, h, bind_map_left]

/-- **The verifier's decision on one forgery** (`Pomfrit.verOne`'s flag, with the hint `0` and
the empty log; the extractor's queries kept), against the hashes and `H_T`. -/
noncomputable def verOneV (E : CTable) (pk : UovPk) (msg sig : ByteArray) :
    OracleComp (specV Ans ByteArray TG) Bool := do
  let n := (pomfritParams lr).proofBytes
  let proof := sig.extract 0 n
  let b1 := sig.extract n (n + 32)
  let b2 := sig.extract (n + 32) (n + 64)
  if toBA (Spec.PomFRIT.commitRefresher (toL b2)) != b1 then return false
  let oc1 ← toV (chal1Pre (pomfritRedeemT pk (fun _ => ByteArray.empty) b1 b2 lr) proof)
  match oc1 with
  | none => return false
  | some c1 =>
    let x := tgtIn pk lr sig msg c1
    let ah ← (liftM ((specV Ans ByteArray TG).query (.inr (x, 0))) :
      OracleComp (specV Ans ByteArray TG) (TG × TG))
    let _ ← toV (extractIC (pomfritRedeemT pk (fun _ => encT ah.1) b1 b2 lr) E ((proof, ()), []))
    let t ← toV (@verifyQ (VoleMole.ZK.Sim.icPrg E.cipher) T
      (pomfritRedeemT pk (fun _ => encT ah.1) b1 b2 lr) proof)
    pure t.accept

/-- Every forgery's decision, in order. -/
noncomputable def verAllV (E : CTable) (pk : UovPk) :
    List (ByteArray × ByteArray) → OracleComp (specV Ans ByteArray TG) (List Bool)
  | [] => pure []
  | (m, sg) :: rest => do
    let v ← verOneV T lr E pk m sg
    let vs ← verAllV E pk rest
    pure (v :: vs)

/-- **The acceptance flag of `Pomfrit.Acomp`** on the signatures `sigs`: there are `ℓ + 1`, every
one verifies, and their messages are pairwise distinct. -/
noncomputable def flagV (E : CTable) (pk : UovPk) (sigs : List (ByteArray × ByteArray)) :
    OracleComp (specV Ans ByteArray TG) Bool :=
  if sigs.length = ℓ + 1 then
    (fun vs => decide ((∀ v ∈ vs, v = true) ∧ (sigs.map Prod.fst).Nodup)) <$>
      verAllV T lr E pk sigs
  else pure false

/-- **The PomFRIT client as a blind-preimage client** (`Blind.Client`), with the blinding `0`:
its coins are the cipher table and the client's coins; session `k` is step 1 for `msgOf k` (the
cipher answered by the table), labelled by `hash_to_target`'s input; the finishing phase makes
the signatures of the claimed sessions and runs PomFRIT's verification on them (`flagV`). -/
noncomputable def toClient : Client Ans ByteArray TG SIss (ℕ × St) (CTable × Cn) UovPk where
  coins := do
    let E ← $ᵗ CTable
    let κ ← cl.coins
    pure (E, κ)
  start pk κ k := (fun o => (label pk lr k o.1 o.2.1, (0 : TG), (k, o.2.2))) <$>
    cellsBy κ.1 (cl.start pk κ.2 k)
  post pk κ cs := do
    let sigs ← cs.mapM fun e => (fun sg => (msgOf e.2.2.1.1, sg)) <$>
      toV (cellsBy κ.1 (cl.finish pk κ.2 e.2.2.1.1 e.2.2.1.2 e.2.2.2.1 e.2.2.2.2))
    flagV T lr ℓ κ.1 pk sigs

/-- **Labels of distinct sessions are distinct** (`Blind.Distinct`), for every key and coins. -/
theorem distinct_toClient (pk : UovPk) (κ : CTable × Cn) :
    Distinct (toClient T lr ℓ cl) pk κ := by
  intro i j hij a ha b hb
  simp only [toClient, support_map, Set.mem_image] at ha hb
  obtain ⟨o, -, rfl⟩ := ha
  obtain ⟨o', -, rfl⟩ := hb
  exact label_ne hij _ _ _ _

variable {DR : Type} {AR : DR → Type}

/-- A client query inside the forger. -/
def liftU : QueryImpl specIC (OracleComp (specUB AR)) := fun d =>
  liftM ((specUB AR).query (.inr (.inl d)))

variable {X' Hn' : Type} [DecidableEq X'] (n : ℕ)

/-- **The blinding forger's handler** of `B`'s queries (as `Blind.blindImpl`, against the
forger's oracles): `B`'s world to the forger's random oracle; `B`'s `k`-th target request
(`k < n`) by step 1 of session `k` and an `H_T` query at its label, whose answer `B` gets; `B`'s
preimage queries to the Issuer. -/
def blindImplU (pk : UovPk) (κ : Cn) : QueryImpl (specB AR X' Hn' TG SIss)
    (StateT (BSt ByteArray TG Hn' (ℕ × St) X') (OracleComp (specUB AR)))
  | .inl d => StateT.mk fun s => (fun a => (a, s)) <$>
      (liftM ((specUB AR).query (.inl d)) : OracleComp (specUB AR) (AR d))
  | .inr (.inl (x', hB)) => StateT.mk fun s =>
      if s.k < n then do
        let o ← (fun o => (label pk lr s.k o.1 o.2.1, (0 : TG), (s.k, o.2.2))) <$>
          simulateQ liftU (cl.start pk κ s.k)
        let a ← (liftM ((specUB AR).query (.inr (.inr (.inl o.1)))) : OracleComp (specUB AR) TG)
        pure (some (a + o.2.1),
          ⟨s.k + 1, Function.update s.ses x' (some ⟨s.k, o.1, o.2.1, o.2.2, a, hB⟩)⟩)
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
    let z ← (simulateQ (blindImplU lr cl n pk κ) b).run bs0
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

theorem simulateQ_mapM {ι ι' β γ : Type} {sp : OracleSpec ι} {sp' : OracleSpec ι'}
    (h : QueryImpl sp (OracleComp sp')) (f : β → OracleComp sp γ) :
    ∀ l : List β, simulateQ h (l.mapM f) = l.mapM fun b => simulateQ h (f b)
  | [] => by simp
  | b :: l => by simp [List.mapM_cons, simulateQ_mapM h f l]

variable {DR : Type} {AR : DR → Type} (E : CTable)

/-- The hint `0`. -/
def hint0 : QueryLog specIC → ByteArray → TG := fun _ _ => 0

/-- The wrapper with the hint `0`, without its log. -/
def wrap0 : QueryImpl (specUB AR) (OracleComp (specCB AR TG))
  | .inl d => liftM ((specCB AR TG).query (.inl (.inl d)))
  | .inr (.inl (.inl d)) => liftM ((specCB AR TG).query (.inl (.inr d)))
  | .inr (.inl (.inr x)) => pure (E x)
  | .inr (.inr (.inl x)) => Prod.fst <$>
      (liftM ((specCB AR TG).query (.inr (.inl (x, 0)))) : OracleComp (specCB AR TG) (TG × TG))
  | .inr (.inr (.inr t)) => liftM ((specCB AR TG).query (.inr (.inr t)))

lemma wrapB_step (q : DR ⊕ (DomIC ⊕ (ByteArray ⊕ TG))) (L : QueryLog specIC) :
    Prod.fst <$> (wrapImplB (AR := AR) E hint0 q).run L = wrap0 E q := by
  rcases q with d | (d | x) | (x | t)
  · simp [wrapImplB, wrap0]
  · simp [wrapImplB, wrapImpl, wrap0]
    rfl
  · simp [wrapImplB, wrapImpl, wrap0]
  · simp [wrapImplB, wrapImpl, wrap0, hint0]
    rfl
  · simp [wrapImplB, wrapImpl, wrap0]
    rfl

/-- **With the hint `0` the wrapper's log is write-only.** -/
theorem wrapB_fst {α : Type} (oc : OracleComp (specUB AR) α) :
    ∀ L, Prod.fst <$> (simulateQ (wrapImplB E hint0) oc).run L = simulateQ (wrap0 E) oc := by
  induction oc using OracleComp.inductionOn with
  | pure x => intro L; simp
  | query_bind q k ih =>
    intro L
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, map_bind]
    rw [← wrapB_step E q L, bind_map_left]
    exact bind_congr fun p => ih p.1 p.2

/-- The client's oracle with the cipher answered by `E`, in the composed world. -/
def icB : QueryImpl specIC (OracleComp (specCB AR TG))
  | .inl d => liftM ((specCB AR TG).query (.inl (.inr d)))
  | .inr x => pure (E x)

theorem wrap0_liftU {α : Type} (oc : OracleComp specIC α) :
    simulateQ (wrap0 (AR := AR) E) (simulateQ liftU oc) = simulateQ (icB E) oc := by
  rw [← QueryImpl.simulateQ_compose]
  congr 1
  funext q
  rw [QueryImpl.apply_compose]
  simp only [liftU]
  erw [simulateQ_spec_query]
  rcases q with d | x <;> rfl

theorem liftC_cellsBy {α : Type} (oc : OracleComp specIC α) :
    simulateQ (liftC (AR := AR) (X := ByteArray) (G := TG) (S := SIss)) (cellsBy E oc) =
      simulateQ (icB E) oc := by
  rw [cellsBy, ← QueryImpl.simulateQ_compose]
  congr 1
  funext q
  rcases q with d | x
  · simp [QueryImpl.apply_compose, liftC, cellImpl, icB]
  · simp [QueryImpl.apply_compose, cellImpl, icB]

theorem liftV_toV_cellsBy {α : Type} (oc : OracleComp specIC α) :
    simulateQ (liftV (AR := AR) (S := SIss)) (toV (cellsBy E oc)) = simulateQ (icB E) oc := by
  rw [toV, cellsBy, ← QueryImpl.simulateQ_compose, ← QueryImpl.simulateQ_compose]
  congr 1
  funext q
  rcases q with d | x
  · rw [QueryImpl.apply_compose]
    simp only [cellImpl]
    erw [simulateQ_spec_query, QueryImpl.apply_compose]
    simp only [liftVW]
    erw [simulateQ_spec_query]
    rfl
  · simp [QueryImpl.apply_compose, cellImpl, icB]

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

end Same

section Ver

variable {DR : Type} {AR : DR → Type} (T : CrtTables) (lr : Bool) (E : CTable)
  (tgts : TG × TG → List TG) (pk : UovPk)

/-- The extractor's queries do not depend on the log. -/
lemma extractIC_unit {β : Type} (st : Statement) (p : ByteArray) (b : β) (L L' : QueryLog specIC) :
    (fun _ => ()) <$> extractIC st E ((p, b), L) = (fun _ => ()) <$> extractIC st E ((p, b), L') := by
  simp [extractIC, map_bind]

/-- **The verifier's decision on one forgery does not depend on the log or the claim rule.** -/
theorem verOne_snd (L : QueryLog specIC) (m sg : ByteArray) :
    Prod.snd <$> simulateQ (liftWB (AR := AR)) (verOne T lr E hint0 tgts pk L m sg) =
      simulateQ (liftV (AR := AR) (S := SIss)) (verOneV T lr E pk m sg) := by
  unfold verOne verOneV
  dsimp only
  split_ifs with hc
  · simp
  · simp only [simulateQ_bind, map_bind, liftWB_toC, liftV_toV]
    refine bind_congr fun oc1 => ?_
    cases oc1 with
    | none => simp
    | some c1 =>
      simp only [simulateQ_bind, map_bind, liftWB_toC, liftV_toV, verTail, tQ, hint0]
      erw [simulateQ_spec_query]
      refine bind_congr fun a => ?_
      simp only [simulateQ_pure, map_pure]
      refine bind_const_congr _ _ _ ?_
      rw [← simulateQ_map, ← simulateQ_map, extractIC_unit]

theorem verAll_snd (L : QueryLog specIC) :
    ∀ outs : List (ByteArray × ByteArray),
      List.map Prod.snd <$> simulateQ (liftWB (AR := AR)) (verAll T lr E hint0 tgts pk L outs) =
        simulateQ (liftV (AR := AR) (S := SIss)) (verAllV T lr E pk outs)
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
      simulateQ (liftV (AR := AR) (S := SIss)) (flagV T lr ℓ E pk r.1) := by
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

theorem blindU_step (q : DR ⊕ ((X' × Hn') ⊕ TG)) (s : BSt ByteArray TG Hn' (ℕ × St) X') :
    simulateQ (wrap0 (AR := AR) E) ((blindImplU lr cl n pk κ q).run s) =
      (blindImpl (AR := AR) (X' := X') (Hn' := Hn') (toClient T lr ℓ cl) n pk (E, κ) q).run s := by
  rcases q with d | ⟨x', hB⟩ | t
  · simp only [blindImplU, blindImpl, StateT.run_mk]
    erw [simulateQ_map, simulateQ_spec_query]
    rfl
  · by_cases hk : s.k < n
    · simp only [blindImplU, blindImpl, hk, ite_true, StateT.run_mk, simulateQ_bind,
        simulateQ_map, wrap0_liftU, toClient, liftC_cellsBy]
      simp only [bind_map_left]
      refine bind_congr fun o => ?_
      erw [simulateQ_spec_query]
      simp only [wrap0, simulateQ_pure]
      rfl
    · simp [blindImplU, blindImpl, hk]
  · simp only [blindImplU, blindImpl, StateT.run_mk]
    erw [simulateQ_map, simulateQ_spec_query]
    rfl

theorem finU_eq (cs : List (ByteArray × TG × (ℕ × St) × TG × SIss)) :
    simulateQ (wrap0 (AR := AR) E) (finU cl pk κ cs) =
      simulateQ (liftV (AR := AR) (S := SIss)) (cs.mapM fun e => (fun sg => (msgOf e.2.2.1.1, sg)) <$>
        toV (cellsBy E (cl.finish pk κ e.2.2.1.1 e.2.2.1.2 e.2.2.2.1 e.2.2.2.2))) := by
  rw [finU, simulateQ_mapM, simulateQ_mapM]
  congr 1
  funext e
  rw [simulateQ_map, simulateQ_map, wrap0_liftU, liftV_toV_cellsBy]

variable (tgts : TG × TG → List TG)

/-- **(★) The forger's flag in the PomFRIT game is the blind client's**: for every cipher table
`E`, client coins `κ` and run `b` of `B`, the composed adversary of the blinding forger and the
blinding forger of `Blind` (with the client `toClient`) have the same flag, as oracle
computations. -/
theorem star (b : OracleComp (specB AR X' Hn' TG SIss) (List (X' × SIss))) :
    Prod.snd <$> AcompB T lr E hint0 tgts pk ℓ (do
        let z ← (simulateQ (blindImplU lr cl n pk κ) b).run bs0
        finU cl pk κ (claimed z)) =
      Prod.snd <$> (do
        let z ← (simulateQ (blindImpl (toClient T lr ℓ cl) n pk (E, κ)) b).run bs0
        let f ← simulateQ liftV ((toClient T lr ℓ cl).post pk (E, κ) (claimed z))
        pure ((claimed z).map fun e => (e.1, e.2.2.2.2), f)) := by
  rw [AcompB, map_bind]
  simp only [acomp_flag]
  have h1 : ∀ (x : OracleComp (specCB AR TG) (List (ByteArray × ByteArray) × QueryLog specIC)),
      (x >>= fun r => simulateQ (liftV (AR := AR) (S := SIss)) (flagV T lr ℓ E pk r.1)) =
        (Prod.fst <$> x) >>= fun a => simulateQ liftV (flagV T lr ℓ E pk a) := fun x => by
    rw [bind_map_left]
  rw [h1, wrapB_fst, simulateQ_bind,
    simulateQ_run_comm _ _ _ (blindU_step T lr ℓ cl n pk E κ) b bs0, bind_assoc]
  simp only [map_bind, map_pure, bind_pure]
  refine bind_congr fun z => ?_
  rw [finU_eq]
  simp only [toClient, simulateQ_bind]

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
  have h : ∀ L, (simulateQ (wrapImplB (AR := AR) E hint) (simulateQ liftUB (A pk))).run L =
      simulateQ liftWB ((simulateQ (wrapImpl E hint) (A pk)).run L) := fun L => by
    rw [← QueryImpl.simulateQ_compose]
    refine (simulateQ_run_comm liftWB (wrapImpl E hint) _ (fun q s => ?_) (A pk) L).symm
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

end VoleMole.Assumptions.BlindPomfrit
