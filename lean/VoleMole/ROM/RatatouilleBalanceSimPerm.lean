import VoleMole.ROM.MoussakaOMUFSimPerm
import VoleMole.ROM.RatatouilleBalanceSim

/-!
# Ratatouille balance (Theorem 1) with simultaneous extraction, permutation model

`ROM/RatatouilleBalanceSim.lean`'s `balance_le_sim_num` with the ideal cipher as random
permutations and an adversary that makes **forward and inverse** cipher queries
(`ROM/PermModel.lean`). The Issuer verifies forward only.

* `RoundAdvP`: a round adversary of the permutation model; `RoundAdvP.toIC lr π`: the adversary
  at a fixed table, its requests normalized (`normJ`).
* `balQP`: the balance game (the adversary's queries answered by `π`, `runP`); per table it is the
  function game of the adversary at that table (`evalWithAnswerFn_balQP`), so the deterministic
  core (`no_win`) applies.
* `provIP`, `provSP`: the `j`-th provers (the game up to round `j`, then the `j`-th request), of
  the permutation model; their extraction games `gameIP`, `gameSP` run the joint normalization
  `normJ (rataPI lr) (rataPS lr) π` (`ROM/PermJoint.lean`). `fullIP`, `fullSP`: the full run;
  after the joint normalization the provers' logs are prefixes of it (`prefixRuns_IP`,
  `prefixRuns_SP`) and the two relations' reference runs have one hash log.
* `ext_issueP`, `ext_spendP`, **`win_impP`**, **`balance_le_simP`** (the reduction),
  **`prEvent_simIS_leP`** (`ratatouille_sim_joint_specP`), **`balance_le_sim_numP`**,
  **`balance_le_lean_simP`**:

      Pr[win BAL] ≤ ε_bal^simP(q', q'_E, n', N) + forgeAdvP + collAdvP,

  `ε_bal^simP` = `epsBalSim` with the permutation model's failure terms (`failEpsP`) and the
  total hash count `n' + 2q'₂₁`, at the budgets of `balance_le` (`q' = N•(qA + qV)`,
  `q'_E = N(eA + eVR)`, `n' = N(nA + nV)`; `eA` counts forward and inverse cipher queries).
  `forgeAdvP`, `collAdvP` are the forger's and the collision finder's success probabilities in
  the reduction's run (as `forgeAdv`, `collAdv`); they stay terms.
-/

open OracleComp OracleSpec
open scoped ENNReal

namespace VoleMole.ROM.IC.RatBalance

open VoleMole.Prob VoleMole.Verifier VoleMole.Verifier.Bridge VoleMole.ROM VoleMole.ROM.IC
open VoleMole.Spec.Ratatouille VoleMole.EndToEnd VoleMole.ZK.Sim

/-- **A round adversary of the permutation model.** -/
structure RoundAdvP (S Q R : Type) where
  init : S
  next : S → OracleComp specP (Q × S)
  recv : S → R → S

/-! ## Rounds in the permutation model -/

section Rounds

variable {S Q R W : Type} (A : RoundAdvP S Q R) (serve : W → Q → OracleComp specP (R × W))

theorem isKindQueryBoundP_roundsM {qA qS : Kind → ℕ}
    (hA : ∀ s, IsKindQueryBoundP (A.next s) qA) (hS : ∀ w q, IsKindQueryBoundP (serve w q) qS)
    (n : ℕ) (x : S × W × List (Q × R)) :
    IsKindQueryBoundP (roundsM A.next serve A.recv n x) (n • (qA + qS)) := by
  induction n generalizing x with
  | zero => trivial
  | succ n ih =>
    rw [succ_nsmul]
    refine isKindQueryBoundP_bind (ih x) fun y => ?_
    have : IsKindQueryBoundP (roundM A.next serve A.recv y) (qA + (qS + 0)) := by
      unfold roundM
      exact isKindQueryBoundP_bind (hA y.1) fun a =>
        isKindQueryBoundP_bind (hS y.2.1 a.1) fun b => isQueryBound_pure _ _ _ _
    simpa only [add_zero] using this

theorem isQueryBoundP_roundsMP (p : DomP → Prop) [DecidablePred p] {a s : ℕ}
    (hA : ∀ s, IsQueryBoundP (A.next s) p a) (hS : ∀ w q, IsQueryBoundP (serve w q) p s)
    (n : ℕ) (x : S × W × List (Q × R)) :
    IsQueryBoundP (roundsM A.next serve A.recv n x) p (n * (a + s)) := by
  induction n generalizing x with
  | zero => trivial
  | succ n ih =>
    rw [Nat.succ_mul]
    refine isQueryBoundP_bind (ih x) fun y _ => ?_
    have : IsQueryBoundP (roundM A.next serve A.recv y) p (a + (s + 0)) := by
      unfold roundM
      exact isQueryBoundP_bind (hA y.1) fun b _ =>
        isQueryBoundP_bind (hS y.2.1 b.1) fun c _ => isQueryBoundP_pure p _ 0
    simpa only [add_zero] using this

/-- **The `j`-th prover of the permutation model.** -/
def proverAtP {ι β : Type} (w₀ : W) (pick : Q → ByteArray × (ι × β)) (j : ℕ) :
    OracleComp specP (ByteArray × (ι × β)) := do
  let x ← roundsM A.next serve A.recv j (A.init, w₀, [])
  let a ← A.next x.1
  pure (pick a.1)

theorem isKindQueryBoundP_proverAtP {ι β : Type} {qA qS : Kind → ℕ}
    (hA : ∀ s, IsKindQueryBoundP (A.next s) qA) (hS : ∀ w q, IsKindQueryBoundP (serve w q) qS)
    (w₀ : W) (pick : Q → ByteArray × (ι × β)) (j : ℕ) :
    IsKindQueryBoundP (proverAtP A serve w₀ pick j) ((j + 1) • (qA + qS)) := by
  refine IsKindQueryBoundP.mono (q := j • (qA + qS) + (qA + 0)) ?_ ?_
  · unfold proverAtP
    exact isKindQueryBoundP_bind (isKindQueryBoundP_roundsM A serve hA hS j _) fun x =>
      isKindQueryBoundP_bind (q₂ := 0) (hA x.1) fun a => isQueryBound_pure (pick a.1) _ _ _
  · intro k; simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, add_zero, Nat.succ_mul]; omega

theorem isQueryBoundP_proverAtP {ι β : Type} (p : DomP → Prop) [DecidablePred p] {a s : ℕ}
    (hA : ∀ s, IsQueryBoundP (A.next s) p a) (hS : ∀ w q, IsQueryBoundP (serve w q) p s)
    (w₀ : W) (pick : Q → ByteArray × (ι × β)) (j : ℕ) :
    IsQueryBoundP (proverAtP A serve w₀ pick j) p ((j + 1) * (a + s)) := by
  refine IsQueryBoundP.mono (n := j * (a + s) + (a + 0)) ?_ (by rw [Nat.succ_mul]; omega)
  unfold proverAtP
  exact isQueryBoundP_bind (isQueryBoundP_roundsMP A serve p hA hS j _) fun x _ =>
    isQueryBoundP_bind (hA x.1) fun b _ => isQueryBoundP_pure p _ 0

variable (pI pR : Params) (π : PTable)

theorem roundsMP_prefix (f : (d : DomIC) → AnsIC d) (x : S × W × List (Q × R)) {k n : ℕ}
    (hkn : k ≤ n) :
    tableQueryLog (normJ pI pR π (roundsM A.next serve A.recv k x)) f <+:
      tableQueryLog (normJ pI pR π (roundsM A.next serve A.recv n x)) f := by
  induction n with
  | zero => rw [Nat.le_zero.1 hkn]
  | succ n ih =>
    rcases Nat.lt_or_ge k (n + 1) with hk | hk
    · refine (ih (by omega)).trans ?_
      show _ <+: tableQueryLog (normJ pI pR π
        (roundsM A.next serve A.recv n x >>= roundM A.next serve A.recv)) f
      rw [normJ_bind, tableQueryLog_bind]
      exact List.prefix_append _ _
    · rw [show k = n + 1 by omega]

theorem proverAtP_prefix {ι β : Type} (w₀ : W) (pick : Q → ByteArray × (ι × β))
    (f : (d : DomIC) → AnsIC d) {k n : ℕ} (hk : k < n) :
    tableQueryLog (normJ pI pR π (proverAtP A serve w₀ pick k)) f <+:
      tableQueryLog (normJ pI pR π (roundsM A.next serve A.recv n (A.init, w₀, []))) f := by
  refine List.IsPrefix.trans ?_ (roundsMP_prefix A serve pI pR π f _ (Nat.succ_le_of_lt hk))
  show tableQueryLog (normJ pI pR π (roundsM A.next serve A.recv k (A.init, w₀, []) >>= fun x =>
      A.next x.1 >>= fun a => (pure (pick a.1) : OracleComp specP _))) f <+:
    tableQueryLog (normJ pI pR π (roundsM A.next serve A.recv k (A.init, w₀, []) >>=
      roundM A.next serve A.recv)) f
  rw [normJ_bind, normJ_bind]
  simp only [tableQueryLog_bind]
  refine (List.prefix_append_right_inj _).2 ?_
  unfold roundM
  simp only [normJ_bind, tableQueryLog_bind, normJ, addIV_pure, normP_pure, tableQueryLog_pure,
    List.append_nil]
  exact List.prefix_append _ _

end Rounds

variable {Z : Sizes} {S : Type} (lr : Bool) (pkU : UovPk)
  (verQ : Statement → ByteArray → OracleComp specIC Bool)

/-! ## The game in the permutation model -/

/-- **The adversary at a fixed permutation table**: its requests normalized (`normJ`), a round
adversary of the PRF view. -/
def RoundAdvP.toIC (π : PTable) (A : RoundAdvP S (Op Z) Resp) : RoundAdv S (Op Z) Resp :=
  ⟨A.init, fun s => normJ (rataPI lr) (rataPS lr) π (A.next s), A.recv⟩

/-- **The balance game in the permutation model**: the adversary's queries answered by the
random oracle and `π` (forward or inverse), the Issuer verifying with the executable verifier at
the forward table. -/
def balQP (A : RoundAdvP S (Op Z) Resp) (N : ℕ) (σ : Signer) (π : PTable) :
    OracleComp spec (S × IssuerState × List (Op Z × Resp)) :=
  roundsM (fun s => runP π (A.next s))
    (serveM lr pkU (fun st pf => (·.accept) <$> @verifyQ (icPrg π.fwd.cipher) CrtGen.tables st pf)
      σ) A.recv N (A.init, (⟨[]⟩ : IssuerState), [])

theorem nextT_toIC (A : RoundAdvP S (Op Z) Resp) (π : PTable) (g : Table) (s : S) :
    nextT (A.toIC lr π) g π.fwd s = evalWithAnswerFn (QueryImpl.ofFn (joinP g π)) (A.next s) :=
  evalWithAnswerFn_normJ _ _ g π _

/-- Per table, the game is the function game of the adversary at that table. -/
theorem evalWithAnswerFn_balQP (A : RoundAdvP S (Op Z) Resp) (N : ℕ) (σ : Signer) (g : Table)
    (π : PTable) :
    evalWithAnswerFn (QueryImpl.ofFn g) (balQP lr pkU A N σ π) =
      balT lr pkU (A.toIC lr π) N σ g π.fwd :=
  evalWithAnswerFn_roundsM _ _ _ _ _ _
    (fun s => by rw [evalWithAnswerFn_runP, nextT_toIC])
    (evalWithAnswerFn_serveM lr pkU _ _ _ (fun st pf => by
      rw [evalWithAnswerFn_map, @evalWithAnswerFn_verifyQ (icPrg π.fwd.cipher)]; rfl) σ) N _

/-- The Issuer, lifted to the permutation model. -/
def serveL (σ : Signer) (st : IssuerState) (op : Op Z) :
    OracleComp specP (Resp × IssuerState) :=
  liftP (serveM lr pkU verQ σ st op)

/-- **The `j`-th issuance prover of the permutation model.** -/
def provIP (A : RoundAdvP S (Op Z) Resp) (σ : Signer) (j : ℕ) :
    OracleComp specP (ByteArray × (IIdx × Unit)) :=
  proverAtP A (serveL lr pkU verQ σ) (⟨[]⟩ : IssuerState) pickI j

/-- **The `j`-th spend prover of the permutation model.** -/
def provSP (A : RoundAdvP S (Op Z) Resp) (σ : Signer) (j : ℕ) :
    OracleComp specP (ByteArray × (SIdx × Unit)) :=
  proverAtP A (serveL lr pkU verQ σ) (⟨[]⟩ : IssuerState) pickS j

/-- The joint normalization of the Ratatouille relations. -/
abbrev nJ (π : PTable) {α : Type} (P : OracleComp specP α) : OracleComp specIC α :=
  normJ (rataPI lr) (rataPS lr) π P

/-- The extraction game of the `j`-th issuance request (`gameA`, jointly normalized). -/
def gameIP (A : RoundAdvP S (Op Z) Resp) (σ : Signer) (j : ℕ) (π : PTable) :
    OracleComp spec (Out ((IIdx × Unit) × QueryLog specIC)) :=
  gameA CrtGen.tables (stI lr) (nJ lr π (provIP lr pkU verQ A σ j)) π.fwd

/-- The extraction game of the `j`-th spend request. -/
def gameSP (A : RoundAdvP S (Op Z) Resp) (σ : Signer) (j : ℕ) (π : PTable) :
    OracleComp spec (Out ((SIdx × Unit) × QueryLog specIC)) :=
  gameA CrtGen.tables (stS lr pkU) (nJ lr π (provSP lr pkU verQ A σ j)) π.fwd

section PerTable

variable (A : RoundAdvP S (Op Z) Resp) (N : ℕ) (σ : Signer) {qV : Kind → ℕ} {nV : ℕ}
  {eV : Params → ℕ}

theorem proverAtP_eval (hver : VerifierIC CrtGen.tables verQ qV nV eV) (g : Table) (π : PTable)
    {ι β : Type} (pick : Op Z → ByteArray × (ι × β)) (k : ℕ) :
    evalWithAnswerFn (QueryImpl.ofFn (join g π.fwd))
        (nJ lr π (proverAtP A (serveL lr pkU verQ σ) (⟨[]⟩ : IssuerState) pick k)) =
      pick (recG lr pkU (A.toIC lr π) σ g π.fwd k).1 := by
  rw [nJ, evalWithAnswerFn_normJ]
  have hn : ∀ s, evalWithAnswerFn (QueryImpl.ofFn (joinP g π)) (A.next s) =
      nextT (A.toIC lr π) g π.fwd s := fun s => (nextT_toIC lr A π g s).symm
  have hs : ∀ (w : IssuerState) (q : Op Z),
      evalWithAnswerFn (QueryImpl.ofFn (joinP g π)) (serveL lr pkU verQ σ w q) =
      serveP lr pkU (verT g π.fwd) σ w q := fun w q => by
    rw [serveL, evalWithAnswerFn_liftP]
    exact evalWithAnswerFn_serveM lr pkU _ verQ _ (fun st pf => hver.eval g π.fwd st pf) σ w q
  simp only [proverAtP, evalWithAnswerFn_bind, evalWithAnswerFn_roundsM _ A.next _ A.recv _ _ hn hs,
    hn, evalWithAnswerFn_pure]
  rfl

/-- **An accepted issuance whose extraction game does not fail has an extracted witness**
(`ext_issue`, permutation model). -/
theorem ext_issueP (hver : VerifierIC CrtGen.tables verQ qV nV eV) (g : Table) (π : PTable)
    {k : ℕ} {req : IssueRequest Z} {tInit : Credits} {ctx : Context} {s : Preimage}
    (hk : (yG lr pkU (A.toIC lr π) σ g π.fwd N).2.2[k]? =
      some (.issue req tInit ctx, .inl (.ok (some s))))
    (hf : ¬ failI lr π.fwd (evalWithAnswerFn (QueryImpl.ofFn g) (gameIP lr pkU verQ A σ k π))) :
    IssueRel ⟨issueReqC req, tInit, ctx⟩
      (annI lr π.fwd (evalWithAnswerFn (QueryImpl.ofFn g) (gameIP lr pkU verQ A σ k π))) := by
  have hkN : k < N := length_trace lr pkU (A.toIC lr π) N σ g π.fwd ▸ lt_of_getElem? hk
  rw [getElem?_trace _ _ _ _ _ _ _ hkN, Option.some.injEq] at hk
  have hresp := resp_eq lr pkU (verT g π.fwd) σ (nextT (A.toIC lr π) g π.fwd)
    (A.toIC lr π).recv (A.toIC lr π).init k
  obtain ⟨h1, h2, h3⟩ := gameA_out CrtGen.tables (stI lr) (nJ lr π (provIP lr pkU verQ A σ k))
    π.fwd g
  rw [provIP, proverAtP_eval lr pkU verQ A σ hver g π pickI k] at h1 h2 h3
  dsimp only [recG] at h1 h2 h3
  rw [hk] at h1 h2 h3 hresp
  simp only [pickI] at h1 h2 h3
  simp only [serveP, Sum.inl.injEq] at hresp
  have hv := issueResponse_verify hresp.symm
  have hacc : (evalWithAnswerFn (QueryImpl.ofFn g)
      (gameIP lr pkU verQ A σ k π)).2.2.accept = true := by
    rw [gameIP, provIP, h3]; exact hv
  have hext : @Extracted (icPrg π.fwd.cipher) _ (stI lr (stOut (evalWithAnswerFn
      (QueryImpl.ofFn g) (gameIP lr pkU verQ A σ k π)))) (WI (stOut (evalWithAnswerFn
      (QueryImpl.ofFn g) (gameIP lr pkU verQ A σ k π)))) (evalWithAnswerFn (QueryImpl.ofFn g)
      (gameIP lr pkU verQ A σ k π)) := by
    by_contra hne; exact hf ⟨hacc, hne⟩
  have := annI_spec lr π.fwd _ hext
  rw [gameIP, provIP, h2] at this
  exact this

/-- **An accepted spend whose extraction game does not fail has an extracted witness**
(`ext_spend`, permutation model). -/
theorem ext_spendP (hver : VerifierIC CrtGen.tables verQ qV nV eV) (g : Table) (π : PTable)
    {k : ℕ} {req : SpendRequest Z} {ctx : Context} {refund : Credits} {out : SpendResult}
    (hk : (yG lr pkU (A.toIC lr π) σ g π.fwd N).2.2[k]? =
      some (.spend req ctx refund, .inr (.ok (some out))))
    (hf : ¬ failS lr pkU π.fwd
      (evalWithAnswerFn (QueryImpl.ofFn g) (gameSP lr pkU verQ A σ k π))) :
    SpendRel ⟨pkU.map, (SpendReq.parse req).nf, (SpendReq.parse req).d,
        (SpendReq.parse req).cNext, ctx⟩
      (annS lr pkU π.fwd (evalWithAnswerFn (QueryImpl.ofFn g) (gameSP lr pkU verQ A σ k π))) := by
  have hkN : k < N := length_trace lr pkU (A.toIC lr π) N σ g π.fwd ▸ lt_of_getElem? hk
  rw [getElem?_trace _ _ _ _ _ _ _ hkN, Option.some.injEq] at hk
  have hresp := resp_eq lr pkU (verT g π.fwd) σ (nextT (A.toIC lr π) g π.fwd)
    (A.toIC lr π).recv (A.toIC lr π).init k
  obtain ⟨h1, h2, h3⟩ := gameA_out CrtGen.tables (stS lr pkU) (nJ lr π (provSP lr pkU verQ A σ k))
    π.fwd g
  rw [provSP, proverAtP_eval lr pkU verQ A σ hver g π pickS k] at h1 h2 h3
  dsimp only [recG] at h1 h2 h3
  rw [hk] at h1 h2 h3 hresp
  simp only [pickS] at h1 h2 h3
  simp only [serveP, Sum.inr.injEq] at hresp
  have hv := issuerSpend_verify hresp.symm
  have hacc : (evalWithAnswerFn (QueryImpl.ofFn g)
      (gameSP lr pkU verQ A σ k π)).2.2.accept = true := by
    rw [gameSP, provSP, h3]; exact hv
  have hext : @Extracted (icPrg π.fwd.cipher) _ (stS lr pkU (stOut (evalWithAnswerFn
      (QueryImpl.ofFn g) (gameSP lr pkU verQ A σ k π)))) (WS pkU (stOut (evalWithAnswerFn
      (QueryImpl.ofFn g) (gameSP lr pkU verQ A σ k π)))) (evalWithAnswerFn (QueryImpl.ofFn g)
      (gameSP lr pkU verQ A σ k π)) := by
    by_contra hne; exact hf ⟨hacc, hne⟩
  have := annS_spec lr pkU π.fwd _ hext
  rw [gameSP, provSP, h2] at this
  exact this

end PerTable

/-! ## The reduction -/

/-- **The reduction's run in the permutation model**: the game's transcript and, for every round,
the extraction games of its request (jointly normalized provers at the forward table). -/
def masterP (A : RoundAdvP S (Op Z) Resp) (N : ℕ) (σ : Signer) (π : PTable) :
    OracleComp spec (List (Op Z × Resp) × List OutI × List OutS) := do
  let r ← balQP lr pkU A N σ π
  let rIs ← (List.range N).mapM fun k => gameIP lr pkU verQ A σ k π
  let rSs ← (List.range N).mapM fun k => gameSP lr pkU verQ A σ k π
  pure (r.2.2, rIs, rSs)

theorem evalWithAnswerFn_masterP (A : RoundAdvP S (Op Z) Resp) (N : ℕ) (σ : Signer) (g : Table)
    (π : PTable) :
    evalWithAnswerFn (QueryImpl.ofFn g) (masterP lr pkU verQ A N σ π) =
      ((balT lr pkU (A.toIC lr π) N σ g π.fwd).2.2,
        (List.range N).map fun k =>
          evalWithAnswerFn (QueryImpl.ofFn g) (gameIP lr pkU verQ A σ k π),
        (List.range N).map fun k =>
          evalWithAnswerFn (QueryImpl.ofFn g) (gameSP lr pkU verQ A σ k π)) := by
  simp only [masterP, evalWithAnswerFn_bind, evalWithAnswerFn_mapM, evalWithAnswerFn_pure,
    evalWithAnswerFn_balQP]

/-- **`Adv^{uf-tag}` in the permutation model**: the forger's success in the reduction's run. -/
noncomputable def forgeAdvP (A : RoundAdvP S (Op Z) Resp) (N : ℕ) (σ : Signer) : ℝ≥0∞ :=
  Pr{let π ← $ᵗ PTable; let m ← (simulateQ randomOracle (masterP lr pkU verQ A N σ π)).run' ∅}[
    ForgeEv lr pkU π.fwd m]

/-- **`Adv^{coll}_{Com}` in the permutation model**: the collision finder's success. -/
noncomputable def collAdvP (A : RoundAdvP S (Op Z) Resp) (N : ℕ) (σ : Signer) : ℝ≥0∞ :=
  Pr{let π ← $ᵗ PTable; let m ← (simulateQ randomOracle (masterP lr pkU verQ A N σ π)).run' ∅}[
    CollEv lr pkU π.fwd m]

/-- **Per table, a win is an extraction failure, a forgery or a collision** (`win_imp`,
permutation model). -/
theorem win_impP (A : RoundAdvP S (Op Z) Resp) (N : ℕ) (σ : Signer) {qV : Kind → ℕ} {nV : ℕ}
    {eV : Params → ℕ} (hver : VerifierIC CrtGen.tables verQ qV nV eV) (π : PTable) (g : Table)
    (hw : Win (evalWithAnswerFn (QueryImpl.ofFn g) (balQP lr pkU A N σ π)).2.2) :
    (∃ k ∈ Finset.range N,
      failI lr π.fwd (evalWithAnswerFn (QueryImpl.ofFn g) (gameIP lr pkU verQ A σ k π))) ∨
    (∃ k ∈ Finset.range N,
      failS lr pkU π.fwd (evalWithAnswerFn (QueryImpl.ofFn g) (gameSP lr pkU verQ A σ k π))) ∨
    ForgeEv lr pkU π.fwd (evalWithAnswerFn (QueryImpl.ofFn g) (masterP lr pkU verQ A N σ π)) ∨
    CollEv lr pkU π.fwd (evalWithAnswerFn (QueryImpl.ofFn g) (masterP lr pkU verQ A N σ π)) := by
  classical
  by_contra hall
  simp only [not_or, not_exists, not_and, Finset.mem_range] at hall
  obtain ⟨hI, hS, hF, hC⟩ := hall
  rw [evalWithAnswerFn_masterP] at hF hC
  rw [evalWithAnswerFn_balQP] at hw
  have hwI : ∀ k < N, wIof lr π.fwd ((balT lr pkU (A.toIC lr π) N σ g π.fwd).2.2,
      (List.range N).map fun k =>
        evalWithAnswerFn (QueryImpl.ofFn g) (gameIP lr pkU verQ A σ k π),
      (List.range N).map fun k =>
        evalWithAnswerFn (QueryImpl.ofFn g) (gameSP lr pkU verQ A σ k π)) k =
      annI lr π.fwd (evalWithAnswerFn (QueryImpl.ofFn g) (gameIP lr pkU verQ A σ k π)) :=
    fun k hk => by simp [wIof, List.getElem?_map, List.getElem?_range hk]
  have hwS : ∀ k < N, wSof lr pkU π.fwd ((balT lr pkU (A.toIC lr π) N σ g π.fwd).2.2,
      (List.range N).map fun k =>
        evalWithAnswerFn (QueryImpl.ofFn g) (gameIP lr pkU verQ A σ k π),
      (List.range N).map fun k =>
        evalWithAnswerFn (QueryImpl.ofFn g) (gameSP lr pkU verQ A σ k π)) k =
      annS lr pkU π.fwd (evalWithAnswerFn (QueryImpl.ofFn g) (gameSP lr pkU verQ A σ k π)) :=
    fun k hk => by simp [wSof, List.getElem?_map, List.getElem?_range hk]
  refine no_win lr pkU (verT g π.fwd) σ (nextT (A.toIC lr π) g π.fwd) (A.toIC lr π).recv
    (A.toIC lr π).init _ _ N ?_ ?_ hF hC hw
  · intro k req tInit ctx s hk
    have hkN : k < N := length_trace lr pkU (A.toIC lr π) N σ g π.fwd ▸ lt_of_getElem? hk
    rw [hwI k hkN]
    exact ext_issueP lr pkU verQ A N σ hver g π hk (hI k hkN)
  · intro k req ctx refund out hk
    have hkN : k < N := length_trace lr pkU (A.toIC lr π) N σ g π.fwd ▸ lt_of_getElem? hk
    rw [hwS k hkN]
    exact ext_spendP lr pkU verQ A N σ hver g π hk (hS k hkN)

/-- **Theorem 1 (balance) in the permutation model, the reduction, with one simultaneous
extraction event.** -/
theorem balance_le_simP (A : RoundAdvP S (Op Z) Resp) (N : ℕ) (σ : Signer) {qV : Kind → ℕ}
    {nV : ℕ} {eV : Params → ℕ} (hver : VerifierIC CrtGen.tables verQ qV nV eV) :
    Pr{let π ← $ᵗ PTable; let r ← (simulateQ randomOracle (balQP lr pkU A N σ π)).run' ∅}[
        Win r.2.2] ≤
      Pr{let π ← $ᵗ PTable; let m ← (simulateQ randomOracle (masterP lr pkU verQ A N σ π)).run' ∅}[
        SimIS lr pkU π.fwd m] +
      forgeAdvP lr pkU verQ A N σ + collAdvP lr pkU verQ A N σ := by
  have h := prEvent_bind_le_sum4_of_table ($ᵗ PTable) (balQP lr pkU A N σ)
    (fun _ r => Win r.2.2) {0} ∅ (fun _ π => masterP lr pkU verQ A N σ π)
    (fun π m => SimIS lr pkU π.fwd m) (fun _ π => masterP lr pkU verQ A N σ π)
    (fun _ _ => False) (fun π => masterP lr pkU verQ A N σ π)
    (fun π m => ForgeEv lr pkU π.fwd m) (fun π m => CollEv lr pkU π.fwd m) fun π g hw => by
      rcases win_impP lr pkU verQ A N σ hver π g hw with ⟨k, hk, hb⟩ | ⟨k, hk, hb⟩ | hF | hC
      · refine Or.inl ⟨0, Finset.mem_singleton_self 0, Or.inl ?_⟩
        rw [evalWithAnswerFn_masterP]
        exact ⟨_, List.mem_map_of_mem (List.mem_range.2 (Finset.mem_range.1 hk)), hb⟩
      · refine Or.inl ⟨0, Finset.mem_singleton_self 0, Or.inr ?_⟩
        rw [evalWithAnswerFn_masterP]
        exact ⟨_, List.mem_map_of_mem (List.mem_range.2 (Finset.mem_range.1 hk)), hb⟩
      · exact Or.inr (Or.inr (Or.inl hF))
      · exact Or.inr (Or.inr (Or.inr hC))
  simpa only [Finset.sum_singleton, Finset.sum_empty, add_zero, forgeAdvP, collAdvP] using h

/-! ## The bound -/

/-- **The full run of `N` rounds as an issuance prover** (permutation model). -/
def fullIP (A : RoundAdvP S (Op Z) Resp) (N : ℕ) (σ : Signer) :
    OracleComp specP (ByteArray × (IIdx × Unit)) :=
  (fun _ => (ByteArray.empty, (zI, ()))) <$>
    roundsM A.next (serveL lr pkU verQ σ) A.recv N (A.init, (⟨[]⟩ : IssuerState), [])

/-- The full run as a spend prover. -/
def fullSP (A : RoundAdvP S (Op Z) Resp) (N : ℕ) (σ : Signer) :
    OracleComp specP (ByteArray × (SIdx × Unit)) :=
  (fun _ => (ByteArray.empty, (zS, ()))) <$>
    roundsM A.next (serveL lr pkU verQ σ) A.recv N (A.init, (⟨[]⟩ : IssuerState), [])

theorem prefixRuns_IP (A : RoundAdvP S (Op Z) Resp) (N : ℕ) (σ : Signer) (π : PTable) :
    PrefixRuns π.fwd (nJ lr π (fullIP lr pkU verQ A N σ))
      (fun k => nJ lr π (provIP lr pkU verQ A σ k)) (Finset.range N) :=
  prefixRuns_of_joint π.fwd _ _ _ fun k hk g => by
    simp only [nJ, fullIP]
    rw [normJ_map, tableQueryLog_map']
    exact proverAtP_prefix A _ _ _ π _ _ _ (Finset.mem_range.1 hk)

theorem prefixRuns_SP (A : RoundAdvP S (Op Z) Resp) (N : ℕ) (σ : Signer) (π : PTable) :
    PrefixRuns π.fwd (nJ lr π (fullSP lr pkU verQ A N σ))
      (fun k => nJ lr π (provSP lr pkU verQ A σ k)) (Finset.range N) :=
  prefixRuns_of_joint π.fwd _ _ _ fun k hk g => by
    simp only [nJ, fullSP]
    rw [normJ_map, tableQueryLog_map']
    exact proverAtP_prefix A _ _ _ π _ _ _ (Finset.mem_range.1 hk)

/-- **The simultaneous extraction failure of the issuance and spend requests together, in the
permutation model** (`epsBalSim` with `failEpsP` and the total hash count `n + 2q₂₁`). -/
noncomputable def epsBalSimP (qE n : ℕ) (q : Kind → ℕ) (m : ℕ) : ℝ≥0∞ :=
  (q .h21 + (m + m)) * (2 ^ 150 : ℝ≥0∞)⁻¹ +
    (q .h22 + (m + m)) * (ENNReal.ofReal (Seed.epsQS (2 ^ 128) (2 ^ 64) 12282) +
      (2 ^ 128 : ℝ≥0∞)⁻¹ + ((n + 2 * q .h21 + 2 + verifierTotal : ℕ) : ℝ≥0∞) / 2 ^ 448) +
    (q .h23 + (m + m)) * ((9 : ℝ≥0∞) / 2 ^ 128) +
    chainHitEpsCombSim q Arith.Ratatouille.uovM (m + m) + stmtBindEpsSim q (m + m) +
    m * failEpsP q qE + m * failEpsP q qE

section Bounds

variable (A : RoundAdvP S (Op Z) Resp) (N : ℕ) (σ : Signer) {qV : Kind → ℕ} {nV : ℕ}
  {eV : Params → ℕ} (hver : VerifierIC CrtGen.tables verQ qV nV eV) {qA : Kind → ℕ} {nA eA : ℕ}
  (hqA : ∀ s, IsKindQueryBoundP (A.next s) qA)
  (hnA : ∀ s, IsQueryBoundP (A.next s) (fun t => t.isLeft = true) nA)
  (heA : ∀ s, IsQueryBoundP (A.next s) (fun t => t.isRight = true) eA)
include hver hqA hnA heA

/-- The `k`-th prover's budget, `k < N`: at most the budget of `N` rounds. -/
theorem prover_boundsP {ι β : Type} (pick : Op Z → ByteArray × (ι × β)) {k : ℕ} (hk : k < N) :
    IsKindQueryBoundP (proverAtP A (serveL lr pkU verQ σ) (⟨[]⟩ : IssuerState) pick k)
        (N • (qA + qV)) ∧
      IsQueryBoundP (proverAtP A (serveL lr pkU verQ σ) (⟨[]⟩ : IssuerState) pick k)
        (fun t => t.isLeft = true) (N * (nA + nV)) ∧
      IsQueryBoundP (proverAtP A (serveL lr pkU verQ σ) (⟨[]⟩ : IssuerState) pick k)
        (fun t => t.isRight = true) (N * (eA + eVR lr pkU eV)) := by
  refine ⟨?_, ?_, ?_⟩
  · refine (isKindQueryBoundP_proverAtP A _ hqA (fun st op => by
      simpa [serveL] using isKindQueryBoundP_liftP (serveM_kinds lr pkU verQ hver σ st op)) _ pick
      k).mono fun j => ?_
    simp only [Pi.smul_apply, smul_eq_mul]
    exact Nat.mul_le_mul_right _ hk
  · exact (isQueryBoundP_proverAtP A _ _ hnA (fun st op => by
      simpa [serveL] using
        isQueryBoundP_left_liftP (serveM_P lr pkU verQ _ hver.hashes σ st op)) _ pick k).mono
      (Nat.mul_le_mul_right _ hk)
  · exact (isQueryBoundP_proverAtP A _ _ heA (fun st op => by
      simpa [serveL] using
        isQueryBoundP_right_liftP (serveM_cipher lr pkU verQ hver σ st op)) _ pick k).mono
      (Nat.mul_le_mul_right _ hk)

omit heA in
/-- The full run's budget: that of `N` rounds. -/
theorem full_boundsP {ι β : Type} (o : ByteArray × (ι × β)) :
    IsKindQueryBoundP ((fun _ => o) <$> roundsM A.next (serveL lr pkU verQ σ) A.recv N
        (A.init, (⟨[]⟩ : IssuerState), [])) (N • (qA + qV)) ∧
      IsQueryBoundP ((fun _ => o) <$> roundsM A.next (serveL lr pkU verQ σ) A.recv N
        (A.init, (⟨[]⟩ : IssuerState), [])) (fun t => t.isLeft = true) (N * (nA + nV)) := by
  refine ⟨isKindQueryBoundP_map _ ?_, (isQueryBoundP_map_iff _ _ _).2 ?_⟩
  · simpa using isKindQueryBoundP_roundsM A _ hqA (fun st op => by
      simpa [serveL] using isKindQueryBoundP_liftP (serveM_kinds lr pkU verQ hver σ st op)) N
      (A.init, (⟨[]⟩ : IssuerState), [])
  · simpa using isQueryBoundP_roundsMP A _ _ hnA (fun st op => by
      simpa [serveL] using
        isQueryBoundP_left_liftP (serveM_P lr pkU verQ _ hver.hashes σ st op)) N _

/-- **The issuance and spend requests, simultaneously and together, in the permutation model**
(`ratatouille_sim_joint_specP`: the reference runs `fullIP`, `fullSP` are one run). -/
theorem prEvent_simIS_leP (hdig : pkU.digest.size = 32) :
    Pr{let π ← $ᵗ PTable; let m ← (simulateQ randomOracle (masterP lr pkU verQ A N σ π)).run' ∅}[
      SimIS lr pkU π.fwd m] ≤
      epsBalSimP (N * (eA + eVR lr pkU eV)) (N * (nA + nV)) (N • (qA + qV)) N := by
  have h := ratatouille_sim_joint_specP instI (fun s => UInt64.toNat_lt _) lr
    (SpecRel.hinj_ratatouilleIssue_spec (fun i : IIdx => (⟨i.1, i.2.1, i.2.2⟩ : IssueInstance)) lr
      (fun a b h => by simpa [Prod.ext_iff] using h))
    (fun _ => pkU) (fun i : SIdx => bOf i.1)
    (fun i => i.2.1.toNat) (fun i => UInt64.toNat_lt _) (fun i => bOf i.2.2.1)
    (fun i => bOf i.2.2.2)
    (SpecRel.hinj_ratatouilleSpend_spec
      (fun i : SIdx => (⟨pkU.map, i.1, i.2.1, i.2.2.1, i.2.2.2⟩ : SpendInstance)) (fun _ => pkU) lr
      (fun _ => hdig) (fun a b h => by simpa [Prod.ext_iff] using h))
    (fullIP lr pkU verQ A N σ) (provIP lr pkU verQ A σ)
    (fullSP lr pkU verQ A N σ) (provSP lr pkU verQ A σ) (Finset.range N) (Finset.range N) _
    (fun k hk => (prover_boundsP lr pkU verQ A N σ hver hqA hnA heA pickI
      (Finset.mem_range.1 hk)).2.2)
    (fun k hk => (prover_boundsP lr pkU verQ A N σ hver hqA hnA heA pickS
      (Finset.mem_range.1 hk)).2.2) _
    (fun k hk => (prover_boundsP lr pkU verQ A N σ hver hqA hnA heA pickI
      (Finset.mem_range.1 hk)).1)
    (full_boundsP lr pkU verQ A N σ hver hqA hnA _).1
    (fun k hk => (prover_boundsP lr pkU verQ A N σ hver hqA hnA heA pickS
      (Finset.mem_range.1 hk)).1) _
    (fun k hk => (prover_boundsP lr pkU verQ A N σ hver hqA hnA heA pickI
      (Finset.mem_range.1 hk)).2.1)
    (full_boundsP lr pkU verQ A N σ hver hqA hnA _).2
    (fun k hk => (prover_boundsP lr pkU verQ A N σ hver hqA hnA heA pickS
      (Finset.mem_range.1 hk)).2.1)
    (prefixRuns_IP lr pkU verQ A N σ) (prefixRuns_SP lr pkU verQ A N σ)
    (fun π g => by
      rw [fullIP, fullSP]
      exact tableQueryLog_runE_normJ_map _ _ π _ _ _ g)
    (masterP lr pkU verQ A N σ) (fun π m => SimIS lr pkU π.fwd m)
    fun π g hev => by
      rcases hev with ⟨r, hr, hb⟩ | ⟨r, hr, hb⟩
      · rw [evalWithAnswerFn_masterP] at hr
        obtain ⟨k, hk, rfl⟩ := List.mem_map.1 hr
        exact Or.inl ⟨k, Finset.mem_range.2 (List.mem_range.1 hk), hb⟩
      · rw [evalWithAnswerFn_masterP] at hr
        obtain ⟨k, hk, rfl⟩ := List.mem_map.1 hr
        exact Or.inr ⟨k, Finset.mem_range.2 (List.mem_range.1 hk), hb⟩
  simpa only [Finset.card_range, epsBalSimP] using h

end Bounds

/-- **Theorem 1 (balance) with simultaneous extraction, permutation model**, for a
cipher-querying verifier (as `balance_le_sim_num`), against an adversary with forward and inverse
cipher queries:

    Pr[win BAL] ≤ ε_bal^simP(q', q'_E, n', N) + forgeAdvP + collAdvP,

`q' = N•(qA + qV)`, `q'_E = N(eA + eVR)`, `n' = N(nA + nV)`. -/
theorem balance_le_sim_numP (A : RoundAdvP S (Op Z) Resp) (N : ℕ) (σ : Signer)
    (hdig : pkU.digest.size = 32) {qV : Kind → ℕ} {nV : ℕ} {eV : Params → ℕ}
    (hver : VerifierIC CrtGen.tables verQ qV nV eV) {qA : Kind → ℕ} {nA eA : ℕ}
    (hqA : ∀ s, IsKindQueryBoundP (A.next s) qA)
    (hnA : ∀ s, IsQueryBoundP (A.next s) (fun t => t.isLeft = true) nA)
    (heA : ∀ s, IsQueryBoundP (A.next s) (fun t => t.isRight = true) eA) :
    Pr{let π ← $ᵗ PTable; let r ← (simulateQ randomOracle (balQP lr pkU A N σ π)).run' ∅}[
        Win r.2.2] ≤
      epsBalSimP (N * (eA + eVR lr pkU eV)) (N * (nA + nV)) (N • (qA + qV)) N +
        forgeAdvP lr pkU verQ A N σ + collAdvP lr pkU verQ A N σ :=
  (balance_le_simP lr pkU verQ A N σ hver).trans (add_le_add (add_le_add
    (prEvent_simIS_leP lr pkU verQ A N σ hver hqA hnA heA hdig) le_rfl) le_rfl)

/-- **Theorem 1 (balance) with simultaneous extraction, permutation model, no hypothesis on the
verifier** (`verifyIC`, as `balance_le_lean_sim`). -/
theorem balance_le_lean_simP (A : RoundAdvP S (Op Z) Resp) (N : ℕ) (σ : Signer)
    (hdig : pkU.digest.size = 32) {qA : Kind → ℕ} {nA eA : ℕ}
    (hqA : ∀ s, IsKindQueryBoundP (A.next s) qA)
    (hnA : ∀ s, IsQueryBoundP (A.next s) (fun t => t.isLeft = true) nA)
    (heA : ∀ s, IsQueryBoundP (A.next s) (fun t => t.isRight = true) eA) :
    Pr{let π ← $ᵗ PTable; let r ← (simulateQ randomOracle (balQP lr pkU A N σ π)).run' ∅}[
        Win r.2.2] ≤
      epsBalSimP (N * (eA + eVR lr pkU verifyCellBound)) (N * (nA + (2 + verifierTotal)))
          (N • (qA + (extractorQueries + verifierQueries))) N +
        forgeAdvP lr pkU verQL A N σ + collAdvP lr pkU verQL A N σ :=
  balance_le_sim_numP lr pkU verQL A N σ hdig (verifierIC_verifyIC CrtGen.tables) hqA hnA heA

end VoleMole.ROM.IC.RatBalance
