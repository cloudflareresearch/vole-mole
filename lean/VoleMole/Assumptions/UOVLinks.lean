import VoleMole.Assumptions.UOV
import VoleMole.ROM.MoussakaOMUF
import VoleMole.ROM.RatatouilleBalance
import VoleMole.ROM.OneMorePomfrit
import VoleMole.Spec.PqovScale

/-!
# The protocol theorems' UOV terms as advantages in the standalone games

`lean/docs/security/uov-assumptions.md` §3, §10. The three protocol reductions bound a winning
adversary's probability by an assumption term; here each term is an advantage in a game of
`Assumptions/UOV.lean`, of an explicit adversary.

* **Ratatouille** (`RatBalance.balance_le_ufTag`): `ufTagAdv pk σ B` is the advantage of `B`
  (reassociated, `ratForger`) in UF-Tag with a signability probe (`ufTagAdv_eq`), the hash
  `Tag(c, x)`, the verification `uovEval pk s = Tag(c, x)`. Corollary `balance_le_ufTagProbe`.
* **PomFRIT** (`Pomfrit.pomfrit_U1_bound`, `pomfrit_U2_bound`): the experiment term is
  `advOMPR` (resp. `advOMPRShift τ`) of the trapdoor `pomTrap KG pre` (the key generation, `relP`,
  the Issuer), by definition (`pomfrit_U1_ompr`, `pomfrit_U2_omprShift`).
* **Moussaka** (`OMUF.omuf_le_num`): its last term `Pr[Forge]` (the CT-UF event of the protocol
  game) is replaced by the CT-UF^open advantage of an explicit forger `ctufForger` against the
  honest Anchors' signers (`omuf_le_open`, `omuf_le_num_open`). The forger runs the OMUF game and
  every extraction with the signers as an oracle (`reads`: its output depends on them only at the
  accepted Issue queries `(k, t)`, its signing log, `game_congr`), and outputs the forgery
  `(k, x*, s*)` of `Forge` and, for every signed target, an extracted issuance opening. When an
  accepted issuance proof is not extracted the opening may be missing; that case is already a term
  of the bound (`BadI`), so the bound is not weakened: a win is a failed extraction, a collision,
  or a CT-UF^open win (`win_imp_open`).
* **CT-UF is false for UOV** (`ctuf_pqov_broken`): for pqov's public map and any signers that
  return preimages, the rescaling forger wins CT-UF with probability 1; it does not win CT-UF^×
  (freshness up to nonzero scalars, `uovCls`, `not_ctxWin_scale`). This is why the Moussaka
  corollary uses CT-UF^open.

No `sorry`, no `axiom`.
-/

open OracleComp OracleSpec
open scoped ENNReal

namespace VoleMole.Assumptions.UOV.Links

open VoleMole.ROM VoleMole.ROM.IC VoleMole.Prob VoleMole.Verifier VoleMole.ZK.Sim

/-! ## Ratatouille: UF-Tag with a signability probe -/

section Ratatouille

open VoleMole.ROM.IC.RatBalance VoleMole.Spec.Ratatouille

/-- Ratatouille's hash of a signing query `(c, x)`: `Tag(c, x)`. -/
def ratTag (q : Commitment × Credits) : Target := tag q.1 q.2

/-- A Ratatouille forger's output with the forgery as `((c, x), s)`. -/
def ratAssoc (r : ForgerOut) :
    Option ((Commitment × Credits) × Preimage) × List (Commitment × Credits) ×
      List (Commitment × Credits) :=
  (r.1.map fun p => ((p.1, p.2.1), p.2.2), r.2.1, r.2.2)

/-- **A Ratatouille `TagForger` is a forger of the generic UF-Tag game with a signability probe.** -/
def ratForger (B : RatBalance.TagForger) :
    ProbeForger Ans CTable (Commitment × Credits) Target Preimage Preimage ratTag where
  run σ E := ratAssoc <$> B.run σ E
  reads σ σ' E g hs hp := by
    simp only [evalWithAnswerFn_map] at hs hp ⊢
    rw [B.reads σ σ' E g hs hp]

theorem ufWin_ratAssoc (pk : PublicKey) (σ : Signer) (r : ForgerOut) :
    UFWin (fun s t => uovEval pk s = t) ratTag σ (ratAssoc r) ↔ RatBalance.UFWin pk σ r := by
  constructor
  · rintro ⟨⟨c, x⟩, s, h1, h2, h3⟩
    rcases r with ⟨_ | ⟨c', x', s'⟩, l1, l2⟩
    · simp [ratAssoc] at h1
    · simp only [ratAssoc, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h1
      obtain ⟨⟨rfl, rfl⟩, rfl⟩ := h1
      exact ⟨c', x', s', rfl, h2, fun q hq hqe => h3 q hq hqe⟩
  · rintro ⟨c, x, s, h1, h2, h3⟩
    refine ⟨(c, x), s, ?_, h2, fun q hq hqe => h3 q hq hqe⟩
    simp [ratAssoc, h1]

/-- **`ufTagAdv` is the UF-Tag-with-probe advantage** of the reassociated forger, at the key
`pk` and the signer `σ`. -/
theorem ufTagAdv_eq (pk : PublicKey) (σ : Signer) (B : RatBalance.TagForger) :
    ufTagAdv pk σ B = advUFTagProbeAt (fun s t => uovEval pk s = t) ratTag σ (ratForger B) := by
  unfold ufTagAdv advUFTagProbeAt semAdv
  refine prEvent_bind_congr_of_support _ _ _ fun E _ => ?_
  simp only [ratForger, simulateQ_map, StateT.run'_eq, StateT.run_map, Functor.map_map]
  exact prEvent_congr _ _ _ fun r => (ufWin_ratAssoc pk σ r.1).symm

/-- **Theorem 1 (balance), with the standalone UF-Tag-with-probe advantage.** -/
theorem balance_le_ufTagProbe {Z : Sizes} {S : Type} (lr : Bool) (pkU : UovPk)
    (A : RoundAdv S (Op Z) Resp) (N : ℕ) (σ : Signer)
    (hdig : pkU.digest.size = 32) {qA : Kind → ℕ} {nA eA : ℕ}
    (hqA : ∀ s, IsKindQueryBoundIC (A.next s) qA)
    (hnA : ∀ s, IsQueryBoundP (A.next s) (fun t => t.isLeft = true) nA)
    (heA : ∀ s, IsQueryBoundP (A.next s) (fun t => t.isRight = true) eA) :
    Pr{let E ← $ᵗ CTable; let r ← (simulateQ randomOracle (balQ lr pkU A N σ E)).run' ∅}[
        Win r.2.2] ≤
      N * epsIss (N * (eA + eVR lr pkU verifyCellBound)) (N • (qA + (extractorQueries + verifierQueries))) +
        N * epsSpend (N * (eA + eVR lr pkU verifyCellBound)) (N * (nA + (2 + verifierTotal)))
          (N • (qA + (extractorQueries + verifierQueries))) +
        advUFTagProbeAt (fun s t => uovEval pkU.map s = t) ratTag σ
          (ratForger (forger lr pkU verQL A N (verifierIC_verifyIC CrtGen.tables))) +
        collAdv lr pkU verQL A N σ := by
  rw [← ufTagAdv_eq]
  exact balance_le_ufTag lr pkU A N σ hdig hqA hnA heA

end Ratatouille

/-! ## PomFRIT: OMPR and OMPR⊕τ -/

section Pomfrit

open VoleMole.ROM.OneMore VoleMole.ROM.OneMore.Pomfrit

variable {K : Type} (KG : ProbComp (UovPk × K)) (pre : K → TG → SIss)

/-- **PomFRIT's trapdoor**: the Issuer's key generation, Def. 3.1's relation `relP` (a 119-byte
preimage under the public map), the Issuer `pre` (`honestPre` for pqov's `derive_preimage`). -/
def pomTrap : Trapdoor UovPk K TG SIss := ⟨KG, relP, pre⟩

variable (ℓ QT : ℕ) (T : CrtTables) (lr : Bool) (A : Forger)

set_option linter.constructorNameAsVariable false in
/-- **Theorem U1 with the standalone OMPR advantage** (Def. 3.1, `n = Q_T + ℓ + 1` targets, `ℓ`
preimage queries) of the explicit reduction `red addHint (advC …)`. -/
theorem pomfrit_U1_ompr (e1 : CTable → QueryLog specIC → ByteArray → TG)
    (hA : ∀ pk, IsQueryBoundP (A pk) (fun q => isHT q = true) QT) :
    Pr{let r ← game KG pre (QT + (ℓ + 1)) ℓ T lr A addHint e1 tgts1}[PomWin ℓ r] ≤
      advOMPR (pomTrap KG pre) (QT + (ℓ + 1)) ℓ (red addHint (advC ℓ T lr A e1 tgts1)) +
      Pr{let r ← game KG pre (QT + (ℓ + 1)) ℓ T lr A addHint e1 tgts1}[
        ∃ i : Fin (ℓ + 1), PFail i.val r] :=
  pomfrit_U1_bound KG pre ℓ QT T lr A e1 hA

set_option linter.constructorNameAsVariable false in
/-- **Theorem U2 with the standalone OMPR⊕τ advantage.** -/
theorem pomfrit_U2_omprShift (τ : ℕ) (sh : CTable → QueryLog specIC → ByteArray → List TG)
    (hA : ∀ pk, IsQueryBoundP (A pk) (fun q => isHT q = true) QT) :
    Pr{let r ← game KG pre (QT + (ℓ + 1)) ℓ T lr A noHint (hint2 τ sh) tgts2}[PomWin ℓ r] ≤
      advOMPRShift (pomTrap KG pre) τ (QT + (ℓ + 1)) ℓ
        (red noHint (advC ℓ T lr A (hint2 τ sh) tgts2)) +
      Pr{let r ← game KG pre (QT + (ℓ + 1)) ℓ T lr A noHint (hint2 τ sh) tgts2}[
        ∃ i : Fin (ℓ + 1), ShiftFail τ i.val r] :=
  pomfrit_U2_bound KG pre ℓ QT T lr A τ sh hA

end Pomfrit

/-! ## Moussaka: CT-UF^open -/

section Moussaka

open VoleMole.ROM.IC.OMUF

variable {K qR : ℕ}

/-- The Anchors' signers from one oracle on `(k, t)`. -/
def skOf (σ : Fin K × Spec.Bytes → Option Spec.Bytes) : Fin K → Spec.Signer :=
  fun k => ⟨fun t => σ (k, t)⟩

/-- The signers as one oracle (`signers`) are the Anchors' signers back. -/
theorem skOf_signers (sk : Fin K → Spec.Signer) :
    skOf (signers (fun (sk : Spec.Signer) => sk.derivePreimage) sk) = sk := rfl

/-- **The signing log of an Issue record list**: the accepted queries' `(k, t)` (the Anchor calls
its signer exactly on these, `anchorIC`). -/
def sigLog (l : List (IssQ K × Bool)) : List (Fin K × Spec.Bytes) :=
  (l.filter (·.2)).map fun p => (p.1.k, toL p.1.t)

section Congr

variable (lr : Bool) (f : (d : DomIC) → AnsIC d)

/-- **The Anchor reads its signer only at an accepted query.** -/
theorem anchorIC_congr (sk sk' : Fin K → Spec.Signer) (q : IssQ K)
    (h : (evalWithAnswerFn (QueryImpl.ofFn f) (anchorIC lr sk q)).2 = true →
      (sk' q.k).derivePreimage (toL q.t) = (sk q.k).derivePreimage (toL q.t)) :
    evalWithAnswerFn (QueryImpl.ofFn f) (anchorIC lr sk' q) =
        evalWithAnswerFn (QueryImpl.ofFn f) (anchorIC lr sk q) ∧
      tableQueryLog (anchorIC lr sk' q) f = tableQueryLog (anchorIC lr sk q) f := by
  unfold anchorIC at h ⊢
  by_cases hw : q.WF lr
  · simp only [hw, ite_true, evalWithAnswerFn_map, tableQueryLog_map', and_true] at h ⊢
    by_cases ha : (evalWithAnswerFn (QueryImpl.ofFn f)
        (verifyIC CrtGen.tables (q.stmt lr) q.pf)).accept = true
    · simp only [ha, ite_true] at h ⊢
      rw [h trivial]
    · simp [ha]
  · simp [hw]

variable {A : Adversary K qR}

/-- **The Issue rounds read the signers only at their accepted queries.** -/
theorem runIss_congr (sk sk' : Fin K → Spec.Signer) :
    ∀ (n : ℕ) (s : A.σ),
      (∀ p ∈ sigLog (evalWithAnswerFn (QueryImpl.ofFn f) (runIss lr sk A n s)).2,
        (sk' p.1).derivePreimage p.2 = (sk p.1).derivePreimage p.2) →
      evalWithAnswerFn (QueryImpl.ofFn f) (runIss lr sk' A n s) =
          evalWithAnswerFn (QueryImpl.ofFn f) (runIss lr sk A n s) ∧
        tableQueryLog (runIss lr sk' A n s) f = tableQueryLog (runIss lr sk A n s) f
  | 0, s, _ => by simp [runIss]
  | n + 1, s, h => by
    have ha := anchorIC_congr lr f sk sk'
      (evalWithAnswerFn (QueryImpl.ofFn f) (A.query s)).2 fun hb => h _ (by
        simp only [runIss, evalWithAnswerFn_bind, evalWithAnswerFn_pure, sigLog]
        exact List.mem_map.2 ⟨_, List.mem_filter.2 ⟨List.mem_cons_self, hb⟩, rfl⟩)
    have hr := runIss_congr sk sk' n (A.absorb (evalWithAnswerFn (QueryImpl.ofFn f) (A.query s)).1
      (evalWithAnswerFn (QueryImpl.ofFn f)
        (anchorIC lr sk (evalWithAnswerFn (QueryImpl.ofFn f) (A.query s)).2)).1) fun p hp => h p (by
        simp only [runIss, evalWithAnswerFn_bind, evalWithAnswerFn_pure, sigLog,
          List.filter_cons] at hp ⊢
        split_ifs <;> simp_all)
    simp only [runIss, evalWithAnswerFn_bind, evalWithAnswerFn_pure, tableQueryLog_bind,
      tableQueryLog_pure, ha.1, ha.2, hr.1, hr.2, and_self]

variable (pk : Fin K → UovPk) (qI : ℕ) (A)

/-- **The OMUF game reads the signers only at the accepted Issue queries.** -/
theorem game_congr (sk sk' : Fin K → Spec.Signer)
    (h : ∀ p ∈ sigLog (evalWithAnswerFn (QueryImpl.ofFn f) (OMUF.game lr pk sk qI A)).1,
      (sk' p.1).derivePreimage p.2 = (sk p.1).derivePreimage p.2) :
    evalWithAnswerFn (QueryImpl.ofFn f) (OMUF.game lr pk sk' qI A) =
        evalWithAnswerFn (QueryImpl.ofFn f) (OMUF.game lr pk sk qI A) ∧
      tableQueryLog (OMUF.game lr pk sk' qI A) f = tableQueryLog (OMUF.game lr pk sk qI A) f := by
  have hr := runIss_congr lr f sk sk' qI (evalWithAnswerFn (QueryImpl.ofFn f) A.init) (by
    simpa only [OMUF.game, evalWithAnswerFn_bind, evalWithAnswerFn_map] using h)
  simp only [OMUF.game, evalWithAnswerFn_bind, evalWithAnswerFn_map, tableQueryLog_bind,
    tableQueryLog_map', hr.1, hr.2, and_self]

end Congr

section Forger

variable (lr : Bool) (pk : Fin K → UovPk) (qI : ℕ) (A : Adversary K qR)

open Classical in
/-- `B₂`'s forgery: an extracted redemption opening `x` with an honest key `k` and a preimage
`s`, `P_k(s) = Com(x)`, whose commitment was never signed (`Forge`), if there is one. -/
noncomputable def forgeOf (E : CTable) (v : View K) : Option (Fin K × Opening × Spec.Bytes) :=
  if h : ∃ p : Fin K × Opening × Spec.Bytes, p.2.1 ∈ SR lr pk E v ∧
      comO p.2.1 ∉ (issL v.1).map (·.1) ∧ (pk p.1).toSpec.eval p.2.2 = comO p.2.1
  then some (Classical.choose h) else none

open Classical in
/-- `B₂`'s openings: for every signed target, an extracted issuance opening of it, if there is
one. -/
noncomputable def opensOf (E : CTable) (v : View K) : List Opening :=
  (sigLog v.1.1).filterMap fun q =>
    if h : ∃ x ∈ SI lr E v, comO x = q.2 then some (Classical.choose h) else none

/-- `B₂`'s output from the view. -/
noncomputable def ctufOut (E : CTable) (v : View K) :
    CTOut K Spec.Bytes Opening × List (Fin K × Spec.Bytes) × List (Fin K × Spec.Bytes) :=
  ((forgeOf lr pk E v, opensOf lr E v), sigLog v.1.1, [])

/-- **The CT-UF^open forger `B₂`**: it runs the OMUF game and every extraction with the signers
as its oracle, and outputs `ctufOut`. Its signing log is the accepted Issue queries `(k, t)`. -/
noncomputable def ctufForger : CTForger Ans CTable K Spec.Bytes (Option Spec.Bytes) Spec.Bytes Opening where
  run σ E := ctufOut lr pk E <$> extAll lr pk (skOf σ) qI A E
  reads σ σ' E g hs _ := by
    simp only [evalWithAnswerFn_map, ctufOut] at hs ⊢
    rw [extAll_eval] at hs
    have hg := game_congr lr (join g E) (A := A) pk qI (skOf σ) (skOf σ') fun p hp => hs p hp
    have h1 : ∀ j, evalWithAnswerFn (QueryImpl.ofFn g)
        (gameA CrtGen.tables (stI lr) (PI lr pk (skOf σ') qI A j) E) =
        evalWithAnswerFn (QueryImpl.ofFn g)
          (gameA CrtGen.tables (stI lr) (PI lr pk (skOf σ) qI A j) E) := fun j =>
      gameA_congr _ _ E g (by simp only [PI, evalWithAnswerFn_map, hg.1])
        (by simp only [PI, tableQueryLog_map', hg.2])
    have h2 : ∀ j, evalWithAnswerFn (QueryImpl.ofFn g)
        (gameA CrtGen.tables (stR lr pk) (PR lr pk (skOf σ') qI A j) E) =
        evalWithAnswerFn (QueryImpl.ofFn g)
          (gameA CrtGen.tables (stR lr pk) (PR lr pk (skOf σ) qI A j) E) := fun j =>
      gameA_congr _ _ E g (by simp only [PR, evalWithAnswerFn_map, hg.1])
        (by simp only [PR, tableQueryLog_map', hg.2])
    rw [extAll_eval, extAll_eval, hg.1]
    simp only [h1, h2]

end Forger

section Win

variable (lr : Bool) (pk : Fin K → UovPk) (sk : Fin K → Spec.Signer) (qI : ℕ) (A : Adversary K qR)

/-- The verification of the CT-UF game for the Anchors' keys: `P_k(s) = t`. -/
def verK (pk : Fin K → UovPk) (k : Fin K) (s t : Spec.Bytes) : Prop := (pk k).toSpec.eval s = t

theorem wfo_of_SR {E : CTable} {v : View K} {x : Opening} (hx : x ∈ SR lr pk E v) : WFO x := by
  rcases hx with ⟨j, rq, r, -, -, hxo⟩
  exact hxo.1

theorem wfo_of_SI {E : CTable} {v : View K} {x : Opening} (hx : x ∈ SI lr E v) : WFO x := by
  rcases hx with ⟨j, q, r, -, -, hxo⟩
  exact hxo.1

theorem mem_sigLog {l : List (IssQ K × Bool)} {q : Fin K × Spec.Bytes} (hq : q ∈ sigLog l) :
    ∃ p ∈ l, p.2 = true ∧ q = (p.1.k, toL p.1.t) := by
  obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hq
  obtain ⟨hp, hb⟩ := List.mem_filter.1 hp
  exact ⟨p, hp, by simpa using hb, rfl⟩

/-- **Per table: a forgery, with every accepted issuance proof extracted, is a CT-UF^open win of
`B₂`.** -/
theorem ctOpenWin_of_forge (g : Table) (E : CTable)
    (hI : ∀ j ∈ Finset.range qI, ¬BadI E lr (evalWithAnswerFn (QueryImpl.ofFn g)
        (gameA CrtGen.tables (stI lr) (PI lr pk sk qI A j) E)))
    (hF : Forge lr pk E (evalWithAnswerFn (QueryImpl.ofFn g) (extAll lr pk sk qI A E))) :
    CTOpenWin (verK pk) comO WFO
      (ctufOut lr pk E (evalWithAnswerFn (QueryImpl.ofFn g) (extAll lr pk sk qI A E))) := by
  classical
  set v := evalWithAnswerFn (QueryImpl.ofFn g) (extAll lr pk sk qI A E) with hv
  obtain ⟨x, hx, hn⟩ := hF
  have hx' := hx
  obtain ⟨-, -, -, -, -, -, -, -, -, s, u, k, -, he, -⟩ := hx'
  have h : ∃ p : Fin K × Opening × Spec.Bytes, p.2.1 ∈ SR lr pk E v ∧
      comO p.2.1 ∉ (issL v.1).map (·.1) ∧ (pk p.1).toSpec.eval p.2.2 = comO p.2.1 :=
    ⟨(k, x, s), hx, hn, he⟩
  obtain ⟨hs1, hs2, hs3⟩ := Classical.choose_spec h
  refine ⟨⟨(Classical.choose h).1, (Classical.choose h).2.1, (Classical.choose h).2.2,
    by simp only [ctufOut]; unfold forgeOf; exact dite_eq_left h, wfo_of_SR lr pk hs1, hs3, ?_⟩, ?_⟩
  · intro q hq hqe
    obtain ⟨p, hp, hb, rfl⟩ := mem_sigLog hq
    refine hs2 (List.mem_map.2 ⟨(toL p.1.t, toL p.1.ctx), ?_, ?_⟩)
    · exact List.mem_map.2 ⟨p, List.mem_filter.2 ⟨hp, by simpa using hb⟩, rfl⟩
    · exact hqe
  · intro q hq
    obtain ⟨p, hp, hb, rfl⟩ := mem_sigLog hq
    obtain ⟨hlI, -, -, -⟩ := game_eval g E lr pk sk A qI
    have hv1 : v.1 = evalWithAnswerFn (QueryImpl.ofFn (join g E)) (OMUF.game lr pk sk qI A) := by
      rw [hv, extAll_eval]
    obtain ⟨j, hj⟩ := List.mem_iff_getElem?.1 hp
    rw [hv1] at hj
    have hjl : j < qI := by rw [← hlI]; exact (List.getElem?_eq_some_iff.1 hj).1
    have hj' : (evalWithAnswerFn (QueryImpl.ofFn (join g E)) (OMUF.game lr pk sk qI A)).1[j]? =
        some (p.1, true) := by rw [hj]; cases p; simp_all
    obtain ⟨hacc, hst⟩ := accepted_I g E lr pk sk qI A hj'
    have hext : ExtI E lr (evalWithAnswerFn (QueryImpl.ofFn g)
        (gameA CrtGen.tables (stI lr) (PI lr pk sk qI A j) E)) := by
      by_contra hne
      exact hI j (Finset.mem_range.2 hjl) ⟨hacc, hne⟩
    obtain ⟨x, hx, hxc, -⟩ := opI_of_ext E lr hext
    have hxS : x ∈ SI lr E v := by
      refine ⟨j, p.1, _, ?_, ?_, hx⟩
      · rw [hv1]; exact hj'
      · rw [hv, extAll_eval]; simp [hjl]
    have h' : ∃ x ∈ SI lr E v, comO x = toL p.1.t := ⟨x, hxS, by rw [hxc, hst]⟩
    obtain ⟨hy1, hy2⟩ := Classical.choose_spec h'
    refine ⟨Classical.choose h', ?_, wfo_of_SI lr hy1, hy2⟩
    simp only [ctufOut, opensOf]
    exact List.mem_filterMap.2 ⟨(p.1.k, toL p.1.t), hq, by simp [h']⟩

/-- **The per-table core of Theorem 1 with CT-UF^open**: a win means that some accepted proof is
not extracted, or `B₁` finds a `Com` collision, or `B₂` wins CT-UF^open. -/
theorem win_imp_open (g : Table) (E : CTable)
    (hwin : Win (evalWithAnswerFn (QueryImpl.ofFn (join g E)) (OMUF.game lr pk sk qI A))) :
    (∃ j ∈ Finset.range qI, BadI E lr (evalWithAnswerFn (QueryImpl.ofFn g)
        (gameA CrtGen.tables (stI lr) (PI lr pk sk qI A j) E))) ∨
    (∃ j ∈ Finset.range qR, BadR E lr pk (evalWithAnswerFn (QueryImpl.ofFn g)
        (gameA CrtGen.tables (stR lr pk) (PR lr pk sk qI A j) E))) ∨
    Coll lr pk E (evalWithAnswerFn (QueryImpl.ofFn g) (extAll lr pk sk qI A E)) ∨
    CTOpenWin (verK pk) comO WFO
      (ctufOut lr pk E (evalWithAnswerFn (QueryImpl.ofFn g) (extAll lr pk sk qI A E))) := by
  by_cases hI : ∃ j ∈ Finset.range qI, BadI E lr (evalWithAnswerFn (QueryImpl.ofFn g)
      (gameA CrtGen.tables (stI lr) (PI lr pk sk qI A j) E))
  · exact Or.inl hI
  push Not at hI
  rcases win_imp lr pk sk qI A g E hwin with h | h | h | h
  · exact absurd h (by push Not; exact hI)
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (Or.inl h))
  · exact Or.inr (Or.inr (Or.inr (ctOpenWin_of_forge lr pk sk qI A g E hI h)))

/-- **`B₂`'s CT-UF^open advantage** against the Anchors' signers is the probability of its win in
the reductions' run. -/
theorem advCTUFOpenAt_ctufForger :
    advCTUFOpenAt (verK pk) comO WFO (signers (fun (sk : Spec.Signer) => sk.derivePreimage) sk)
        (ctufForger lr pk qI A) =
      Pr{let E ← $ᵗ CTable; let v ← (simulateQ randomOracle (extAll lr pk sk qI A E)).run' ∅}[
        CTOpenWin (verK pk) comO WFO (ctufOut lr pk E v)] := by
  unfold advCTUFOpenAt semAdv
  refine prEvent_bind_congr_of_support _ _ _ fun E _ => ?_
  simp only [ctufForger, skOf_signers, simulateQ_map, StateT.run'_eq, StateT.run_map,
    Functor.map_map]

/-- **Theorem 1 with `B₂`'s standalone CT-UF^open advantage**: for every OMUF adversary, honest
Anchors with any public keys and signers, either layout,

    Pr[Win] ≤ Σ_{j<qI} Pr[BadI_j] + Σ_{j<qR} Pr[BadR_j] + AdvBind(B₁) + Adv^{ct-uf-open}_K(B₂),

`B₂ = ctufForger lr pk qI A` against the signers `(k, t) ↦ derive_preimage(sk_k, t)`. -/
theorem omuf_le_open :
    Pr{let E ← $ᵗ CTable; let r ← (simulateQ randomOracle (runE E (OMUF.game lr pk sk qI A))).run' ∅}[
        Win r.1] ≤
      ∑ j ∈ Finset.range qI, Pr{let E ← $ᵗ CTable; let r ← (simulateQ randomOracle
        (gameA CrtGen.tables (stI lr) (PI lr pk sk qI A j) E)).run' ∅}[BadI E lr r] +
      ∑ j ∈ Finset.range qR, Pr{let E ← $ᵗ CTable; let r ← (simulateQ randomOracle
        (gameA CrtGen.tables (stR lr pk) (PR lr pk sk qI A j) E)).run' ∅}[BadR E lr pk r] +
      Pr{let E ← $ᵗ CTable; let v ← (simulateQ randomOracle (extAll lr pk sk qI A E)).run' ∅}[
        Coll lr pk E v] +
      advCTUFOpenAt (verK pk) comO WFO (signers (fun (sk : Spec.Signer) => sk.derivePreimage) sk)
        (ctufForger lr pk qI A) := by
  rw [advCTUFOpenAt_ctufForger]
  refine prEvent_bind_le_sum4_of_table ($ᵗ CTable) (fun E => runE E (OMUF.game lr pk sk qI A))
    (fun _ r => Win r.1) (Finset.range qI) (Finset.range qR) _ _ _ _ _ _
    (fun E v => CTOpenWin (verK pk) comO WFO (ctufOut lr pk E v)) fun E g hw => ?_
  rw [evalWithAnswerFn_runE] at hw
  exact win_imp_open lr pk sk qI A g E hw

end Win

section Num

variable (lr : Bool) (pk : Fin K → UovPk) (sk : Fin K → Spec.Signer) (qI : ℕ) {A : Adversary K qR}
  {q : Kind → ℕ} {qE n : ℕ}

/-- **Theorem 1 (`omuf_le_num`) with `Adv^{ct-uf-open}_K` in place of `AdvCTUF(B₂)`**: for an
adversary within its budget and honest Anchors with distinct 32-byte key digests,

    Pr[Win] ≤ qI·εI(q', q'_E) + qR·εR(q', q'_E, n') + AdvBind(B₁) + Adv^{ct-uf-open}_K(B₂),

`B₂ = ctufForger lr pk qI A`, a CT-UF^open forger against the Anchors' signers. -/
theorem omuf_le_num_open (hA : A.Budget q qE n) (hdig : ∀ k, (pk k).digest.size = 32)
    (hdinj : Function.Injective fun k => (pk k).digest) :
    Pr{let E ← $ᵗ CTable; let r ← (simulateQ randomOracle (runE E (OMUF.game lr pk sk qI A))).run' ∅}[
        Win r.1] ≤
      qI * epsI (gameK q qI qR) (gameE lr qE qI qR) +
      qR * epsR (gameK q qI qR) (gameE lr qE qI qR) (gameH n qI qR) +
      Pr{let E ← $ᵗ CTable; let v ← (simulateQ randomOracle (extAll lr pk sk qI A E)).run' ∅}[
        Coll lr pk E v] +
      advCTUFOpenAt (verK pk) comO WFO (signers (fun (sk : Spec.Signer) => sk.derivePreimage) sk)
        (ctufForger lr pk qI A) := by
  refine (omuf_le_open lr pk sk qI A).trans
    (add_le_add (add_le_add (add_le_add ?_ ?_) le_rfl) le_rfl)
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

end Moussaka

/-! ## CT-UF is false for UOV; CT-UF^× -/

section Scaling

open VoleMole.Spec VoleMole.Spec.Pqov VoleMole.Arith

/-- UOV targets as vectors. -/
abbrev Tgt := Fin 45 → GF256

/-- **Same class up to a nonzero scalar**, the freshness of CT-UF^× for UOV. -/
def uovCls (t t' : Tgt) : Prop := ∃ μ : GF256, μ ≠ 0 ∧ t = μ • t'

theorem uovCls_refl (t : Tgt) : uovCls t t := ⟨1, one_ne_zero, (one_smul _ _).symm⟩

theorem exists_ne_zero_one : ∃ μ : GF256, μ ≠ 0 ∧ μ ≠ 1 := by
  classical
  by_contra h
  push Not at h
  have hsub : (Finset.univ : Finset GF256) ⊆ {0, 1} := fun μ _ => by
    by_cases h0 : μ = 0
    · simp [h0]
    · simp [h μ h0]
  have := Finset.card_le_card hsub
  rw [Finset.card_univ, GF256.card_eq] at this
  exact absurd (this.trans Finset.card_le_two) (by norm_num)

variable {K : ℕ} {Xc : Type}

/-- **CT-UF (`moussaka.md` §3.3) is false for UOV**: for any keys, any signers that return
preimages (`P_k(D_k(y)) = y`), any commitment function and any `x*` in its domain with
`Com(x*) ≠ 0`, the one-query rescaling forger wins CT-UF with probability 1 (it queries
`μ • Com(x*)`, `μ ∉ {0, 1}`, and rescales the answer by `(μ⁻¹)^128`; `ctuf_scaling_attack`). -/
theorem ctuf_pqov_broken (pk : Fin K → UOVKey) (D : Fin K → Tgt → ℕ → GF256)
    (hD : ∀ k y, qmap (pk k) (D k y) = y) (Com : Xc → Tgt) (DCom : Xc → Prop) (k : Fin K)
    (x : Xc) (hx : DCom x) (hc : Com x ≠ 0) :
    ∃ B : CTForger Ans CTable K Tgt (Option (ℕ → GF256)) (ℕ → GF256) Xc,
      advCTUFAt (fun k s t => qmap (pk k) s = t) Com DCom (fun p => some (D p.1 p.2)) B = 1 := by
  obtain ⟨μ, h0, h1⟩ := exists_ne_zero_one
  obtain ⟨hne, hpre⟩ := ctuf_scaling_attack (pk k) (D k) (hD k) h0 h1 hc
  exact ⟨scaleForger k x (μ • Com x) (fun s' => (μ⁻¹) ^ 128 • s'),
    advCTUFAt_scaleForger _ _ _ _ _ _ _ _ _ rfl hx hpre hne⟩

/-- The rescaling forger does not win CT-UF^×: its query is in the class of `Com(x*)`. -/
theorem not_ctxWin_scale (pk : Fin K → UOVKey) (Com : Xc → Tgt) (DCom : Xc → Prop) (k : Fin K)
    (x : Xc) {μ : GF256} (h0 : μ ≠ 0) (o : CTOut K (ℕ → GF256) Xc)
    (ho : ∀ k' x' s, o.1 = some (k', x', s) → x' = x) :
    ¬CTXWin (fun k s t => qmap (pk k) s = t) Com DCom uovCls (o, [(k, μ • Com x)], []) := by
  rintro ⟨k', x', s, h1, -, -, h4⟩
  obtain rfl := ho _ _ _ h1
  exact h4 _ List.mem_cons_self ⟨μ, h0, rfl⟩

end Scaling

end VoleMole.Assumptions.UOV.Links
