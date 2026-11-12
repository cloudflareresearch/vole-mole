import VoleMole.ROM.RatatouilleBalance
import VoleMole.Privacy.Hybrid

/-!
# UF-Tag with a signability probe: removing the probe (`lean/docs/security/uov-assumptions.md` §5.8)

`ROM/RatatouilleBalance.lean` bounds Ratatouille's balance by the advantage `ufTagAdv` of a UF-Tag
forger *with a signability probe* (`TagForger`): besides its signing log, the forger has a probe
log, the pairs `(c, x)` on which it only learns whether the signer succeeds on `Tag(c, x)` (the
Issuer's duplicate-nullifier path, finding F5). This file shows that the probe is worth no more
than the signer's failures on the logged pairs.

* `patch σ τ`: the signer `σ` with its failures filled in by `τ` (a total signer).
* `FailOut`, `failAdv`: the event that `σ` fails on a signed or probed pair of the forger's run.
* `run_patch_of_not_fail`, `failOut_iff_patch`: **the deterministic core.** Outside the failure
  event, the forger's run against `σ` equals its run against `patch σ τ`, for every `τ`; and the
  failure event of the run against `σ` is the failure event of `σ` on the logs of the run against
  `patch σ τ`. A total signer answers every probe "yes", so the probe carries no information.
* `TagForger.noProbe`: the forger run against `patch σ τ`, with its probe log dropped. It is a
  forger that never probes (`noProbe_probeFree`).
* **`ufTagAdv_le_noProbe`**: `Adv^{uf-tag+probe}(B) ≤ Adv^{uf-tag}(B.noProbe τ) + failAdv(B)`.
* `withFail`, **`pr_failOut_le`**: if `σ` fails on a target `y` exactly when an independent uniform
  coordinate `f(κ y)` lies in a set `bad` (and otherwise returns `τ y`), then for every table the
  failure event has probability at most `ℓ·Pr[bad]` over `f`, with `ℓ` the length of the logs of
  the run against the total signer `τ`. For pqov's `derive_preimage` with SHAKE256 a random oracle,
  `Pr[bad] = δ(sk)^255` (`uov-assumptions.md` §2, Lemma D; that the real signer has this law is
  the paper step).
* `logs_length_le`, `forger_logs_le`: one Issuer call signs or probes at most one pair, so the
  reduction's forger `B` (`forger`) has at most `N` logged pairs.
* **`balance_le_noProbe`**: Theorem 1 with a probe-free forger and the failure term:
  `Pr[win] ≤ N·ε_iss + N·ε_spend + Adv^{uf-tag}(B.noProbe τ) + failAdv(B) + Adv^{coll}(C)`.

No `sorry`, no `axiom`.
-/

open OracleComp OracleSpec
open scoped ENNReal

namespace VoleMole.ROM.IC.RatBalance

open VoleMole.Prob VoleMole.Verifier VoleMole.Verifier.Bridge VoleMole.ROM VoleMole.ROM.IC
open VoleMole.Spec.Ratatouille VoleMole.EndToEnd VoleMole.ZK.Sim

variable {Z : Sizes}

/-! ## Patching the signer, and the failure event -/

/-- **The signer completed by `τ`**: `σ` where it succeeds, `τ` where it fails. It never fails. -/
def patch (σ : Signer) (τ : Target → Preimage) : Signer := fun y => some ((σ y).getD (τ y))

theorem patch_isSome (σ : Signer) (τ : Target → Preimage) (y : Target) :
    (patch σ τ y).isSome = true := rfl

theorem patch_of_ne_none {σ : Signer} (τ : Target → Preimage) {y : Target} (h : σ y ≠ none) :
    patch σ τ y = σ y := by
  obtain ⟨s, hs⟩ := Option.ne_none_iff_exists'.1 h
  simp [patch, hs]

/-- **The failure event**: the signer fails on a pair the forger signed or probed. -/
def FailOut (σ : Signer) (r : ForgerOut) : Prop :=
  ∃ q ∈ r.2.1 ++ r.2.2, σ (tag q.1 q.2) = none

/-- The probability of the failure event in the forger's run. -/
noncomputable def failAdv (σ : Signer) (B : TagForger) : ℝ≥0∞ :=
  Pr{let E ← $ᵗ CTable; let r ← (simulateQ randomOracle (B.run σ E)).run' ∅}[FailOut σ r]

/-- The forger's output against `σ` at the tables. -/
abbrev TagForger.out (B : TagForger) (σ : Signer) (E : CTable) (g : Table) : ForgerOut :=
  evalWithAnswerFn (QueryImpl.ofFn g) (B.run σ E)

/-- **Outside the failure event, the run against `σ` is the run against `patch σ τ`.** -/
theorem run_patch_of_not_fail (B : TagForger) (σ : Signer) (τ : Target → Preimage) (E : CTable)
    (g : Table) (h : ¬ FailOut σ (B.out σ E g)) : B.out (patch σ τ) E g = B.out σ E g := by
  have hne : ∀ q ∈ (B.out σ E g).2.1 ++ (B.out σ E g).2.2, σ (tag q.1 q.2) ≠ none :=
    fun q hq hn => h ⟨q, hq, hn⟩
  refine B.reads σ (patch σ τ) E g (fun q hq => patch_of_ne_none τ ?_) (fun q hq => ?_)
  · exact hne q (List.mem_append_left _ hq)
  · rw [patch_isSome, eq_comm, Option.isSome_iff_ne_none]
    exact hne q (List.mem_append_right _ hq)

/-- **The failure event is read off the run against the total signer.** -/
theorem failOut_iff_patch (B : TagForger) (σ : Signer) (τ : Target → Preimage) (E : CTable)
    (g : Table) : FailOut σ (B.out σ E g) ↔ FailOut σ (B.out (patch σ τ) E g) := by
  constructor
  · intro hF
    by_contra hP
    have hne : ∀ q ∈ (B.out (patch σ τ) E g).2.1 ++ (B.out (patch σ τ) E g).2.2,
        σ (tag q.1 q.2) ≠ none := fun q hq hn => hP ⟨q, hq, hn⟩
    have heq : B.out σ E g = B.out (patch σ τ) E g := by
      refine B.reads (patch σ τ) σ E g (fun q hq => (patch_of_ne_none τ ?_).symm) (fun q hq => ?_)
      · exact hne q (List.mem_append_left _ hq)
      · rw [patch_isSome, Option.isSome_iff_ne_none]
        exact hne q (List.mem_append_right _ hq)
    exact hP (heq ▸ hF)
  · intro hP
    by_contra hF
    exact hF (run_patch_of_not_fail B σ τ E g hF ▸ hP)

/-! ## The probe-free forger -/

/-- **The forger without its probe**: `B` run against `patch σ τ` (every probe answers "yes"),
with its probe log dropped. -/
noncomputable def TagForger.noProbe (B : TagForger) (τ : Target → Preimage) : TagForger where
  run σ E := (fun r => (r.1, r.2.1, ([] : List (Commitment × Credits)))) <$> B.run (patch σ τ) E
  reads σ σ' E g hs _ := by
    simp only [evalWithAnswerFn_map] at hs ⊢
    rw [B.reads (patch σ τ) (patch σ' τ) E g (fun q hq => by simp [patch, hs q hq])
      (fun q _ => rfl)]

/-- A forger **never probes** if its probe log is always empty. -/
def TagForger.ProbeFree (B : TagForger) : Prop :=
  ∀ σ E (g : Table), (B.out σ E g).2.2 = []

theorem noProbe_probeFree (B : TagForger) (τ : Target → Preimage) : (B.noProbe τ).ProbeFree := by
  intro σ E g
  simp [TagForger.out, TagForger.noProbe, evalWithAnswerFn_map]

/-- A probe-free forger reads the signer only through its signing log. -/
theorem ProbeFree.reads {B : TagForger} (hB : B.ProbeFree) (σ σ' : Signer) (E : CTable)
    (g : Table) (hs : ∀ q ∈ (B.out σ E g).2.1, σ' (tag q.1 q.2) = σ (tag q.1 q.2)) :
    B.out σ' E g = B.out σ E g :=
  B.reads σ σ' E g hs (fun q hq => by rw [hB σ E g] at hq; cases hq)

/-- Per table: a win of `B` is a win of `B.noProbe τ` or a failure. -/
theorem ufWin_noProbe (pk : PublicKey) (B : TagForger) (σ : Signer) (τ : Target → Preimage)
    (E : CTable) (g : Table) (hW : UFWin pk σ (B.out σ E g)) :
    UFWin pk σ ((B.noProbe τ).out σ E g) ∨ FailOut σ (B.out σ E g) := by
  by_cases hF : FailOut σ (B.out σ E g)
  · exact .inr hF
  · left
    have h := run_patch_of_not_fail B σ τ E g hF
    simp only [TagForger.out, TagForger.noProbe, evalWithAnswerFn_map] at h ⊢
    rw [h]
    exact hW

/-- **The probe costs at most the failure event**:
`Adv^{uf-tag+probe}(B) ≤ Adv^{uf-tag}(B.noProbe τ) + failAdv(B)`, for every completion `τ`. -/
theorem ufTagAdv_le_noProbe (pk : PublicKey) (σ : Signer) (B : TagForger)
    (τ : Target → Preimage) :
    ufTagAdv pk σ B ≤ ufTagAdv pk σ (B.noProbe τ) + failAdv σ B := by
  unfold ufTagAdv failAdv
  let : MeasurableSpace CTable := ⊤
  rw [prEvent_bind_of_discrete, prEvent_bind_of_discrete, prEvent_bind_of_discrete,
    ← MeasureTheory.lintegral_add_left measurable_from_top]
  refine MeasureTheory.lintegral_mono fun E => ?_
  have h := prEvent_le_sum_of_table (B.run σ E) (Finset.univ : Finset Bool)
    (Y := fun _ => ForgerOut) (fun b => if b then (B.noProbe τ).run σ E else B.run σ E)
    (UFWin pk σ) (fun b r => if b then UFWin pk σ r else FailOut σ r) (fun g hW => by
      rcases ufWin_noProbe pk B σ τ E g hW with h | h
      · exact ⟨true, Finset.mem_univ _, by simpa using h⟩
      · exact ⟨false, Finset.mem_univ _, by simpa using h⟩)
  simpa [add_comm] using h

/-! ## The failure event for a signer with independent failures -/

section Fail

open VoleMole.Privacy (pr pr_def pr_equiv pr_prod_fst pr_mono pr_or_le)

variable {K Ω : Type*} [Fintype K] [DecidableEq K] [Fintype Ω] [Nonempty Ω]
  (bad : Ω → Prop) [DecidablePred bad] (κ : Target → K)

/-- **A signer with independent failures**: it fails at `y` when the coordinate `f (κ y)` is bad,
and otherwise returns `τ y`. (pqov's `derive_preimage` in the vinegar random-oracle model has
this law, with `Pr[bad] = δ(sk)^255`: `uov-assumptions.md` §2, Lemma D.) -/
def withFail (f : K → Ω) (τ : Target → Preimage) : Signer :=
  fun y => if bad (f (κ y)) then none else some (τ y)

omit [Fintype K] [DecidableEq K] [Fintype Ω] [Nonempty Ω] in
theorem patch_withFail (f : K → Ω) (τ : Target → Preimage) :
    patch (withFail bad κ f τ) τ = fun y => some (τ y) := by
  funext y
  unfold patch withFail
  split_ifs <;> rfl

/-- A uniformly random function, evaluated at a point, is uniform. -/
theorem pr_eval_pt (k : K) (P : Ω → Prop) : pr (K → Ω) (fun f => P (f k)) = pr Ω P := by
  rw [← pr_equiv (Equiv.funSplitAt k Ω).symm (fun f => P (f k))]
  have h (a : Ω × ({j // j ≠ k} → Ω)) : (Equiv.funSplitAt k Ω).symm a k = a.1 := by
    simp [Equiv.funSplitAt, Equiv.piSplitAt]
  simp only [h]
  exact pr_prod_fst P

omit [DecidablePred bad] in
/-- The union bound over a list of points. -/
theorem pr_exists_list_le (L : List K) :
    pr (K → Ω) (fun f => ∃ k ∈ L, bad (f k)) ≤ L.length * pr Ω bad := by
  induction L with
  | nil => classical simp [pr_def]
  | cons k L ih =>
    have h1 : pr (K → Ω) (fun f => ∃ k' ∈ k :: L, bad (f k')) ≤
        pr (K → Ω) (fun f => bad (f k) ∨ ∃ k' ∈ L, bad (f k')) :=
      pr_mono fun f hf => by simpa using hf
    refine h1.trans ((pr_or_le _ _).trans ?_)
    rw [pr_eval_pt, List.length_cons, Nat.cast_succ]
    linarith

/-- **The failure event of a forger against a signer with independent failures**: at every
table, over the failure coordinates `f`, its probability is at most `ℓ·Pr[bad]`, with `ℓ` the
number of pairs logged by the run against the total signer `τ` (which does not depend on `f`). -/
theorem pr_failOut_le (B : TagForger) (τ : Target → Preimage) (E : CTable) (g : Table) :
    pr (K → Ω) (fun f => FailOut (withFail bad κ f τ) (B.out (withFail bad κ f τ) E g)) ≤
      ((B.out (fun y => some (τ y)) E g).2.1 ++ (B.out (fun y => some (τ y)) E g).2.2).length *
        pr Ω bad := by
  set L := (B.out (fun y => some (τ y)) E g).2.1 ++ (B.out (fun y => some (τ y)) E g).2.2
  have h := pr_exists_list_le (Ω := Ω) bad (L.map fun q => κ (tag q.1 q.2))
  rw [List.length_map] at h
  refine (pr_mono fun f hf => ?_).trans h
  rw [failOut_iff_patch B _ τ, patch_withFail] at hf
  obtain ⟨q, hq, hn⟩ := hf
  refine ⟨κ (tag q.1 q.2), List.mem_map.2 ⟨q, hq, rfl⟩, ?_⟩
  by_contra hb
  simp [withFail, hb] at hn

end Fail

/-! ## The reduction's forger logs at most `N` pairs -/

/-- One Issuer call signs or probes at most one pair. -/
theorem signRec_probeRec_le (st : List Key) (p : Op Z × Resp) :
    (signRec st p).length + (probeRec st p).length ≤ 1 := by
  rcases p with ⟨op, resp⟩
  cases op with
  | issue req tInit ctx =>
    simp only [probeRec, List.length_nil, add_zero]
    unfold signRec
    split <;> simp_all
  | spend req ctx refund =>
    unfold signRec probeRec
    by_cases h : (ctx, (SpendReq.parse req).nf) ∈ st <;> split <;> simp_all

/-- **A transcript of `n` calls logs at most `n` pairs.** -/
theorem logs_length_le (tr : List (Op Z × Resp)) :
    (signLog tr).length + (probeLog tr).length ≤ tr.length := by
  unfold signLog probeLog
  rw [List.length_flatMap, List.length_flatMap, ← List.sum_map_add]
  refine (List.sum_le_length_nsmul _ 1 fun x hx => ?_).trans (by simp)
  obtain ⟨p, -, rfl⟩ := List.mem_map.1 hx
  exact signRec_probeRec_le _ _

section Forger

variable {S : Type} (lr : Bool) (pkU : UovPk)
  (verQ : Statement → ByteArray → OracleComp specIC Bool)
  (A : RoundAdv S (Op Z) Resp) (N : ℕ) {qV : Kind → ℕ} {nV : ℕ} {eV : Params → ℕ}

/-- **The reduction's forger `B` logs at most `N` pairs** (signed and probed together). -/
theorem forger_logs_le (hver : VerifierIC CrtGen.tables verQ qV nV eV) (σ : Signer) (E : CTable)
    (g : Table) :
    ((forger lr pkU verQ A N hver).out σ E g).2.1.length +
      ((forger lr pkU verQ A N hver).out σ E g).2.2.length ≤ N := by
  simp only [TagForger.out, forger, evalWithAnswerFn_map]
  generalize hm : evalWithAnswerFn (QueryImpl.ofFn g) (master lr pkU verQ A N σ E) = m
  have hm1 : m.1 = (yG lr pkU A σ g E N).2.2 := by
    rw [← hm, evalWithAnswerFn_master]; rfl
  have hlen : m.1.length = N := hm1 ▸ length_trace lr pkU A N σ g E
  unfold bOut
  split
  · refine (logs_length_le _).trans ?_
    rw [List.length_take]; omega
  · exact hlen ▸ logs_length_le _

/-- **Theorem 1 with a probe-free forger**: for every completion `τ`,

    Pr[win BAL] ≤ N·ε_iss + N·ε_spend + Adv^{uf-tag}(B.noProbe τ) + failAdv(B) + Adv^{coll}(C),

with `B.noProbe τ` a UF-Tag forger that never probes (`noProbe_probeFree`) and `failAdv(B)` the
probability that the Issuer's signer fails on one of the at most `N` pairs `B` signs or probes
(`forger_logs_le`; `≤ N·Pr[bad]` per table for a signer with independent failures,
`pr_failOut_le`). -/
theorem balance_le_noProbe (σ : Signer) (τ : Target → Preimage)
    (hdig : pkU.digest.size = 32) {qA : Kind → ℕ} {nA eA : ℕ}
    (hqA : ∀ s, IsKindQueryBoundIC (A.next s) qA)
    (hnA : ∀ s, IsQueryBoundP (A.next s) (fun t => t.isLeft = true) nA)
    (heA : ∀ s, IsQueryBoundP (A.next s) (fun t => t.isRight = true) eA) :
    Pr{let E ← $ᵗ CTable; let r ← (simulateQ randomOracle (balQ lr pkU A N σ E)).run' ∅}[
        Win r.2.2] ≤
      N * epsIss (N * (eA + eVR lr pkU verifyCellBound)) (N • (qA + (extractorQueries + verifierQueries))) +
        N * epsSpend (N * (eA + eVR lr pkU verifyCellBound)) (N * (nA + (2 + verifierTotal)))
          (N • (qA + (extractorQueries + verifierQueries))) +
        (ufTagAdv pkU.map σ ((forger lr pkU verQL A N (verifierIC_verifyIC CrtGen.tables)).noProbe τ) +
          failAdv σ (forger lr pkU verQL A N (verifierIC_verifyIC CrtGen.tables))) +
        collAdv lr pkU verQL A N σ := by
  refine le_trans (balance_le_ufTag lr pkU A N σ hdig hqA hnA heA) ?_
  have h := ufTagAdv_le_noProbe pkU.map σ
    (forger lr pkU verQL A N (verifierIC_verifyIC CrtGen.tables)) τ
  gcongr

end Forger

end VoleMole.ROM.IC.RatBalance
