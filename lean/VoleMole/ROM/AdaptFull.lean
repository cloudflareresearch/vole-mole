import VoleMole.ROM.AdaptChain

/-!
# Adaptively chosen statements, every term explicit (plan M6, statement binding; issue relations)

`ROM/CipherFull.lean`'s bounds are for a fixed statement. Here the prover outputs a proof together
with the index `s : ι` of the statement it proves (`gameA`, `ROM/AdaptGame.lean`); the
straight-line extractor runs on the log and the output statement. For a family of non-delayed
statements with common parameters and an injective instance encoding:

    Pr[accept(stF s) ∧ ¬Extracted(stF s)] ≤ (the `_full` bound) + stmtBindEps q,

`stmtBindEps q = (q₀+3)·(q₂₁+q₀+4)·2⁻²⁵⁶` with `q₀` the prover's `H₂⁰` queries (`+3`: the
extractor's and the verifier's two), the statement-binding term of L4 (H-stmt): an `H₂⁰` answer
equal to the `mu₁` field of an earlier `H₂¹` input or to an earlier `H₂⁰` answer. The
statement is not encoded in the bound otherwise: every other term is the fixed-statement one
(`prEvent_accept_le_adaptive_E`'s charges are those of the statement committed at each query).

* `prEvent_accept_le_adaptive`: the joint experiment (cipher table uniform, then the lazy hash
  oracle), with Post, binding and an opened dead leaf bounded adaptively.
* `moussakaIssue_accept_le_adaptive`, `ratatouilleIssue_accept_le_adaptive`: the issue relations,
  the instance (`t`, `ctx_iss`; `c`, `t_init`, `ctx_iss`) chosen by the prover from a family
  `inst : ι → …` whose instance encodings are injective.

The combined relations are in `ROM/AdaptComb.lean` (Moussaka redemption, Ratatouille spend) and
`ROM/AdaptPomfrit.lean` (PomFRIT, delayed binding); see `docs/probabilistic-plan.md` §2g.
-/

open Finset OracleComp OracleSpec
open scoped ENNReal

namespace VoleMole.ROM.IC

open VoleMole.Prob VoleMole.Arith VoleMole.Verifier VoleMole.Verifier.Bridge VoleMole.ZK.Sim
open VoleMole.EndToEnd VoleMole.SeedExtraction VoleMole.ROM

/-! ## Decoding an injective encoding -/

section Dec

variable {ι : Type}

/-- **The decoder of an encoding `f`**: the (unique, for injective `f`) preimage. -/
noncomputable def decOf (f : ι → ByteArray) (w : ByteArray) : Option ι := by
  classical
  exact if h : ∃ s, f s = w then some h.choose else none

lemma decOf_apply {f : ι → ByteArray} (hf : Function.Injective f) (s : ι) :
    decOf f (f s) = some s := by
  classical
  have h : ∃ s', f s' = f s := ⟨s, rfl⟩
  unfold decOf
  rw [dite_eq_left_of_eq_true (eq_true h)]
  exact congrArg some (hf h.choose_spec)

/-- `X.push b` determines `X`. -/
lemma push_inj {X Y : ByteArray} {b : UInt8} (h : X.push b = Y.push b) : X = Y := by
  have hs : X.size = Y.size := by
    have := congrArg ByteArray.size h
    simp only [ByteArray.size_push] at this
    omega
  have e1 : (X.push b).extract 0 X.size = X := by
    rw [extract_push_of_le _ _ le_rfl, ByteArray.extract_zero_size]
  have e2 : (Y.push b).extract 0 Y.size = Y := by
    rw [extract_push_of_le _ _ le_rfl, ByteArray.extract_zero_size]
  rw [← e1, ← e2, h, hs]

/-- `A ++ D` determines `A`. -/
lemma append_right_inj' {A B D : ByteArray} (h : A ++ D = B ++ D) : A = B := by
  have hs : A.size = B.size := by
    have := congrArg ByteArray.size h
    simp only [ByteArray.size_append] at this
    omega
  have e1 : (A ++ D).extract 0 A.size = A := ByteArray.extract_append_eq_left rfl
  have e2 : (B ++ D).extract 0 B.size = B := ByteArray.extract_append_eq_left rfl
  rw [← e1, ← e2, h, hs]

/-- **Statements with one DST and injective instance encodings have injective `H₂⁰` inputs.** -/
lemma muIn_injective {stF : ι → Statement} {dst : ByteArray} (hdst : ∀ s, (stF s).dst = dst)
    (hinj : Function.Injective fun s => (stF s).instEnc ByteArray.empty) :
    Function.Injective fun s => muIn (stF s) := by
  intro s s' h
  simp only [muIn, hdst] at h
  exact hinj (append_right_inj' (push_inj h))

end Dec

/-! ## The joint experiment -/

/-- **The statement-binding term**: `(q₀+3)·(q₂₁+1 + q₀+3)·2⁻²⁵⁶`, for a prover with `q₀` `H₂⁰`
queries and `q₂₁` `H₂¹` queries (the game adds the extractor's `H₂⁰` query and the verifier's). -/
noncomputable def stmtBindEps (q : Kind → ℕ) : ℝ≥0∞ :=
  (q .mu + 3) * (((q .h21 + 1 + (q .mu + 3) : ℕ) : ℝ≥0∞) / 2 ^ 256)

lemma stmtEps_game (q : Kind → ℕ) :
    ((q + extractorQueries + verifierQueries) .mu : ℝ≥0∞) *
        stmtEps (q + extractorQueries + verifierQueries) .mu = stmtBindEps q := by
  simp only [stmtEps, stmtBindEps, Pi.add_apply, extractorQueries, verifierQueries, or_true,
    ite_true, reduceCtorEq, or_false, ite_false, add_zero]
  push_cast
  ring_nf

section Joint

variable {ι β : Type} (T : CrtTables) (stF : ι → Statement) (dec : ByteArray → Option ι)
  (sys : ι → System GF128) (P : OracleComp specIC (ByteArray × (ι × β)))

/-- **The adaptive bound in the joint experiment** (the cipher table uniform, then the lazy hash
oracle): `prEvent_accept_le_adaptive_E` averaged over the cipher table, with binding (`2·q_E²·2⁻²⁵⁶
+ ε_open`), an opened dead leaf (`ε_open = openHashEps q + q₁·2⁻²⁵⁶`) and Post
(`1024·q_E·q₁·2⁻²⁵⁶`) bounded adaptively. -/
theorem prEvent_accept_le_adaptive (hT : liftInvOk T = true) (st₀ : Statement)
    (hparams : ∀ s, (stF s).params = st₀.params) (hdel : ∀ s, (stF s).delayed = false)
    (cb : Option (ℕ × ByteArray)) (hcomb : ∀ s, (stF s).comb = cb)
    (hdec : ∀ s, dec (muIn (stF s)) = some s) {n : ℕ} (hn : ∀ s, (sys s).length = n) (N : ℕ)
    (Wit : ι → ByteArray → (ℕ → GF128) → Prop)
    (hvals : ∀ s c1 lb w, (stF s).values c1 lb w = (sys s).values w)
    (hdet : ∀ (E : CTable) s, @ChainDet (icPrg E.cipher) T (stF s) (sys s) N (Wit s))
    (qE : ℕ) (hqE : IsQueryBoundP P (fun t => t.isRight = true) qE) (q : Kind → ℕ)
    (hq : IsKindQueryBoundIC P q) :
    let n' := q + extractorQueries + verifierQueries
    Pr{let E ← $ᵗ CTable; let r ← (simulateQ randomOracle (gameA T stF P E)).run' ∅}[
        r.2.2.accept = true ∧ ¬@Extracted (icPrg E.cipher) _ (stF (stOut r)) (Wit (stOut r)) r] ≤
      n' .h21 * epsKOS #chal3Blocks (Chain.kosL st₀) +
        n' .h22 * ENNReal.ofReal (Seed.epsQS (2 ^ 128) (2 ^ 64) n) +
        n' .h23 * ((N : ℝ≥0∞) / 2 ^ 128) + hitSum n' (hitEps n' (combCount cb n')) +
        n' .mu * stmtEps n' .mu +
        (2 * qE ^ 2 * (2 ^ 256)⁻¹ + (openHashEps q + q .h1 * (2 ^ 256 : ℝ≥0∞)⁻¹)) +
        (openHashEps q + q .h1 * (2 ^ 256 : ℝ≥0∞)⁻¹) +
        ((qE * 2 : ℕ) : ℝ≥0∞) * (((512 * q .h1 : ℕ) : ℝ≥0∞) * (2 ^ 256 : ℝ≥0∞)⁻¹) := by
  intro n'
  have hE := fun E => prEvent_accept_le_adaptive_E T stF dec sys P E hT st₀ hparams hdel cb hcomb
    hdec hn N Wit hvals (hdet E) q hq
  have hdo := prEvent_joint_deadOpen_le_A T stF P st₀.params hparams q hq
  refine (prEvent_avg_le_add3 _ _ (fun E r => bindFailA stF E r) (fun E r => deadOpenA stF E r)
    (fun E r => PostOut E r) _ hE).trans ?_
  gcongr
  · exact (prEvent_joint_bindFail_le_A T stF P qE hqE).trans (add_le_add le_rfl hdo)
  · exact prEvent_joint_postOut_le_A T stF P qE hqE q hq

end Joint

/-! ## The issue relations -/

section Issue

variable {ι β : Type}

/-- **Moussaka issuance with an adaptively chosen instance**, in the random-oracle and
ideal-cipher model, every term explicit: the prover `P` (at most `q_E` cipher queries and `q k`
hash queries of each kind `k`) outputs a proof and an index `s` of the instance
`(t, ctx_iss) = inst s` it proves, from a family with injective instance encodings
(`t ‖ ctx_iss`, e.g. `t` of fixed length, `Spec.Moussaka.issueEncode_inj`); the straight-line
extractor runs on the log at that instance and the executable verifier checks the proof for it.
The verifier accepts and the extractor's candidate is not an issuance witness for the chosen
instance with probability

    ≤ (the bound of `moussakaIssue_accept_le_full`) + (q₀+3)·(q₂₁+q₀+4)·2⁻²⁵⁶. -/
theorem moussakaIssue_accept_le_adaptive (inst : ι → ByteArray × ByteArray) (labelRows : Bool)
    (hinj : Function.Injective fun s =>
      (moussakaIssue (inst s).1 (inst s).2 labelRows).instEnc ByteArray.empty)
    (P : OracleComp specIC (ByteArray × (ι × β))) (qE : ℕ)
    (hqE : IsQueryBoundP P (fun t => t.isRight = true) qE) (q : Kind → ℕ)
    (hq : IsKindQueryBoundIC P q) :
    Pr{let E ← $ᵗ CTable; let r ← (simulateQ randomOracle (gameA CrtGen.tables
      (fun s => moussakaIssue (inst s).1 (inst s).2 labelRows) P E)).run' ∅}[
        r.2.2.accept = true ∧ ¬@Extracted (icPrg E.cipher) _
          (moussakaIssue (inst (stOut r)).1 (inst (stOut r)).2 labelRows)
          (fun _ => moussakaIssueWit (fun k => fnOf (inst (stOut r)).1 k.val)
            (fnOf (inst (stOut r)).2)) r] ≤
      (q .h21 + 1) * (2 ^ 150 : ℝ≥0∞)⁻¹ +
        (q .h22 + 1) * ENNReal.ofReal (Seed.epsQS (2 ^ 128) (2 ^ 64) 4008) +
        (q .h23 + 1) * ((9 : ℝ≥0∞) / 2 ^ 128) +
        (2 * qE ^ 2 * (2 ^ 256)⁻¹ + (openHashEps q + q .h1 * (2 ^ 256 : ℝ≥0∞)⁻¹)) +
        (openHashEps q + q .h1 * (2 ^ 256 : ℝ≥0∞)⁻¹) +
        ((qE * 2 : ℕ) : ℝ≥0∞) * (((512 * q .h1 : ℕ) : ℝ≥0∞) * (2 ^ 256 : ℝ≥0∞)⁻¹) +
        chainHitEps q + stmtBindEps q := by
  classical
  set stF : ι → Statement := fun s => moussakaIssue (inst s).1 (inst s).2 labelRows
  set st₀ := moussakaIssue ByteArray.empty ByteArray.empty labelRows
  have hmu := muIn_injective (stF := stF) (dst := st₀.dst) (fun _ => rfl) hinj
  have h := prEvent_accept_le_adaptive CrtGen.tables stF (decOf fun s => muIn (stF s))
    (fun s => moussakaIssueSys (inst s).1 (inst s).2) P liftInvOk_tables st₀ (fun _ => rfl)
    (fun _ => rfl) none (fun _ => rfl) (fun s => decOf_apply hmu s)
    (fun s => Moussaka.issueSystem_length _ _) 9
    (fun s _ => moussakaIssueWit (fun k => fnOf (inst s).1 k.val) (fnOf (inst s).2))
    (fun s c1 lb w => moussakaIssue_values (inst s).1 (inst s).2 labelRows c1 lb w)
    (fun E s => by
      let _ : HasPrg := icPrg E.cipher
      exact fun ch known acc hv A hA hAS hkos hQS hP =>
        moussakaIssue_extract_chain (inst s).1 (inst s).2 labelRows ch hv hA hAS hkos hP.1 hQS
          admissible deltaBlocks deltaBlocks_injOn acc hP.2)
    qE hqE q hq
  refine h.trans ?_
  rw [hitSum_add_extractorQueries, hitSum_hitEps, stmtEps_game]
  have hkos : epsKOS #chal3Blocks (Chain.kosL st₀) ≤ (2 ^ 150 : ℝ≥0∞)⁻¹ :=
    epsKOS_chal3Blocks_le _ (by norm_num [st₀, moussakaIssue]) (by norm_num [st₀, moussakaIssue])
  simp only [Pi.add_apply, extractorQueries, verifierQueries, reduceCtorEq, or_self, ite_false,
    add_zero, Nat.cast_add, Nat.cast_one, Nat.cast_ofNat]
  calc _ ≤ ((q .h21 : ℝ≥0∞) + 1) * (2 ^ 150 : ℝ≥0∞)⁻¹ +
          ((q .h22 : ℝ≥0∞) + 1) * ENNReal.ofReal (Seed.epsQS (2 ^ 128) (2 ^ 64) 4008) +
          ((q .h23 : ℝ≥0∞) + 1) * ((9 : ℝ≥0∞) / 2 ^ 128) + chainHitEps q + stmtBindEps q +
          (2 * qE ^ 2 * (2 ^ 256)⁻¹ + (openHashEps q + q .h1 * (2 ^ 256 : ℝ≥0∞)⁻¹)) +
          (openHashEps q + q .h1 * (2 ^ 256 : ℝ≥0∞)⁻¹) +
          ((qE * 2 : ℕ) : ℝ≥0∞) * (((512 * q .h1 : ℕ) : ℝ≥0∞) * (2 ^ 256 : ℝ≥0∞)⁻¹) := by
        gcongr
    _ = _ := by ring

/-- **Ratatouille issuance with an adaptively chosen instance** `(c, t_init, ctx_iss) = inst s`
(as `moussakaIssue_accept_le_adaptive`, with `ε_QS(3776)`; the encoding `c ‖ le64(t_init) ‖ ctx_iss`
injective on the family, e.g. `c` of fixed length and `t_init < 2⁶⁴`). -/
theorem ratatouilleIssue_accept_le_adaptive (inst : ι → ByteArray × ℕ × ByteArray)
    (labelRows : Bool)
    (hinj : Function.Injective fun s =>
      (ratatouilleIssue (inst s).1 (inst s).2.1 (inst s).2.2 labelRows).instEnc ByteArray.empty)
    (P : OracleComp specIC (ByteArray × (ι × β))) (qE : ℕ)
    (hqE : IsQueryBoundP P (fun t => t.isRight = true) qE) (q : Kind → ℕ)
    (hq : IsKindQueryBoundIC P q) :
    Pr{let E ← $ᵗ CTable; let r ← (simulateQ randomOracle (gameA CrtGen.tables
      (fun s => ratatouilleIssue (inst s).1 (inst s).2.1 (inst s).2.2 labelRows) P E)).run' ∅}[
        r.2.2.accept = true ∧ ¬@Extracted (icPrg E.cipher) _
          (ratatouilleIssue (inst (stOut r)).1 (inst (stOut r)).2.1 (inst (stOut r)).2.2 labelRows)
          (fun _ => ratatouilleIssueWit (fnOf (inst (stOut r)).1) (inst (stOut r)).2.1
            (fnOf (inst (stOut r)).2.2)) r] ≤
      (q .h21 + 1) * (2 ^ 150 : ℝ≥0∞)⁻¹ +
        (q .h22 + 1) * ENNReal.ofReal (Seed.epsQS (2 ^ 128) (2 ^ 64) 3776) +
        (q .h23 + 1) * ((9 : ℝ≥0∞) / 2 ^ 128) +
        (2 * qE ^ 2 * (2 ^ 256)⁻¹ + (openHashEps q + q .h1 * (2 ^ 256 : ℝ≥0∞)⁻¹)) +
        (openHashEps q + q .h1 * (2 ^ 256 : ℝ≥0∞)⁻¹) +
        ((qE * 2 : ℕ) : ℝ≥0∞) * (((512 * q .h1 : ℕ) : ℝ≥0∞) * (2 ^ 256 : ℝ≥0∞)⁻¹) +
        chainHitEps q + stmtBindEps q := by
  classical
  set stF : ι → Statement := fun s =>
    ratatouilleIssue (inst s).1 (inst s).2.1 (inst s).2.2 labelRows
  set st₀ := ratatouilleIssue ByteArray.empty 0 ByteArray.empty labelRows
  have hmu := muIn_injective (stF := stF) (dst := st₀.dst) (fun _ => rfl) hinj
  have h := prEvent_accept_le_adaptive CrtGen.tables stF (decOf fun s => muIn (stF s))
    (fun s => ratatouilleIssueSys (inst s).1 (inst s).2.1 (inst s).2.2) P liftInvOk_tables st₀
    (fun _ => rfl) (fun _ => rfl) none (fun _ => rfl) (fun s => decOf_apply hmu s)
    (fun s => Ratatouille.issueSystem_length _ _ _) 9
    (fun s _ => ratatouilleIssueWit (fnOf (inst s).1) (inst s).2.1 (fnOf (inst s).2.2))
    (fun s c1 lb w => ratatouilleIssue_values (inst s).1 (inst s).2.1 (inst s).2.2 labelRows c1
      lb w)
    (fun E s => by
      let _ : HasPrg := icPrg E.cipher
      exact fun ch known acc hv A hA hAS hkos hQS hP =>
        ratatouilleIssue_extract_chain (inst s).1 (inst s).2.1 (inst s).2.2 labelRows ch hv hA hAS
          hkos hP.1 hQS admissible deltaBlocks deltaBlocks_injOn acc hP.2)
    qE hqE q hq
  refine h.trans ?_
  rw [hitSum_add_extractorQueries, hitSum_hitEps, stmtEps_game]
  have hkos : epsKOS #chal3Blocks (Chain.kosL st₀) ≤ (2 ^ 150 : ℝ≥0∞)⁻¹ :=
    epsKOS_chal3Blocks_le _ (by norm_num [st₀, ratatouilleIssue])
      (by norm_num [st₀, ratatouilleIssue])
  simp only [Pi.add_apply, extractorQueries, verifierQueries, reduceCtorEq, or_self, ite_false,
    add_zero, Nat.cast_add, Nat.cast_one, Nat.cast_ofNat]
  calc _ ≤ ((q .h21 : ℝ≥0∞) + 1) * (2 ^ 150 : ℝ≥0∞)⁻¹ +
          ((q .h22 : ℝ≥0∞) + 1) * ENNReal.ofReal (Seed.epsQS (2 ^ 128) (2 ^ 64) 3776) +
          ((q .h23 : ℝ≥0∞) + 1) * ((9 : ℝ≥0∞) / 2 ^ 128) + chainHitEps q + stmtBindEps q +
          (2 * qE ^ 2 * (2 ^ 256)⁻¹ + (openHashEps q + q .h1 * (2 ^ 256 : ℝ≥0∞)⁻¹)) +
          (openHashEps q + q .h1 * (2 ^ 256 : ℝ≥0∞)⁻¹) +
          ((qE * 2 : ℕ) : ℝ≥0∞) * (((512 * q .h1 : ℕ) : ℝ≥0∞) * (2 ^ 256 : ℝ≥0∞)⁻¹) := by
        gcongr
    _ = _ := by ring

end Issue

end VoleMole.ROM.IC
