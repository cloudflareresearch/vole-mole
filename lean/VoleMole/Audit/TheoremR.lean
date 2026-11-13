import VoleMole.Assumptions.TheoremRBad
import VoleMole.Assumptions.UOVLinks

/-!
# Non-vacuity of Theorem R

`Assumptions/TheoremR.lean` (`lean/docs/security/ompr-shift-algebra.md` §2), checked at PomFRIT's
trapdoor (`Links.pomTrap`: Def. 3.1's relation `relP`, the honest Issuer `honestPre`, any fixed
key) with `τ = 17` and UOV's class relation `Links.uovCls` (equality up to a nonzero scalar).

* The hypotheses of `thmR` are `τ ≥ 7`, `q ≥ 1` and that the class relation is an equivalence:
  `uovCls_equiv`.
* **The reduction class contains the natural reductions.**
  - Every OMPR adversary, run without `A**_D` (`liftRed`), with its OMPR advantage
    (`redExp_liftRed`): the experiment's challenger is the OMPR challenger.
  - The guessing reduction of [UA] Prop. 8(a) (`guessRed`): it guesses `g ∈ [τ]^{q+1}`, sends
    `h_k = t_k − δ_{k,g_k}` for challenge targets `t_k`, answers the `q` junk queries with `q`
    calls, and outputs the `q + 1` forgeries. Its success probability `≈ τ^{−(q+1)}` is not
    mechanized; the term shows that the interface (lists, junk, output, with rewinding by
    re-querying) is the one such a reduction needs.
* `thmR` applies to both at PomFRIT's trapdoor.
* **The bad events** (`Assumptions/TheoremRBad.lean`): UOV's class relation is `scls GF256 45`
  (`uovCls_eq_scls`), so `thmR_V4` (Theorem R with `V⁴·2^{−343}`) and `corR'` (Corollary R′)
  apply at PomFRIT's trapdoor. Their hypothesis, a bound `T` on the messages to `A**_D`, holds for
  the guessing reduction with `T = q + 3` (`guessR_bound`: `q + 1` shift lists, one junk query,
  one output query).
-/

open OracleComp OracleSpec VoleMole.ROM.OneMore VoleMole.ROM.OneMore.Pomfrit
open VoleMole.Assumptions.UOV VoleMole.Assumptions.UOV.Links VoleMole.Assumptions.TheoremR
open scoped ENNReal

namespace VoleMole.Audit.TheoremR

/-- UOV's class relation is an equivalence. -/
theorem uovCls_equiv : Equivalence uovCls where
  refl := uovCls_refl
  symm := by
    rintro t t' ⟨μ, h0, rfl⟩
    exact ⟨μ⁻¹, inv_ne_zero h0, by rw [smul_smul, inv_mul_cancel₀ h0, one_smul]⟩
  trans := by
    rintro t t' t'' ⟨μ, h0, rfl⟩ ⟨μ', h0', rfl⟩
    exact ⟨μ * μ', mul_ne_zero h0 h0', by rw [smul_smul]⟩

/-! ## The guessing reduction -/

section Guess

variable {DR : Type} {AR : DR → Type} {τ q : ℕ} {T S : Type}

/-- The reduction's queries: a challenge target, a preimage call, and the three messages to
`A**_D`. -/
def qTgt (x : ℕ) : OracleComp (specRed AR τ q ℕ T S) (Option T) :=
  liftM ((specRed AR τ q ℕ T S).query (.inl (.inr (.inl (x, ())))))

@[inherit_doc qTgt]
def qInv (t : T) : OracleComp (specRed AR τ q ℕ T S) S :=
  liftM ((specRed AR τ q ℕ T S).query (.inl (.inr (.inr t))))

@[inherit_doc qTgt]
def qLst (hs : List T) : OracleComp (specRed AR τ q ℕ T S) (Fin τ → T) :=
  liftM ((specRed AR τ q ℕ T S).query (.inr (.inl hs)))

@[inherit_doc qTgt]
def qJunk (H : List T) : OracleComp (specRed AR τ q ℕ T S) (List T) :=
  liftM ((specRed AR τ q ℕ T S).query (.inr (.inr (.inl H))))

@[inherit_doc qTgt]
def qFin (H : List T) (ans : List S) : OracleComp (specRed AR τ q ℕ T S) (Option (Out τ q S)) :=
  liftM ((specRed AR τ q ℕ T S).query (.inr (.inr (.inr (H, ans)))))

variable [AddCommGroup T]

/-- The requests of one run: for `m` more requests after `hs`, get the shift list, a challenge
target `t`, and send `h = t − δ_g`. -/
def guessRun (g : ℕ → Fin τ) : ℕ → List T → OracleComp (specRed AR τ q ℕ T S) (List T)
  | 0, hs => pure hs
  | m + 1, hs => do
    let t ← qTgt hs.length
    let δ ← qLst hs
    guessRun g m (hs ++ [t.getD 0 - δ (g hs.length)])

/-- **The guessing reduction** with the guess `g`: one run of `A**_D`, the junk queries answered
with `q` calls, the forgeries output as claims on the `q + 1` challenge targets. -/
def guessR [NeZero τ] (g : Fin (q + 1) → Fin τ) :
    OracleComp (specRed AR τ q ℕ T S) (List (ℕ × S)) := do
  let H ← guessRun (fun k => if h : k < q + 1 then g ⟨k, h⟩ else 0) (q + 1) []
  let us ← qJunk H
  let ans ← us.mapM qInv
  let o ← qFin H ans
  pure (match o with
    | some (_, ss) => ss.zipIdx.map fun p => (p.2, p.1)
    | none => [])

/-- The guessing reduction with a uniform guess. -/
def guessRed [NeZero τ] {PK : Type} (_ : PK) :
    ProbComp (OracleComp (specRed AR τ q ℕ T S) (List (ℕ × S))) := do
  let g ← $ᵗ (Fin (q + 1) → Fin τ)
  pure (guessR g)

end Guess

/-! ## The query bound of the guessing reduction -/

section GuessBound

variable {DR : Type} {AR : DR → Type} {τ q : ℕ} {T S : Type} [AddCommGroup T]

/-- A message to `A**_D`. -/
abbrev isAdv : (DR ⊕ ((ℕ × Unit) ⊕ T)) ⊕ (List T ⊕ (List T ⊕ (List T × List S))) → Prop :=
  fun o => o.isRight = true

omit [AddCommGroup T] in
theorem qTgt_bound (x : ℕ) :
    IsQueryBoundP (qTgt (AR := AR) (τ := τ) (q := q) (T := T) (S := S) x) isAdv 0 := by
  unfold qTgt; exact (isQueryBoundP_query_iff isAdv _ 0).mpr (by simp [isAdv])

omit [AddCommGroup T] in
theorem qInv_bound (t : T) :
    IsQueryBoundP (qInv (AR := AR) (τ := τ) (q := q) (S := S) t) isAdv 0 := by
  unfold qInv; exact (isQueryBoundP_query_iff isAdv _ 0).mpr (by simp [isAdv])

omit [AddCommGroup T] in
theorem qLst_bound (hs : List T) :
    IsQueryBoundP (qLst (AR := AR) (τ := τ) (q := q) (S := S) hs) isAdv 1 := by
  unfold qLst; exact (isQueryBoundP_query_iff isAdv _ 1).mpr (by simp)

omit [AddCommGroup T] in
theorem qJunk_bound (H : List T) :
    IsQueryBoundP (qJunk (AR := AR) (τ := τ) (q := q) (S := S) H) isAdv 1 := by
  unfold qJunk; exact (isQueryBoundP_query_iff isAdv _ 1).mpr (by simp)

omit [AddCommGroup T] in
theorem qFin_bound (H : List T) (ans : List S) :
    IsQueryBoundP (qFin (AR := AR) (τ := τ) (q := q) H ans) isAdv 1 := by
  unfold qFin; exact (isQueryBoundP_query_iff isAdv _ 1).mpr (by simp)

theorem guessRun_bound (g : ℕ → Fin τ) : ∀ (k : ℕ) (hs : List T),
    IsQueryBoundP (guessRun (AR := AR) (q := q) (S := S) g k hs) isAdv k
  | 0, hs => by simp [guessRun]
  | k + 1, hs => by
    simp only [guessRun]
    refine (isQueryBoundP_bind (qTgt_bound hs.length) fun t _ =>
      isQueryBoundP_bind (qLst_bound hs) fun δ _ => guessRun_bound g k _).mono (by omega)

omit [AddCommGroup T] in
theorem mapM_qInv_bound (L : List T) :
    IsQueryBoundP (L.mapM (qInv (AR := AR) (τ := τ) (q := q) (S := S))) isAdv 0 := by
  induction L with
  | nil => simp
  | cons t L ih =>
    rw [List.mapM_cons]
    exact isQueryBoundP_bind (n := 0) (m := 0) (qInv_bound t) fun _ _ =>
      isQueryBoundP_bind (n := 0) (m := 0) ih fun _ _ => by simp

/-- **The guessing reduction sends `q + 3` messages to `A**_D`**: `q + 1` shift lists, the junk
query and the output query. -/
theorem guessR_bound [NeZero τ] (g : Fin (q + 1) → Fin τ) :
    IsQueryBoundP (guessR (AR := AR) (T := T) (S := S) g) isAdv (q + 3) := by
  unfold guessR
  refine (isQueryBoundP_bind (guessRun_bound (AR := AR) (S := S) _ (q + 1) []) fun H _ =>
    isQueryBoundP_bind (qJunk_bound H) fun us _ =>
      isQueryBoundP_bind (mapM_qInv_bound us) fun ans _ =>
        isQueryBoundP_bind (qFin_bound H ans) fun o _ =>
          isQueryBoundP_pure isAdv _ 0).mono (by omega)

theorem guessRed_bound [NeZero τ] {PK : Type} (pk : PK) :
    ∀ r ∈ support (guessRed (AR := AR) (τ := τ) (q := q) (T := T) (S := S) pk),
      IsQueryBoundP r isAdv (q + 3) := by
  intro r hr
  simp only [guessRed, mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hr
  obtain ⟨g, -, rfl⟩ := hr
  exact guessR_bound g

end GuessBound

/-! ## Theorem R at PomFRIT's trapdoor -/

section Pomfrit

variable (pk : VoleMole.Verifier.UovPk) (sk : VoleMole.Spec.Signer) (q n c J K₀ : ℕ)

/-- The reduction's world in these examples: a random oracle `Unit → Bool` (its coins). -/
abbrev AB : Unit → Type := fun _ => Bool

open Classical in
/-- **Theorem R** at PomFRIT's trapdoor, `τ = 17`, for every reduction. -/
example (hq : 1 ≤ q) (R : VoleMole.Verifier.UovPk →
    ProbComp (OracleComp (specRed AB 17 q ByteArray TG SIss) (List (ByteArray × SIss)))) :=
  thmR uovCls (pomTrap (pure (pk, sk)) honestPre) n uovCls_equiv (by norm_num) hq c J K₀ R

open Classical in
/-- **Theorem R for the guessing reduction** at PomFRIT's trapdoor, `τ = 17`: `n = q + 1`
targets, `c = q` calls, `q` junk targets, one completed run. -/
example (hq : 1 ≤ q) :=
  thmR (AR := AB) uovCls (pomTrap (pure (pk, sk)) honestPre) (q + 1) uovCls_equiv
    (τ := 17) (by norm_num) hq q q 1 guessRed

open Classical in
/-- **Every OMPR adversary is in the class**, with its OMPR advantage, at PomFRIT's trapdoor. -/
example (B : VoleMole.Verifier.UovPk →
    ProbComp (OracleComp (specB AB ByteArray Unit TG SIss) (List (ByteArray × SIss)))) :=
  redExp_liftRed (τ := 17) (q := q) (pomTrap (pure (pk, sk)) honestPre) n c B

/-- UOV's class relation is the scalar-class relation of `Assumptions/TheoremRBad.lean`. -/
theorem uovCls_eq_scls : uovCls = scls VoleMole.Arith.GF256 45 := rfl

open Classical in
/-- **Theorem R with `V⁴·2^{−343}`** at PomFRIT's trapdoor, `τ = 17`, for every reduction with at
most `T` messages to `A**_D`. -/
example (hq : 1 ≤ q) (Tq : ℕ) (R : VoleMole.Verifier.UovPk →
    ProbComp (OracleComp (specRed AB 17 q ByteArray TG SIss) (List (ByteArray × SIss))))
    (hR : ∀ pk, ∀ r ∈ support (R pk), IsQueryBoundP r (fun o => o.isRight = true) Tq) :=
  thmR_V4 (pomTrap (pure (pk, sk)) honestPre) n (by norm_num) hq c Tq R hR

open Classical in
/-- **Theorem R with `V⁴·2^{−343}` for the guessing reduction**: its query bound holds
(`guessRed_bound`, `T = q + 3`), so every term is explicit: `V = (q + 1) + q + 18·(q + 1)(q + 3)`. -/
example (hq : 1 ≤ q) :=
  thmR_V4 (AR := AB) (pomTrap (pure (pk, sk)) honestPre) (q + 1) (τ := 17) (by norm_num) hq q
    (q + 3) guessRed fun pk => guessRed_bound pk

end Pomfrit

end VoleMole.Audit.TheoremR
