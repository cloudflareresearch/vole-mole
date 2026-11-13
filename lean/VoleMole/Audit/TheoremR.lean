import VoleMole.Assumptions.TheoremR
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

end Pomfrit

end VoleMole.Audit.TheoremR
