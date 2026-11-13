import Mathlib

/-!
# Q1: the key database of a purified ideal cipher holds at most `q` keys

This file is the finite-dimensional linear-algebra core of
`lean/docs/extraction/Q1-quantum-ideal-cipher.md`, §2 (Lemma 2.1).

**Model.** An ideal cipher is a uniformly random function `π : K → Sym(X)`. Its purification is a
vector in `ℂ^{Sym(X)} ⊗ … ⊗ ℂ^{Sym(X)}` (one factor per key) tensored with the adversary's space
`E`. Following `VoleMole/Extraction/`, we write such a vector as a function
`ψ : (K → V) → E`, where `V` is the register alphabet (`V = Sym(X)` for the cipher). The value
`ψ H` is the adversary's (unnormalised) state on the oracle branch `H`. No tensor products are
formed.

**Operations.**
- An adversary step is a linear map `U : E → E`, applied pointwise: `H ↦ U (ψ H)`
  (`LinearMap.compLeft`).
- A cipher query (forward or inverse) is controlled on the adversary's key register and acts on
  the oracle only through the register of that key. In the function picture it is
  `H ↦ Σ_k B k (H k) (ψ H)`, where `B k v : E → E` is the block that applies when key `k` holds
  the permutation `v`. For the forward query,
  `B k σ = |k⟩⟨k|_key ⊗ (|x,y⟩ ↦ |x, y ⊕ σ(x)⟩)`; for the inverse query, `σ⁻¹` in place of `σ`.
  Only the shape "each summand depends on a single register" is used, so the statement covers
  forward and inverse queries, and also queries that reveal the whole value `π(k)`.

**Statement.** Call `ψ` an *`m`-junta state* if it is a sum of functions each of which depends on at
most `m` registers. A function that depends only on the registers in `S` is constant along every
register `k ∉ S`, i.e. register `k` is in the uniform state `|u_Sym⟩` on that summand
(`dependsOn_update`). We prove:
- adversary steps preserve `m`-junta states (`compLeft_mem_junta`);
- a query maps `m`-junta states to `(m+1)`-junta states (`query_mem_junta`);
- hence after `q` queries, starting from the purified initial state (a constant function), the
  joint state is a `q`-junta state (`run_mem_junta`).

The `q`-junta subspace equals the span of the images of the database projectors
`Π_S = ⊗_{k∈S} (1 − |u⟩⟨u|) ⊗ ⊗_{k∉S} |u⟩⟨u|` with `|S| ≤ q`; that identification is in the
paper (Lemma 2.1) and not needed here.
-/

namespace VoleMole.Seed.QuantumCipher

open Finset

set_option linter.unusedSectionVars false

variable {𝕜 : Type*} [Field 𝕜] {K V : Type*} {E : Type*} [AddCommGroup E] [Module 𝕜 E]

/-- `ψ` depends only on the registers in `S`. -/
def DependsOn (S : Finset K) (ψ : (K → V) → E) : Prop :=
  ∀ H H' : K → V, (∀ k ∈ S, H k = H' k) → ψ H = ψ H'

variable (𝕜 K V E) in
/-- The `m`-junta states: sums of functions that each depend on at most `m` registers. -/
def junta (m : ℕ) : Submodule 𝕜 ((K → V) → E) :=
  Submodule.span 𝕜 {ψ | ∃ S : Finset K, S.card ≤ m ∧ DependsOn S ψ}

lemma dependsOn_mono {S T : Finset K} (h : S ⊆ T) {ψ : (K → V) → E} (hψ : DependsOn S ψ) :
    DependsOn T ψ :=
  fun H H' hHH' => hψ H H' fun k hk => hHH' k (h hk)

/-- A register outside `S` is irrelevant to a function that depends only on `S`. On such a
summand the register is in the uniform state. -/
lemma dependsOn_update [DecidableEq K] {S : Finset K} {ψ : (K → V) → E} (hψ : DependsOn S ψ)
    {k : K} (hk : k ∉ S) (H : K → V) (v : V) : ψ (Function.update H k v) = ψ H :=
  hψ _ _ fun j hj => by
    have : j ≠ k := fun h => hk (h ▸ hj)
    simp [Function.update_of_ne this]

lemma mem_junta_of_dependsOn {m : ℕ} {S : Finset K} (hS : S.card ≤ m) {ψ : (K → V) → E}
    (hψ : DependsOn S ψ) : ψ ∈ junta 𝕜 K V E m :=
  Submodule.subset_span ⟨S, hS, hψ⟩

lemma junta_mono {m m' : ℕ} (h : m ≤ m') : junta 𝕜 K V E m ≤ junta 𝕜 K V E m' :=
  Submodule.span_mono fun _ ⟨S, hS, hψ⟩ => ⟨S, hS.trans h, hψ⟩

/-- The purified initial state of the oracle, `|u⟩^{⊗K} ⊗ v₀`, is a constant function. -/
lemma const_mem_junta_zero (v₀ : E) : (fun _ : K → V => v₀) ∈ junta 𝕜 K V E 0 :=
  mem_junta_of_dependsOn (S := ∅) (by simp) fun _ _ _ => rfl

/-- Adversary steps act pointwise and preserve `m`-junta states. -/
lemma compLeft_mem_junta (U : E →ₗ[𝕜] E) {m : ℕ} {ψ : (K → V) → E}
    (hψ : ψ ∈ junta 𝕜 K V E m) : U.compLeft (K → V) ψ ∈ junta 𝕜 K V E m := by
  have hle : junta 𝕜 K V E m ≤ (junta 𝕜 K V E m).comap (U.compLeft (K → V)) := by
    refine Submodule.span_le.2 ?_
    rintro φ ⟨S, hS, hφ⟩
    refine mem_junta_of_dependsOn hS ?_
    intro H H' hHH'
    simp only [LinearMap.compLeft_apply, Function.comp_apply, hφ H H' hHH']
  exact hle hψ

section Query

variable [Fintype K] [DecidableEq K]

/-- A cipher query: `(O ψ)(H) = Σ_k B k (H k) (ψ H)`. Each summand reads only register `k`. -/
def query (B : K → V → E →ₗ[𝕜] E) : ((K → V) → E) →ₗ[𝕜] ((K → V) → E) where
  toFun ψ H := ∑ k, B k (H k) (ψ H)
  map_add' ψ φ := by
    funext H
    simp [Finset.sum_add_distrib]
  map_smul' c ψ := by
    funext H
    simp [Finset.smul_sum]

/-- One summand of a query adds at most the queried key to the set of relevant registers. -/
lemma dependsOn_term (B : K → V → E →ₗ[𝕜] E) (k : K) {S : Finset K} {ψ : (K → V) → E}
    (hψ : DependsOn S ψ) : DependsOn (insert k S) (fun H => B k (H k) (ψ H)) := by
  intro H H' hHH'
  have hk : H k = H' k := hHH' k (mem_insert_self k S)
  have hS : ψ H = ψ H' := hψ H H' fun j hj => hHH' j (mem_insert_of_mem hj)
  simp only [hk, hS]

/-- **A query adds at most one key to the database**: it maps `m`-junta states to
`(m+1)`-junta states. -/
lemma query_mem_junta (B : K → V → E →ₗ[𝕜] E) {m : ℕ} {ψ : (K → V) → E}
    (hψ : ψ ∈ junta 𝕜 K V E m) : query B ψ ∈ junta 𝕜 K V E (m + 1) := by
  have hle : junta 𝕜 K V E m ≤ (junta 𝕜 K V E (m + 1)).comap (query B) := by
    refine Submodule.span_le.2 ?_
    rintro φ ⟨S, hS, hφ⟩
    show query B φ ∈ junta 𝕜 K V E (m + 1)
    have hsum : query B φ = ∑ k, (fun H => B k (H k) (φ H)) := by
      funext H
      simp [query, Finset.sum_apply]
    rw [hsum]
    refine Submodule.sum_mem _ fun k _ => ?_
    refine mem_junta_of_dependsOn ?_ (dependsOn_term B k hφ)
    calc (insert k S).card ≤ S.card + 1 := card_insert_le k S
      _ ≤ m + 1 := Nat.add_le_add_right hS 1
  exact hle hψ

/-- A run of `q` queries interleaved with adversary steps: `U 0`, then for each `n < q` the query
`B n` followed by the step `U (n+1)`. -/
def run (U : ℕ → E →ₗ[𝕜] E) (B : ℕ → K → V → E →ₗ[𝕜] E) (ψ₀ : (K → V) → E) :
    ℕ → (K → V) → E
  | 0 => (U 0).compLeft (K → V) ψ₀
  | n + 1 => (U (n + 1)).compLeft (K → V) (query (B n) (run U B ψ₀ n))

/-- **Database bound (Lemma 2.1).** After `q` queries the joint state is a `q`-junta state: a sum of
branches in each of which at most `q` key registers differ from the uniform state. -/
theorem run_mem_junta (U : ℕ → E →ₗ[𝕜] E) (B : ℕ → K → V → E →ₗ[𝕜] E) {ψ₀ : (K → V) → E}
    (h₀ : ψ₀ ∈ junta 𝕜 K V E 0) (q : ℕ) : run U B ψ₀ q ∈ junta 𝕜 K V E q := by
  induction q with
  | zero => exact compLeft_mem_junta (U 0) h₀
  | succ n ih => exact compLeft_mem_junta (U (n + 1)) (query_mem_junta (B n) ih)

/-- The purified ideal cipher started in `|u⟩^{⊗K} ⊗ v₀`. -/
theorem run_const_mem_junta (U : ℕ → E →ₗ[𝕜] E) (B : ℕ → K → V → E →ₗ[𝕜] E) (v₀ : E)
    (q : ℕ) : run U B (fun _ => v₀) q ∈ junta 𝕜 K V E q :=
  run_mem_junta U B (const_mem_junta_zero v₀) q

end Query

end VoleMole.Seed.QuantumCipher
