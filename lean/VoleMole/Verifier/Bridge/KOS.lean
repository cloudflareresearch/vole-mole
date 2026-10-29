import VoleMole.Verifier.Bridge.Field

/-!
# Bridge: the executable VOLE check is `Seed/KOS.lean`'s `kosValue`

`Verifier.voleHashReceiver` computes, from `chal1`, the CRT-lifted corrected rows, the masks
`q_mask`, the lifted `Δ` and the prover's `ũ`, the four field elements
`h_i = q_mask[d−1+i] + P_{y_i}(x) + r_i·P_{s₀}(x) + Δ·ũ_i` that go into `chal2`. `Seed/KOS.lean`
models the same check as `kosValue c e Q D u Δ = VOLEHash_c(Q(Δ)) + D(Δ) + e(Δ)·u`, with
`VOLEHash_c(x)_j = r_j·P_x(s₀) + (P_x(s₁), P_x(s₂), P_x(s₃), P_x(t))_j`.

`map_voleHashReceiver`: for any field embedding `φ` (`Bridge/Field.lean`), `φ (h_i)` is
`kosValue c e Q D u Δ i` with
* `c = chOf φ chal1`: `chal1` parsed as `(r, s, t)` (`kos_vole_check_challenge::load`), mapped by
  `φ`; `t` (a 64-bit key) lies in any `T` containing the images of the 64-bit elements;
* `Q(Δ) = φ ∘ hashedRows`: the `ℓ' + d − 1` hashed rows (corrected rows, then the first `d − 1`
  masks; `ℓ' = Params.correctionRows`, so this covers both label-row layouts);
* `D(Δ)_j = φ q_mask[d − 1 + j]` (the four direct masks), `e(Δ) = φ Δ_lifted`, `u_j = φ ũ_j`.

The model's response functions `Q`, `D` vary with `Δ`; the verifier computes them at the proof's
`Δ` only, so the statement is pointwise (`X := Unit`). Across `Δ`, with the commitments fixed,
`Bridge/Chain.lean` (`vole_kosValue`) restates it with `X` the challenge blocks and `Q`, `D` the
committed responses.
-/

namespace VoleMole.Verifier.Bridge

open VoleMole.Arith VoleMole.Verifier

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] (φ : GFEmbedding F)

/-- `chal1` parsed as a VOLEHash challenge `(r, s, t)`, in `F`. -/
def chOf {T : Finset F} (hT : ∀ w : UInt64, φ ⟨w, 0⟩ ∈ T) (chal1 : ByteArray) : Seed.Ch F T :=
  (fun j => φ (gfOfBytes chal1 (16 * j)), fun j => φ (gfOfBytes chal1 (64 + 16 * j)),
    ⟨φ ⟨W128.word chal1 128, 0⟩, hT _⟩)

/-- The rows the VOLE check hashes: the CRT-lifted corrected rows, then `q_mask[0 .. d − 1)`. -/
def hashedRows (p : Params) (rows qMask : Array W128) : Array GF128 :=
  rows.map (·.toGF) ++ (qMask.extract 0 (p.qsDegree - 1)).map (·.toGF)

/-- **The executable VOLE check is `kosValue`.** -/
theorem map_voleHashReceiver {T : Finset F} (hT : ∀ w : UInt64, φ ⟨w, 0⟩ ∈ T) (p : Params)
    (chal1 : ByteArray) (rows qMask : Array W128) (deltaL : GF128) (uTilde : ByteArray)
    (i : Fin 4) :
    φ (voleHashReceiver p chal1 rows qMask deltaL uTilde)[(i : ℕ)]! =
      Seed.kosValue (chOf φ hT chal1) (fun _ : Unit => φ deltaL)
        (fun _ (k : Fin (hashedRows p rows qMask).size) => φ (hashedRows p rows qMask)[k])
        (fun _ j => φ qMask[p.qsDegree - 1 + j]!.toGF) (fun j => φ (gfOfBytes uTilde (16 * j)))
        () i := by
  let xs := hashedRows p rows qMask
  let key : Fin 4 → GF128 := ![gfOfBytes chal1 80, gfOfBytes chal1 96, gfOfBytes chal1 112,
    ⟨W128.word chal1 128, 0⟩]
  have hv : (voleHashReceiver p chal1 rows qMask deltaL uTilde)[(i : ℕ)]! =
      qMask[p.qsDegree - 1 + i]!.toGF + horner (key i) xs +
        horner (gfOfBytes chal1 64) xs * gfOfBytes chal1 (16 * i) +
        deltaL * gfOfBytes uTilde (16 * i) := by
    fin_cases i <;> simp [voleHashReceiver, hashedRows, xs, key]
  rw [hv]
  simp only [GFEmbedding.map_add', GFEmbedding.map_mul', GFEmbedding.map_horner_eq_eval]
  simp only [Seed.kosValue, Seed.voleHash, Seed.voleHashP, Seed.ys, chOf, Pi.add_apply,
    Pi.smul_apply, smul_eq_mul]
  fin_cases i <;> simp [key, xs] <;> ring

end VoleMole.Verifier.Bridge
