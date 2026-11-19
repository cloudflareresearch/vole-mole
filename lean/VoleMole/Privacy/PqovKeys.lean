import VoleMole.Privacy.PqovDelta
import VoleMole.Spec.PqovKey

/-!
# The bounds on `δ` and Theorem 4(b′) over pqov's real key generation

`Privacy/PqovDelta.lean` bounds the fraction `δ` of bad vinegars on average over the key family
`keyO0 P1 P2` (oil matrix `O = 0`). Here the same bounds hold for **pqov's keys with any oil matrix**
(`Spec.Pqov.pqovKey O P1 P2`, `Spec/PqovKey.lean`: the `P1`, `P2` blocks and the `P3` block that
`calculate_F2_P3` computes from them and `O`):

* `pqovKey_zero`: for `O = 0` the key is `keyO0` (its `P3` block is `0`), so the results below
  generalize those of `PqovDelta.lean`.
* `oilSpace_pqovKey` (`Spec/PqovKey.lean`): `P` vanishes on the oil space, so pqov's signer model is
  correct for the key with its own `O`.
* `sysCoef_pqovKey`: `S = (P1 + P1ᵀ)·O + P2`, so for fixed `O` and `P1` the map `P2 ↦ S` is a
  translate of the bijection `p2Equiv` and **`S` is uniform when `P2` is** (`sysMat_pqovKey`).
* **`avg_delta_pqovKey`**, **`avg_delta_pow_pqovKey`**, **`avg_delta255_pqovKey`**: for every oil
  matrix `O` and `P1` part, over a uniform `P2` part, `E[δ] ≤ 1/255 + 256⁻⁷⁴`,
  `E[δ^m] ≤ 255⁻ᵐ + 256^m/(255·256⁷⁴)` (`m ≤ 74`), `E[δ²⁵⁵] ≤ 255⁻³⁷ + 1/(255·256³⁷)`.
* **`anonymityNC_pqov_pqovKeys`**, **`anonymityNCRO_pqov_pqovKeys`**: Theorem 4(b′) with pqov's
  signers (each Anchor with its own oil matrix `O c`) for keys `pqovKey (O c) (P1 c) (κ c)`,
  averaged over independent uniform `P2` parts `κ` and the vinegar tables, for every choice of the
  oil matrices and `P1` parts: abort term `≤ 4·(255⁻³⁷ + 1/(255·256³⁷))`.

**The modelling step.** pqov expands `P1 ‖ P2` from `pk_seed` by AES-128-CTR
(`prng_gen_publicinputs`, `Verifier.Keygen.publicInputs`) and draws `pk_seed ‖ O` from
`SHAKE256(sk_seed)`. The theorems take `O` and `P1` arbitrary and fixed and `P2` uniform: this is
the case when the `P2` bytes of the AES-CTR stream are uniform given `(O, P1)` (AES-128 under the
uniform key `pk_seed` as a random function, and `O` independent of `pk_seed`: SHAKE256 as a random
oracle). Since the bounds hold for every `(O, P1)`, they hold on average over any law of `(O, P1)`
with `P2` uniform given `(O, P1)`. Neither step (AES-CTR output as uniform, SHAKE256's split) is
derived here.
-/

open Finset

set_option synthInstance.maxSize 1024

namespace VoleMole.Privacy.Moussaka

open VoleMole.Spec VoleMole.Spec.Pqov VoleMole.Arith VoleMole.Arith.UOV VoleMole.ZK.Sim

section Keys

variable (O : OilMat) (P1 : ℕ → GF256)

lemma keyO0_eq_keyP12 (P2 : P2Part) : keyO0 P1 P2 = keyP12 P1 P2 := rfl

/-- **For `O = 0`, pqov's key is `keyO0`** (`M = Oᵀ(P1·O + P2) = 0`, so `P3 = 0`). -/
theorem pqovKey_zero (P2 : P2Part) : (pqovKey 0 P1 P2).map = (keyO0 P1 P2).map := by
  funext n
  unfold pqovKey
  dsimp only
  split_ifs with hn
  · rfl
  · rw [keyO0_map_p3 P1 P2 (by omega)]
    refine Finset.sum_eq_zero fun x _ => ?_
    simp [pqovP3, pqovM]

/-- pqov's `S` for the `P1` part, `(P1 + P1ᵀ)·O`, as system coefficients. -/
noncomputable def sP1C : Coef := fun k i j => sP1 O P1 k i j

/-- `P2 ↦ S = (P1 + P1ᵀ)·O + P2`: a bijection, for fixed `O` and `P1`. -/
noncomputable def sEquiv : P2Part ≃ Coef := p2Equiv.trans (Equiv.addLeft (sP1C O P1))

lemma sysMat_pqovKey (P2 : P2Part) (v : Vin) :
    sysMat (pqovKey O P1 P2) O v = lin v (sEquiv O P1 P2) := by
  rw [sysMat_eq_sum]
  ext k j
  simp only [Matrix.of_apply, lin, AddMonoidHom.coe_mk, ZeroHom.coe_mk, sysCoef_pqovKey, sEquiv,
    Equiv.trans_apply, Equiv.coe_addLeft, Pi.add_apply, sP1C, p2Equiv, Equiv.coe_fn_mk]

/-- **`E_{P2}[δ] ≤ 1/255 + 256⁻⁷⁴`** for pqov's keys `pqovKey O P1 P2`, any `O` and `P1`, uniform
`P2`. -/
theorem avg_delta_pqovKey :
    (∑ P2 : P2Part, delta (pqovKey O P1 P2) O) / Fintype.card P2Part ≤
      1 / 255 + 1 / 256 ^ 74 := by
  have e : pr (P2Part × Vin) (fun z => (lin z.2 (sEquiv O P1 z.1)).det = 0) =
      pr (Coef × Vin) (fun z => (lin z.2 z.1).det = 0) :=
    pr_equiv ((sEquiv O P1).prodCongr (Equiv.refl Vin)) (fun z => (lin z.2 z.1).det = 0)
  rw [pr_prod] at e
  have hd : ∀ P2 : P2Part, delta (pqovKey O P1 P2) O =
      pr Vin (fun v => (lin v (sEquiv O P1 P2)).det = 0) :=
    fun P2 => pr_congr fun v => by rw [sysMat_pqovKey]
  simp only [hd]
  rw [e]
  exact pr_singular_avg

/-- **`E_{P2}[δ^m] ≤ (1/255)^m + 256^m / (255·256⁷⁴)`** for `m ≤ 74`, pqov's keys. -/
theorem avg_delta_pow_pqovKey (m : ℕ) (hm : m ≤ 74) :
    (∑ P2 : P2Part, delta (pqovKey O P1 P2) O ^ m) / Fintype.card P2Part ≤
      (1 / 255) ^ m + 256 ^ m / (255 * 256 ^ 74) := by
  have e : pr (P2Part × (Fin m → Vin)) (fun z => ∀ l, (lin (z.2 l) (sEquiv O P1 z.1)).det = 0) =
      pr (Coef × (Fin m → Vin)) (fun z => ∀ l, (lin (z.2 l) z.1).det = 0) :=
    pr_equiv ((sEquiv O P1).prodCongr (Equiv.refl (Fin m → Vin)))
      (fun z => ∀ l, (lin (z.2 l) z.1).det = 0)
  rw [pr_prod] at e
  have hd : ∀ P2 : P2Part, delta (pqovKey O P1 P2) O ^ m =
      pr (Fin m → Vin) (fun vs => ∀ l, (lin (vs l) (sEquiv O P1 P2)).det = 0) := fun P2 => by
    rw [pr_forall_fin m (fun v : Vin => (lin v (sEquiv O P1 P2)).det = 0)]
    exact congrArg (· ^ m) (pr_congr fun v => by rw [sysMat_pqovKey])
  simp only [hd]
  rw [e]
  refine (pr_singular_all m).trans ?_
  have hσ := pr_det_zero_le
  have hσ0 := pr_nonneg (α := Mat45) (fun M => M.det = 0)
  have h1 : pr Mat45 (fun M => M.det = 0) ^ m ≤ (1 / 255) ^ m := pow_le_pow_left₀ hσ0 hσ m
  have h2 := pr_dependent_le m hm
  linarith

/-- **pqov's abort probability on average over its real key generation**: for every oil matrix
`O` and `P1` part, `E_{P2}[δ²⁵⁵] ≤ 255⁻³⁷ + 1/(255·256³⁷)` (about `2⁻²⁹⁵·⁸`). -/
theorem avg_delta255_pqovKey :
    (∑ P2 : P2Part, delta (pqovKey O P1 P2) O ^ 255) / Fintype.card P2Part ≤ abortKeys := by
  have hcard : (0 : ℝ) < Fintype.card P2Part := by exact_mod_cast Fintype.card_pos
  have hle : ∀ P2 : P2Part, delta (pqovKey O P1 P2) O ^ 255 ≤ delta (pqovKey O P1 P2) O ^ 37 :=
    fun P2 => pow_le_pow_of_le_one (pr_nonneg _) (pr_le_one _) (by norm_num)
  refine (div_le_div_of_nonneg_right (Finset.sum_le_sum fun P2 _ => hle P2) hcard.le).trans ?_
  refine (avg_delta_pow_pqovKey O P1 37 (by norm_num)).trans (le_of_eq ?_)
  unfold abortKeys
  congr 1
  rw [show (256 : ℝ) ^ 74 = 256 ^ 37 * 256 ^ 37 by rw [← pow_add]]
  field_simp

end Keys

lemma avg_delta255_pqovKeys (O : Bool → OilMat) (P1 : Bool → ℕ → GF256) (c : Bool) :
    (∑ κ : Bool → P2Part, delta (pqovKey (O c) (P1 c) (κ c)) (O c) ^ 255) /
      Fintype.card (Bool → P2Part) ≤ abortKeys := by
  rw [avg_bool_arrow (fun P2 => delta (pqovKey (O c) (P1 c) P2) (O c) ^ 255) c]
  exact avg_delta255_pqovKey (O c) (P1 c)

/-- **Theorem 4(b′) with pqov's real key generation and pqov's signers**: Anchor `c`'s key is
`pqovKey (O c) (P1 c) (κ c)` (any oil matrices and `P1` parts, independent uniform `P2` parts `κ`)
and its signer pqov's with its own oil matrix `O c`. For every family of Moderators indexed by the
`P2` parts (whose choices may depend on the keys), averaged over `κ` and the vinegar tables,
`≤ 4εR + 4·(255⁻³⁷ + 1/(255·256³⁷))`. `anonymityNC_pqov_keys` is the case `O = 0`. -/
theorem anonymityNC_pqov_pqovKeys (O : Bool → OilMat) (P1 : Bool → ℕ → GF256)
    (A : (Bool → P2Part) → AdversaryNC)
    (hpk : ∀ κ c, ((A κ).pk c).map = (pqovKey (O c) (P1 c) (κ c)).map)
    (idx : Spec.Moussaka.AnchorSet → UOVKey → ℕ)
    (PI : Spec.Moussaka.NIZK Spec.Moussaka.IssueInstance) (hidx : IdxSound idx) {CR : Type}
    [Fintype CR] [Nonempty CR]
    (simR : Spec.Moussaka.RedeemInstance → CR → Bytes)
    (PR : Spec.Moussaka.NIZK Spec.Moussaka.RedeemInstance) {εR : ℝ} (hεR : 0 ≤ εR)
    (hR : ZeroKnowledge RedeemRelW (proveR PR) simR εR) :
    |pr ((Bool → P2Part) × (VTab Vin × TapeNC)) (fun z =>
        realGameNC (A z.1) idx PI (pqovRO (A z.1).pk O 255 z.2.1) PR false z.2.2) -
      pr ((Bool → P2Part) × (VTab Vin × TapeNC)) (fun z =>
        realGameNC (A z.1) idx PI (pqovRO (A z.1).pk O 255 z.2.1) PR true z.2.2)| ≤
      4 * εR + 2 * (abortKeys + abortKeys) := by
  have hO : ∀ κ c, OilSpace ((A κ).pk c) (O c) := fun κ c =>
    oilSpace_of_map_eq (hpk κ c) (O c) (oilSpace_pqovKey _ _ _)
  have hw (κ : Bool → P2Part) := anonymityNC_pqov (A κ) idx PI O (hO κ) hidx simR PR hεR hR
  refine abs_pr_avg_abort
    (fun κ (z : VTab Vin × TapeNC) =>
      realGameNC (A κ) idx PI (pqovRO (A κ).pk O 255 z.1) PR false z.2)
    (fun κ (z : VTab Vin × TapeNC) =>
      realGameNC (A κ) idx PI (pqovRO (A κ).pk O 255 z.1) PR true z.2)
    (4 * εR) (fun κ c => delta ((A κ).pk c) (O c) ^ 255) (fun _ => abortKeys) hw fun c => ?_
  simp only [delta_of_map_eq (hpk _ c)]
  exact avg_delta255_pqovKeys O P1 c

/-- **Theorem 4(b′) in the random-oracle and ideal-cipher model with pqov's real key generation
and pqov's signers** (the Lean prover and verifier on the shared tables, every type of cipher
rows), averaged over the `P2` parts and the vinegar tables, for every choice of the oil matrices
and `P1` parts:

    4·εz(pR; q₃, q₅ + 2496, q_E + 23035) + 2·(noHitProb + 2⁻¹⁰²⁴) + 4·q₃·2⁻¹²⁸
      + 4·(255⁻³⁷ + 1/(255·256³⁷)). -/
theorem anonymityNCRO_pqov_pqovKeys {R : Type} [Fintype R] [Nonempty R] [CipherRow R] [ZKRow R]
    (O : Bool → OilMat) (P1 : Bool → ℕ → GF256) (A : (Bool → P2Part) → AdversaryNCRO R)
    (hpk : ∀ κ c, ((A κ).pk c).map = (pqovKey (O c) (P1 c) (κ c)).map)
    (idx : Spec.Moussaka.AnchorSet → UOVKey → ℕ)
    (hidx : IdxSound idx) {q3 q5 qE : ℕ} (hA : ∀ κ, (A κ).Budget q3 q5 qE) :
    |pr ((Bool → P2Part) × (VTab Vin × (((TIr × TIr) × (TRr × TRr)) × ShM R))) (fun z =>
        realGameNCRO (A z.1) idx leanPI leanVI (pqovRO (A z.1).pk O 255 z.2.1) leanPR
          false z.2.2) -
      pr ((Bool → P2Part) × (VTab Vin × (((TIr × TIr) × (TRr × TRr)) × ShM R))) (fun z =>
        realGameNCRO (A z.1) idx leanPI leanVI (pqovRO (A z.1).pk O 255 z.2.1) leanPR
          true z.2.2)| ≤
      4 * ZKRow.εz R pR q3 (q5 + 2496) (qE + 23035) + 2 * (noHitProb + 1 / 2 ^ 1024) +
        4 * (q3 / 2 ^ 128) + 2 * (abortKeys + abortKeys) := by
  have hO : ∀ κ c, OilSpace ((A κ).pk c) (O c) := fun κ c =>
    oilSpace_of_map_eq (hpk κ c) (O c) (oilSpace_pqovKey _ _ _)
  have hw (κ : Bool → P2Part) := anonymityNCRO_pqov (A κ) idx O (hO κ) hidx (hA κ)
  generalize (2 : ℝ) ^ 1024 = M at hw ⊢
  refine abs_pr_avg_abort
    (fun κ (z : VTab Vin × (((TIr × TIr) × (TRr × TRr)) × ShM R)) =>
      realGameNCRO (A κ) idx leanPI leanVI (pqovRO (A κ).pk O 255 z.1) leanPR false z.2)
    (fun κ (z : VTab Vin × (((TIr × TIr) × (TRr × TRr)) × ShM R)) =>
      realGameNCRO (A κ) idx leanPI leanVI (pqovRO (A κ).pk O 255 z.1) leanPR true z.2)
    (4 * ZKRow.εz R pR q3 (q5 + 2496) (qE + 23035) + 2 * (noHitProb + 1 / M) + 4 * (q3 / 2 ^ 128))
    (fun κ c => delta ((A κ).pk c) (O c) ^ 255) (fun _ => abortKeys) hw fun c => ?_
  simp only [delta_of_map_eq (hpk _ c)]
  exact avg_delta255_pqovKeys O P1 c

end VoleMole.Privacy.Moussaka
