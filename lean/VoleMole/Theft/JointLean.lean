import VoleMole.Theft.JointCharge

/-!
# The joint many-proof bound for a game of Lean proofs

`real_sim_leN_game` (`Theft/JointGame.lean`), with the Lean prover's per-proof theorem
(`lean_zkExp`, at every value of the extra table, the base record `Hb x`) and the hop's charge
bounded by the view (`hopRd_charges`, `Theft/JointCharge.lean`):

* `GRd.Bnd`, `progsRd_bnd`, `realFromRd_bnd`, **`hopRd_bnd`**: the hop reader's worst-case budgets,
  `(a₃, a₅ + N·h₅, a_E + N·h_E)` for a game reader within `(a₃, a₅, a_E)` and honest readers within
  `h₅`, `h_E` (they enter only the denominators and `B`);
* **`real_sim_leN_lean`**: for a game of Lean proofs (an output map `φ` with an `iv` decoder
  `ivO`), honest readers confined to their `iv`s (`Conf`: the later real proofs, the earlier
  programmings), and a consistent game reader `R`: for every event `R` reads,

      |Pr_real[Ev] − Pr_sim[Ev]| ≤ (Σ_i (εZK/(1 − βZK) + (1 + B)·Pr[deltaN i]) + J) / (1 − N·B),

  with the charge of slot `i` in a view `wZK₃·n3 + wZK_E·nE + wZK₅·n5` (the game reader's `H₃` keys
  of slice `i`; its cipher keys at CTR blocks of slot `i`'s `iv` plus `h_E` per slot whose `iv` has
  the same middle bytes; its `H₅` keys at gate inputs of slot `i`'s `iv` plus `h₅` per slot with the
  same `iv`), `B` the largest such charge and `J` their sum over the slots in the simulated game.
-/

open Finset

set_option synthInstance.maxSize 1024

namespace VoleMole.Theft

open VoleMole.Privacy VoleMole.ZK.Sim VoleMole.ZK.IC VoleMole.Verifier VoleMole.Verifier.Bridge
  VoleMole.Arith

/-! ## Budgets of the hop reader -/

section Bnd

variable {p : Params} {X : Type} {I W C O Ω : Type*} {N : ℕ}

/-- **Budgets of a game reader**: each slice at `a₃` keys, `H₅` at `a₅`, the cipher at `a_E` keys. -/
structure GRd.Bnd (R : GRd Ω O p X N) (a3 a5 aE : ℕ) : Prop where
  h3 : ∀ ω l gs t j, (R.Q3 ω l gs t j).card ≤ a3
  h5 : ∀ ω l gs t, (R.Q5 ω l gs t).card ≤ a5
  hE : ∀ ω l gs t, ((R.QE ω l gs t).image Prod.fst).card ≤ aE

lemma GRd.bnd_atRd {R : GRd Ω O p X N} {a3 a5 aE : ℕ} (hb : R.Bnd a3 a5 aE) (hc : R.Cons)
    (F : Ω × List O × (Fin N → Tab3) × ShX (Blk → Blk) p X → Prop) (hF : R.Reads F) (ω : Ω)
    (l : List O) (gs : Fin N → Tab3) (i : Fin N) (x : X) :
    (R.atRd hc F hF ω l gs i x).Bnd a3 a5 aE :=
  ⟨fun _ _ => hb.h3 _ _ _ _ _, fun _ _ => hb.h5 _ _ _ _, fun _ _ => hb.hE _ _ _ _⟩

lemma Conf.bnd {Y : Type*} {F : Tab3 → Sh p → Y} {R : TRd F} {iv : Sh p → Option ByteArray}
    {a5 aE : ℕ} (hc : Conf R iv a5 aE) : R.Bnd 0 a5 aE :=
  ⟨fun g s => by rw [hc.h3]; rfl, hc.h5, hc.hE⟩

variable {prove : X → I → W → Bytes 16 → Tab3 → Sh p → O} {sim : I → C → O}
  {prog : X → I → C → Sh p → Sh p} {xOf : Ω → List O → I} {wOf : Ω → List O → W}
  (ivO : X → I → O → Option ByteArray)

/-- **The first `j` programmings' budgets.** -/
theorem progsRd_bnd (hkeep : ∀ x xI c s, (prog x xI c s).2 = s.2)
    (Rpg : ∀ x xI c, TRd (fun (_ : Tab3) s => (prog x xI c s).1)) {m5 mE : ℕ}
    (hRpg : ∀ x xI c, Conf (Rpg x xI c) (fun _ => ivO x xI (sim xI c)) m5 mE)
    (x : X) (ω : Ω) (cs : ℕ → C) :
    ∀ j, (progsRd (sim := sim) (xOf := xOf) hkeep Rpg x ω cs j).Bnd 0 (j * m5) (j * mE)
  | 0 => ⟨fun _ _ => le_rfl, fun _ _ => by simp [progsRd, h23Rd, TRd.congr],
      fun _ _ => by simp [progsRd, h23Rd, TRd.congr]⟩
  | j + 1 => by
    have h0 := TRd.bnd_prog (hL := hkeep x (xOf ω (simPre (gS sim xOf) (gPg prog xOf) ω cs j).1) (cs j))
        (hRpg x _ _).bnd (progsRd_bnd hkeep Rpg hRpg x ω cs j)
    have h : (progsRd (sim := sim) (xOf := xOf) hkeep Rpg x ω cs (j + 1)).Bnd (0 + 0)
        (m5 + j * m5) (mE + j * mE) := ⟨fun g s => h0.h3 g s, fun g s => h0.h5 g s, fun g s => h0.hE g s⟩
    exact h.mono le_rfl (by rw [Nat.succ_mul]; omega) (by rw [Nat.succ_mul]; omega)

/-- **`m` real proofs and then a reader**: the budgets add up. -/
theorem realFromRd_bnd
    (RP : ∀ x xI w r g', TRd (fun (_ : Tab3) (s : Sh p) => prove x xI w r g' s)) {s5 sE : ℕ}
    (hRP : ∀ x xI w r g', Conf (RP x xI w r g') (fun s => ivO x xI (prove x xI w r g' s)) s5 sE)
    (x : X) (ω : Ω) (rs : ℕ → Bytes 16 × Tab3) {Φ : List O → Tab3 → Sh p → Prop}
    (RΦ : ∀ l, TRd (Φ l)) {b3 b5 bE : ℕ} (hΦ : ∀ l, (RΦ l).Bnd b3 b5 bE) :
    ∀ m (h : List O) j, (realFromRd (xOf := xOf) prove wOf RP x ω rs RΦ m h j).Bnd b3
      (m * s5 + b5) (m * sE + bE)
  | 0, h, _ => (hΦ h).mono le_rfl (by omega) (by omega)
  | m + 1, h, j => by
    have hb := TRd.bnd_bind (hRP x (xOf ω h) (wOf ω h) (rs j).1 (rs j).2).bnd
      fun o => realFromRd_bnd RP hRP x ω rs RΦ hΦ m (h ++ [o]) (j + 1)
    have h : (realFromRd (xOf := xOf) prove wOf RP x ω rs RΦ (m + 1) h j).Bnd (0 + b3)
        (s5 + (m * s5 + b5)) (sE + (m * sE + bE)) :=
      ⟨fun g s => hb.h3 g s, fun g s => hb.h5 g s, fun g s => hb.hE g s⟩
    exact h.mono (by omega) (by rw [Nat.succ_mul]; omega) (by rw [Nat.succ_mul]; omega)

variable [Nonempty C]

/-- **The hop reader's budgets**: `(a₃, a₅ + N·h₅, a_E + N·h_E)`. -/
theorem hopRd_bnd (hkeep : ∀ x xI c s, (prog x xI c s).2 = s.2)
    (Rpg : ∀ x xI c, TRd (fun (_ : Tab3) s => (prog x xI c s).1)) {m5 mE : ℕ}
    (hRpg : ∀ x xI c, Conf (Rpg x xI c) (fun _ => ivO x xI (sim xI c)) m5 mE)
    (RP : ∀ x xI w r g', TRd (fun (_ : Tab3) (s : Sh p) => prove x xI w r g' s)) {s5 sE : ℕ}
    (hRP : ∀ x xI w r g', Conf (RP x xI w r g') (fun s => ivO x xI (prove x xI w r g' s)) s5 sE)
    (R : GRd Ω O p X N) (hc : R.Cons) {a3 a5 aE : ℕ} (hb : R.Bnd a3 a5 aE)
    (Ev : Ω → List O → (Fin N → Tab3) → ShX (Blk → Blk) p X → Prop)
    (hEv : R.Reads (fun v => Ev v.1 v.2.1 v.2.2.1 v.2.2.2)) (i : Fin N) (ω : Ω)
    (τ : Fin N → Slot (Bytes 16) C Tab3) (x : X) (o : O) :
    (hopRd (sim := sim) (xOf := xOf) prove wOf hkeep Rpg RP R hc Ev hEv i ω τ x o).Bnd a3
      (a5 + N * max m5 s5) (aE + N * max mE sE) := by
  have h1 := progsRd_bnd (xOf := xOf) ivO hkeep Rpg hRpg x ω (tapeC τ) i
  have h2 := realFromRd_bnd (xOf := xOf) (wOf := wOf) ivO RP hRP x ω (tapeR τ)
    (Φ := fun l g s => Ev ω l (Function.update (tapeG τ) i g) (atX s x))
    (fun l => R.atRd hc (fun v => Ev v.1 v.2.1 v.2.2.1 v.2.2.2) hEv ω l (tapeG τ) i x)
    (fun l => GRd.bnd_atRd hb hc _ hEv ω l (tapeG τ) i x) (N - (i.val + 1))
    ((simPre (gS sim xOf) (gPg prog xOf) ω (tapeC τ) i).1 ++ [o]) (i.val + 1)
  have h0 := TRd.bnd_prog (hL := progsAt_keep hkeep x ω (tapeC τ) i) h1 h2
  have h : (hopRd (sim := sim) (xOf := xOf) prove wOf hkeep Rpg RP R hc Ev hEv i ω τ x o).Bnd
      (0 + a3) (i.val * m5 + ((N - (i.val + 1)) * s5 + a5))
      (i.val * mE + ((N - (i.val + 1)) * sE + aE)) :=
    ⟨fun g s => h0.h3 g s, fun g s => h0.h5 g s, fun g s => h0.hE g s⟩
  have hi := i.isLt
  have e5 : i.val * m5 + ((N - (i.val + 1)) * s5 + a5) ≤ a5 + N * max m5 s5 := by
    have : i.val * m5 + (N - (i.val + 1)) * s5 ≤ N * max m5 s5 := by
      calc i.val * m5 + (N - (i.val + 1)) * s5 ≤ i.val * max m5 s5 + (N - (i.val + 1)) * max m5 s5 :=
            add_le_add (Nat.mul_le_mul_left _ (le_max_left _ _))
              (Nat.mul_le_mul_left _ (le_max_right _ _))
        _ = (i.val + (N - (i.val + 1))) * max m5 s5 := by rw [Nat.add_mul]
        _ ≤ N * max m5 s5 := Nat.mul_le_mul_right _ (by omega)
    omega
  have eE : i.val * mE + ((N - (i.val + 1)) * sE + aE) ≤ aE + N * max mE sE := by
    have : i.val * mE + (N - (i.val + 1)) * sE ≤ N * max mE sE := by
      calc i.val * mE + (N - (i.val + 1)) * sE ≤ i.val * max mE sE + (N - (i.val + 1)) * max mE sE :=
            add_le_add (Nat.mul_le_mul_left _ (le_max_left _ _))
              (Nat.mul_le_mul_left _ (le_max_right _ _))
        _ = (i.val + (N - (i.val + 1))) * max mE sE := by rw [Nat.add_mul]
        _ ≤ N * max mE sE := Nat.mul_le_mul_right _ (by omega)
    omega
  exact h.mono (by omega) e5 eE

end Bnd

/-! ## The Lean game -/

section Lean

variable {X : Type} {I W O Ω : Type*} (p : Params) (Hb : X → Hashes) (stOf : I → Statement)
  (enc : I → W → ByteArray) (φ : Except String ByteArray → O)

/-- The Lean prover with the base record of the extra table and an output map. -/
noncomputable def lProve (x : X) (xI : I) (w : W) (ρ : Bytes 16) (g : Tab3) (s : Sh p) : O :=
  φ (realRO p (Hb x) (stOf xI) (enc xI w) ρ g s)

/-- The simulator with an output map. -/
def lSim (_ : I) (c : SimCoins p) : O := φ (simulate p c)

/-- The simulator's programming with the base record of the extra table. -/
noncomputable def lProg (x : X) (xI : I) (c : SimCoins p) (s : Sh p) : Sh p :=
  progRO p (Hb x) (stOf xI) c s

/-- **The weights of the charge**: `H₃` keys over `2¹²⁸ − q₃`, cipher keys `221` over `d_E`, `H₅`
keys over `2¹²⁸`, all over `1 − βZK`. -/
noncomputable def wZK (q3 q5 qE : ℕ) : Fin 3 → ℝ :=
  ![1 / (2 ^ 128 - q3) / (1 - βZK q5 qE), 221 / dEZK qE / (1 - βZK q5 qE),
    1 / 2 ^ 128 / (1 - βZK q5 qE)]

variable {N : ℕ}

/-- **The charge counts of slot `i` in a view**: `n3`, `nE`, `n5`. -/
noncomputable def nZK (ivO : X → I → O → Option ByteArray) (xOf : Ω → List O → I)
    (R : GRd Ω O p X N) (h5 hE : ℕ) (i : ℕ) (k : Fin 3)
    (v : Ω × List O × (Fin N → Tab3) × ShX (Blk → Blk) p X) : ℕ :=
  ![n3 R i v, nE ivO (xOf := xOf) R hE i v, n5 ivO (xOf := xOf) R h5 i v] k

/-- **The bounds of the counts.** -/
def MZK (N a3 a5 aE h5 hE : ℕ) : Fin 3 → ℕ := ![a3, aE + N * hE, a5 + N * h5]

variable {p}

lemma nE_le (ivO : X → I → O → Option ByteArray) (xOf : Ω → List O → I) (R : GRd Ω O p X N)
    {a3 a5 aE : ℕ} (hb : R.Bnd a3 a5 aE) (hE : ℕ) (i : ℕ) (v) :
    nE ivO (xOf := xOf) R hE i v ≤ aE + N * hE := by
  unfold nE
  have h1 := (cEof_le_keys (ivAt ivO xOf v.2.2.2.2.2 v.1 v.2.1 i) (R.QE v.1 v.2.1 v.2.2.1 v.2.2.2)).trans
    (hb.hE _ _ _ _)
  have h2 : ∑ j ∈ (range N).erase i, hE * ovE (ivAt ivO xOf v.2.2.2.2.2 v.1 v.2.1 i)
      (ivAt ivO xOf v.2.2.2.2.2 v.1 v.2.1 j) ≤ N * hE := by
    calc _ ≤ ∑ _j ∈ (range N).erase i, hE :=
          Finset.sum_le_sum fun j _ => by
            have := ovE_le_one (ivAt ivO xOf v.2.2.2.2.2 v.1 v.2.1 i) (ivAt ivO xOf v.2.2.2.2.2 v.1 v.2.1 j)
            calc hE * _ ≤ hE * 1 := Nat.mul_le_mul_left _ this
              _ = hE := mul_one _
      _ ≤ ∑ _j ∈ range N, hE := Finset.sum_le_sum_of_subset (Finset.erase_subset _ _)
      _ = N * hE := by rw [Finset.sum_const, Finset.card_range, smul_eq_mul]
  omega

lemma n5_le (ivO : X → I → O → Option ByteArray) (xOf : Ω → List O → I) (R : GRd Ω O p X N)
    {a3 a5 aE : ℕ} (hb : R.Bnd a3 a5 aE) (h5 : ℕ) (i : ℕ) (v) :
    n5 ivO (xOf := xOf) R h5 i v ≤ a5 + N * h5 := by
  unfold n5
  have h1 := (c5of_le_card p CrtGen.tables (ivAt ivO xOf v.2.2.2.2.2 v.1 v.2.1 i)
    (R.Q5 v.1 v.2.1 v.2.2.1 v.2.2.2)).trans (hb.h5 _ _ _ _)
  have h2 : ∑ j ∈ (range N).erase i, h5 * ov5 (ivAt ivO xOf v.2.2.2.2.2 v.1 v.2.1 i)
      (ivAt ivO xOf v.2.2.2.2.2 v.1 v.2.1 j) ≤ N * h5 := by
    calc _ ≤ ∑ _j ∈ (range N).erase i, h5 :=
          Finset.sum_le_sum fun j _ => by
            have := ov5_le_one (ivAt ivO xOf v.2.2.2.2.2 v.1 v.2.1 i) (ivAt ivO xOf v.2.2.2.2.2 v.1 v.2.1 j)
            calc h5 * _ ≤ h5 * 1 := Nat.mul_le_mul_left _ this
              _ = h5 := mul_one _
      _ ≤ ∑ _j ∈ range N, h5 := Finset.sum_le_sum_of_subset (Finset.erase_subset _ _)
      _ = N * h5 := by rw [Finset.sum_const, Finset.card_range, smul_eq_mul]
  omega

lemma n3_le (R : GRd Ω O p X N) {a3 a5 aE : ℕ} (hb : R.Bnd a3 a5 aE) (i : ℕ) (v) :
    n3 R i v ≤ a3 := by
  unfold n3; split
  · exact hb.h3 _ _ _ _ _
  · exact Nat.zero_le _

lemma nZK_le (ivO : X → I → O → Option ByteArray) (xOf : Ω → List O → I) (R : GRd Ω O p X N)
    {a3 a5 aE : ℕ} (hb : R.Bnd a3 a5 aE) (h5 hE : ℕ) (i : ℕ) (k : Fin 3) (v) :
    nZK p ivO xOf R h5 hE i k v ≤ MZK N a3 a5 aE h5 hE k := by
  fin_cases k
  · exact n3_le R hb i v
  · exact nE_le ivO xOf R hb hE i v
  · exact n5_le ivO xOf R hb h5 i v

/-- The counts depend on the slices and tables only through the reads. -/
lemma nZK_agree (ivO : X → I → O → Option ByteArray) (xOf : Ω → List O → I) (R : GRd Ω O p X N)
    (hc : R.Cons) (h5 hE : ℕ) (i : ℕ) (k : Fin 3) (ω l gs t gs' t')
    (h : R.Agree ω l gs t gs' t') :
    nZK p ivO xOf R h5 hE i k (ω, l, gs', t') = nZK p ivO xOf R h5 hE i k (ω, l, gs, t) := by
  obtain ⟨e3, e5, eE⟩ := hc ω l gs t gs' t' h
  have hx : t'.2.2 = t.2.2 := h.2.1
  fin_cases k
  · show n3 R i _ = n3 R i _
    unfold n3; simp only [e3]
  · show nE ivO R hE i _ = nE ivO R hE i _
    unfold nE; simp only [eE, hx]
  · show n5 ivO R h5 i _ = n5 ivO R h5 i _
    unfold n5; simp only [e5, hx]

end Lean

/-! ## The joint bound for a game of Lean proofs -/

lemma lin3_le {a b c a' b' c' d1 d2 d3 D : ℝ} (hd1 : 0 < d1) (hd2 : 0 < d2) (hd3 : 0 < d3)
    (hD : 0 < D) (ha : a = a') (hb : b ≤ b') (hc : c ≤ c') :
    (a / d1 + 221 * b / d2 + c / d3) / D ≤ 1 / d1 / D * a' + 221 / d2 / D * b' + 1 / d3 / D * c' := by
  rw [ha]
  have e : 1 / d1 / D * a' + 221 / d2 / D * b' + 1 / d3 / D * c' =
      (a' / d1 + 221 * b' / d2 + c' / d3) / D := by field_simp
  rw [e]
  gcongr

section LeanJoint

variable {X : Type} [Fintype X] [Nonempty X] {I W O Ω : Type*} [Fintype Ω] [Nonempty Ω]
  {p : Params} {N : ℕ}

/-- **The joint many-proof bound for a game of Lean proofs.** The slots are Lean proofs (base
record `Hb x` of the extra table, output map `φ` with an `iv` decoder `ivO` that never invents an
`iv`), the instance and witness functions of the history; the later real proofs and the earlier
programmings are read by readers confined to their `iv`s (`hRP`, `hRpg`, within `(s₅, s_E)` and
`(m₅, m_E)`); `R` is a consistent game reader within `(a₃, a₅, a_E)`. With
`q₅ = a₅ + N·max(m₅, s₅)`, `q_E = a_E + N·max(m_E, s_E)`, for every event `R` reads,

    |Pr_real[Ev] − Pr_sim[Ev]| ≤ (Σ_i (εZK/(1 − βZK) + (1 + B)·Pr[deltaN i]) + J) / (1 − N·B),

`B = Σ_k wZK k · MZK k` and `J` a bound on `Σ_i Σ_k wZK k · E_sim[nZK i k]`. -/
theorem real_sim_leN_lean (Hb : X → Hashes) (hHb : ∀ x, HashesWF (Hb x)) (stOf : I → Statement)
    (hp : ∀ xI, (stOf xI).params = p) (hlr : p.labelRows = true) (enc : I → W → ByteArray)
    (Rl : I → W → Prop) (cs : I → ByteArray → ByteArray → System GF128)
    (hz : ∀ xI w, Rl xI w → ZKHyp CrtGen.tables (stOf xI) (enc xI w) (cs xI))
    (hsp : SmallParams p) (φ : Except String ByteArray → O) (ivO : X → I → O → Option ByteArray)
    (hiv : ∀ x xI e v, ivO x xI (φ e) = some v → ivV (Hb x) (stOf xI) e = some v)
    (xOf : Ω → List O → I) (wOf : Ω → List O → W) (hrel : ∀ ω h, Rl (xOf ω h) (wOf ω h))
    (Rpg : ∀ x xI c, TRd (fun (_ : Tab3) s => (lProg p Hb stOf x xI c s).1)) {m5 mE : ℕ}
    (hRpg : ∀ x xI c, Conf (Rpg x xI c) (fun _ => ivO x xI (lSim p φ xI c)) m5 mE)
    (RP : ∀ x xI w r g', TRd (fun (_ : Tab3) (s : Sh p) => lProve p Hb stOf enc φ x xI w r g' s))
    {s5 sE : ℕ}
    (hRP : ∀ x xI w r g', Conf (RP x xI w r g')
      (fun s => ivO x xI (lProve p Hb stOf enc φ x xI w r g' s)) s5 sE)
    (R : GRd Ω O p X N) (hc : R.Cons) {a3 a5 aE : ℕ} (hb : R.Bnd a3 a5 aE)
    (h3 : (a3 : ℝ) < 2 ^ 128) (hE : 221 * ((aE + N * max mE sE + 4607 : ℕ) : ℝ) < 2 ^ 128)
    (hβ : βZK (a5 + N * max m5 s5) (aE + N * max mE sE) < 1) {J : ℝ}
    (hJ : ∑ i ∈ range N, ∑ k, wZK a3 (a5 + N * max m5 s5) (aE + N * max mE sE) k *
      exU _ (fun z => (nZK p ivO xOf R (max m5 s5) (max mE sE) i k
        (viewN (C := SimCoins p) (ρ := Bytes 16) (gP (lProve p Hb stOf enc φ) xOf wOf)
          (gS (lSim p φ) xOf) (gPg (lProg p Hb stOf) xOf) N z) : ℝ)) ≤ J)
    (hNB : N * ∑ k, wZK a3 (a5 + N * max m5 s5) (aE + N * max mE sE) k *
      MZK N a3 a5 aE (max m5 s5) (max mE sE) k < 1)
    (Ev : Ω → List O → (Fin N → Tab3) → ShX (Blk → Blk) p X → Prop)
    (hEv : R.Reads (fun v => Ev v.1 v.2.1 v.2.2.1 v.2.2.2)) :
    |pr _ (realGN (C := SimCoins p) (gP (lProve p Hb stOf enc φ) xOf wOf) Ev) -
        pr _ (simGN (ρ := Bytes 16) (gS (lSim p φ) xOf) (gPg (lProg p Hb stOf) xOf) Ev)| ≤
      (∑ i : Fin N, (εZK (aE + N * max mE sE) /
          (1 - βZK (a5 + N * max m5 s5) (aE + N * max mE sE)) +
        (1 + ∑ k, wZK a3 (a5 + N * max m5 s5) (aE + N * max mE sE) k *
          MZK N a3 a5 aE (max m5 s5) (max mE sE) k) *
          pr _ (deltaN (gP (lProve p Hb stOf enc φ) xOf wOf) (gS (lSim p φ) xOf)
            (gPg (lProg p Hb stOf) xOf) i)) + J) /
        (1 - N * ∑ k, wZK a3 (a5 + N * max m5 s5) (aE + N * max mE sE) k *
          MZK N a3 a5 aE (max m5 s5) (max mE sE) k) := by
  set q5 := a5 + N * max m5 s5
  set qE := aE + N * max mE sE
  have hd : 0 < dEZK qE := dEZK_pos hE
  have hden : 0 < 1 - βZK q5 qE := by linarith
  have h3' : (0 : ℝ) < 2 ^ 128 - a3 := by linarith
  have hkeep : ∀ x xI c s, (lProg p Hb stOf x xI c s).2 = s.2 := fun _ _ _ _ => rfl
  have hw : ∀ k, 0 ≤ wZK a3 q5 qE k := by
    intro k
    fin_cases k
    · exact div_nonneg (div_nonneg zero_le_one h3'.le) hden.le
    · exact div_nonneg (div_nonneg (by norm_num) hd.le) hden.le
    · exact div_nonneg (by positivity) hden.le
  refine real_sim_leN_game (lProve p Hb stOf enc φ) (sim := lSim p φ) (prog := lProg p Hb stOf)
    (xOf := xOf) wOf
    (fun x xI o Q3 Q5 QE => chPt p CrtGen.tables a3 qE (ivO x xI o) Q3 Q5 QE / (1 - βZK q5 qE))
    (fun x => lean_zkExp p (Hb x) stOf hp hlr enc Rl cs hz (hHb x) hsp φ (ivO x) (hiv x) h3 hE hβ)
    hrel hkeep Rpg RP R hc
    (fun Ev' hEv' i ω τ x o => hopRd_bnd ivO hkeep Rpg hRpg RP hRP R hc hb Ev' hEv' i ω τ x o)
    (wZK a3 q5 qE) hw (nZK p ivO xOf R (max m5 s5) (max mE sE)) (MZK N a3 a5 aE (max m5 s5) (max mE sE))
    (fun i _ k v => nZK_le ivO xOf R hb _ _ i k v)
    (fun i _ k ω l gs t gs' t' h => nZK_agree ivO xOf R hc _ _ i k ω l gs t gs' t' h)
    (fun Ev' hEv' i ω τ r g t => ?_) hJ hNB Ev hEv
  obtain ⟨c3, cE, c5⟩ := hopRd_charges (ivO := ivO) (prove := lProve p Hb stOf enc φ) (wOf := wOf)
    (sim := lSim p φ) (xOf := xOf) hkeep Rpg hRpg RP hRP R hc
    Ev' hEv' i ω τ t.2.2 (gP (lProve p Hb stOf enc φ) xOf wOf ω
      (simPre (gS (lSim p φ) xOf) (gPg (lProg p Hb stOf) xOf) ω (tapeC τ) i).1 r g t) g (shOf t)
  rw [Fin.sum_univ_three]
  simp only [wZK, nZK, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons]
  unfold chPt
  exact lin3_le h3' hd (by positivity) hden (by exact_mod_cast c3) (by exact_mod_cast cE)
    (by exact_mod_cast c5)

end LeanJoint

end VoleMole.Theft
