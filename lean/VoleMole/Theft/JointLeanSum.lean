import VoleMole.Theft.JointProg

/-!
# The joint step for games of several Lean proof systems

`real_sim_leN_lean` (`Theft/JointLean.lean`) is for a game whose slots are proofs of **one** Lean
proof system, with an output map `φ` that does not see the instance and one parameter set `p` for
every statement. The theft games have two systems (issuance and spend, or token and redemption),
with different parameters, whose log entries carry the statement, and slots where the Client
refuses and no proof is made. Here:

* **`gate5_params`**, `c5of_params`, `chPt_params`: whether a 37-byte key is a gate input of an
  `iv` does not depend on the parameters or the CRT tables (the label offset `off` is free), so
  the point charge does not either;
* **`lean_zkExpD`**: `lean_zkExp` for an output map `φ x` that depends on the instance;
* **`ZKExp.osum`**: two systems with the same tables, and a third "no proof" case with a constant
  output and no programming, as one system on `Option (I₁ ⊕ I₂)` (`osumProve`, `osumSim`,
  `osumProg`, `osumRel`);
* **`real_sim_leN_leanG`**: `real_sim_leN_lean` for **any** proof system with `ZKExp` at the point
  charge `chPt`, the programmings and the real proofs confined to their `iv`s (`real_sim_leN_lean`
  is the case of one Lean system, `lean_zkExp`).
-/

open Finset

set_option synthInstance.maxSize 1024

namespace VoleMole.Theft

open VoleMole.Privacy VoleMole.ZK.Sim VoleMole.ZK VoleMole.Verifier VoleMole.Verifier.Bridge
  VoleMole.Arith VoleMole.ZK.IC

/-! ## Gate inputs do not depend on the parameters -/

section Params

lemma w128_xor_cancel (a b : W128) : a.xor (a.xor b) = b := by
  rcases a with ⟨a1, a2⟩
  rcases b with ⟨b1, b2⟩
  simp only [W128.xor, ← UInt64.xor_assoc, UInt64.xor_self, UInt64.zero_xor]

/-- **A gate input of an `iv` for some parameters is one for any parameters.** The label part is
`L_e(cols) ⊕ off` with `off` free. -/
lemma gate5_params {p p' : Params} {T T' : CrtTables} {iv : ByteArray} {k : Bytes 37}
    (h : Gate5 p T iv k) : Gate5 p' T' iv k := by
  obtain ⟨cols, off, e, he⟩ := h
  refine ⟨cols, (labelOf p' T' cols e).xor ((labelOf p T cols e).xor off), e, ?_⟩
  rw [he, gateInputsOff_getD p T _ _ _ e.isLt, gateInputsOff_getD p' T' _ _ _ e.isLt,
    w128_xor_cancel]

lemma gate5_iff_params (p p' : Params) (T T' : CrtTables) (iv : ByteArray) (k : Bytes 37) :
    Gate5 p T iv k ↔ Gate5 p' T' iv k := ⟨gate5_params, gate5_params⟩

lemma c5of_params (p p' : Params) (T T' : CrtTables) (iv : Option ByteArray)
    (Q5 : Finset (Bytes 37)) : c5of p T iv Q5 = c5of p' T' iv Q5 := by
  rcases iv with _ | v
  · rfl
  · show (Q5.filter (Gate5 p T v)).card = (Q5.filter (Gate5 p' T' v)).card
    congr 1
    exact filter_congr fun k _ => gate5_iff_params p p' T T' v k

/-- **The point charge does not depend on the parameters.** -/
lemma chPt_params (p p' : Params) (T T' : CrtTables) (q3 qE : ℕ) (iv : Option ByteArray)
    (Q3 : Finset (Bytes 16)) (Q5 : Finset (Bytes 37)) (QE : Finset (Blk × Blk)) :
    chPt p T q3 qE iv Q3 Q5 QE = chPt p' T' q3 qE iv Q3 Q5 QE := by
  unfold chPt
  rw [c5of_params p p' T T']

end Params

/-! ## `lean_zkExp` with an instance-dependent output map -/

/-- **The Lean prover is `ZKExp`, for an output map that depends on the instance.** -/
theorem lean_zkExpD {I W O : Type*} (p : Params) (Hb : Hashes) (stOf : I → Statement)
    (hp : ∀ x, (stOf x).params = p) (hlr : p.labelRows = true) (enc : I → W → ByteArray)
    (Rl : I → W → Prop) (cs : I → ByteArray → ByteArray → System GF128)
    (h : ∀ x w, Rl x w → ZKHyp CrtGen.tables (stOf x) (enc x w) (cs x)) (hHb : HashesWF Hb)
    (hsp : SmallParams p) (φ : I → Except String ByteArray → O) (ivO : I → O → Option ByteArray)
    (hiv : ∀ x e v, ivO x (φ x e) = some v → ivV Hb (stOf x) e = some v) {q3 q5 qE : ℕ}
    (h3 : (q3 : ℝ) < 2 ^ 128) (hE : 221 * ((qE + 4607 : ℕ) : ℝ) < 2 ^ 128) (hβ : βZK q5 qE < 1) :
    ZKExp Rl (fun x w ρ g (s : Sh p) => φ x (realRO p Hb (stOf x) (enc x w) ρ g s))
      (fun x c => φ x (simulate p c)) (fun x c s => progRO p Hb (stOf x) c s) q3 q5 qE
      (εZK qE / (1 - βZK q5 qE))
      (fun x o Q3 Q5 QE => chPt p CrtGen.tables q3 qE (ivO x o) Q3 Q5 QE / (1 - βZK q5 qE)) := by
  intro x w hxw D R hR
  beta_reduce
  have hz := h x w hxw
  have hpx := hp x
  have hivx := hiv x
  generalize stOf x = st at hz hpx hivx ⊢
  subst hpx
  have hden : 0 < 1 - βZK q5 qE := by linarith
  let R' : ∀ e, TRd (fun g s => D (φ x e) g s) := fun e => R (φ x e)
  have key := zk_ro_exp Hb st (enc x w) hlr hz hHb hsp (TRd.toPt R') (TRd.toPt_cons R')
    (TRd.toPt_bnd R' fun e => hR (φ x e)) h3 hE hβ (fun e g s => D (φ x e) g s)
    (TRd.toPt_reads (fun e g s => D (φ x e) g s) R')
  refine key.trans ?_
  rw [add_div, ← exP_div]
  gcongr
  refine exP_mono fun a => ?_
  rw [chZK_toPt Hb st R' q3 qE]
  exact div_le_div_of_nonneg_right (chPt_mono_iv st.params CrtGen.tables hE (hivx _) _ _ _) hden.le

/-! ## Two proof systems and "no proof" as one -/

section OSum

variable {p : Params} {I₁ I₂ W₁ W₂ C₁ C₂ ρ O : Type*}

/-- The provers of two systems, and a constant output `o₀` when there is no instance. -/
def osumProve (p₁ : I₁ → W₁ → ρ → Tab3 → Sh p → O) (p₂ : I₂ → W₂ → ρ → Tab3 → Sh p → O) (o₀ : O) :
    Option (I₁ ⊕ I₂) → W₁ × W₂ → ρ → Tab3 → Sh p → O
  | none, _, _, _, _ => o₀
  | some (.inl x), w, r, g, s => p₁ x w.1 r g s
  | some (.inr x), w, r, g, s => p₂ x w.2 r g s

/-- The simulators of two systems, with coins for both, and `o₀` when there is no instance. -/
def osumSim (s₁ : I₁ → C₁ → O) (s₂ : I₂ → C₂ → O) (o₀ : O) : Option (I₁ ⊕ I₂) → C₁ × C₂ → O
  | none, _ => o₀
  | some (.inl x), c => s₁ x c.1
  | some (.inr x), c => s₂ x c.2

/-- The programmings of two systems, none when there is no instance. -/
def osumProg (g₁ : I₁ → C₁ → Sh p → Sh p) (g₂ : I₂ → C₂ → Sh p → Sh p) :
    Option (I₁ ⊕ I₂) → C₁ × C₂ → Sh p → Sh p
  | none, _, s => s
  | some (.inl x), c, s => g₁ x c.1 s
  | some (.inr x), c, s => g₂ x c.2 s

/-- The two relations, and anything for no instance. -/
def osumRel (R₁ : I₁ → W₁ → Prop) (R₂ : I₂ → W₂ → Prop) : Option (I₁ ⊕ I₂) → W₁ × W₂ → Prop
  | none, _ => True
  | some (.inl x), w => R₁ x w.1
  | some (.inr x), w => R₂ x w.2

lemma osumProg_keep {g₁ : I₁ → C₁ → Sh p → Sh p} {g₂ : I₂ → C₂ → Sh p → Sh p}
    (h₁ : ∀ x c s, (g₁ x c s).2 = s.2) (h₂ : ∀ x c s, (g₂ x c s).2 = s.2) :
    ∀ x c s, (osumProg g₁ g₂ x c s).2 = s.2
  | none, _, _ => rfl
  | some (.inl x), c, s => h₁ x c.1 s
  | some (.inr x), c, s => h₂ x c.2 s

lemma pr_drop1 {α β γ : Type*} [Fintype α] [Nonempty α] [Fintype β] [Fintype γ]
    (P : β × γ → Prop) : pr ((α × β) × γ) (fun a => P (a.1.2, a.2)) = pr (β × γ) P := by
  let e : (α × β) × γ ≃ α × (β × γ) := Equiv.prodAssoc α β γ
  rw [← pr_prod_snd (α := α) P, ← pr_equiv e]
  rfl

/-- Marginal of the first of two coins. -/
lemma pr_coins_fst {α α' β γ : Type*} [Fintype α] [Fintype α'] [Nonempty α'] [Fintype β] [Fintype γ]
    (P : (α × β) × γ → Prop) :
    pr (((α × α') × β) × γ) (fun a => P ((a.1.1.1, a.1.2), a.2)) = pr ((α × β) × γ) P := by
  let e : ((α × α') × β) × γ ≃ α' × ((α × β) × γ) :=
    { toFun := fun a => (a.1.1.2, ((a.1.1.1, a.1.2), a.2))
      invFun := fun y => (((y.2.1.1, y.1), y.2.1.2), y.2.2)
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [← pr_prod_snd (α := α') P, ← pr_equiv e]
  rfl

/-- Marginal of the second of two coins. -/
lemma pr_coins_snd {α α' β γ : Type*} [Fintype α] [Nonempty α] [Fintype α'] [Fintype β] [Fintype γ]
    (P : (α' × β) × γ → Prop) :
    pr (((α × α') × β) × γ) (fun a => P ((a.1.1.2, a.1.2), a.2)) = pr ((α' × β) × γ) P := by
  let e : ((α × α') × β) × γ ≃ α × ((α' × β) × γ) :=
    { toFun := fun a => (a.1.1.1, ((a.1.1.2, a.1.2), a.2))
      invFun := fun y => (((y.1, y.2.1.1), y.2.1.2), y.2.2)
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [← pr_prod_snd (α := α) P, ← pr_equiv e]
  rfl

variable [Fintype ρ] [Nonempty ρ] [Fintype C₁] [Nonempty C₁] [Fintype C₂] [Nonempty C₂]

/-- **Two systems with `ZKExp` and "no proof" are one system with `ZKExp`**, for a common
nonnegative charge. -/
theorem ZKExp.osum {R₁ : I₁ → W₁ → Prop} {R₂ : I₂ → W₂ → Prop}
    {p₁ : I₁ → W₁ → ρ → Tab3 → Sh p → O} {p₂ : I₂ → W₂ → ρ → Tab3 → Sh p → O}
    {s₁ : I₁ → C₁ → O} {s₂ : I₂ → C₂ → O} {g₁ : I₁ → C₁ → Sh p → Sh p}
    {g₂ : I₂ → C₂ → Sh p → Sh p} {q3 q5 qE : ℕ} {ε : ℝ}
    {ch : Option (I₁ ⊕ I₂) → O → Finset (Bytes 16) → Finset (Bytes 37) → Finset (Blk × Blk) → ℝ}
    (h₁ : ZKExp R₁ p₁ s₁ g₁ q3 q5 qE ε (fun x => ch (some (.inl x))))
    (h₂ : ZKExp R₂ p₂ s₂ g₂ q3 q5 qE ε (fun x => ch (some (.inr x))))
    (hε : 0 ≤ ε) (hch : ∀ o Q3 Q5 QE, 0 ≤ ch none o Q3 Q5 QE) (o₀ : O) :
    ZKExp (osumRel R₁ R₂) (osumProve p₁ p₂ o₀) (osumSim s₁ s₂ o₀) (osumProg g₁ g₂) q3 q5 qE ε ch := by
  intro x w hxw D R hR
  rcases x with _ | x | x
  · simp only [osumProve, osumSim, osumProg]
    rw [pr_drop1 (α := ρ) (fun b => D o₀ b.1 b.2), pr_drop1 (α := C₁ × C₂) (fun b => D o₀ b.1 b.2),
      sub_self, abs_zero]
    exact add_nonneg hε (exP_nonneg fun _ => hch _ _ _ _)
  · have h := h₁ x w.1 hxw D R hR
    simp only [osumProve, osumSim, osumProg]
    rw [pr_coins_fst (α' := C₂) (fun a : (C₁ × Tab3) × Sh p => D (s₁ x a.1.1) a.1.2 (g₁ x a.1.1 a.2))]
    exact h
  · have h := h₂ x w.2 hxw D R hR
    simp only [osumProve, osumSim, osumProg]
    rw [pr_coins_snd (α := C₁) (fun a : (C₂ × Tab3) × Sh p => D (s₂ x a.1.1) a.1.2 (g₂ x a.1.1 a.2))]
    exact h

end OSum

/-! ## The joint step for any system with `ZKExp` at the point charge -/

section LeanJointG

variable {X : Type} [Fintype X] [Nonempty X] {I W C O Ω : Type*} [Fintype Ω] [Nonempty Ω]
  [Fintype C] [Nonempty C] {p : Params} {N : ℕ}

/-- **The joint many-proof bound for a game of proofs with `ZKExp` at the point charge.** As
`real_sim_leN_lean`, for any prover, simulator and programming (`hkeep`: the programmings change
only `H₂³`) with `ZKExp` at error `εZK/(1 − βZK)` and charge `chPt/(1 − βZK)` of the `iv` decoder
`ivO` at every value of the extra table (`hzk`), the programmings and the real proofs confined to
their `iv`s. -/
theorem real_sim_leN_leanG (prove : X → I → W → Bytes 16 → Tab3 → Sh p → O) (sim : I → C → O)
    (prog : X → I → C → Sh p → Sh p) (hkeep : ∀ x xI c s, (prog x xI c s).2 = s.2)
    (Rl : I → W → Prop) (ivO : X → I → O → Option ByteArray)
    (xOf : Ω → List O → I) (wOf : Ω → List O → W) (hrel : ∀ ω h, Rl (xOf ω h) (wOf ω h))
    (Rpg : ∀ x xI c, TRd (fun (_ : Tab3) s => (prog x xI c s).1)) {m5 mE : ℕ}
    (hRpg : ∀ x xI c, Conf (Rpg x xI c) (fun _ => ivO x xI (sim xI c)) m5 mE)
    (RP : ∀ x xI w r g', TRd (fun (_ : Tab3) (s : Sh p) => prove x xI w r g' s))
    {s5 sE : ℕ}
    (hRP : ∀ x xI w r g', Rl xI w → Conf (RP x xI w r g')
      (fun s => ivO x xI (prove x xI w r g' s)) s5 sE)
    (R : GRd Ω O p X N) (hc : R.Cons) {a3 a5 aE : ℕ} (hb : R.Bnd a3 a5 aE)
    (h3 : (a3 : ℝ) < 2 ^ 128) (hE : 221 * ((aE + N * max mE sE + 4607 : ℕ) : ℝ) < 2 ^ 128)
    (hβ : βZK (a5 + N * max m5 s5) (aE + N * max mE sE) < 1)
    (hzk : ∀ x, ZKExp Rl (prove x) sim (prog x) a3 (a5 + N * max m5 s5) (aE + N * max mE sE)
      (εZK (aE + N * max mE sE) / (1 - βZK (a5 + N * max m5 s5) (aE + N * max mE sE)))
      (fun xI o Q3 Q5 QE => chPt p CrtGen.tables a3 (aE + N * max mE sE) (ivO x xI o) Q3 Q5 QE /
        (1 - βZK (a5 + N * max m5 s5) (aE + N * max mE sE))))
    {J : ℝ}
    (hJ : ∑ i ∈ range N, ∑ k, wZK a3 (a5 + N * max m5 s5) (aE + N * max mE sE) k *
      exU _ (fun z => (nZK p ivO xOf R (max m5 s5) (max mE sE) i k
        (viewN (C := C) (ρ := Bytes 16) (gP prove xOf wOf) (gS sim xOf) (gPg prog xOf) N z) : ℝ))
      ≤ J)
    (hNB : N * ∑ k, wZK a3 (a5 + N * max m5 s5) (aE + N * max mE sE) k *
      MZK N a3 a5 aE (max m5 s5) (max mE sE) k < 1)
    (Ev : Ω → List O → (Fin N → Tab3) → ShX (Blk → Blk) p X → Prop)
    (hEv : R.Reads (fun v => Ev v.1 v.2.1 v.2.2.1 v.2.2.2)) :
    |pr _ (realGN (C := C) (gP prove xOf wOf) Ev) -
        pr _ (simGN (ρ := Bytes 16) (gS sim xOf) (gPg prog xOf) Ev)| ≤
      (∑ i : Fin N, (εZK (aE + N * max mE sE) /
          (1 - βZK (a5 + N * max m5 s5) (aE + N * max mE sE)) +
        (1 + ∑ k, wZK a3 (a5 + N * max m5 s5) (aE + N * max mE sE) k *
          MZK N a3 a5 aE (max m5 s5) (max mE sE) k) *
          pr _ (deltaN (gP prove xOf wOf) (gS sim xOf) (gPg prog xOf) i)) + J) /
        (1 - N * ∑ k, wZK a3 (a5 + N * max m5 s5) (aE + N * max mE sE) k *
          MZK N a3 a5 aE (max m5 s5) (max mE sE) k) := by
  set q5 := a5 + N * max m5 s5
  set qE := aE + N * max mE sE
  have hd : 0 < dEZK qE := dEZK_pos hE
  have hden : 0 < 1 - βZK q5 qE := by linarith
  have h3' : (0 : ℝ) < 2 ^ 128 - a3 := by linarith
  have hw : ∀ k, 0 ≤ wZK a3 q5 qE k := by
    intro k
    fin_cases k
    · exact div_nonneg (div_nonneg zero_le_one h3'.le) hden.le
    · exact div_nonneg (div_nonneg (by norm_num) hd.le) hden.le
    · exact div_nonneg (by positivity) hden.le
  refine real_sim_leN_game prove (sim := sim) (prog := prog) (xOf := xOf) wOf
    (fun x xI o Q3 Q5 QE => chPt p CrtGen.tables a3 qE (ivO x xI o) Q3 Q5 QE / (1 - βZK q5 qE))
    hzk hrel hkeep Rpg RP R hc
    (fun Ev' hEv' i ω τ x o => hopRd_bnd ivO hkeep Rpg (fun x ω h c => hRpg x _ c) RP
      (fun x ω h r g' => hRP x _ _ r g' (hrel ω h)) R hc hb Ev' hEv' i ω τ x o)
    (wZK a3 q5 qE) hw (nZK p ivO xOf R (max m5 s5) (max mE sE)) (MZK N a3 a5 aE (max m5 s5) (max mE sE))
    (fun i _ k v => nZK_le ivO xOf R hb _ _ i k v)
    (fun i _ k ω l gs t gs' t' h => nZK_agree ivO xOf R hc _ _ i k ω l gs t gs' t' h)
    (fun Ev' hEv' i ω τ r g t => ?_) hJ hNB Ev hEv
  obtain ⟨c3, cE, c5⟩ := hopRd_charges (ivO := ivO) (prove := prove) (wOf := wOf)
    (sim := sim) (xOf := xOf) hkeep Rpg (fun x ω h c => hRpg x _ c) RP
    (fun x ω h r g' => hRP x _ _ r g' (hrel ω h)) R hc
    Ev' hEv' i ω τ t.2.2 (gP prove xOf wOf ω
      (simPre (gS sim xOf) (gPg prog xOf) ω (tapeC τ) i).1 r g t) g (shOf t)
  rw [Fin.sum_univ_three]
  simp only [wZK, nZK, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons]
  unfold chPt
  exact lin3_le h3' hd (by positivity) hden (by exact_mod_cast c3) (by exact_mod_cast cE)
    (by exact_mod_cast c5)

end LeanJointG


/-! ## Slots with no proof are charged nothing -/

section Active

variable {X : Type} [Fintype X] [Nonempty X] {I W C O Ω : Type*} [Fintype Ω] [Nonempty Ω]
  [Fintype C] [Nonempty C] {p : Params} {N : ℕ}

/-- **The charge of slot `i` in a view, zero when the slot's instance is not active** (no proof
is made: the Client refused). -/
noncomputable def nZKA (act : I → Prop) [DecidablePred act] (ivO : X → I → O → Option ByteArray)
    (xOf : Ω → List O → I) (R : GRd Ω O p X N) (h5 hE : ℕ) (i : ℕ) (k : Fin 3)
    (v : Ω × List O × (Fin N → Tab3) × ShX (Blk → Blk) p X) : ℕ :=
  if act (xOf v.1 (v.2.1.take i)) then nZK p ivO xOf R h5 hE i k v else 0

omit [Fintype X] [Nonempty X] [Fintype Ω] [Nonempty Ω] in
lemma nZKA_le_nZK (act : I → Prop) [DecidablePred act] (ivO : X → I → O → Option ByteArray)
    (xOf : Ω → List O → I) (R : GRd Ω O p X N) (h5 hE : ℕ) (i : ℕ) (k : Fin 3) (v) :
    nZKA act ivO xOf R h5 hE i k v ≤ nZK p ivO xOf R h5 hE i k v := by
  unfold nZKA; split_ifs <;> omega

omit [Fintype X] [Nonempty X] [Fintype Ω] [Nonempty Ω] [Fintype C] in
/-- The history of the view of hop `i` begins with the hop's history. -/
lemma contView_take (P : Ω → List O → Bytes 16 → Tab3 → ShX (Blk → Blk) p X → O)
    (Sm : Ω → List O → C → O) (pg : Ω → List O → C → ShX (Blk → Blk) p X → ShX (Blk → Blk) p X)
    (i : Fin N) (ω : Ω) (τ : Fin N → Slot (Bytes 16) C Tab3) (o : O) (g : Tab3)
    (u : ShX (Blk → Blk) p X) :
    ((contView P Sm pg i ω τ o g u).2.1).take i.val = (simPre Sm pg ω (tapeC τ) i).1 := by
  obtain ⟨r, hr⟩ := realFrom_prefix P ω (tapeR τ) u (N - (i.val + 1))
    ((simPre Sm pg ω (tapeC τ) i).1 ++ [o]) (i.val + 1)
  have hlen : (simPre Sm pg ω (tapeC τ) i).1.length = i.val := simPre_length _ _ ω _ i.val
  show (realFrom P ω (tapeR τ) u ((simPre Sm pg ω (tapeC τ) i).1 ++ [o]) (i.val + 1)
    (N - (i.val + 1))).take i.val = _
  rw [hr, List.append_assoc]
  exact List.take_left' hlen

/-- **The joint bound with inactive slots charged nothing.** As `real_sim_leN_leanG`, with the
charge of an instance zero unless it is active (`act`): `ZKExp` at the charge `chPt` for active
instances and `0` for the others (`hzk`; for a slot with no proof the hop is an identity). The
counts are `nZKA`: `nZK` for the active slots, `0` for the others. -/
theorem real_sim_leN_leanA (prove : X → I → W → Bytes 16 → Tab3 → Sh p → O) (sim : I → C → O)
    (prog : X → I → C → Sh p → Sh p) (hkeep : ∀ x xI c s, (prog x xI c s).2 = s.2)
    (Rl : I → W → Prop) (act : I → Prop) [DecidablePred act] (ivO : X → I → O → Option ByteArray)
    (xOf : Ω → List O → I) (wOf : Ω → List O → W) (hrel : ∀ ω h, Rl (xOf ω h) (wOf ω h))
    (Rpg : ∀ x xI c, TRd (fun (_ : Tab3) s => (prog x xI c s).1)) {m5 mE : ℕ}
    (hRpg : ∀ x xI c, Conf (Rpg x xI c) (fun _ => ivO x xI (sim xI c)) m5 mE)
    (RP : ∀ x xI w r g', TRd (fun (_ : Tab3) (s : Sh p) => prove x xI w r g' s))
    {s5 sE : ℕ}
    (hRP : ∀ x xI w r g', Rl xI w → Conf (RP x xI w r g')
      (fun s => ivO x xI (prove x xI w r g' s)) s5 sE)
    (R : GRd Ω O p X N) (hc : R.Cons) {a3 a5 aE : ℕ} (hb : R.Bnd a3 a5 aE)
    (h3 : (a3 : ℝ) < 2 ^ 128) (hE : 221 * ((aE + N * max mE sE + 4607 : ℕ) : ℝ) < 2 ^ 128)
    (hβ : βZK (a5 + N * max m5 s5) (aE + N * max mE sE) < 1)
    (hzk : ∀ x, ZKExp Rl (prove x) sim (prog x) a3 (a5 + N * max m5 s5) (aE + N * max mE sE)
      (εZK (aE + N * max mE sE) / (1 - βZK (a5 + N * max m5 s5) (aE + N * max mE sE)))
      (fun xI o Q3 Q5 QE => if act xI then chPt p CrtGen.tables a3 (aE + N * max mE sE)
        (ivO x xI o) Q3 Q5 QE / (1 - βZK (a5 + N * max m5 s5) (aE + N * max mE sE)) else 0))
    {J : ℝ}
    (hJ : ∑ i ∈ range N, ∑ k, wZK a3 (a5 + N * max m5 s5) (aE + N * max mE sE) k *
      exU _ (fun z => (nZKA act ivO xOf R (max m5 s5) (max mE sE) i k
        (viewN (C := C) (ρ := Bytes 16) (gP prove xOf wOf) (gS sim xOf) (gPg prog xOf) N z) : ℝ))
      ≤ J)
    (hNB : N * ∑ k, wZK a3 (a5 + N * max m5 s5) (aE + N * max mE sE) k *
      MZK N a3 a5 aE (max m5 s5) (max mE sE) k < 1)
    (Ev : Ω → List O → (Fin N → Tab3) → ShX (Blk → Blk) p X → Prop)
    (hEv : R.Reads (fun v => Ev v.1 v.2.1 v.2.2.1 v.2.2.2)) :
    |pr _ (realGN (C := C) (gP prove xOf wOf) Ev) -
        pr _ (simGN (ρ := Bytes 16) (gS sim xOf) (gPg prog xOf) Ev)| ≤
      (∑ i : Fin N, (εZK (aE + N * max mE sE) /
          (1 - βZK (a5 + N * max m5 s5) (aE + N * max mE sE)) +
        (1 + ∑ k, wZK a3 (a5 + N * max m5 s5) (aE + N * max mE sE) k *
          MZK N a3 a5 aE (max m5 s5) (max mE sE) k) *
          pr _ (deltaN (gP prove xOf wOf) (gS sim xOf) (gPg prog xOf) i)) + J) /
        (1 - N * ∑ k, wZK a3 (a5 + N * max m5 s5) (aE + N * max mE sE) k *
          MZK N a3 a5 aE (max m5 s5) (max mE sE) k) := by
  set q5 := a5 + N * max m5 s5
  set qE := aE + N * max mE sE
  have hd : 0 < dEZK qE := dEZK_pos hE
  have hden : 0 < 1 - βZK q5 qE := by linarith
  have h3' : (0 : ℝ) < 2 ^ 128 - a3 := by linarith
  have hw : ∀ k, 0 ≤ wZK a3 q5 qE k := by
    intro k
    fin_cases k
    · exact div_nonneg (div_nonneg zero_le_one h3'.le) hden.le
    · exact div_nonneg (div_nonneg (by norm_num) hd.le) hden.le
    · exact div_nonneg (by positivity) hden.le
  refine real_sim_leN_game prove (sim := sim) (prog := prog) (xOf := xOf) wOf
    (fun x xI o Q3 Q5 QE => if act xI then chPt p CrtGen.tables a3 qE (ivO x xI o) Q3 Q5 QE /
      (1 - βZK q5 qE) else 0)
    hzk hrel hkeep Rpg RP R hc
    (fun Ev' hEv' i ω τ x o => hopRd_bnd ivO hkeep Rpg (fun x ω h c => hRpg x _ c) RP
      (fun x ω h r g' => hRP x _ _ r g' (hrel ω h)) R hc hb Ev' hEv' i ω τ x o)
    (wZK a3 q5 qE) hw (nZKA act ivO xOf R (max m5 s5) (max mE sE))
    (MZK N a3 a5 aE (max m5 s5) (max mE sE))
    (fun i _ k v => (nZKA_le_nZK act ivO xOf R _ _ i k v).trans (nZK_le ivO xOf R hb _ _ i k v))
    (fun i _ k ω l gs t gs' t' h => by
      unfold nZKA
      simp only [nZK_agree ivO xOf R hc _ _ i k ω l gs t gs' t' h])
    (fun Ev' hEv' i ω τ r g t => ?_) hJ hNB Ev hEv
  have htake := contView_take (gP prove xOf wOf) (gS sim xOf) (gPg prog xOf) i ω τ
    (gP prove xOf wOf ω (simPre (gS sim xOf) (gPg prog xOf) ω (tapeC τ) i).1 r g t) g
    ((simPre (gS sim xOf) (gPg prog xOf) ω (tapeC τ) i).2 t)
  obtain ⟨c3, cE, c5⟩ := hopRd_charges (ivO := ivO) (prove := prove) (wOf := wOf)
    (sim := sim) (xOf := xOf) hkeep Rpg (fun x ω h c => hRpg x _ c) RP
    (fun x ω h r g' => hRP x _ _ r g' (hrel ω h)) R hc
    Ev' hEv' i ω τ t.2.2 (gP prove xOf wOf ω
      (simPre (gS sim xOf) (gPg prog xOf) ω (tapeC τ) i).1 r g t) g (shOf t)
  by_cases ha : act (xOf ω (simPre (gS sim xOf) (gPg prog xOf) ω (tapeC τ) i).1)
  · have ha' : act (xOf (contView (gP prove xOf wOf) (gS sim xOf) (gPg prog xOf) i ω τ
        (gP prove xOf wOf ω (simPre (gS sim xOf) (gPg prog xOf) ω (tapeC τ) i).1 r g t) g
        ((simPre (gS sim xOf) (gPg prog xOf) ω (tapeC τ) i).2 t)).1
        ((contView (gP prove xOf wOf) (gS sim xOf) (gPg prog xOf) i ω τ
        (gP prove xOf wOf ω (simPre (gS sim xOf) (gPg prog xOf) ω (tapeC τ) i).1 r g t) g
        ((simPre (gS sim xOf) (gPg prog xOf) ω (tapeC τ) i).2 t)).2.1.take i.val)) := by
      rw [htake]; exact ha
    unfold nZKA
    simp only [ha, ha', ↓reduceIte]
    rw [Fin.sum_univ_three]
    simp only [wZK, nZK, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons]
    unfold chPt
    exact lin3_le h3' hd (by positivity) hden (by exact_mod_cast c3) (by exact_mod_cast cE)
      (by exact_mod_cast c5)
  · have ha' : ¬ act (xOf (contView (gP prove xOf wOf) (gS sim xOf) (gPg prog xOf) i ω τ
        (gP prove xOf wOf ω (simPre (gS sim xOf) (gPg prog xOf) ω (tapeC τ) i).1 r g t) g
        ((simPre (gS sim xOf) (gPg prog xOf) ω (tapeC τ) i).2 t)).1
        ((contView (gP prove xOf wOf) (gS sim xOf) (gPg prog xOf) i ω τ
        (gP prove xOf wOf ω (simPre (gS sim xOf) (gPg prog xOf) ω (tapeC τ) i).1 r g t) g
        ((simPre (gS sim xOf) (gPg prog xOf) ω (tapeC τ) i).2 t)).2.1.take i.val)) := by
      rw [htake]; exact ha
    unfold nZKA
    simp only [ha, ha', ↓reduceIte, Nat.cast_zero, mul_zero, Finset.sum_const_zero, le_refl]

end Active

/-! ## `real_sim_leN_lean` with the programmings discharged -/

section LeanPg

variable {X : Type} [Fintype X] [Nonempty X] {I W O Ω : Type*} [Fintype Ω] [Nonempty Ω]
  {p : Params} {N : ℕ}

/-- **`real_sim_leN_lean` with its hypothesis on the programmings proved** (`lProgRd_conf`: the
simulator's programming is a point reader confined to the simulated proof's `iv`, within
`(312, 4607)`). What is left: the real proofs' readers (`hRP`) and the game reader. -/
theorem real_sim_leN_lean_pg (Hb : X → Hashes) (hHb : ∀ x, HashesWF (Hb x)) (stOf : I → Statement)
    (hp : ∀ xI, (stOf xI).params = p) (hlr : p.labelRows = true) (enc : I → W → ByteArray)
    (Rl : I → W → Prop) (cs : I → ByteArray → ByteArray → System GF128)
    (hz : ∀ xI w, Rl xI w → ZKHyp CrtGen.tables (stOf xI) (enc xI w) (cs xI))
    (hsp : SmallParams p) (φ : Except String ByteArray → O) (ivO : X → I → O → Option ByteArray)
    (hiv : ∀ x xI e v, ivO x xI (φ e) = some v → ivV (Hb x) (stOf xI) e = some v)
    (xOf : Ω → List O → I) (wOf : Ω → List O → W) (hrel : ∀ ω h, Rl (xOf ω h) (wOf ω h))
    (RP : ∀ x xI w r g', TRd (fun (_ : Tab3) (s : Sh p) => lProve p Hb stOf enc φ x xI w r g' s))
    {s5 sE : ℕ}
    (hRP : ∀ x xI w r g', Rl xI w → Conf (RP x xI w r g')
      (fun s => ivO x xI (lProve p Hb stOf enc φ x xI w r g' s)) s5 sE)
    (R : GRd Ω O p X N) (hc : R.Cons) {a3 a5 aE : ℕ} (hb : R.Bnd a3 a5 aE)
    (h3 : (a3 : ℝ) < 2 ^ 128) (hE : 221 * ((aE + N * max 4607 sE + 4607 : ℕ) : ℝ) < 2 ^ 128)
    (hβ : βZK (a5 + N * max 312 s5) (aE + N * max 4607 sE) < 1) {J : ℝ}
    (hJ : ∑ i ∈ range N, ∑ k, wZK a3 (a5 + N * max 312 s5) (aE + N * max 4607 sE) k *
      exU _ (fun z => (nZK p ivO xOf R (max 312 s5) (max 4607 sE) i k
        (viewN (C := SimCoins p) (gP (lProve p Hb stOf enc φ) xOf wOf)
          (gS (lSim p φ) xOf) (gPg (lProg p Hb stOf) xOf) N z) : ℝ)) ≤ J)
    (hNB : N * ∑ k, wZK a3 (a5 + N * max 312 s5) (aE + N * max 4607 sE) k *
      MZK N a3 a5 aE (max 312 s5) (max 4607 sE) k < 1)
    (Ev : Ω → List O → (Fin N → Tab3) → ShX (Blk → Blk) p X → Prop)
    (hEv : R.Reads (fun v => Ev v.1 v.2.1 v.2.2.1 v.2.2.2)) :
    |pr _ (realGN (C := SimCoins p) (gP (lProve p Hb stOf enc φ) xOf wOf) Ev) -
        pr _ (simGN (ρ := Bytes 16) (gS (lSim p φ) xOf) (gPg (lProg p Hb stOf) xOf) Ev)| ≤
      (∑ i : Fin N, (εZK (aE + N * max 4607 sE) /
          (1 - βZK (a5 + N * max 312 s5) (aE + N * max 4607 sE)) +
        (1 + ∑ k, wZK a3 (a5 + N * max 312 s5) (aE + N * max 4607 sE) k *
          MZK N a3 a5 aE (max 312 s5) (max 4607 sE) k) *
          pr _ (deltaN (gP (lProve p Hb stOf enc φ) xOf wOf) (gS (lSim p φ) xOf)
            (gPg (lProg p Hb stOf) xOf) i)) + J) /
        (1 - N * ∑ k, wZK a3 (a5 + N * max 312 s5) (aE + N * max 4607 sE) k *
          MZK N a3 a5 aE (max 312 s5) (max 4607 sE) k) :=
  real_sim_leN_lean Hb hHb stOf hp hlr enc Rl cs hz hsp φ ivO hiv xOf wOf hrel
    (lProgRd Hb stOf) (lProgRd_conf Hb hHb stOf hp φ ivO hiv) RP hRP R hc hb h3 hE hβ hJ hNB Ev hEv

end LeanPg

/-! ## The real provers' readers, at any parameter variable -/

section Real

/-- **A function of a confined reader's value is confined, with the reader's reads.** -/
theorem Conf.map {p : Params} {Y Z : Type*} {F : Tab3 → Sh p → Y} {R : TRd F} (f : Y → Z)
    {iv : Sh p → Option ByteArray} {a5 aE : ℕ} (hc : Conf R iv a5 aE) : Conf (R.map f) iv a5 aE :=
  ⟨hc.h3, hc.h5, hc.hE, hc.in5, hc.inE⟩

/-- `realPtRd` at a parameter variable `p` with `st.params = p`. -/
noncomputable def realPtRdP {p : Params} (Hb : Hashes) (st : Statement) (w : ByteArray)
    (hp : st.params = p) (hHb : HashesWF Hb) (ρ : Bytes 16) (G3 : Tab3) :
    TRd (fun (_ : Tab3) (s : Sh p) => realRO p Hb st w ρ G3 s) := by
  subst hp; exact realPtRd Hb st w hHb ρ G3

/-- **The real prover's reader is confined**, at a parameter variable. -/
theorem realPtRdP_conf {p : Params} {Hb : Hashes} {st : Statement} {w : ByteArray}
    {cs : ByteArray → ByteArray → System GF128} (hzk : ZKHyp CrtGen.tables st w cs)
    (hHb : HashesWF Hb) (hp : st.params = p) (hlr : p.labelRows = true) (ρ : Bytes 16)
    (G3 : Tab3) :
    Conf (realPtRdP Hb st w hp hHb ρ G3) (fun s => ivV Hb st (realRO p Hb st w ρ G3 s)) 624 4607 := by
  subst hp
  obtain ⟨hl1, -, -, hl2⟩ := labelRows_sizes hlr
  exact realPtRd_conf hzk hHb (by omega) ρ G3

variable {X : Type} {I W O : Type*} {p : Params}

/-- **The Lean game's real provers as point readers.** -/
noncomputable def lProveRd (Hb : X → Hashes) (hHb : ∀ x, HashesWF (Hb x)) (stOf : I → Statement)
    (hp : ∀ xI, (stOf xI).params = p) (enc : I → W → ByteArray) (φ : Except String ByteArray → O)
    (x : X) (xI : I) (w : W) (r : Bytes 16) (g' : Tab3) :
    TRd (fun (_ : Tab3) (s : Sh p) => lProve p Hb stOf enc φ x xI w r g' s) :=
  (realPtRdP (Hb x) (stOf xI) (enc xI w) (hp xI) (hHb x) r g').map φ

/-- **`real_sim_leN_lean`'s `hRP`**, with `(s₅, s_E) = (624, 4607)`. -/
theorem lProveRd_conf (Hb : X → Hashes) (hHb : ∀ x, HashesWF (Hb x)) (stOf : I → Statement)
    (hp : ∀ xI, (stOf xI).params = p) (hlr : p.labelRows = true) (enc : I → W → ByteArray)
    (Rl : I → W → Prop) (cs : I → ByteArray → ByteArray → System GF128)
    (hz : ∀ xI w, Rl xI w → ZKHyp CrtGen.tables (stOf xI) (enc xI w) (cs xI))
    (φ : Except String ByteArray → O) (ivO : X → I → O → Option ByteArray)
    (hiv : ∀ x xI e v, ivO x xI (φ e) = some v → ivV (Hb x) (stOf xI) e = some v)
    (x : X) (xI : I) (w : W) (r : Bytes 16) (g' : Tab3) (hw : Rl xI w) :
    Conf (lProveRd Hb hHb stOf hp enc φ x xI w r g')
      (fun s => ivO x xI (lProve p Hb stOf enc φ x xI w r g' s)) 624 4607 :=
  ((realPtRdP_conf (hz xI w hw) (hHb x) (hp xI) hlr r g').map φ).of_iv fun _ v h => hiv x xI _ v h

end Real

/-! ## `real_sim_leN_lean` with the honest readers discharged -/

section LeanFull

variable {X : Type} [Fintype X] [Nonempty X] {I W O Ω : Type*} [Fintype Ω] [Nonempty Ω]
  {p : Params} {N : ℕ}

/-- **The joint bound for a game of Lean proofs, for every event a consistent game reader reads**,
with the programmings and the later real proofs as proved point readers (`lProgRd_conf`,
`lProveRd_conf`): `(m₅, m_E) = (312, 4607)`, `(s₅, s_E) = (624, 4607)`, so `max` is `(624, 4607)`.
What is left is the game reader `R` (its budgets `(a₃, a₅, a_E)`) and `J`. -/
theorem real_sim_leN_lean_full (Hb : X → Hashes) (hHb : ∀ x, HashesWF (Hb x))
    (stOf : I → Statement) (hp : ∀ xI, (stOf xI).params = p) (hlr : p.labelRows = true)
    (enc : I → W → ByteArray) (Rl : I → W → Prop) (cs : I → ByteArray → ByteArray → System GF128)
    (hz : ∀ xI w, Rl xI w → ZKHyp CrtGen.tables (stOf xI) (enc xI w) (cs xI))
    (hsp : SmallParams p) (φ : Except String ByteArray → O) (ivO : X → I → O → Option ByteArray)
    (hiv : ∀ x xI e v, ivO x xI (φ e) = some v → ivV (Hb x) (stOf xI) e = some v)
    (xOf : Ω → List O → I) (wOf : Ω → List O → W) (hrel : ∀ ω h, Rl (xOf ω h) (wOf ω h))
    (R : GRd Ω O p X N) (hc : R.Cons) {a3 a5 aE : ℕ} (hb : R.Bnd a3 a5 aE)
    (h3 : (a3 : ℝ) < 2 ^ 128) (hE : 221 * ((aE + N * max 4607 4607 + 4607 : ℕ) : ℝ) < 2 ^ 128)
    (hβ : βZK (a5 + N * max 312 624) (aE + N * max 4607 4607) < 1) {J : ℝ}
    (hJ : ∑ i ∈ range N, ∑ k, wZK a3 (a5 + N * max 312 624) (aE + N * max 4607 4607) k *
      exU _ (fun z => (nZK p ivO xOf R (max 312 624) (max 4607 4607) i k
        (viewN (C := SimCoins p) (gP (lProve p Hb stOf enc φ) xOf wOf)
          (gS (lSim p φ) xOf) (gPg (lProg p Hb stOf) xOf) N z) : ℝ)) ≤ J)
    (hNB : N * ∑ k, wZK a3 (a5 + N * max 312 624) (aE + N * max 4607 4607) k *
      MZK N a3 a5 aE (max 312 624) (max 4607 4607) k < 1)
    (Ev : Ω → List O → (Fin N → Tab3) → ShX (Blk → Blk) p X → Prop)
    (hEv : R.Reads (fun v => Ev v.1 v.2.1 v.2.2.1 v.2.2.2)) :
    |pr _ (realGN (C := SimCoins p) (gP (lProve p Hb stOf enc φ) xOf wOf) Ev) -
        pr _ (simGN (ρ := Bytes 16) (gS (lSim p φ) xOf) (gPg (lProg p Hb stOf) xOf) Ev)| ≤
      (∑ i : Fin N, (εZK (aE + N * max 4607 4607) /
          (1 - βZK (a5 + N * max 312 624) (aE + N * max 4607 4607)) +
        (1 + ∑ k, wZK a3 (a5 + N * max 312 624) (aE + N * max 4607 4607) k *
          MZK N a3 a5 aE (max 312 624) (max 4607 4607) k) *
          pr _ (deltaN (gP (lProve p Hb stOf enc φ) xOf wOf) (gS (lSim p φ) xOf)
            (gPg (lProg p Hb stOf) xOf) i)) + J) /
        (1 - N * ∑ k, wZK a3 (a5 + N * max 312 624) (aE + N * max 4607 4607) k *
          MZK N a3 a5 aE (max 312 624) (max 4607 4607) k) :=
  real_sim_leN_lean_pg Hb hHb stOf hp hlr enc Rl cs hz hsp φ ivO hiv xOf wOf hrel
    (lProveRd Hb hHb stOf hp enc φ)
    (fun x xI w r g' hw => lProveRd_conf Hb hHb stOf hp hlr enc Rl cs hz φ ivO hiv x xI w r g' hw)
    R hc hb h3 hE hβ hJ hNB Ev hEv

end LeanFull

end VoleMole.Theft
