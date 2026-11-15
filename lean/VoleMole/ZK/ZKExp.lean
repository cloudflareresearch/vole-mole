import VoleMole.ZK.PtRd

/-!
# Zero knowledge with expected point charges, as a property of a proof system

`zk_ro_exp` (`ZK/ReadsROExp.lean`) is a statement about one statement and one point reader of the
view. The many-proof games need it as a property of a proof system (as `ZeroKnowledgeRO` is for
worst-case budgets), for distinguishers given with a consistent **table** reader (`TRd`,
`ZK/PtRd.lean`), and with the charge a function of the proof's output and of the reads:

* **`chPt`**: the charge of reads `(Q₃, Q₅, Q_E)` for an output with `iv` `iv?`: the `H₃` keys over
  `2¹²⁸ − q₃`, `221` times the cipher keys read at CTR blocks of the `iv` over `d_E`, the `H₅` keys
  at its gate inputs over `2¹²⁸` (every key, for an output with no `iv`). `chZK_toPt`: it is
  `chZK` of the view reader. `chPt_mono_iv`: an output map that forgets the `iv` only charges more.
* **`ZKExp`**: for every instance with a witness and every distinguisher with a consistent table
  reader within budgets `(q₃, q₅, q_E)`,

      |Pr_real[D] − Pr_sim[D]| ≤ ε + E_real[ch x o (reads at the real tables)],

  the expectation over the prover's coins, the slice and the (unprogrammed) tables.
* **`lean_zkExp`**: the Lean prover (any output map `φ` with an `iv` decoder `ivO` that never
  invents an `iv`) is `ZKExp` with `ε = εZK/(1 − βZK)` and the charge `chPt/(1 − βZK)`. Function
  rows.
-/

open Finset

set_option synthInstance.maxSize 1024

set_option linter.unusedSectionVars false

namespace VoleMole.ZK.Sim

open VoleMole.Verifier VoleMole.Verifier.Bridge VoleMole.Arith VoleMole.ZK VoleMole.Privacy
  VoleMole.ZK.IC

/-! ## The charge of a set of reads -/

/-- The cipher keys charged: read at a CTR block of the `iv`, or every key read without one. -/
noncomputable def cEof (iv : Option ByteArray) (QE : Finset (Blk × Blk)) : ℕ :=
  match iv with
  | some iv => (qkeys (InY iv) QE).card
  | none => (QE.image Prod.fst).card

/-- The `H₅` keys charged: gate inputs of the `iv`, or every key read without one. -/
noncomputable def c5of (p : Params) (T : CrtTables) (iv : Option ByteArray) (Q5 : Finset (Bytes 37)) :
    ℕ :=
  match iv with
  | some iv => (Q5.filter (Gate5 p T iv)).card
  | none => Q5.card

/-- **The charge of reads `(Q₃, Q₅, Q_E)`** for an output with `iv` `iv?`. -/
noncomputable def chPt (p : Params) (T : CrtTables) (q3 qE : ℕ) (iv : Option ByteArray)
    (Q3 : Finset (Bytes 16)) (Q5 : Finset (Bytes 37)) (QE : Finset (Blk × Blk)) : ℝ :=
  (Q3.card : ℝ) / (2 ^ 128 - q3) + 221 * (cEof iv QE : ℝ) / dEZK qE + (c5of p T iv Q5 : ℝ) / 2 ^ 128

lemma cEof_le_some (iv : ByteArray) (QE : Finset (Blk × Blk)) :
    cEof (some iv) QE ≤ cEof none QE :=
  card_le_card (image_subset_image (filter_subset _ _))

lemma c5of_le_some (p : Params) (T : CrtTables) (iv : ByteArray) (Q5 : Finset (Bytes 37)) :
    c5of p T (some iv) Q5 ≤ c5of p T none Q5 := card_filter_le _ _

lemma dEZK_pos {qE : ℕ} (hE : 221 * ((qE + 4607 : ℕ) : ℝ) < 2 ^ 128) : 0 < dEZK qE := by
  unfold dEZK; linarith

/-- **Forgetting the `iv` only charges more.** -/
lemma chPt_mono_iv (p : Params) (T : CrtTables) {q3 qE : ℕ} (hE : 221 * ((qE + 4607 : ℕ) : ℝ) < 2 ^ 128)
    {iv iv' : Option ByteArray} (h : ∀ v, iv' = some v → iv = some v) (Q3 Q5 QE) :
    chPt p T q3 qE iv Q3 Q5 QE ≤ chPt p T q3 qE iv' Q3 Q5 QE := by
  have hd := dEZK_pos hE
  unfold chPt
  rcases iv' with _ | v
  · have h1 : (cEof iv QE : ℝ) ≤ cEof none QE := by
      rcases iv with _ | v
      · exact le_rfl
      · exact_mod_cast cEof_le_some v QE
    have h2 : (c5of p T iv Q5 : ℝ) ≤ c5of p T none Q5 := by
      rcases iv with _ | v
      · exact le_rfl
      · exact_mod_cast c5of_le_some p T v Q5
    gcongr
  · rw [h v rfl]

/-- **The charge of the view reader** of a family of table readers is `chPt` at the raw output's
`iv`. -/
lemma chZK_toPt {X : Type*} (Hb : Hashes) (st : Statement)
    {D : Except String ByteArray → Tab3 → Sh st.params → X} (R : ∀ o, TRd (D o)) (q3 qE : ℕ)
    (e : Except String ByteArray) (g : Tab3) (s : Sh st.params) :
    chZK (TRd.toPt R) Hb st q3 qE (toVw e g s) =
      chPt st.params CrtGen.tables q3 qE (ivV Hb st e) ((R e).Q3 g s) ((R e).Q5 g s)
        ((R e).QE g s) := by
  unfold chZK chPt ch3 chE ch5 cEof c5of
  rfl

/-- The charge is nonnegative. -/
lemma chPt_nonneg (p : Params) (T : CrtTables) {q3 qE : ℕ} (h3 : (q3 : ℝ) < 2 ^ 128)
    (hE : 221 * ((qE + 4607 : ℕ) : ℝ) < 2 ^ 128) (iv Q3 Q5 QE) :
    0 ≤ chPt p T q3 qE iv Q3 Q5 QE := by
  have hd := dEZK_pos hE
  have h3' : (0 : ℝ) < 2 ^ 128 - q3 := by linarith
  unfold chPt; positivity

/-- **The charge is at most the budget term** for reads within budgets. -/
lemma chPt_le (p : Params) (T : CrtTables) {q3 q5 qE : ℕ} (h3 : (q3 : ℝ) < 2 ^ 128)
    (hE : 221 * ((qE + 4607 : ℕ) : ℝ) < 2 ^ 128) (iv : Option ByteArray) {Q3 : Finset (Bytes 16)}
    {Q5 : Finset (Bytes 37)} {QE : Finset (Blk × Blk)} (b3 : Q3.card ≤ q3) (b5 : Q5.card ≤ q5)
    (bE : (QE.image Prod.fst).card ≤ qE) :
    chPt p T q3 qE iv Q3 Q5 QE ≤ q3 / (2 ^ 128 - q3) + 221 * qE / dEZK qE + q5 / 2 ^ 128 := by
  have hd := dEZK_pos hE
  have h3' : (0 : ℝ) < 2 ^ 128 - q3 := by linarith
  have cE : (cEof iv QE : ℝ) ≤ qE := by
    have : cEof iv QE ≤ qE := by
      rcases iv with _ | v
      · exact bE
      · exact (cEof_le_some v QE).trans bE
    exact_mod_cast this
  have c5 : (c5of p T iv Q5 : ℝ) ≤ q5 := by
    have : c5of p T iv Q5 ≤ q5 := by
      rcases iv with _ | v
      · exact b5
      · exact (c5of_le_some p T v Q5).trans b5
    exact_mod_cast this
  have c3 : (Q3.card : ℝ) ≤ q3 := by exact_mod_cast b3
  unfold chPt
  gcongr

/-! ## Zero knowledge with expected charges, for a proof system -/

section ZKExp

variable {I W ρ C O : Type*} [Fintype ρ] [Fintype C] {p : Params}

/-- **Zero knowledge with expected point charges** for distinguishers with a consistent table
reader within budgets `(q₃, q₅, q_E)`: the advantage is at most `ε` plus the expectation, over the
real prover's coins, the slice and the tables, of the charge `ch x o` of the reads at the real
output and tables. -/
def ZKExp (Rel : I → W → Prop) (prove : I → W → ρ → Tab3 → Sh p → O) (sim : I → C → O)
    (prog : I → C → Sh p → Sh p) (q3 q5 qE : ℕ) (ε : ℝ)
    (ch : I → O → Finset (Bytes 16) → Finset (Bytes 37) → Finset (Blk × Blk) → ℝ) : Prop :=
  ∀ x w, Rel x w → ∀ (D : O → Tab3 → Sh p → Prop) (R : ∀ o, TRd (D o)),
    (∀ o, (R o).Bnd q3 q5 qE) →
    |pr ((ρ × Tab3) × Sh p) (fun a => D (prove x w a.1.1 a.1.2 a.2) a.1.2 a.2) -
        pr ((C × Tab3) × Sh p) (fun a => D (sim x a.1.1) a.1.2 (prog x a.1.1 a.2))| ≤
      ε + exP ((ρ × Tab3) × Sh p) (fun a => ch x (prove x w a.1.1 a.1.2 a.2)
        ((R (prove x w a.1.1 a.1.2 a.2)).Q3 a.1.2 a.2) ((R (prove x w a.1.1 a.1.2 a.2)).Q5 a.1.2 a.2)
        ((R (prove x w a.1.1 a.1.2 a.2)).QE a.1.2 a.2))

end ZKExp

/-! ## The Lean prover -/

/-- **The Lean prover is `ZKExp`**: for an output map `φ` and an `iv` decoder `ivO` that never
invents an `iv` (`hiv`), with error `εZK/(1 − βZK)` and charge `chPt/(1 − βZK)`. -/
theorem lean_zkExp {I W O : Type*} (p : Params) (Hb : Hashes) (stOf : I → Statement)
    (hp : ∀ x, (stOf x).params = p) (hlr : p.labelRows = true) (enc : I → W → ByteArray)
    (Rl : I → W → Prop) (cs : I → ByteArray → ByteArray → System GF128)
    (h : ∀ x w, Rl x w → ZKHyp CrtGen.tables (stOf x) (enc x w) (cs x)) (hHb : HashesWF Hb)
    (hsp : SmallParams p) (φ : Except String ByteArray → O) (ivO : I → O → Option ByteArray)
    (hiv : ∀ x e v, ivO x (φ e) = some v → ivV Hb (stOf x) e = some v) {q3 q5 qE : ℕ}
    (h3 : (q3 : ℝ) < 2 ^ 128) (hE : 221 * ((qE + 4607 : ℕ) : ℝ) < 2 ^ 128) (hβ : βZK q5 qE < 1) :
    ZKExp Rl (fun x w ρ g (s : Sh p) => φ (realRO p Hb (stOf x) (enc x w) ρ g s))
      (fun _ c => φ (simulate p c)) (fun x c s => progRO p Hb (stOf x) c s) q3 q5 qE
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
  let R' : ∀ e, TRd (fun g s => D (φ e) g s) := fun e => R (φ e)
  have key := zk_ro_exp Hb st (enc x w) hlr hz hHb hsp (TRd.toPt R') (TRd.toPt_cons R')
    (TRd.toPt_bnd R' fun e => hR (φ e)) h3 hE hβ (fun e g s => D (φ e) g s)
    (TRd.toPt_reads (fun e g s => D (φ e) g s) R')
  refine key.trans ?_
  rw [add_div, ← exP_div]
  gcongr
  refine exP_mono fun a => ?_
  rw [chZK_toPt Hb st R' q3 qE]
  exact div_le_div_of_nonneg_right (chPt_mono_iv st.params CrtGen.tables hE (hivx _) _ _ _) hden.le

end VoleMole.ZK.Sim
