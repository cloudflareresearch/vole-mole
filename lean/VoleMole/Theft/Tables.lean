import VoleMole.Theft.LeanHb

/-!
# The theft theorems with the other hashes read off a random table

In the table model of the zero-knowledge theorems the shared tables are `H₂³`, `H₅` and the
cipher (`ShG R p`); the other hashes (`H₁`, `H₂⁰`, `H₂¹`, `H₂²`, `H₄`, `H_comb`) are a base record
`Hb`. Plain extraction needs `chal1` and `chal2` random, so those hashes must be random too. Here
the shared tables get one more uniform component `x : X` (any finite type), and the base record is
a function `Hb x` of it:

    ShX R p X = H₂³ × ((H₅ × cipher) × X).

* **`zkRO_tables`**: zero knowledge for every value of the extra table gives zero knowledge with
  the extra table uniform, shared and visible to the distinguisher (which must be admissible at
  every value of it). The proof averages (`abs_pr_prod_sub_le`): the zero-knowledge theorems are
  uniform in `Hb` (`Theft/LeanHb.lean`), so the hops lift with the same error.
* `leanPIRX`, `leanPSRX`, `leanProgIRX`, `leanProgSRX`, `leanVIRX`, `leanVSRX` (Ratatouille) and
  `leanPIX`, `leanPRX`, `leanProgIX`, `leanProgRX`, `verILX`, `verRLX` (Moussaka): the Lean prover,
  simulator programming and verifier with the base record `Hb x` read off the tables.
* `StageBudgetX`, `BudgetX`: the read budgets of `Theft/Reads.lean`, at every value of the extra
  table. They bound the reads of `H₃`, `H₅` and the cipher only: for the zero-knowledge hops the
  adversary may read the extra table freely.
* **`noTheft_leanX_plain`**, **`noRedirect_leanX_plain`**: the theft theorems in this model,

      Pr[Bad] ≤ εz(pI; q) + εz(pS or pR; q) + δ + ε_plain + ε_hit + Adv^ow(inverter),

  with the same budgets `q = (a₃ + x₃, a₅ + x₅ + 936, a_E + x_E + 9214)`. `PlainSE` and
  `ProgEv … HitOpX` are now statements about uniform `X` as well: plain extraction against an
  admissibility class `Adm₀` of the caller's choice (it may bound the reads of `X`), which must
  contain the adversary's last stage composed with both programmings (`hadm`;
  `StageBudgetX.comp_progT` for the read budgets).
* **`XTab L`**, **`hbX`**: a concrete extra table. `H₁`, `H₂⁰`, `H₂⁴`, `H₄`, `H₂¹`, `H₂²` are
  uniform tables on all inputs of at most `L` bytes (SHAKE on longer inputs); `hbX_wf`. With it,
  `noTheft_leanX_plain` and `noRedirect_leanX_plain` hold with `chal1`, `chal2`, `mu`, `iv` and the
  leaf commitments read off uniform tables.

**What remains** (see `docs/security/ratatouille.md` §5): `PlainSE` in this model from `ROM/`'s
extraction bounds, a bound on `ε_hit`, and `Adv^ow`.
-/

-- (The coin types are large products: their `Fintype` instances exceed the default size.)
set_option synthInstance.maxSize 1024

namespace VoleMole.Theft

open VoleMole.Privacy VoleMole.ZK.Sim VoleMole.Verifier VoleMole.Verifier.Bridge

/-! ## Zero knowledge with one more shared table -/

section Lift

variable {I W ρ C G S T X O : Type*} [Fintype ρ] [Fintype C] [Fintype G] [Fintype S] [Fintype T]
  [Fintype X] [Nonempty X]

/-- **Zero knowledge at every value of an extra table is zero knowledge with the extra table
uniform.** The tables `T` are the tables `S` and an extra component `X` (`e : T ≃ S × X`); the
prover and the programming may depend on the extra component, the simulator does not, and the
distinguisher sees it. -/
theorem zkRO_tables (e : T ≃ S × X) {R : I → W → Prop} (prove : X → I → W → ρ → G → S → O)
    (sim : I → C → O) (prog : X → I → C → S → S) (Adm : X → (O → G → S → Prop) → Prop) {ε : ℝ}
    (h : ∀ x, ZeroKnowledgeRO R (prove x) sim (prog x) (Adm x) ε) :
    ZeroKnowledgeRO R (fun i w r g t => prove (e t).2 i w r g (e t).1) sim
      (fun i c t => e.symm (prog (e t).2 i c (e t).1, (e t).2))
      (fun D => ∀ x, Adm x (fun o g s => D o g (e.symm (s, x)))) ε := by
  intro i w hiw D hD
  let f₁ : X × ((ρ × G) × S) ≃ (ρ × G) × T :=
    ⟨fun z => (z.2.1, e.symm (z.2.2, z.1)), fun z => ((e z.2).2, (z.1, (e z.2).1)),
      fun z => by simp, fun z => by simp⟩
  let f₂ : X × ((C × G) × S) ≃ (C × G) × T :=
    ⟨fun z => (z.2.1, e.symm (z.2.2, z.1)), fun z => ((e z.2).2, (z.1, (e z.2).1)),
      fun z => by simp, fun z => by simp⟩
  rw [← pr_equiv f₁, ← pr_equiv f₂]
  refine abs_pr_prod_sub_le _ _ fun x => ?_
  have := h x i w hiw _ (hD x)
  simpa [f₁, f₂] using this

end Lift

/-! ## The shared tables with an extra table -/

section Tables

variable {R : Type} {p : Params} {X : Type} {Y : Type*}

/-- **The shared tables with an extra table `X`**: `H₂³`, and the part no simulator programs
(`H₅`, the cipher, the extra table). -/
abbrev ShX (R : Type) (p : Params) (X : Type) := Tab2G p × ((Tab5F × (Blk → R)) × X)

/-- The tables of the zero-knowledge model. -/
def shOf (t : ShX R p X) : ShG R p := (t.1, t.2.1)

/-- The tables with the extra table `x`. -/
def atX (s : ShG R p) (x : X) : ShX R p X := (s.1, (s.2, x))

/-- `ShX R p X` is `ShG R p × X`. -/
def eX : ShX R p X ≃ ShG R p × X where
  toFun t := (shOf t, t.2.2)
  invFun z := atX z.1 z.2
  left_inv _ := rfl
  right_inv _ := rfl

/-- **The read budget of a last stage, at every value of the extra table** (which it may read
freely). -/
def StageBudgetX (F : Tab3 → Tab3 → ShX R p X → Y) (q3 q5 qE : ℕ) : Prop :=
  ∀ x, StageBudget (fun g₁ g₂ s => F g₁ g₂ (atX s x)) q3 q5 qE

/-- **The budget of a distinguisher, at every value of the extra table.** -/
def BudgetX {O : Type*} (p : Params) (q3 q5 qE : ℕ) (D : O → Tab3 → ShX R p X → Prop) : Prop :=
  ∀ x, Budget p q3 q5 qE (fun o g s => D o g (atX s x))

/-- A programming of the zero-knowledge tables that depends on the extra table, on `ShX`. -/
def progX {I C : Type*} (prog : X → I → C → ShG R p → ShG R p) (i : I) (c : C) (t : ShX R p X) :
    ShX R p X :=
  atX (prog t.2.2 i c (shOf t)) t.2.2

lemma progO_progX {I C : Type*} (prog : X → I → C → ShG R p → ShG R p) (i : Option I) (c : C)
    (s : ShG R p) (x : X) : progO (progX prog) i c (atX s x) = atX (progO (prog x) i c s) x := by
  rcases i with _ | i <;> rfl

lemma progT_progX {I₁ I₂ : Type*} {C₁ C₂ : Type} (prog₁ : X → I₁ → C₁ → ShG R p → ShG R p)
    (prog₂ : X → I₂ → C₂ → ShG R p → ShG R p) (x₁ : Option I₁) (c₁ : C₁) (x₂ : Option I₂) (c₂ : C₂)
    (s : ShG R p) (x : X) :
    progT (progX prog₁) (progX prog₂) x₁ c₁ x₂ c₂ (atX s x) =
      atX (progT (prog₁ x) (prog₂ x) x₁ c₁ x₂ c₂ s) x := by
  unfold progT
  rw [progO_progX, progO_progX]

/-- **A last stage after both programmings** reads what it reads and what the programmings
read, at every value of the extra table. -/
lemma StageBudgetX.comp_progT {I₁ I₂ : Type*} {C₁ C₂ : Type} {F : Tab3 → Tab3 → ShX R p X → Y}
    {prog₁ : X → I₁ → C₁ → ShG R p → ShG R p} {prog₂ : X → I₂ → C₂ → ShG R p → ShG R p}
    {q3 q5 qE a b a' b' : ℕ} (hF : StageBudgetX F q3 q5 qE)
    (h₁ : ∀ x i c, IsProg (prog₁ x i c) a b) (h₂ : ∀ x i c, IsProg (prog₂ x i c) a' b')
    (x₁ : Option I₁) (c₁ : C₁) (x₂ : Option I₂) (c₂ : C₂) :
    StageBudgetX (fun g₁ g₂ t => F g₁ g₂ (progT (progX prog₁) (progX prog₂) x₁ c₁ x₂ c₂ t))
      q3 (q5 + (a + a')) (qE + (b + b')) := by
  intro x
  have h := (hF x).comp_prog (isProg_progT (h₁ x) (h₂ x) x₁ c₁ x₂ c₂)
  have e : (fun g₁ g₂ s => F g₁ g₂ (progT (progX prog₁) (progX prog₂) x₁ c₁ x₂ c₂ (atX s x))) =
      fun g₁ g₂ s => F g₁ g₂ (atX (progT (prog₁ x) (prog₂ x) x₁ c₁ x₂ c₂ s) x) := by
    funext g₁ g₂ s
    rw [progT_progX]
  rw [e]
  exact h

end Tables

/-! ## A concrete extra table: the other hashes on all short inputs -/

section XTab

/-- **The inputs of at most `L` bytes.** -/
abbrev KL (L : ℕ) := (n : Fin (L + 1)) × Bytes n

/-- An input as a byte string. -/
def encL {L : ℕ} (k : KL L) : ByteArray := ba k.2

lemma encL_injective {L : ℕ} : Function.Injective (encL (L := L)) := by
  rintro ⟨n, b⟩ ⟨n', b'⟩ h
  have hn : n = n' := by
    have := congrArg ByteArray.size h
    simp only [encL, size_ba] at this
    exact Fin.ext this
  subst hn
  exact congrArg _ (ba_injective h)

/-- **The extra tables**: `H₁`, `H₂⁰` (`mu`), `H₂⁴` (`mu` for delayed binding), `H₄`, `H₂¹`,
`H₂²` and `H_comb` for `M` equations, each a table on all inputs of at most `L` bytes. -/
abbrev XTab (L M : ℕ) :=
  (KL L → Bytes 32) × (KL L → Bytes 32) × (KL L → Bytes 32) × (KL L → Bytes 16) ×
    (KL L → Bytes 136) × (KL L → Bytes 56) × (KL L → Bytes (16 * M))

/-- **The base record of an extra table**: the seven hashes read off the tables on inputs of at
most `L` bytes, SHAKE elsewhere. (`H₂³`, `H₅` and `H₃` are tables of the zero-knowledge model.) -/
noncomputable def hbX {L M : ℕ} (x : XTab L M) : Hashes :=
  ((((((Hashes.shake.withTable .h1 encL x.1).withTable .mu encL x.2.1).withTable .muDelayed encL
    x.2.2.1).withTable .h4 encL x.2.2.2.1).withTable .h21 encL x.2.2.2.2.1).withTable .h22 encL
    x.2.2.2.2.2.1).withTable (.comb M) encL x.2.2.2.2.2.2

lemma hbX_wf {L M : ℕ} (x : XTab L M) : HashesWF (hbX x) :=
  ((((((hashesWF_shake.withTable .h1 encL x.1).withTable .mu encL x.2.1).withTable .muDelayed encL
    x.2.2.1).withTable .h4 encL x.2.2.2.1).withTable .h21 encL x.2.2.2.2.1).withTable .h22 encL
    x.2.2.2.2.2.1).withTable (.comb M) encL x.2.2.2.2.2.2

/-- **`H₂²` (`chal2`) is the table**, on inputs of at most `L` bytes. -/
lemma hbX_h22 {L M : ℕ} (x : XTab L M) (k : KL L) :
    (hbX x).hash .h22 (encL k) = ba (x.2.2.2.2.2.1 k) :=
  (Hashes.withTable_ne _ (.comb M) .h22 (by simp) _ _ _).trans
    ((Hashes.withTable_enc _ .h22 encL _ k).trans (by rw [keyOf_eq encL_injective]; rfl))

/-- **`H₂¹` (`chal1`) is the table**, on inputs of at most `L` bytes. -/
lemma hbX_h21 {L M : ℕ} (x : XTab L M) (k : KL L) :
    (hbX x).hash .h21 (encL k) = ba (x.2.2.2.2.1 k) :=
  (Hashes.withTable_ne _ (.comb M) .h21 (by simp) _ _ _).trans
    ((Hashes.withTable_ne _ (.h22) .h21 (by simp) _ _ _).trans
    ((Hashes.withTable_enc _ .h21 encL _ k).trans (by rw [keyOf_eq encL_injective]; rfl)))

/-- **`H₂⁰` (`mu`) is the table**, on inputs of at most `L` bytes. -/
lemma hbX_mu {L M : ℕ} (x : XTab L M) (k : KL L) :
    (hbX x).hash .mu (encL k) = ba (x.2.1 k) :=
  (Hashes.withTable_ne _ (.comb M) .mu (by simp) _ _ _).trans
    ((Hashes.withTable_ne _ (.h22) .mu (by simp) _ _ _).trans
    ((Hashes.withTable_ne _ (.h21) .mu (by simp) _ _ _).trans
    ((Hashes.withTable_ne _ (.h4) .mu (by simp) _ _ _).trans
    ((Hashes.withTable_ne _ (.muDelayed) .mu (by simp) _ _ _).trans
    ((Hashes.withTable_enc _ .mu encL _ k).trans (by rw [keyOf_eq encL_injective]; rfl))))))

/-- **`H₁` (the leaf and commitment hash) is the table**, on inputs of at most `L` bytes. -/
lemma hbX_h1 {L M : ℕ} (x : XTab L M) (k : KL L) :
    (hbX x).hash .h1 (encL k) = ba (x.1 k) :=
  (Hashes.withTable_ne _ (.comb M) .h1 (by simp) _ _ _).trans
    ((Hashes.withTable_ne _ (.h22) .h1 (by simp) _ _ _).trans
    ((Hashes.withTable_ne _ (.h21) .h1 (by simp) _ _ _).trans
    ((Hashes.withTable_ne _ (.h4) .h1 (by simp) _ _ _).trans
    ((Hashes.withTable_ne _ (.muDelayed) .h1 (by simp) _ _ _).trans
    ((Hashes.withTable_ne _ (.mu) .h1 (by simp) _ _ _).trans
    ((Hashes.withTable_enc _ .h1 encL _ k).trans (by rw [keyOf_eq encL_injective]; rfl)))))))

end XTab

/-! ## Ratatouille -/

namespace Ratatouille

open VoleMole.Privacy.Ratatouille VoleMole.Spec.Ratatouille

section X

variable {R : Type} [CipherRow R] {X : Type} (Hb : X → Hashes)

/-- The Lean provers, the base record read off the extra table. -/
noncomputable def leanPIRX : IssueInstance → IssueWitness → Rho → Tab3 → ShX R pI X →
    Option (IssueProof Sizes.labelRows) := fun x w ρ g t => leanPIRH (Hb t.2.2) x w ρ g (shOf t)
noncomputable def leanPSRX : SpendInstance → SpendWitness → Rho → Tab3 → ShX R pI X →
    Option (SpendProof Sizes.labelRows) := fun x w ρ g t => leanPSRH (Hb t.2.2) x w ρ g (shOf t)

/-- The simulators' programmings. -/
noncomputable def leanProgIRX : IssueInstance → SimCoins pI → ShX R pI X → ShX R pI X :=
  progX fun x => leanProgIRH (Hb x)
noncomputable def leanProgSRX : SpendInstance → SimCoins pS → ShX R pI X → ShX R pI X :=
  progX fun x => leanProgSRH (Hb x)

/-- The Lean verifiers. -/
noncomputable def leanVIRX : IssueInstance → IssueProof Sizes.labelRows → ShX R pI X → Bool :=
  fun x π t => leanVIRH (Hb t.2.2) x π (shOf t)
noncomputable def leanVSRX : SpendInstance → SpendProof Sizes.labelRows → ShX R pI X → Bool :=
  fun x π t => leanVSRH (Hb t.2.2) x π (shOf t)

variable {Hb}

/-- **Zero knowledge of the Lean issuance prover with the extra table.** -/
theorem leanPIRX_zkRO [Fintype R] [ZKRow R] [Fintype X] [Nonempty X] (hHb : ∀ x, HashesWF (Hb x))
    (q3 q5 qE : ℕ) :
    ZeroKnowledgeRO IssueRel
      (fun x w (ρ : Coins 16) g (t : ShX R pI X) => leanPIRX Hb x w (vec ρ) g t) leanSimIR
      (leanProgIRX Hb) (BudgetX pI q3 q5 qE) (ZKRow.εz R pI q3 q5 qE) :=
  zkRO_tables eX (fun x i w (ρ : Coins 16) g s => leanPIRH (Hb x) i w (vec ρ) g s) leanSimIR
    (fun x => leanProgIRH (Hb x)) (fun _ => Budget pI q3 q5 qE) fun x => leanPIRH_zkRO (hHb x) _ _ _

/-- **Zero knowledge of the Lean spend prover with the extra table.** -/
theorem leanPSRX_zkRO [Fintype R] [ZKRow R] [Fintype X] [Nonempty X] (hHb : ∀ x, HashesWF (Hb x))
    (q3 q5 qE : ℕ) :
    ZeroKnowledgeRO SpendRel
      (fun x w (ρ : Coins 16) g (t : ShX R pI X) => leanPSRX Hb x w (vec ρ) g t) leanSimSR
      (leanProgSRX Hb) (BudgetX pS q3 q5 qE) (ZKRow.εz R pS q3 q5 qE) :=
  zkRO_tables eX (fun x i w (ρ : Coins 16) g s => leanPSRH (Hb x) i w (vec ρ) g s) leanSimSR
    (fun x => leanProgSRH (Hb x)) (fun _ => Budget pS q3 q5 qE) fun x => leanPSRH_zkRO (hHb x) _ _ _

variable (A : Thief Sizes.labelRows Tab3 (ShX R pI X))

/-- **The adversary at a value of the extra table.** -/
def atT (x : X) : Thief Sizes.labelRows Tab3 (ShR R) :=
  ⟨A.pk, A.ctx, A.tInit, A.respond, A.d, fun o₁ o₂ g₁ g₂ s => A.out o₁ o₂ g₁ g₂ (atX s x)⟩

/-- **An extractor from extractors at every value of the extra table**: at `x` it sees the
adversary's last stage at `x`. -/
def extX (E : X → Ext Sizes.labelRows Tab3 (ShR R)) : Ext Sizes.labelRows Tab3 (ShX R pI X) :=
  fun p₁ p₂ F g₁ g₂ t => E t.2.2 p₁ p₂ (fun g₁ g₂ s => F g₁ g₂ (atX s t.2.2)) g₁ g₂ (shOf t)

variable (E : X → Ext Sizes.labelRows Tab3 (ShR R)) {a3 a5 aE x3 x5 xE : ℕ}

/-- **The first hop's budget**, at every value of the extra table. -/
theorem distI_budgetX (hHb : ∀ x, HashesWF (Hb x))
    (hA : ∀ o₁ o₂, StageBudgetX (A.out o₁ o₂) a3 a5 aE)
    (hX : ∀ x o₁ o₂, StageBudget (E x (stI (atT A x) o₁) (stS (atT A x) o₂) ((atT A x).out o₁ o₂))
      x3 x5 xE) (ω : Sec) (r₂ : Coins 16) (g₂ : Tab3) :
    BudgetX pI (a3 + x3) (a5 + x5 + 936) (aE + xE + 9214)
      (distI A (leanPIRX Hb) (leanPSRX Hb) (leanVIRX Hb) (leanVSRX Hb) (extX E) ω r₂ g₂) :=
  fun x => distI_budgetLH (Hb := Hb x) (atT A x) (E x) (hHb x) (fun o₁ o₂ => hA o₁ o₂ x) (hX x)
    ω r₂ g₂

variable (Hb) in
/-- **The second hop's budget**, at every value of the extra table. -/
theorem distS_budgetX (hA : ∀ o₁ o₂, StageBudgetX (A.out o₁ o₂) a3 a5 aE)
    (hX : ∀ x o₁ o₂, StageBudget (E x (stI (atT A x) o₁) (stS (atT A x) o₂) ((atT A x).out o₁ o₂))
      x3 x5 xE) (ω : Sec) (c₁ : SimCoins pI) (g₁ : Tab3) :
    BudgetX pS (a3 + x3) (a5 + x5 + 936) (aE + xE + 9214)
      (distS A (leanVIRX Hb) (leanVSRX Hb) (extX E) leanSimIR (leanProgIRX Hb) ω c₁ g₁) :=
  fun x => by
    have h := distS_budgetLH (Hb x) (atT A x) (E x) (fun o₁ o₂ => hA o₁ o₂ x) (hX x) ω c₁ g₁
    have e : (fun o g s => distS A (leanVIRX Hb) (leanVSRX Hb) (extX E) leanSimIR (leanProgIRX Hb)
        ω c₁ g₁ o g (atX s x)) = distS (atT A x) (leanVIRH (Hb x)) (leanVSRH (Hb x)) (E x)
          leanSimIR (leanProgIRH (Hb x)) ω c₁ g₁ := by
      funext o g s
      simp only [distS, D₂, pgI, leanProgIRX, progO_progX]
      rfl
    -- (`pI` and `pS` have the same `H₂³` table type)
    exact Eq.mpr (congrArg (fun D => Budget pS (a3 + x3) (a5 + x5 + 936) (aE + xE + 9214) D) e) h

/-- **The verifier's `H₂³` point of an operation is a programmed point**, the base record read
off the extra table. -/
def HitOpX (op : Op Sizes.labelRows) (t' t : ShX R pI X) : Prop :=
  HitOpH (Hb t.2.2) (atT A t.2.2) op (shOf t') (shOf t)

variable (Hb) in
/-- **The programming moves the Lean verifiers only at their `H₂³` point.** -/
theorem accOp_movesX (op : Op Sizes.labelRows) (t' t : ShX R pI X) (h2 : t'.2 = t.2)
    (h' : AccOp A (leanVIRX Hb) (leanVSRX Hb) op t')
    (h : ¬ AccOp A (leanVIRX Hb) (leanVSRX Hb) op t) : HitOpX (Hb := Hb) A op t' t := by
  obtain ⟨a', b'⟩ := t'
  obtain ⟨a, b⟩ := t
  simp only at h2
  subst h2
  exact accOp_movesH (Hb b'.2) (atT A b'.2) op (a', b'.1) (a, b'.1) rfl h' h

variable [Fintype R] [Nonempty R] [ZKRow R] [Fintype X] [Nonempty X]

/-- **No theft with the extra table, the hops' budgets proved** (as `noTheft_lean_reads`). The
extractor is a family `E x` of extractors of the zero-knowledge model. -/
theorem noTheft_leanX_reads (hHb : ∀ x, HashesWF (Hb x))
    {AdmE : (Tab3 → Tab3 → ShX R pI X → Op Sizes.labelRows) → Prop} {εSE : ℝ}
    (hA : ∀ o₁ o₂, StageBudgetX (A.out o₁ o₂) a3 a5 aE)
    (hX : ∀ x o₁ o₂, StageBudget (E x (stI (atT A x) o₁) (stS (atT A x) o₂) ((atT A x).out o₁ o₂))
      x3 x5 xE)
    (hse : WeakSE2 leanSimIR (leanProgIRX Hb) leanSimSR (leanProgSRX Hb)
      (AccOp A (leanVIRX Hb) (leanVSRX Hb)) (FreshOp A) (RelOp A) (extX E) AdmE εSE)
    (hAE : ∀ o₁ o₂, AdmE (A.out o₁ o₂)) :
    pr _ (theftReal A (leanPIRX Hb) (leanPSRX Hb) (leanVIRX Hb) (leanVSRX Hb) (extX E)) ≤
      ZKRow.εz R pI (a3 + x3) (a5 + x5 + 936) (aE + xE + 9214) +
        ZKRow.εz R pS (a3 + x3) (a5 + x5 + 936) (aE + xE + 9214) +
        pr _ (deltaS A (leanPIRX Hb) (leanPSRX Hb) leanSimIR (leanProgIRX Hb)) + εSE +
        owAdv A.ctx (inverter A (extX E) leanSimIR (leanProgIRX Hb) leanSimSR (leanProgSRX Hb)) :=
  noTheft (CI := SimCoins pI) (CS := SimCoins pS) A (leanPIRX Hb) (leanPSRX Hb) (leanVIRX Hb)
    (leanVSRX Hb) (extX E) leanSimIR (leanProgIRX Hb) leanSimSR (leanProgSRX Hb)
    (leanPIRX_zkRO hHb _ _ _) (ZKRow.εz_nonneg _ _ _ _) (leanPSRX_zkRO hHb _ _ _)
    (ZKRow.εz_nonneg _ _ _ _) (distI_budgetX A E hHb hA hX) (distS_budgetX Hb A E hA hX) hse hAE

/-- **No theft with the other hashes read off a uniform table, with plain extraction.** The
shared tables are `H₂³`, `H₅`, the cipher and an extra table `x : X`; the prover, the verifiers
and the simulators' programming use the base record `Hb x`. For an adversary whose last stage
reads `(a₃, a₅, a_E)` at every `x` and an extractor `extOf e` (it sees the output, the slices,
`H₅`, the cipher and `x`, not `H₂³`) that reads `(x₃, x₅, x_E)`:

    Pr[Bad] ≤ εz(pI; q) + εz(pS; q) + δ_S + ε_plain + ε_hit + Adv^ow(inverter),

`q = (a₃ + x₃, a₅ + x₅ + 936, a_E + x_E + 9214)`. Plain extraction (`hplain`) is against a class
`Adm₀` that contains the last stage composed with both programmings (`hadm`), and `ε_hit`
(`hhit`) against a class `Adm` that contains the last stage (`hAdm`). -/
theorem noTheft_leanX_plain (hHb : ∀ x, HashesWF (Hb x))
    {e : Option (IssueInstance × IssueProof Sizes.labelRows) →
      Option (SpendInstance × SpendProof Sizes.labelRows) → Op Sizes.labelRows → Tab3 → Tab3 →
      (Tab5F × (Blk → R)) × X → Wit}
    {Adm Adm₀ : (Tab3 → Tab3 → ShX R pI X → Op Sizes.labelRows) → Prop} {ε₀ εh : ℝ}
    (hA : ∀ o₁ o₂, StageBudgetX (A.out o₁ o₂) a3 a5 aE)
    (hX : ∀ o₁ o₂, StageBudgetX (extOf e (stI A o₁) (stS A o₂) (A.out o₁ o₂)) x3 x5 xE)
    (hplain : PlainSE (AccOp A (leanVIRX Hb) (leanVSRX Hb)) (FreshOp A) (RelOp A) e Adm₀ ε₀)
    (hhit : ProgEv leanSimIR (leanProgIRX Hb) leanSimSR (leanProgSRX Hb) (FreshOp A)
      (HitOpX (Hb := Hb) A) Adm εh)
    (hAdm : ∀ o₁ o₂, Adm (A.out o₁ o₂))
    (hadm : ∀ F x₁ c₁ x₂ c₂, Adm F → Adm₀ (fun g₁ g₂ t =>
      F g₁ g₂ (progT (leanProgIRX Hb) (leanProgSRX Hb) x₁ c₁ x₂ c₂ t))) :
    pr _ (theftReal A (leanPIRX Hb) (leanPSRX Hb) (leanVIRX Hb) (leanVSRX Hb) (extOf e)) ≤
      ZKRow.εz R pI (a3 + x3) (a5 + x5 + 936) (aE + xE + 9214) +
        ZKRow.εz R pS (a3 + x3) (a5 + x5 + 936) (aE + xE + 9214) +
        pr _ (deltaS A (leanPIRX Hb) (leanPSRX Hb) leanSimIR (leanProgIRX Hb)) + (ε₀ + εh) +
        owAdv A.ctx (inverter A (extOf e) leanSimIR (leanProgIRX Hb) leanSimSR
          (leanProgSRX Hb)) :=
  noTheft_leanX_reads A
    (fun x => extOf fun p₁ p₂ o g₁ g₂ b => e p₁ p₂ o g₁ g₂ (b, x)) hHb hA
    (fun x o₁ o₂ => hX o₁ o₂ x)
    (weakSE2_of_plain hplain
      (progMoves_of_ev (fun _ _ _ => rfl) (fun _ _ _ => rfl) (accOp_movesX Hb A) hhit)
      (fun _ _ _ => rfl) (fun _ _ _ => rfl) hadm) hAdm

end X

end Ratatouille

/-! ## Moussaka -/

namespace Moussaka

open VoleMole.Privacy.Moussaka VoleMole.Spec VoleMole.Spec.Moussaka

section X

variable {R : Type} [CipherRow R] {X : Type} (Hb : X → Hashes)

/-- The Lean provers, the base record read off the extra table. -/
noncomputable def leanPIX : Bytes → IssueInstance → Bytes → Tab3 → ShX R pI X → Bytes :=
  fun w x rho g t => leanPIH (Hb t.2.2) w x rho g (shOf t)
noncomputable def leanPRX : Bytes → RedeemInstance → Bytes → Tab3 → ShX R pI X → Bytes :=
  fun w x rho g t => leanPRH (Hb t.2.2) w x rho g (shOf t)

/-- The simulators' programmings. -/
noncomputable def leanProgIX : IssueInstance → SimCoins pI → ShX R pI X → ShX R pI X :=
  progX fun x => leanProgIH (Hb x)
noncomputable def leanProgRX : RedeemInstance → SimCoins pR → ShX R pI X → ShX R pI X :=
  progX fun x => leanProgRH (Hb x)

/-- The Lean verifiers. -/
noncomputable def verILX : IssueInstance → Bytes → ShX R pI X → Bool :=
  fun x pf t => verILH (Hb t.2.2) x pf (shOf t)
noncomputable def verRLX : RedeemInstance → Bytes → ShX R pI X → Bool :=
  fun x pf t => verRLH (Hb t.2.2) x pf (shOf t)

variable {Hb}

/-- **Zero knowledge of the Lean issuance prover with the extra table.** -/
theorem leanPIX_zkRO [Fintype R] [ZKRow R] [Fintype X] [Nonempty X] (hHb : ∀ x, HashesWF (Hb x))
    (q3 q5 qE : ℕ) :
    ZeroKnowledgeRO IssueRelW
      (fun x w (ρ : Coins proveSeedBytes) g (t : ShX R pI X) => leanPIX Hb w x (List.ofFn ρ) g t)
      (leanSim pI) (leanProgIX Hb) (BudgetX pI q3 q5 qE) (ZKRow.εz R pI q3 q5 qE) :=
  zkRO_tables eX (fun x i w (ρ : Coins proveSeedBytes) g s => leanPIH (Hb x) w i (List.ofFn ρ) g s)
    (leanSim pI) (fun x => leanProgIH (Hb x)) (fun _ => Budget pI q3 q5 qE)
    fun x => leanPIH_zkRO (hHb x) _ _ _

/-- **Zero knowledge of the Lean redemption prover with the extra table.** -/
theorem leanPRX_zkRO [Fintype R] [ZKRow R] [Fintype X] [Nonempty X] (hHb : ∀ x, HashesWF (Hb x))
    (q3 q5 qE : ℕ) :
    ZeroKnowledgeRO RedeemRelW
      (fun x w (ρ : Coins proveSeedBytes) g (t : ShX R pI X) => leanPRX Hb w x (List.ofFn ρ) g t)
      (leanSim pR) (leanProgRX Hb) (BudgetX pR q3 q5 qE) (ZKRow.εz R pR q3 q5 qE) :=
  zkRO_tables eX (fun x i w (ρ : Coins proveSeedBytes) g s => leanPRH (Hb x) w i (List.ofFn ρ) g s)
    (leanSim pR) (fun x => leanProgRH (Hb x)) (fun _ => Budget pR q3 q5 qE)
    fun x => leanPRH_zkRO (hHb x) _ _ _

variable (A : Thief Tab3 (ShX R pI X))

/-- **The adversary at a value of the extra table.** -/
def atT (x : X) : Thief Tab3 (ShM R) :=
  ⟨A.ctxIss, A.ctxRed, A.pk, A.respond, A.choose, fun o₁ o₂ g₁ g₂ s => A.out o₁ o₂ g₁ g₂ (atX s x)⟩

/-- **An extractor from extractors at every value of the extra table.** -/
def extX (E : X → Moussaka.Ext Tab3 (ShM R)) : Moussaka.Ext Tab3 (ShX R pI X) :=
  fun p₁ p₂ F g₁ g₂ t => E t.2.2 p₁ p₂ (fun g₁ g₂ s => F g₁ g₂ (atX s t.2.2)) g₁ g₂ (shOf t)

variable (E : X → Moussaka.Ext Tab3 (ShM R)) {a3 a5 aE x3 x5 xE : ℕ}

omit [CipherRow R] in
lemma tOf_atT (x : X) (ω : Sec) : tOf (atT A x) ω = tOf A ω := rfl

lemma specR_atT (x : X) (ω : Sec) (req : Bytes) (ρ : Coins proveSeedBytes) (g : Tab3)
    (s : ShM R) :
    specR A (leanPRX Hb) ω req ρ g (atX s x) = specR (atT A x) (leanPRH (Hb x)) ω req ρ g s := by
  have ht : tokS (atT A x) ω req = tokS A ω req := by
    unfold tokS sig
    rfl
  have hn : nizkG (leanPRX Hb) g (atX s x) = nizkG (leanPRH (Hb x)) g s := rfl
  unfold specR
  rw [ht, hn]
  cases tokS A ω req <;> rfl

lemma accOp_atX (op : MOp) (x : X) (s : ShM R) :
    AccOp (verILX Hb) (verRLX Hb) op (atX s x) = AccOp (verILH (Hb x)) (verRLH (Hb x)) op s := by
  cases op <;> rfl

lemma bad_atT (x : X) (ω : Sec) (o₁ : Bytes) (o₂ : Except Error Bytes) (g₁ g₂ : Tab3)
    (s : ShM R) :
    Bad A (verILX Hb) (verRLX Hb) (extX E) ω o₁ o₂ g₁ g₂ (atX s x) =
      Bad (atT A x) (verILH (Hb x)) (verRLH (Hb x)) (E x) ω o₁ o₂ g₁ g₂ s := by
  simp only [Bad, accE, freshE, relE, opensE, accOp_atX]
  rfl

/-- **The first hop's budget**, at every value of the extra table. -/
theorem distI_budgetX (hHb : ∀ x, HashesWF (Hb x))
    (hA : ∀ o₁ o₂, StageBudgetX (A.out o₁ o₂) a3 a5 aE)
    (hX : ∀ x o₁ o₂, StageBudget (E x (stI (atT A x) o₁) (stR (atT A x) o₁ o₂)
      ((atT A x).out o₁ o₂)) x3 x5 xE) (ω : Sec) (r₂ : Coins proveSeedBytes) (g₂ : Tab3) :
    BudgetX pI (a3 + x3) (a5 + x5 + 936) (aE + xE + 9214)
      (distI A (leanPRX Hb) (verILX Hb) (verRLX Hb) (extX E) ω r₂ g₂) :=
  fun x => by
    have h := distI_budgetLH (Hb := Hb x) (atT A x) (E x) (hHb x) (fun o₁ o₂ => hA o₁ o₂ x) (hX x)
      ω r₂ g₂
    have e : (fun o g s => distI A (leanPRX Hb) (verILX Hb) (verRLX Hb) (extX E) ω r₂ g₂ o g
        (atX s x)) = distI (atT A x) (leanPRH (Hb x)) (verILH (Hb x)) (verRLH (Hb x)) (E x)
          ω r₂ g₂ := by
      funext o g s
      simp only [distI, D₁, specR_atT, bad_atT, tOf_atT]
    rw [e]
    exact h

variable (Hb) in
/-- **The second hop's budget**, at every value of the extra table. -/
theorem distR_budgetX (hA : ∀ o₁ o₂, StageBudgetX (A.out o₁ o₂) a3 a5 aE)
    (hX : ∀ x o₁ o₂, StageBudget (E x (stI (atT A x) o₁) (stR (atT A x) o₁ o₂)
      ((atT A x).out o₁ o₂)) x3 x5 xE) (ω : Sec) (c₁ : SimCoins pI) (g₁ : Tab3) :
    BudgetX pR (a3 + x3) (a5 + x5 + 936) (aE + xE + 9214)
      (distR A (verILX Hb) (verRLX Hb) (extX E) (leanSim pI) (leanProgIX Hb) ω c₁ g₁) :=
  fun x => by
    have h := distR_budgetLH (Hb x) (atT A x) (E x) (fun o₁ o₂ => hA o₁ o₂ x) (hX x) ω c₁ g₁
    have e : (fun o g s => distR A (verILX Hb) (verRLX Hb) (extX E) (leanSim pI) (leanProgIX Hb)
        ω c₁ g₁ o g (atX s x)) = distR (atT A x) (verILH (Hb x)) (verRLH (Hb x)) (E x)
          (leanSim pI) (leanProgIH (Hb x)) ω c₁ g₁ := by
      funext o g s
      simp only [distR, D₂, pgIP, leanProgIX, progO_progX, bad_atT, tOf_atT]
      rfl
    -- (`pI` and `pR` have the same `H₂³` table type)
    exact Eq.mpr (congrArg (fun D => Budget pR (a3 + x3) (a5 + x5 + 936) (aE + xE + 9214) D) e) h

/-- **The verifier's `H₂³` point of an operation is a programmed point**, the base record read
off the extra table. -/
def HitOpX (op : MOp) (t' t : ShX R pI X) : Prop :=
  HitOpH (Hb t.2.2) op (shOf t') (shOf t)

variable (Hb) in
/-- **The programming moves the Lean verifiers only at their `H₂³` point.** -/
theorem accOp_movesX (op : MOp) (t' t : ShX R pI X) (h2 : t'.2 = t.2)
    (h' : AccOp (verILX Hb) (verRLX Hb) op t') (h : ¬ AccOp (verILX Hb) (verRLX Hb) op t) :
    HitOpX (Hb := Hb) op t' t := by
  obtain ⟨a', b'⟩ := t'
  obtain ⟨a, b⟩ := t
  simp only at h2
  subst h2
  exact accOp_movesH (Hb b'.2) op (a', b'.1) (a, b'.1) rfl h' h

variable [Fintype R] [Nonempty R] [ZKRow R] [Fintype X] [Nonempty X]

/-- **Redemption non-malleability with the extra table, the hops' budgets proved** (as
`noRedirect_lean_reads`). -/
theorem noRedirect_leanX_reads (hHb : ∀ x, HashesWF (Hb x))
    {AdmE : (Tab3 → Tab3 → ShX R pI X → MOp) → Prop} {εSE : ℝ}
    (hA : ∀ o₁ o₂, StageBudgetX (A.out o₁ o₂) a3 a5 aE)
    (hX : ∀ x o₁ o₂, StageBudget (E x (stI (atT A x) o₁) (stR (atT A x) o₁ o₂)
      ((atT A x).out o₁ o₂)) x3 x5 xE)
    (hse : WeakSE2 (simI' (leanSim pI)) (leanProgIX Hb) (simR' (leanSim pR)) (leanProgRX Hb)
      (AccOp (verILX Hb) (verRLX Hb)) FreshOp RelOp (extX E) AdmE εSE)
    (hAE : ∀ o₁ o₂, AdmE (A.out o₁ o₂)) :
    pr _ (nmReal A (leanPIX Hb) (leanPRX Hb) (verILX Hb) (verRLX Hb) (extX E)) ≤
      ZKRow.εz R pI (a3 + x3) (a5 + x5 + 936) (aE + xE + 9214) +
        ZKRow.εz R pR (a3 + x3) (a5 + x5 + 936) (aE + xE + 9214) +
        pr _ (deltaR A (leanPRX Hb) (leanSim pI) (leanProgIX Hb)) + εSE +
        owAdv A.ci A.cr (inverter A (extX E) (leanSim pI) (leanProgIX Hb) (leanSim pR)
          (leanProgRX Hb)) :=
  noRedirect (CI := SimCoins pI) (CR := SimCoins pR) A (leanPIX Hb) (leanPRX Hb) (verILX Hb)
    (verRLX Hb) (extX E) (leanSim pI) (leanProgIX Hb) (leanSim pR) (leanProgRX Hb)
    (leanPIX_zkRO hHb _ _ _) (ZKRow.εz_nonneg _ _ _ _) (leanPRX_zkRO hHb _ _ _)
    (ZKRow.εz_nonneg _ _ _ _) (distI_budgetX A E hHb hA hX) (distR_budgetX Hb A E hA hX) hse hAE

/-- **Redemption non-malleability with the other hashes read off a uniform table, with plain
extraction** (as `noTheft_leanX_plain`):

    Pr[Bad] ≤ εz(pI; q) + εz(pR; q) + δ_R + ε_plain + ε_hit + Adv^ow(inverter),

`q = (a₃ + x₃, a₅ + x₅ + 936, a_E + x_E + 9214)`. -/
theorem noRedirect_leanX_plain (hHb : ∀ x, HashesWF (Hb x))
    {e : Option (IssueInstance × Bytes) → Option (RedeemInstance × Bytes) → MOp → Tab3 → Tab3 →
      (Tab5F × (Blk → R)) × X → Bytes}
    {Adm Adm₀ : (Tab3 → Tab3 → ShX R pI X → MOp) → Prop} {ε₀ εh : ℝ}
    (hA : ∀ o₁ o₂, StageBudgetX (A.out o₁ o₂) a3 a5 aE)
    (hX : ∀ o₁ o₂, StageBudgetX (extOf e (stI A o₁) (stR A o₁ o₂) (A.out o₁ o₂)) x3 x5 xE)
    (hplain : PlainSE (AccOp (verILX Hb) (verRLX Hb)) FreshOp RelOp e Adm₀ ε₀)
    (hhit : ProgEv (simI' (leanSim pI)) (leanProgIX Hb) (simR' (leanSim pR)) (leanProgRX Hb)
      FreshOp (HitOpX (R := R) (Hb := Hb)) Adm εh)
    (hAdm : ∀ o₁ o₂, Adm (A.out o₁ o₂))
    (hadm : ∀ F x₁ c₁ x₂ c₂, Adm F → Adm₀ (fun g₁ g₂ t =>
      F g₁ g₂ (progT (leanProgIX Hb) (leanProgRX Hb) x₁ c₁ x₂ c₂ t))) :
    pr _ (nmReal A (leanPIX Hb) (leanPRX Hb) (verILX Hb) (verRLX Hb) (extOf e)) ≤
      ZKRow.εz R pI (a3 + x3) (a5 + x5 + 936) (aE + xE + 9214) +
        ZKRow.εz R pR (a3 + x3) (a5 + x5 + 936) (aE + xE + 9214) +
        pr _ (deltaR A (leanPRX Hb) (leanSim pI) (leanProgIX Hb)) + (ε₀ + εh) +
        owAdv A.ci A.cr (inverter A (extOf e) (leanSim pI) (leanProgIX Hb) (leanSim pR)
          (leanProgRX Hb)) :=
  noRedirect_leanX_reads A
    (fun x => extOf fun p₁ p₂ o g₁ g₂ b => e p₁ p₂ o g₁ g₂ (b, x)) hHb hA
    (fun x o₁ o₂ => hX o₁ o₂ x)
    (weakSE2_of_plain hplain
      (progMoves_of_ev (fun _ _ _ => rfl) (fun _ _ _ => rfl) (accOp_movesX (R := R) Hb) hhit)
      (fun _ _ _ => rfl) (fun _ _ _ => rfl) hadm) hAdm

end X

end Moussaka

end VoleMole.Theft
