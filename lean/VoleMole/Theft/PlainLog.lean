import VoleMole.Theft.HitTheft
import VoleMole.ROM.TableReads

/-!
# Plain extraction with the adversary's query log, and the programming step for it

`PlainSE` (`Theft/SimExtract.lean`) is plain extraction against a last stage that is a *function*
of the tables, with read budgets that are certificate sizes, and an extractor `extOf e` that sees
the output, the slices and the unprogrammed tables, but not the adversary's queries. `ROM/`'s
extraction bounds are of another shape: the prover is an oracle computation with query bounds,
and the straight-line extractor reads the prover's query log (its cipher-query log finds the leaf
keys). An adversary that derives its GGM root key from an `H₂³` answer is extractable from its
log but not by `extOf e` (`docs/security/ratatouille.md` §5). Here plain extraction and the
programming step of L8 are restated for that shape, for any oracle (`spec`) whose answers are read
off the tables (`ans g₁ g₂ s`):

* **`PlainSEL`**: plain extraction against last stages that are oracle computations `oa a` (in a
  class `Bud`, for instance query bounds) run on the tables (`runT`); the extractor `e` sees the
  honest pairs, the output, **the list of the queries of the run** (`qlog`), the slices and the
  unprogrammed tables `s.2`.
* **`AdmL Bud ans`**: the last stages (functions of the tables) that are the run of an oracle
  computation in `Bud`.
* **`simP`**: an oracle computation with its answers patched (`runT_simP`, `qlog_simP`: the run
  with patched answers, the same queries). The reduction of the programming step answers the
  simulators' programmed points itself: it computes the patches by queries to the unprogrammed
  tables (`progQ`, whose query list depends on the coins only through the simulated proof,
  `logQ`), then runs the adversary with patched answers (`redQ`).
* **`extL`**: the extractor of the simulation-extractability game: `e` on the query list the
  reduction makes (the patches' queries, then the queries of a realization of the adversary's last
  stage), which it computes from the honest pairs and the programmed tables.
* **`weakSE2_of_plainL`**: `WeakSE2 ≤ ε_plain + ε_moves`, as `weakSE2_of_plain`, with `PlainSEL`
  for the class `Bud₀` of the reductions (`hadm`).

The extractor of `PlainSEL` sees the list of queries, not their answers: the answers of the
unprogrammed tables it can read itself, and the `H₂³` answers differ between the two worlds at the
programmed points. `ROM/`'s extractor reads the cipher-query log only (`proverIC`: `keysOf`,
`knownOf` of `cipherLog`), whose answers are cipher cells.
-/

-- (The coin types are large products: their `Fintype` instances exceed the default size.)
set_option synthInstance.maxSize 1024

open OracleComp OracleSpec

namespace VoleMole.Theft

open VoleMole.Privacy VoleMole.ROM.Reads

/-! ## Runs on fixed answers -/

section Run

variable {ι : Type} {spec : OracleSpec.{0, 0} ι} {α β : Type}

@[simp] lemma runT_pure (f : (k : ι) → spec k) (x : α) :
    runT f (pure x : OracleComp spec α) = x := rfl

@[simp] lemma qlog_pure (f : (k : ι) → spec k) (x : α) :
    qlog f (pure x : OracleComp spec α) = [] := rfl

lemma runT_query_bind (f : (k : ι) → spec k) (t : ι) (k : spec t → OracleComp spec α) :
    runT f (liftM (spec.query t) >>= k) = runT f (k (f t)) := rfl

lemma qlog_query_bind (f : (k : ι) → spec k) (t : ι) (k : spec t → OracleComp spec α) :
    qlog f (liftM (spec.query t) >>= k) = t :: qlog f (k (f t)) := rfl

@[simp] lemma runT_query (f : (k : ι) → spec k) (t : ι) :
    runT f (liftM (spec.query t) : OracleComp spec (spec t)) = f t := rfl

@[simp] lemma qlog_query (f : (k : ι) → spec k) (t : ι) :
    qlog f (liftM (spec.query t) : OracleComp spec (spec t)) = [t] := rfl

lemma runT_bind (f : (k : ι) → spec k) (oa : OracleComp spec α) (ob : α → OracleComp spec β) :
    runT f (oa >>= ob) = runT f (ob (runT f oa)) := by
  induction oa with
  | pure x => rfl
  | queryBind t k ih => exact ih (f t)

lemma qlog_bind (f : (k : ι) → spec k) (oa : OracleComp spec α) (ob : α → OracleComp spec β) :
    qlog f (oa >>= ob) = qlog f oa ++ qlog f (ob (runT f oa)) := by
  induction oa with
  | pure x => rfl
  | queryBind t k ih =>
    show t :: qlog f (k (f t) >>= ob) = (t :: qlog f (k (f t))) ++ _
    rw [ih (f t)]
    rfl

lemma runT_map (f : (k : ι) → spec k) (g : α → β) (oa : OracleComp spec α) :
    runT f (g <$> oa) = g (runT f oa) := by
  rw [map_eq_bind_pure_comp, runT_bind]
  rfl

lemma qlog_map (f : (k : ι) → spec k) (g : α → β) (oa : OracleComp spec α) :
    qlog f (g <$> oa) = qlog f oa := by
  rw [map_eq_bind_pure_comp, qlog_bind]
  simp

/-- **An oracle computation with patched answers**: each answer `u` to a query `t` is replaced by
`pt t u` (the queries are made as before). -/
def simP (pt : (i : ι) → spec i → spec i) : OracleComp spec α → OracleComp spec α
  | .pure x => pure x
  | .queryBind t k => liftM (spec.query t) >>= fun u => simP pt (k (pt t u))

/-- **The run with patched answers** is the run on the patched answers. -/
theorem runT_simP (pt : (i : ι) → spec i → spec i) (f : (k : ι) → spec k)
    (oa : OracleComp spec α) : runT f (simP pt oa) = runT (fun i => pt i (f i)) oa := by
  induction oa with
  | pure x => rfl
  | queryBind t k ih => exact ih (pt t (f t))

/-- **The queries with patched answers** are the queries on the patched answers. -/
theorem qlog_simP (pt : (i : ι) → spec i → spec i) (f : (k : ι) → spec k)
    (oa : OracleComp spec α) : qlog f (simP pt oa) = qlog (fun i => pt i (f i)) oa := by
  induction oa with
  | pure x => rfl
  | queryBind t k ih =>
    show t :: qlog f (simP pt (k (pt t (f t)))) = t :: qlog _ (k (pt t (f t)))
    rw [ih]

/-- Patching answers keeps every query bound (the queries are the same). -/
theorem isQueryBound_simP {B : Type} (pt : (i : ι) → spec i → spec i) {oa : OracleComp spec α}
    {b : B} {canQuery : ι → B → Prop} {cost : ι → B → B}
    (h : IsQueryBound oa b canQuery cost) : IsQueryBound (simP pt oa) b canQuery cost := by
  induction oa generalizing b with
  | pure x => trivial
  | queryBind t k ih =>
    have h' := (isQueryBound_query_bind_iff t k b canQuery cost).1 h
    exact (isQueryBound_query_bind_iff t _ b canQuery cost).2
      ⟨h'.1, fun u => ih (pt t u) (h'.2 (pt t u))⟩

theorem isQueryBoundP_simP (pt : (i : ι) → spec i → spec i) {oa : OracleComp spec α}
    {p : ι → Prop} [DecidablePred p] {n : ℕ} (h : IsQueryBoundP oa p n) :
    IsQueryBoundP (simP pt oa) p n :=
  isQueryBound_simP pt h

end Run

/-! ## Plain extraction against oracle computations -/

section Plain

variable {ι : Type} {spec : OracleSpec.{0, 0} ι} {I₁ I₂ P₁ P₂ G A B Out W : Type}

/-- **The last stages that are oracle computations in `Bud`**: `F` is the run of some `oa` with
`Bud oa`, on the answers `ans g₁ g₂ s` of the slices and the tables. -/
def AdmL (Bud : OracleComp spec Out → Prop) (ans : G → G → A × B → (i : ι) → spec i)
    (F : G → G → A × B → Out) : Prop :=
  ∃ oa : OracleComp spec Out, Bud oa ∧ F = fun g₁ g₂ s => runT (ans g₁ g₂ s) oa

variable [Fintype G] [Fintype A] [Fintype B]

/-- **Plain extraction with the query list**, with error `ε`, against the oracle computations
`Bud` admits. The adversary has advice `a`, honest pairs `p₁ a`, `p₂ a` that define freshness
(any values, not read off the tables) and a last stage `oa a`, run on uniform slices and tables
(answers `ans`). The extractor `e` sees the pairs, the output, the list of the run's queries, the
slices and `s.2`. -/
def PlainSEL (ans : G → G → A × B → (i : ι) → spec i) (Acc : Out → A × B → Prop)
    (Fresh : Option (I₁ × P₁) → Option (I₂ × P₂) → Out → Prop) (Rel : Out → W → Prop)
    (e : Option (I₁ × P₁) → Option (I₂ × P₂) → Out → List ι → G → G → B → W)
    (Bud : OracleComp spec Out → Prop) (ε : ℝ) : Prop :=
  ∀ (α : Type) [Fintype α] [Nonempty α] (p₁ : α → Option (I₁ × P₁)) (p₂ : α → Option (I₂ × P₂))
    (oa : α → OracleComp spec Out), (∀ a, Bud (oa a)) →
    pr (α × ((G × G) × (A × B))) (fun z =>
      Acc (runT (ans z.2.1.1 z.2.1.2 z.2.2) (oa z.1)) z.2.2 ∧
        Fresh (p₁ z.1) (p₂ z.1) (runT (ans z.2.1.1 z.2.1.2 z.2.2) (oa z.1)) ∧
        ¬ Rel (runT (ans z.2.1.1 z.2.1.2 z.2.2) (oa z.1))
          (e (p₁ z.1) (p₂ z.1) (runT (ans z.2.1.1 z.2.1.2 z.2.2) (oa z.1))
            (qlog (ans z.2.1.1 z.2.1.2 z.2.2) (oa z.1)) z.2.1.1 z.2.1.2 z.2.2.2)) ≤ ε

/-- **Non-vacuity**: plain extraction holds with error `1`. -/
theorem plainSEL_one (ans : G → G → A × B → (i : ι) → spec i) (Acc : Out → A × B → Prop)
    (Fresh : Option (I₁ × P₁) → Option (I₂ × P₂) → Out → Prop) (Rel : Out → W → Prop)
    (e : Option (I₁ × P₁) → Option (I₂ × P₂) → Out → List ι → G → G → B → W)
    (Bud : OracleComp spec Out → Prop) : PlainSEL ans Acc Fresh Rel e Bud 1 :=
  fun _ _ _ _ _ _ _ => pr_le_one _

lemma PlainSEL.mono {ans : G → G → A × B → (i : ι) → spec i} {Acc : Out → A × B → Prop}
    {Fresh Fresh' : Option (I₁ × P₁) → Option (I₂ × P₂) → Out → Prop} {Rel : Out → W → Prop}
    {e : Option (I₁ × P₁) → Option (I₂ × P₂) → Out → List ι → G → G → B → W}
    {Bud Bud' : OracleComp spec Out → Prop} {ε ε' : ℝ} (h : PlainSEL ans Acc Fresh Rel e Bud ε)
    (hF : ∀ p₁ p₂ o, Fresh' p₁ p₂ o → Fresh p₁ p₂ o) (hB : ∀ oa, Bud' oa → Bud oa)
    (hε : ε ≤ ε') : PlainSEL ans Acc Fresh' Rel e Bud' ε' :=
  fun α _ _ p₁ p₂ oa hoa => ((Privacy.pr_mono fun _ hz => ⟨hz.1, hF _ _ _ hz.2.1, hz.2.2⟩).trans
    (h α p₁ p₂ oa fun a => hB _ (hoa a))).trans hε

end Plain

/-! ## The programming step -/

section Step

variable {ι : Type} {spec : OracleSpec.{0, 0} ι} {I₁ I₂ P₁ P₂ G A B Out W M₁ M₂ : Type}
  {C₁ C₂ : Type}

/-- The patch of an optional statement (none: no patch). -/
def progQO {I C M : Type} (progQ : I → C → OracleComp spec M) (x : Option I) (c : C) :
    OracleComp spec (Option M) :=
  match x with
  | some x => some <$> progQ x c
  | none => pure none

/-- The patched answer of an optional patch. -/
def patchO {M : Type} (patch : M → (i : ι) → spec i → spec i) : Option M → (i : ι) → spec i → spec i
  | some m => patch m
  | none => fun _ u => u

/-- **The reduction of the programming step**: compute the second simulation's patch, then the
first's, by queries to the unprogrammed tables, and run the adversary's last stage with its
answers patched (the first simulation's patch over the second's, as `progT`). -/
def redQ (progQ₁ : I₁ → C₁ → OracleComp spec M₁) (patch₁ : M₁ → (i : ι) → spec i → spec i)
    (progQ₂ : I₂ → C₂ → OracleComp spec M₂) (patch₂ : M₂ → (i : ι) → spec i → spec i)
    (x₁ : Option I₁) (c₁ : C₁) (x₂ : Option I₂) (c₂ : C₂) (oa : OracleComp spec Out) :
    OracleComp spec Out :=
  progQO progQ₂ x₂ c₂ >>= fun m₂ => progQO progQ₁ x₁ c₁ >>= fun m₁ =>
    simP (fun i u => patchO patch₁ m₁ i (patchO patch₂ m₂ i u)) oa

/-- **The extractor of the simulation-extractability game**: `e` on the queries the reduction
makes, computed from the honest pairs (`logQ₁`, `logQ₂`: the patches' queries), the programmed
tables and a realization of the last stage (`AdmL`; none if there is no realization). -/
noncomputable def extL (ans : G → G → A × B → (i : ι) → spec i) (Bud : OracleComp spec Out → Prop)
    (logQ₁ : Option (I₁ × P₁) → G → G → B → List ι) (logQ₂ : Option (I₂ × P₂) → G → G → B → List ι)
    (e : Option (I₁ × P₁) → Option (I₂ × P₂) → Out → List ι → G → G → B → W) :
    Option (I₁ × P₁) → Option (I₂ × P₂) → (G → G → A × B → Out) → G → G → A × B → W :=
  fun p₁ p₂ F g₁ g₂ s => by
    classical
    exact e p₁ p₂ (F g₁ g₂ s)
      (logQ₂ p₂ g₁ g₂ s.2 ++ (logQ₁ p₁ g₁ g₂ s.2 ++
        if h : AdmL Bud ans F then qlog (ans g₁ g₂ s) h.choose else []))
      g₁ g₂ s.2

variable [Fintype G] [Fintype A] [Fintype B] [Fintype C₁] [Fintype C₂]

/-- The run of an optional patch, and its queries. -/
lemma runT_progQO {I C M : Type} (progQ : I → C → OracleComp spec M) (f : (k : ι) → spec k)
    (x : Option I) (c : C) :
    runT f (progQO progQ x c) = x.map fun x => runT f (progQ x c) := by
  rcases x with _ | x
  · rfl
  · exact runT_map _ _ _

lemma qlog_progQO {I C M : Type} (progQ : I → C → OracleComp spec M) (f : (k : ι) → spec k)
    (x : Option I) (c : C) :
    qlog f (progQO progQ x c) = match x with
      | some x => qlog f (progQ x c)
      | none => [] := by
  rcases x with _ | x
  · rfl
  · exact qlog_map _ _ _

/-- **Weak simulation-extractability from plain extraction with the query list.** The simulators'
programmings change only `s.1`, and the answers on the programmed tables are the answers on the
unprogrammed ones patched (`hpatch`) by a patch that an oracle computation (`progQ`) computes by
queries that read only `s.2` (`hpre`), and whose query list depends on the coins only through the
simulated pair (`hlog`; for no proof, no queries, `hlog0`). Then the extractor `extL` (which sees
the reduction's queries, computed from the pairs) is weakly simulation-extractable with error
`ε_plain + ε_moves`, where `ε_plain` is plain extraction for the class `Bud₀` that contains the
reductions (`hadm`). -/
theorem weakSE2_of_plainL [Nonempty C₁] [Nonempty C₂] {ans : G → G → A × B → (i : ι) → spec i}
    {sim₁ : I₁ → C₁ → Option P₁} {prog₁ : I₁ → C₁ → A × B → A × B}
    {sim₂ : I₂ → C₂ → Option P₂} {prog₂ : I₂ → C₂ → A × B → A × B} {Acc : Out → A × B → Prop}
    {Fresh : Option (I₁ × P₁) → Option (I₂ × P₂) → Out → Prop} {Rel : Out → W → Prop}
    {e : Option (I₁ × P₁) → Option (I₂ × P₂) → Out → List ι → G → G → B → W}
    {Bud Bud₀ : OracleComp spec Out → Prop} {ε₀ εm : ℝ}
    (progQ₁ : I₁ → C₁ → OracleComp spec M₁) (patch₁ : M₁ → (i : ι) → spec i → spec i)
    (progQ₂ : I₂ → C₂ → OracleComp spec M₂) (patch₂ : M₂ → (i : ι) → spec i → spec i)
    (logQ₁ : Option (I₁ × P₁) → G → G → B → List ι) (logQ₂ : Option (I₂ × P₂) → G → G → B → List ι)
    (hplain : PlainSEL ans Acc Fresh Rel e Bud₀ ε₀)
    (hmoves : ProgMoves sim₁ prog₁ sim₂ prog₂ Acc Fresh (AdmL Bud ans) εm)
    (hp₁ : ∀ x c s, (prog₁ x c s).2 = s.2) (hp₂ : ∀ x c s, (prog₂ x c s).2 = s.2)
    (hpatch₁ : ∀ x c g₁ g₂ s i, ans g₁ g₂ (prog₁ x c s) i =
      patch₁ (runT (ans g₁ g₂ s) (progQ₁ x c)) i (ans g₁ g₂ s i))
    (hpatch₂ : ∀ x c g₁ g₂ s i, ans g₁ g₂ (prog₂ x c s) i =
      patch₂ (runT (ans g₁ g₂ s) (progQ₂ x c)) i (ans g₁ g₂ s i))
    (hpre₁ : ∀ x c g₁ g₂ s s', s'.2 = s.2 →
      runT (ans g₁ g₂ s') (progQ₁ x c) = runT (ans g₁ g₂ s) (progQ₁ x c))
    (hlog₁ : ∀ x c g₁ g₂ s, qlog (ans g₁ g₂ s) (progQ₁ x c) =
      logQ₁ (pairO (some x) (sim₁ x c)) g₁ g₂ s.2)
    (hlog₂ : ∀ x c g₁ g₂ s, qlog (ans g₁ g₂ s) (progQ₂ x c) =
      logQ₂ (pairO (some x) (sim₂ x c)) g₁ g₂ s.2)
    (hlog0₁ : ∀ g₁ g₂ b, logQ₁ none g₁ g₂ b = [])
    (hlog0₂ : ∀ g₁ g₂ b, logQ₂ none g₁ g₂ b = [])
    (hadm : ∀ oa x₁ c₁ x₂ c₂, Bud oa →
      Bud₀ (redQ progQ₁ patch₁ progQ₂ patch₂ x₁ c₁ x₂ c₂ oa)) :
    WeakSE2 sim₁ prog₁ sim₂ prog₂ Acc Fresh Rel (extL ans Bud logQ₁ logQ₂ e) (AdmL Bud ans)
      (ε₀ + εm) := by
  classical
  intro α _ _ x₁ x₂ out hout
  -- the realization of each last stage, and the reduction on it
  let oaF : α → Option P₁ → Option P₂ → OracleComp spec Out := fun a π₁ π₂ =>
    (hout a π₁ π₂).choose
  have hF : ∀ a π₁ π₂, out a π₁ π₂ = fun g₁ g₂ s => runT (ans g₁ g₂ s) (oaF a π₁ π₂) :=
    fun a π₁ π₂ => (hout a π₁ π₂).choose_spec.2
  have hP := hplain (α × C₁ × C₂) (fun b => pairO (x₁ b.1) (simO sim₁ (x₁ b.1) b.2.1))
    (fun b => pairO (x₂ b.1 (simO sim₁ (x₁ b.1) b.2.1))
      (simO sim₂ (x₂ b.1 (simO sim₁ (x₁ b.1) b.2.1)) b.2.2))
    (fun b => redQ progQ₁ patch₁ progQ₂ patch₂ (x₁ b.1) b.2.1 (x₂ b.1 (simO sim₁ (x₁ b.1) b.2.1))
      b.2.2 (oaF b.1 (simO sim₁ (x₁ b.1) b.2.1)
        (simO sim₂ (x₂ b.1 (simO sim₁ (x₁ b.1) b.2.1)) b.2.2)))
    fun b => hadm _ _ _ _ _ (hout _ _ _).choose_spec.1
  rw [← pr_equiv (seEquiv α)] at hP
  have hM := hmoves α x₁ x₂ out hout
  refine (pr_mono fun z hz => ?_).trans ((pr_or_le _ _).trans (add_le_add hP hM))
  obtain ⟨hacc, hfr, hrel⟩ := hz
  -- notation for the point
  set a := z.1.1
  set c₁ := z.1.2.1
  set c₂ := z.2.1.1
  set g₁ := z.1.2.2
  set g₂ := z.2.1.2
  set s := z.2.2
  set π₁ := simO sim₁ (x₁ a) c₁
  set y₂ := x₂ a π₁
  set π₂ := simO sim₂ y₂ c₂
  set s' := progT prog₁ prog₂ (x₁ a) c₁ y₂ c₂ s
  have hs2 : s'.2 = s.2 := progT_snd hp₁ hp₂ _ _ _ _ _
  -- the patches, run on the unprogrammed tables
  set m₂ := runT (ans g₁ g₂ s) (progQO progQ₂ y₂ c₂)
  set m₁ := runT (ans g₁ g₂ s) (progQO progQ₁ (x₁ a) c₁)
  have hpt : ∀ i, ans g₁ g₂ s' i = patchO patch₁ m₁ i (patchO patch₂ m₂ i (ans g₁ g₂ s i)) := by
    intro i
    have e₂ : ∀ i, ans g₁ g₂ (progO prog₂ y₂ c₂ s) i = patchO patch₂ m₂ i (ans g₁ g₂ s i) := by
      intro i
      simp only [m₂, runT_progQO]
      rcases y₂ with _ | y
      · rfl
      · exact hpatch₂ y c₂ g₁ g₂ s i
    have hs₂ : (progO prog₂ y₂ c₂ s).2 = s.2 := progO_snd hp₂ _ _ _
    show ans g₁ g₂ (progO prog₁ (x₁ a) c₁ (progO prog₂ y₂ c₂ s)) i = _
    rcases hx : x₁ a with _ | x
    · have hm : m₁ = none := by simp only [m₁, runT_progQO, hx, Option.map_none]
      rw [hm]
      exact e₂ i
    · have hm : m₁ = some (runT (ans g₁ g₂ s) (progQ₁ x c₁)) := by
        simp only [m₁, runT_progQO, hx, Option.map_some]
      rw [hm]
      show ans g₁ g₂ (prog₁ x c₁ (progO prog₂ y₂ c₂ s)) i = patch₁ _ i _
      rw [hpatch₁ x c₁ g₁ g₂ _ i, hpre₁ x c₁ g₁ g₂ s _ hs₂, e₂ i]
  -- the reduction's run and queries
  set oa := oaF a π₁ π₂
  have hrun : runT (ans g₁ g₂ s) (redQ progQ₁ patch₁ progQ₂ patch₂ (x₁ a) c₁ y₂ c₂ oa) =
      runT (ans g₁ g₂ s') oa := by
    simp only [redQ, runT_bind, runT_simP]
    congr 1
    funext i
    exact (hpt i).symm
  have hlogO₂ : qlog (ans g₁ g₂ s) (progQO progQ₂ y₂ c₂) = logQ₂ (pairO y₂ π₂) g₁ g₂ s.2 := by
    rw [qlog_progQO]
    rcases y₂ with _ | y
    · exact (hlog0₂ _ _ _).symm
    · exact hlog₂ y c₂ g₁ g₂ s
  have hlogO₁ : qlog (ans g₁ g₂ s) (progQO progQ₁ (x₁ a) c₁) =
      logQ₁ (pairO (x₁ a) π₁) g₁ g₂ s.2 := by
    rw [qlog_progQO]
    rcases hx : x₁ a with _ | x
    · exact (hlog0₁ _ _ _).symm
    · simp only [π₁, hx]
      exact hlog₁ x c₁ g₁ g₂ s
  have hlog : qlog (ans g₁ g₂ s) (redQ progQ₁ patch₁ progQ₂ patch₂ (x₁ a) c₁ y₂ c₂ oa) =
      logQ₂ (pairO y₂ π₂) g₁ g₂ s.2 ++ (logQ₁ (pairO (x₁ a) π₁) g₁ g₂ s.2 ++
        qlog (ans g₁ g₂ s') oa) := by
    simp only [redQ, qlog_bind, qlog_simP]
    rw [hlogO₂, hlogO₁]
    congr 3
    funext i
    exact (hpt i).symm
  have hout' : out a π₁ π₂ g₁ g₂ s' = runT (ans g₁ g₂ s') oa := by rw [hF]
  by_cases h : Acc (out a π₁ π₂ g₁ g₂ s') s
  · left
    show Acc (runT (ans g₁ g₂ s) (redQ progQ₁ patch₁ progQ₂ patch₂ (x₁ a) c₁ y₂ c₂ oa)) s ∧
      Fresh (pairO (x₁ a) π₁) (pairO y₂ π₂)
        (runT (ans g₁ g₂ s) (redQ progQ₁ patch₁ progQ₂ patch₂ (x₁ a) c₁ y₂ c₂ oa)) ∧
      ¬ Rel (runT (ans g₁ g₂ s) (redQ progQ₁ patch₁ progQ₂ patch₂ (x₁ a) c₁ y₂ c₂ oa))
        (e (pairO (x₁ a) π₁) (pairO y₂ π₂)
          (runT (ans g₁ g₂ s) (redQ progQ₁ patch₁ progQ₂ patch₂ (x₁ a) c₁ y₂ c₂ oa))
          (qlog (ans g₁ g₂ s) (redQ progQ₁ patch₁ progQ₂ patch₂ (x₁ a) c₁ y₂ c₂ oa)) g₁ g₂ s.2)
    rw [hrun, hlog, ← hout']
    refine ⟨h, hfr, ?_⟩
    have hA : AdmL Bud ans (out a π₁ π₂) := hout a π₁ π₂
    have hx : extL ans Bud logQ₁ logQ₂ e (pairO (x₁ a) π₁) (pairO y₂ π₂) (out a π₁ π₂) g₁ g₂ s' =
        e (pairO (x₁ a) π₁) (pairO y₂ π₂) (out a π₁ π₂ g₁ g₂ s')
          (logQ₂ (pairO y₂ π₂) g₁ g₂ s.2 ++ (logQ₁ (pairO (x₁ a) π₁) g₁ g₂ s.2 ++
            qlog (ans g₁ g₂ s') oa)) g₁ g₂ s.2 := by
      simp only [extL, hA, ↓reduceDIte, hs2]
      rfl
    rw [← hx]
    exact hrel
  · right
    exact ⟨hfr, hacc, h⟩

end Step

end VoleMole.Theft
