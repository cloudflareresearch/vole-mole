import VoleMole.Theft.PlainLog
import VoleMole.Theft.ManyPlain

/-!
# Plain extraction with the query log, and the programming step, for `N` simulated proofs

`PlainSEN` (`Theft/ManyPlain.lean`) is plain extraction against last stages that are functions of
the tables, with an extractor that sees neither the adversary's queries nor `H₂³`. `PlainSEL`
(`Theft/PlainLog.lean`) restates it for two simulated proofs in the shape of `ROM/`'s extraction
bounds: the last stage is an oracle computation run on the tables and the extractor reads the
list of its queries. Here the same is done for `N` simulated proofs (`WeakSEN`):

* **`PlainSENL`**: plain extraction against last stages that are oracle computations `oa a` in a
  class `Bud`, run on the slices `g : Fin N → G` and the tables (`runT (ans g s)`); the extractor
  `e` sees the log `lg a` of honest pairs, the output, **the list of the run's queries**, the
  slices and `s.2`.
* **`AdmLN Bud ans`**: the last stages that are the run of an oracle computation in `Bud`.
* **`redQN`**: the reduction of the programming step. For the simulated proofs, most recent first,
  it computes each proof's patch by queries to the unprogrammed tables (`progQ`) and runs the rest
  with its answers patched; the adversary's last stage runs innermost, on the answers patched by
  all `N` patches. `seXs` lists the game's statements and coins, most recent first.
* **`extLN`**: `e` on the reduction's query list: the patches' queries, which it computes from the
  first `N` entries of the log (`logsL`, one list `logQ e` per entry; the game's log has `N`), then
  the queries of a realization of the last stage.
* **`weakSEN_of_plainL`**: `WeakSEN ≤ ε_plain + ε_moves` for `extLN`, with `PlainSENL` for the
  class `Bud₀` of the reductions (`hadm`, for patch lists of length `N`). This is
  `weakSEN_of_plain` with the query list and `weakSE2_of_plainL` for `N` proofs. As there, the
  patches are computed by queries (`hpatch`) whose list depends on the coins only through the
  simulated pair (`hlog`). Unlike `weakSE2_of_plainL`, no hypothesis on the patches' reads of the
  programmed part is needed: each patch is computed on the tables the later proofs' programmings
  have already produced, which is how the game composes them.
-/

open OracleComp OracleSpec

namespace VoleMole.Theft

open VoleMole.Privacy VoleMole.ROM.Reads

/-! ## Plain extraction against oracle computations, `N` slices -/

section Plain

variable {ι : Type} {spec : OracleSpec.{0, 0} ι} {N : ℕ} {I P G A B Out W : Type}

/-- **The last stages that are oracle computations in `Bud`**: `F` is the run of some `oa` with
`Bud oa`, on the answers `ans g s` of the slices and the tables. -/
def AdmLN (Bud : OracleComp spec Out → Prop) (ans : (Fin N → G) → A × B → (i : ι) → spec i)
    (F : (Fin N → G) → A × B → Out) : Prop :=
  ∃ oa : OracleComp spec Out, Bud oa ∧ F = fun g s => runT (ans g s) oa

variable [Fintype G] [Fintype A] [Fintype B]

/-- **Plain extraction with the query list, `N` slices**, with error `ε`, against the oracle
computations `Bud` admits. The adversary has advice `a`, a log `lg a` of honest statement–proof
pairs that defines freshness (any values, not read off the tables) and a last stage `oa a`, run on
uniform slices and tables (answers `ans`). The extractor `e` sees the log, the output, the list of
the run's queries, the slices and `s.2`. -/
def PlainSENL (N : ℕ) (ans : (Fin N → G) → A × B → (i : ι) → spec i) (Acc : Out → A × B → Prop)
    (Fresh : List (Option (I × P)) → Out → Prop) (Rel : Out → W → Prop)
    (e : List (Option (I × P)) → Out → List ι → (Fin N → G) → B → W)
    (Bud : OracleComp spec Out → Prop) (ε : ℝ) : Prop :=
  ∀ (α : Type) [Fintype α] [Nonempty α] (lg : α → List (Option (I × P)))
    (oa : α → OracleComp spec Out), (∀ a, Bud (oa a)) →
    pr (α × ((Fin N → G) × (A × B))) (fun z =>
      Acc (runT (ans z.2.1 z.2.2) (oa z.1)) z.2.2 ∧
        Fresh (lg z.1) (runT (ans z.2.1 z.2.2) (oa z.1)) ∧
        ¬ Rel (runT (ans z.2.1 z.2.2) (oa z.1))
          (e (lg z.1) (runT (ans z.2.1 z.2.2) (oa z.1)) (qlog (ans z.2.1 z.2.2) (oa z.1)) z.2.1
            z.2.2.2)) ≤ ε

/-- **Non-vacuity**: plain extraction holds with error `1`. -/
theorem plainSENL_one (N : ℕ) (ans : (Fin N → G) → A × B → (i : ι) → spec i)
    (Acc : Out → A × B → Prop) (Fresh : List (Option (I × P)) → Out → Prop) (Rel : Out → W → Prop)
    (e : List (Option (I × P)) → Out → List ι → (Fin N → G) → B → W)
    (Bud : OracleComp spec Out → Prop) : PlainSENL N ans Acc Fresh Rel e Bud 1 :=
  fun _ _ _ _ _ _ => pr_le_one _

lemma PlainSENL.mono {ans : (Fin N → G) → A × B → (i : ι) → spec i} {Acc : Out → A × B → Prop}
    {Fresh Fresh' : List (Option (I × P)) → Out → Prop} {Rel : Out → W → Prop}
    {e : List (Option (I × P)) → Out → List ι → (Fin N → G) → B → W}
    {Bud Bud' : OracleComp spec Out → Prop} {ε ε' : ℝ} (h : PlainSENL N ans Acc Fresh Rel e Bud ε)
    (hF : ∀ l o, Fresh' l o → Fresh l o) (hB : ∀ oa, Bud' oa → Bud oa) (hε : ε ≤ ε') :
    PlainSENL N ans Acc Fresh' Rel e Bud' ε' :=
  fun α _ _ lg oa hoa => ((Privacy.pr_mono fun _ hz => ⟨hz.1, hF _ _ hz.2.1, hz.2.2⟩).trans
    (h α lg oa fun a => hB _ (hoa a))).trans hε

end Plain

/-! ## The programming step, `N` simulated proofs -/

section Step

variable {ι : Type} {spec : OracleSpec.{0, 0} ι} {N : ℕ} {I P C G A B Out W M : Type}

/-- **The reduction of the programming step**: for each simulated proof, most recent first, compute
its patch by queries (`progQ`, none for no statement), then run the rest with its answers patched.
The adversary's last stage `oa` runs innermost. -/
def redQN (progQ : I → C → OracleComp spec M) (patch : M → (i : ι) → spec i → spec i) :
    List (Option I × C) → OracleComp spec Out → OracleComp spec Out
  | [], oa => oa
  | y :: ys, oa => progQO progQ y.1 y.2 >>= fun m => simP (patchO patch m) (redQN progQ patch ys oa)

/-- **The patches' queries, from the log**: `logQ` of each entry, the most recent first. -/
def logsL (logQ : Option (I × P) → (Fin N → G) → B → List ι) (l : List (Option (I × P)))
    (g : Fin N → G) (b : B) : List ι :=
  l.reverse.flatMap fun e => logQ e g b

lemma logsL_append (logQ : Option (I × P) → (Fin N → G) → B → List ι) (l : List (Option (I × P)))
    (e : Option (I × P)) (g : Fin N → G) (b : B) :
    logsL logQ (l ++ [e]) g b = logQ e g b ++ logsL logQ l g b := by
  simp [logsL]

/-- **The statements and coins of `WeakSEN`'s game** after `n` simulated proofs, the most recent
first. -/
def seXs {α : Type} (sim : I → C → Option P) (prog : I → C → A × B → A × B)
    (x : α → List (Option (I × P)) → Option I) (a : α) (cs : ℕ → C) : ℕ → List (Option I × C)
  | 0 => []
  | n + 1 => (x a (seLog sim prog x a cs n).1, cs n) :: seXs sim prog x a cs n

lemma seXs_length {α : Type} (sim : I → C → Option P) (prog : I → C → A × B → A × B)
    (x : α → List (Option (I × P)) → Option I) (a : α) (cs : ℕ → C) :
    ∀ n, (seXs sim prog x a cs n).length = n
  | 0 => rfl
  | n + 1 => by simp [seXs, seXs_length sim prog x a cs n]

/-- **The extractor of `WeakSEN`'s game**: `e` on the queries the reduction makes, computed from
the first `N` entries of the log (`logsL`: the patches' queries), the programmed tables and a realization of the last
stage (`AdmLN`; none if there is no realization). -/
noncomputable def extLN (ans : (Fin N → G) → A × B → (i : ι) → spec i)
    (Bud : OracleComp spec Out → Prop) (logQ : Option (I × P) → (Fin N → G) → B → List ι)
    (e : List (Option (I × P)) → Out → List ι → (Fin N → G) → B → W) :
    List (Option (I × P)) → ((Fin N → G) → A × B → Out) → (Fin N → G) → A × B → W :=
  fun l F g s => by
    classical
    exact e l (F g s)
      (logsL logQ (l.take N) g s.2 ++ if h : AdmLN Bud ans F then qlog (ans g s) h.choose else [])
      g s.2

/-- **On a realized last stage, `extLN` is `e` on the run and its queries.** -/
lemma extLN_of_admLN {ans : (Fin N → G) → A × B → (i : ι) → spec i}
    {Bud : OracleComp spec Out → Prop} {logQ : Option (I × P) → (Fin N → G) → B → List ι}
    {e : List (Option (I × P)) → Out → List ι → (Fin N → G) → B → W}
    {F : (Fin N → G) → A × B → Out} (h : AdmLN Bud ans F) :
    ∃ oa, Bud oa ∧ F = (fun g s => runT (ans g s) oa) ∧ ∀ l, extLN ans Bud logQ e l F = fun g s =>
      e l (runT (ans g s) oa) (logsL logQ (l.take N) g s.2 ++ qlog (ans g s) oa) g s.2 := by
  refine ⟨h.choose, h.choose_spec.1, h.choose_spec.2, fun l => funext fun g => funext fun s => ?_⟩
  unfold extLN
  rw [dite_eq_left h, congrFun (congrFun h.choose_spec.2 g) s]

/-- **The reduction's run and queries**: on the unprogrammed tables `s`, the reduction for the
game's first `n` simulated proofs runs the last stage on the tables the `n` simulations programmed,
after the patches' queries (`logsL` of the log). -/
theorem redQN_seXs {α : Type} {ans : (Fin N → G) → A × B → (i : ι) → spec i}
    {sim : I → C → Option P} {prog : I → C → A × B → A × B}
    (progQ : I → C → OracleComp spec M) (patch : M → (i : ι) → spec i → spec i)
    (logQ : Option (I × P) → (Fin N → G) → B → List ι)
    (hp : ∀ x c s, (prog x c s).2 = s.2)
    (hpatch : ∀ x c g s i, ans g (prog x c s) i =
      patch (runT (ans g s) (progQ x c)) i (ans g s i))
    (hlog : ∀ x c g s, qlog (ans g s) (progQ x c) = logQ (pairO (some x) (sim x c)) g s.2)
    (hlog0 : ∀ g b, logQ none g b = [])
    (x : α → List (Option (I × P)) → Option I) (a : α) (cs : ℕ → C) (oa : OracleComp spec Out)
    (g : Fin N → G) :
    ∀ n (s : A × B),
      runT (ans g s) (redQN progQ patch (seXs sim prog x a cs n) oa) =
          runT (ans g ((seLog sim prog x a cs n).2 s)) oa ∧
        qlog (ans g s) (redQN progQ patch (seXs sim prog x a cs n) oa) =
          logsL logQ (seLog sim prog x a cs n).1 g s.2 ++
            qlog (ans g ((seLog sim prog x a cs n).2 s)) oa
  | 0, s => ⟨rfl, rfl⟩
  | n + 1, s => by
    set y := x a (seLog sim prog x a cs n).1
    set m := runT (ans g s) (progQO progQ y (cs n))
    -- the patched answers are the answers on the tables the `n`-th simulation programmed
    have hpt : (fun i => patchO patch m i (ans g s i)) = ans g (progO prog y (cs n) s) := by
      funext i
      simp only [m, runT_progQO]
      rcases y with _ | y
      · rfl
      · exact (hpatch y (cs n) g s i).symm
    have hs2 : (progO prog y (cs n) s).2 = s.2 := progO_snd' hp _ _ _
    obtain ⟨ih1, ih2⟩ := redQN_seXs progQ patch logQ hp hpatch hlog hlog0 x a cs oa g n
      (progO prog y (cs n) s)
    have hq : qlog (ans g s) (progQO progQ y (cs n)) =
        logQ (pairO y (simO sim y (cs n))) g s.2 := by
      rw [qlog_progQO]
      rcases y with _ | y
      · exact (hlog0 _ _).symm
      · exact hlog y (cs n) g s
    have hL : (seLog sim prog x a cs (n + 1)).2 s =
        (seLog sim prog x a cs n).2 (progO prog y (cs n) s) := rfl
    have hl : (seLog sim prog x a cs (n + 1)).1 =
        (seLog sim prog x a cs n).1 ++ [pairO y (simO sim y (cs n))] := rfl
    refine ⟨?_, ?_⟩
    · show runT (ans g s) (progQO progQ y (cs n) >>= fun m =>
        simP (patchO patch m) (redQN progQ patch (seXs sim prog x a cs n) oa)) = _
      rw [runT_bind, runT_simP, hpt, ih1, hL]
    · show qlog (ans g s) (progQO progQ y (cs n) >>= fun m =>
        simP (patchO patch m) (redQN progQ patch (seXs sim prog x a cs n) oa)) = _
      rw [qlog_bind, qlog_simP, hpt, ih2, hq, hl, logsL_append, hs2, hL, List.append_assoc]

variable [Fintype C] [Nonempty C] [Fintype G] [Fintype A] [Fintype B]

/-- **Weak simulation-extractability with `N` simulated proofs, from plain extraction with the
query list.** The simulator's programming changes only `s.1`, and the answers on the programmed
tables are the answers on the unprogrammed ones patched (`hpatch`) by a patch that an oracle
computation (`progQ`) computes by queries whose list depends on the coins only through the
simulated pair (`hlog`; for no proof, no queries, `hlog0`). Then the extractor `extLN` (which sees
the reduction's queries, computed from the log) is weakly simulation-extractable with error
`ε_plain + ε_moves`, where `ε_plain` is plain extraction for the class `Bud₀` that contains the
reductions for `N` patches (`hadm`). -/
theorem weakSEN_of_plainL {ans : (Fin N → G) → A × B → (i : ι) → spec i}
    {sim : I → C → Option P} {prog : I → C → A × B → A × B} {Acc : Out → A × B → Prop}
    {Fresh : List (Option (I × P)) → Out → Prop} {Rel : Out → W → Prop}
    {e : List (Option (I × P)) → Out → List ι → (Fin N → G) → B → W}
    {Bud Bud₀ : OracleComp spec Out → Prop} {ε₀ εm : ℝ}
    (progQ : I → C → OracleComp spec M) (patch : M → (i : ι) → spec i → spec i)
    (logQ : Option (I × P) → (Fin N → G) → B → List ι)
    (hplain : PlainSENL N ans Acc Fresh Rel e Bud₀ ε₀)
    (hmoves : ProgMovesN N sim prog Acc Fresh (AdmLN Bud ans) εm)
    (hp : ∀ x c s, (prog x c s).2 = s.2)
    (hpatch : ∀ x c g s i, ans g (prog x c s) i =
      patch (runT (ans g s) (progQ x c)) i (ans g s i))
    (hlog : ∀ x c g s, qlog (ans g s) (progQ x c) = logQ (pairO (some x) (sim x c)) g s.2)
    (hlog0 : ∀ g b, logQ none g b = [])
    (hadm : ∀ oa (ys : List (Option I × C)), ys.length = N → Bud oa →
      Bud₀ (redQN progQ patch ys oa)) :
    WeakSEN N sim prog Acc Fresh Rel (extLN ans Bud logQ e) (AdmLN Bud ans) (ε₀ + εm) := by
  classical
  intro α _ _ x out hout
  -- the realization of each last stage, and the reduction on it
  let oaF : α → List (Option (I × P)) → OracleComp spec Out := fun a l => (hout a l).choose
  have hF : ∀ a l, out a l = fun g s => runT (ans g s) (oaF a l) :=
    fun a l => (hout a l).choose_spec.2
  have hP := hplain (α × (Fin N → C)) (fun b => (seLog sim prog x b.1 (extN b.2) N).1)
    (fun b => redQN progQ patch (seXs sim prog x b.1 (extN b.2) N)
      (oaF b.1 (seLog sim prog x b.1 (extN b.2) N).1))
    fun b => hadm _ _ (seXs_length _ _ _ _ _ _) (hout _ _).choose_spec.1
  rw [← pr_equiv (seEquivN α)] at hP
  have hM := hmoves α x out hout
  refine (pr_mono fun z hz => ?_).trans ((pr_or_le _ _).trans (add_le_add hP hM))
  obtain ⟨hacc, hfr, hrel⟩ := hz
  set a := z.1.1
  set cs := extN fun j => (z.1.2 j).1
  set g : Fin N → G := fun j => (z.1.2 j).2
  set s := z.2
  set l := (seLog sim prog x a cs N).1
  set Lp := (seLog sim prog x a cs N).2
  have e2 : (Lp s).2 = s.2 := (seLog_isProgs sim prog x a cs N).snd hp s
  obtain ⟨hrun, hlg⟩ := redQN_seXs progQ patch logQ hp hpatch hlog hlog0 x a cs (oaF a l) g N s
  have hout' : out a l g (Lp s) = runT (ans g (Lp s)) (oaF a l) := by rw [hF]
  by_cases h : Acc (out a l g (Lp s)) s
  · left
    show Acc (runT (ans g s) (redQN progQ patch (seXs sim prog x a cs N) (oaF a l))) s ∧
      Fresh l (runT (ans g s) (redQN progQ patch (seXs sim prog x a cs N) (oaF a l))) ∧
      ¬ Rel (runT (ans g s) (redQN progQ patch (seXs sim prog x a cs N) (oaF a l)))
        (e l (runT (ans g s) (redQN progQ patch (seXs sim prog x a cs N) (oaF a l)))
          (qlog (ans g s) (redQN progQ patch (seXs sim prog x a cs N) (oaF a l))) g s.2)
    rw [hrun, hlg, ← hout']
    refine ⟨h, hfr, ?_⟩
    have hA : AdmLN Bud ans (out a l) := hout a l
    have hx : extLN ans Bud logQ e l (out a l) g (Lp s) =
        e l (out a l g (Lp s)) (logsL logQ l g s.2 ++ qlog (ans g (Lp s)) (oaF a l)) g s.2 := by
      have ht : l.take N = l := List.take_of_length_le (le_of_eq (simPre_length _ _ _ _ N))
      simp only [extLN, hA, ↓reduceDIte, e2, ht]
      rfl
    rw [← hx]
    exact hrel
  · right
    exact ⟨hfr, hacc, h⟩

end Step

end VoleMole.Theft
