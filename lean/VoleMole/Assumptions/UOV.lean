import VoleMole.ROM.OneMore

/-!
# The UOV assumptions as standalone security games

`lean/docs/security/uov-assumptions.md` §3. Each assumption of the note is a game here, generic in
the key generator, the public map (as a preimage relation `IsPre pk s t`, "`P(s) = t`") and the
deterministic sampler `D = derive_preimage` (`Trapdoor`). The protocol theorems' assumption terms
are advantages in these games (`Assumptions/UOVLinks.lean`). No reduction between the games is
proved here, except the trivial ones listed at the end.

**The trapdoor** (`Trapdoor PK SK T S`): `keyGen`, `IsPre`, `D`. `S` is both the oracle's answer
and the type of a claimed preimage, so a failing sampler is `S = Option X` (`Trapdoor.ofEval`:
`IsPre pk s t ↔ s = some x ∧ P(x) = t`). For pqov, `D` is `Spec.Signer.derivePreimage` (its model
`Spec.Pqov.signer`, 255 vinegar attempts) and `P` is `UOVKey.eval`; PomFRIT's instance is
`OneMore.Pomfrit.relP` and `honestPre`.

**Oracle games** (VCVio oracle computations against a stateful challenger, as `OneMore.omExp`).
Every adversary also gets a *world*, a lazy random oracle `specR AR` (its coins, or the hashes; any
`AR`), as in `omExp`.
* `advUOV` (item 1), `advUOVn` (n-target), `advOW` (item 2), `advGPI` (item 3, decisional; the good
  sampler is a parameter): adversaries are plain `ProbComp`s.
* `advFDH` (item 6, det-FDH EUF-CMA in the ROM): `H` a lazy random oracle into `T`, `Sign(m) =
  D(H(m))`; win: a preimage of `H(m*)` for an unsigned `m*`, within `q_H` hash and `q_S` signing
  queries.
* `advOMPR` (item 7, Def. 3.1) and `advOMPRShift` (item 8, OMPR⊕τ): `OneMore.omExp` with
  `goodPre` and `goodShift τ`, i.e. labelled targets on demand (at most `n`), at most `ℓ` preimage
  queries, `ℓ + 1` good claims on distinct labels. `ompr31` is Def. 3.1 literally (all `n` targets
  given up front, claims by index); `advOMPR_le_ompr31` shows that the on-demand game is no
  stronger: any on-demand adversary is a Def. 3.1 adversary (`popAdv`, which pops the targets) with
  at least the same advantage.
* `advOMPI` (item 9, A-OMPI(q_T, Q)): targets on demand from a stream of `q_T`, an index oracle
  `i ↦ D(y_i)`; win: a preimage of an unopened `y_{i*}` within `Q` index queries.

**Semantic-oracle games** (`SemForger`). The signing oracles of CT-UF and UF-Tag are given to the
adversary as a *function* `σ` together with a proof (`reads`) that, against every table of the
hash oracles and every coin value `E`, its output depends on `σ` only through `σ`'s values at the
points it logs (its *signing log*), and through a view `pv` of `σ`'s values at the points of its
*probe log*. This is the form of `ROM/RatatouilleBalance.lean`'s `TagForger`, and the form the
protocol reductions produce (they run a whole protocol game in which an honest party calls the
signer). An oracle adversary is a semantic one with the same advantage (`SemForger.ofOracle`); the
converse is not claimed (a semantic adversary may need more adaptive queries to be realized; the
CT-UF and UF-Tag wins do not count queries).
* `advCTUF` (item 10) and `advCTUFOpen` (item 11) for `K` keys: oracle `(k, t) ↦ D(sk_k, t)` on
  arbitrary targets; win: `(k, x*, s*)` with `x* ∈ D_Com`, `P_k(s*) = Com(x*)` and `Com(x*)` never
  signed; `CT-UF^open` also requires an opening in `D_Com` of every signed target.
* `advUFTag` (item 12) and `advUFTagProbe` (UF-Tag with a signability probe: the forger also learns,
  at the points of its probe log, whether `σ` succeeds): oracle `m ↦ σ(H(m))`; win: a preimage of
  `H(m*)` for an `m*` none of whose signing queries was answered.

The per-key (`…At`) advantages are what the protocol theorems bound (they hold for every key); the
keyed ones average them over `keyGen`.

**Trivial reductions.** `advUOVn_le_sum` (n-target ≤ Σᵢ single-target, embedding at each `i`),
`advCTUFOpen_le` (CT-UF^open ≤ CT-UF, the same forger), `advUFTag_eq_probe` (a forger without
probe is a probe forger), `advOMPI_le_one`-style sanity bounds are in the audit section.

No `sorry`, no `axiom`.
-/

open OracleComp OracleSpec VoleMole.ROM.OneMore
open scoped ENNReal

namespace VoleMole.Assumptions.UOV

/-! ## The trapdoor -/

/-- **A trapdoor preimage-sampleable function** in the sense of the note: a key generator, the
preimage relation of the public map (`IsPre pk s t`: `s` is a preimage of `t`), and the
deterministic sampler `D` (`derive_preimage`), whose answers are also the claims' type. -/
structure Trapdoor (PK SK T S : Type) where
  keyGen : ProbComp (PK × SK)
  IsPre : PK → S → T → Prop
  D : SK → T → S

/-- The trapdoor of a public map `P` and a sampler that may fail (`none`). -/
def Trapdoor.ofEval {PK SK T X : Type} (keyGen : ProbComp (PK × SK)) (P : PK → X → T)
    (D : SK → T → Option X) : Trapdoor PK SK T (Option X) where
  keyGen := keyGen
  IsPre pk s t := ∃ x, s = some x ∧ P pk x = t
  D := D

/-- The sampler is **correct** for the keys `keyGen` outputs: on a valid target its answer is a
preimage, or a failure (`fails`). -/
def Trapdoor.Correct {PK SK T S : Type} (tr : Trapdoor PK SK T S) (valid : T → Prop)
    (fails : S → Prop) : Prop :=
  ∀ kp ∈ support tr.keyGen, ∀ t, valid t → tr.IsPre kp.1 (tr.D kp.2 t) t ∨ fails (tr.D kp.2 t)

/-! ## Item 1: the UOV problem, and its `n`-target version -/

section Problem

variable {PK SK T S : Type} (tr : Trapdoor PK SK T S) [SampleableType T]

/-- **`Adv^{uov}`**: a preimage of a uniform target. -/
noncomputable def advUOV (A : PK → T → ProbComp S) : ℝ≥0∞ :=
  Pr{let kp ← tr.keyGen; let t ← $ᵗ T; let s ← A kp.1 t}[tr.IsPre kp.1 s t]

/-- `n` independent uniform targets. -/
def unifVec (T : Type) [SampleableType T] : (n : ℕ) → ProbComp (Fin n → T)
  | 0 => pure Fin.elim0
  | n + 1 => do
    let t ← $ᵗ T
    let ts ← unifVec T n
    pure (Fin.cons t ts)

/-- **`Adv^{uov-n}`**: a preimage of any one of `n` uniform targets. -/
noncomputable def advUOVn (n : ℕ) (A : PK → (Fin n → T) → ProbComp S) : ℝ≥0∞ :=
  Pr{let kp ← tr.keyGen; let ts ← unifVec T n; let s ← A kp.1 ts}[∃ i, tr.IsPre kp.1 s (ts i)]

end Problem

/-! ## Item 2: one-wayness; item 3: good-preimage indistinguishability -/

section OWGPI

variable {PK SK T S : Type} (tr : Trapdoor PK SK T S)

/-- **`Adv^{ow}`**: a preimage of `P(x)` for a uniform point `x` of the domain `X`. -/
noncomputable def advOW {X : Type} [SampleableType X] (P : PK → X → T) (A : PK → T → ProbComp S) :
    ℝ≥0∞ :=
  Pr{let kp ← tr.keyGen; let x ← $ᵗ X; let s ← A kp.1 (P kp.1 x)}[tr.IsPre kp.1 s (P kp.1 x)]

/-- `q` independent samples. -/
def iid {X : Type} (μ : ProbComp X) : ℕ → ProbComp (List X)
  | 0 => pure []
  | q + 1 => do
    let x ← μ
    let xs ← iid μ q
    pure (x :: xs)

/-- The GPI experiment with the sampler `μ sk`: the distinguisher's output bit. -/
noncomputable def gpiPr {X : Type} (μ : SK → ProbComp X) (q : ℕ)
    (A : PK → List X → ProbComp Bool) : ℝ≥0∞ :=
  Pr{let kp ← tr.keyGen; let xs ← iid (μ kp.2) q; let b ← A kp.1 xs}[b = true]

/-- **`Adv^{gpi}(q)`**: `q` uniform points (`U`) against `q` uniform *good* points (`G sk`, the
uniform distribution on `Good_sk`, which needs the secret key), given the public key. The absolute
difference, in `ℝ≥0∞`. -/
noncomputable def advGPI {X : Type} (U : ProbComp X) (G : SK → ProbComp X) (q : ℕ)
    (A : PK → List X → ProbComp Bool) : ℝ≥0∞ :=
  max (gpiPr tr (fun _ => U) q A - gpiPr tr G q A) (gpiPr tr G q A - gpiPr tr (fun _ => U) q A)

end OWGPI

/-! ## Item 6: det-FDH EUF-CMA in the random-oracle model -/

section FDH

variable {DR : Type} (AR : DR → Type) (M T S : Type)

abbrev AnsF : DR ⊕ (M ⊕ M) → Type := Sum.elim AR (Sum.elim (fun _ => T) fun _ => S)

/-- The det-FDH adversary's oracles: the world, the hash `H : M → T`, the signer `m ↦ D(H(m))`. -/
abbrev specF : OracleSpec (DR ⊕ (M ⊕ M)) := OracleSpec.ofFn (AnsF AR M T S)

/-- The det-FDH challenger's state: the world's cache, `H`'s table, the signed messages (newest
first), the number of hash queries. -/
structure FDHSt where
  ro : (specR AR).QueryCache
  h : M → Option T
  signed : List M
  hq : ℕ

end FDH

section FDHImpl

variable {DR : Type} [DecidableEq DR] {AR : DR → Type} [∀ d, SampleableType (AR d)]
  {M : Type} [DecidableEq M] {T S : Type} [SampleableType T]

/-- `H(m)`, lazily. -/
def hStep (m : M) (c : FDHSt AR M T) : ProbComp (T × FDHSt AR M T) :=
  match c.h m with
  | some t => pure (t, c)
  | none => (fun t => (t, { c with h := Function.update c.h m (some t) })) <$> ($ᵗ T)

/-- **The det-FDH challenger.** -/
def fdhImpl (D : T → S) : QueryImpl (specF AR M T S) (StateT (FDHSt AR M T) ProbComp)
  | .inl d => StateT.mk fun c =>
      (fun r => (r.1, { c with ro := r.2 })) <$> ((specR AR).randomOracle d).run c.ro
  | .inr (.inl m) => StateT.mk fun c => (fun r => (r.1, { r.2 with hq := r.2.hq + 1 })) <$> hStep m c
  | .inr (.inr m) => StateT.mk fun c =>
      (fun r => (D r.1, { r.2 with signed := m :: r.2.signed })) <$> hStep m c

/-- The initial state. -/
def fdh0 : FDHSt AR M T := ⟨∅, fun _ => none, [], 0⟩

variable {PK SK : Type} (tr : Trapdoor PK SK T S)

/-- **The det-FDH experiment**: the adversary's forgery `(m*, s*)`, `H(m*)` (evaluated by the
challenger after the run) and the state after the run. -/
def fdhExp (A : PK → ProbComp (OracleComp (specF AR M T S) (M × S))) :
    ProbComp (PK × (M × S) × T × FDHSt AR M T) := do
  let kp ← tr.keyGen
  let a ← A kp.1
  let r ← (simulateQ (fdhImpl (tr.D kp.2)) a).run fdh0
  let h ← hStep r.1.1 r.2
  pure (kp.1, r.1, h.1, r.2)

/-- **The det-FDH win**: a preimage of `H(m*)` for an unsigned `m*`, within `q_H` hash and `q_S`
signing queries. -/
def FDHWin (qH qS : ℕ) (r : PK × (M × S) × T × FDHSt AR M T) : Prop :=
  r.2.1.1 ∉ r.2.2.2.signed ∧ tr.IsPre r.1 r.2.1.2 r.2.2.1 ∧ r.2.2.2.hq ≤ qH ∧
    r.2.2.2.signed.length ≤ qS

/-- **`Adv^{euf}_{det}(q_H, q_S)`.** -/
noncomputable def advFDH (qH qS : ℕ) (A : PK → ProbComp (OracleComp (specF AR M T S) (M × S))) :
    ℝ≥0∞ :=
  Pr{let r ← fdhExp tr A}[FDHWin tr qH qS r]

end FDHImpl

/-! ## Items 7 and 8: OMPR and OMPR⊕τ (`OneMore.omExp`) -/

section OMPR

variable {DR : Type} [DecidableEq DR] {AR : DR → Type} [∀ d, SampleableType (AR d)]
  {X : Type} [DecidableEq X] {Hn T S : Type} [AddCommGroup T] [SampleableType T]
  {PK SK : Type} (tr : Trapdoor PK SK T S)

/-- **`Adv^{ompr}(n, ℓ)`** (Def. 3.1, item 7), with targets requested on demand under labels (`n`
uniform targets, at most `ℓ` preimage queries, `ℓ + 1` preimages of targets of distinct labels).
This is `omExp` with `goodPre`, the game of PomFRIT's U1. -/
noncomputable def advOMPR (n ℓ : ℕ)
    (B : PK → ProbComp (OracleComp (specB AR X Hn T S) (List (X × S)))) : ℝ≥0∞ :=
  Pr{let r ← omExp tr.keyGen tr.D n B}[Wins ℓ (goodPre tr.IsPre) r.1 r.2.1 r.2.2]

/-- **`Adv^{ompr⊕τ}(N, ℓ)`** (item 8): each target request carries a list of shifts (its hint),
and a claim is good for a shifted target `h ⊕ δ` with `δ` among the first at most `τ` shifts. This
is `omExp` with `goodShift τ`, the game of PomFRIT's U2. -/
noncomputable def advOMPRShift (τ n ℓ : ℕ)
    (B : PK → ProbComp (OracleComp (specB AR X (List T) T S) (List (X × S)))) : ℝ≥0∞ :=
  Pr{let r ← omExp tr.keyGen tr.D n B}[Wins ℓ (goodShift τ tr.IsPre) r.1 r.2.1 r.2.2]

end OMPR

/-! ## Def. 3.1 literally, and the on-demand game reduces to it -/

section Def31

variable {DR : Type} (AR : DR → Type) (T S : Type)

abbrev AnsP : DR ⊕ T → Type := Sum.elim AR fun _ => S

/-- Def. 3.1's oracles: the world and the preimage oracle `SPre`. -/
abbrev specP : OracleSpec (DR ⊕ T) := OracleSpec.ofFn (AnsP AR T S)

/-- Def. 3.1's challenger state: the world's cache, the number of preimage queries. -/
structure St31 where
  ro : (specR AR).QueryCache
  iq : ℕ

variable (X Hn : Type)

/-- The popping adversary's state: the next target's index, and each label's index and hint. -/
structure PopSt where
  next : ℕ
  tg : X → Option (ℕ × Hn)

end Def31

section Def31Impl

variable {DR : Type} [DecidableEq DR] {AR : DR → Type} [∀ d, SampleableType (AR d)]
  {X : Type} [DecidableEq X] {Hn T S : Type} [SampleableType T]

/-- **Def. 3.1's challenger.** -/
def impl31 (pre : T → S) : QueryImpl (specP AR T S) (StateT (St31 AR) ProbComp)
  | .inl d => StateT.mk fun c =>
      (fun r => (r.1, { c with ro := r.2 })) <$> ((specR AR).randomOracle d).run c.ro
  | .inr t => StateT.mk fun c => pure (pre t, { c with iq := c.iq + 1 })

def st31 : St31 AR := ⟨∅, 0⟩

variable {PK SK : Type} (tr : Trapdoor PK SK T S)

/-- **Def. 3.1's experiment** with `n` targets: the adversary gets the key and all targets
`t_1 … t_n` up front. -/
def ompr31Exp (n : ℕ) (B : PK → List T → ProbComp (OracleComp (specP AR T S) (List (ℕ × S)))) :
    ProbComp (PK × List T × List (ℕ × S) × St31 AR) := do
  let kp ← tr.keyGen
  let L ← unifList T n
  let b ← B kp.1 L
  let r ← (simulateQ (impl31 (tr.D kp.2)) b).run st31
  pure (kp.1, L, r.1, r.2)

/-- **Def. 3.1's win**: `ℓ + 1` preimages of targets of distinct indices, after at most `ℓ`
preimage queries. -/
def Win31 (ℓ : ℕ) (r : PK × List T × List (ℕ × S) × St31 AR) : Prop :=
  r.2.2.1.length = ℓ + 1 ∧ (r.2.2.1.map Prod.fst).Nodup ∧ r.2.2.2.iq ≤ ℓ ∧
    ∀ p ∈ r.2.2.1, ∃ t, r.2.1[p.1]? = some t ∧ tr.IsPre r.1 p.2 t

/-- **`Adv^{ompr}(n, ℓ)` of Def. 3.1, literally.** -/
noncomputable def advOMPR31 (n ℓ : ℕ)
    (B : PK → List T → ProbComp (OracleComp (specP AR T S) (List (ℕ × S)))) : ℝ≥0∞ :=
  Pr{let r ← ompr31Exp tr n B}[Win31 tr ℓ r]

/-- The popping adversary's handler: the world and the preimage oracle forwarded; a target request
`(x, h)` answered by the next target `L[next]`, recorded with its index. -/
def popImpl (L : List T) :
    QueryImpl (specB AR X Hn T S) (StateT (PopSt X Hn) (OracleComp (specP AR T S)))
  | .inl d => StateT.mk fun s => (fun a => (a, s)) <$>
      (liftM ((specP AR T S).query (.inl d)) : OracleComp (specP AR T S) (AR d))
  | .inr (.inl (x, h)) => StateT.mk fun s => pure <| match L[s.next]? with
      | some u => (some u, ⟨s.next + 1, Function.update s.tg x (some (s.next, h))⟩)
      | none => (none, s)
  | .inr (.inr t) => StateT.mk fun s => (fun a => (a, s)) <$>
      (liftM ((specP AR T S).query (.inr t)) : OracleComp (specP AR T S) S)

/-- **The on-demand adversary as a Def. 3.1 adversary**: it pops the given targets on request and
names each claim by its label's index. -/
def popAdv (B : PK → ProbComp (OracleComp (specB AR X Hn T S) (List (X × S)))) (pk : PK)
    (L : List T) : ProbComp (OracleComp (specP AR T S) (List (ℕ × S))) :=
  (fun b => (fun r : List (X × S) × PopSt X Hn =>
    r.1.map fun p => (((r.2.tg p.1).map Prod.fst).getD 0, p.2)) <$>
      (simulateQ (popImpl L) b).run ⟨0, fun _ => none⟩) <$> B pk

/-- The popping adversary run against Def. 3.1's challenger, as one handler. -/
def comb31 (pre : T → S) (L : List T) :
    QueryImpl (specB AR X Hn T S) (StateT (PopSt X Hn × St31 AR) ProbComp) :=
  fun q => StateT.mk fun s => (fun r => (r.1.1, (r.1.2, r.2))) <$>
    (simulateQ (impl31 pre) ((popImpl L q).run s.1)).run s.2

omit [SampleableType T] in
theorem collapse31 (pre : T → S) (L : List T) {α : Type} (oa : OracleComp (specB AR X Hn T S) α)
    (s : PopSt X Hn) (c : St31 AR) :
    (simulateQ (impl31 pre) ((simulateQ (popImpl L) oa).run s)).run c =
      (fun r => ((r.1, r.2.1), r.2.2)) <$> (simulateQ (comb31 pre L) oa).run (s, c) := by
  refine simulateQ_StateT_StateT_compose _ _ _ (fun q s c => ?_) oa s c
  show _ = _ <$> ((fun r : (_ × _) × _ => (r.1.1, (r.1.2, r.2))) <$> _)
  rw [Functor.map_map]
  exact (id_map _).symm

/-- The on-demand challenger's state that a popping state represents. -/
def proj31 (L : List T) (s : PopSt X Hn × St31 AR) : Ch AR X Hn T :=
  ⟨s.2.ro, L.drop s.1.next, fun x => (s.1.tg x).bind fun ih => (L[ih.1]?).map (·, ih.2), s.2.iq⟩

/-- The popping state's invariant: recorded indices are below `next` and name one label each. -/
def Inv31 (s : PopSt X Hn × St31 AR) : Prop :=
  ∀ x i h, s.1.tg x = some (i, h) → i < s.1.next ∧ ∀ y h', s.1.tg y = some (i, h') → y = x

variable (pre : T → S) (L : List T)

omit [SampleableType T] in
theorem comb31_step (q : DR ⊕ ((X × Hn) ⊕ T)) (s : PopSt X Hn × St31 AR) :
    (fun z => (z.1, proj31 L z.2)) <$> (comb31 pre L q).run s = (chImpl pre q).run (proj31 L s) := by
  rcases q with d | ⟨x, h⟩ | t
  · simp only [comb31, popImpl, StateT.run_mk]
    erw [simulateQ_map, simulateQ_spec_query]
    simp [impl31, chImpl, roStep, proj31]
  · cases hL : L[s.1.next]? with
    | none =>
      have hd : L.drop s.1.next = [] := List.drop_eq_nil_of_le (by
        simpa using hL)
      simp [comb31, popImpl, chImpl, proj31, hL, hd]
    | some u =>
      have hlt : s.1.next < L.length := (List.getElem?_eq_some_iff.1 hL).1
      have hd : L.drop s.1.next = u :: L.drop (s.1.next + 1) := by
        rw [List.drop_eq_getElem_cons hlt, (List.getElem?_eq_some_iff.1 hL).2]
      simp only [comb31, popImpl, chImpl, proj31, StateT.run_mk, hL, simulateQ_pure,
        StateT.run_pure, map_pure, hd]
      congr 3
      funext y
      by_cases hy : y = x
      · subst hy; simp [hL]
      · simp [Function.update_of_ne hy]
  · simp only [comb31, popImpl, StateT.run_mk]
    erw [simulateQ_map, simulateQ_spec_query]
    simp [impl31, chImpl, proj31]

omit [SampleableType T] in
theorem comb31_inv : QueryImpl.PreservesInv (comb31 (X := X) (Hn := Hn) (AR := AR) pre L) Inv31 := by
  intro q s hs z hz
  rcases q with d | ⟨x, h⟩ | t
  · simp only [comb31, popImpl, StateT.run_mk] at hz
    erw [simulateQ_map, simulateQ_spec_query] at hz
    simp [impl31] at hz
    obtain ⟨a, b, -, rfl⟩ := hz
    exact hs
  · simp only [comb31, popImpl, StateT.run_mk] at hz
    cases hL : L[s.1.next]? with
    | none =>
      simp only [hL, simulateQ_pure, StateT.run_pure, map_pure, support_pure,
        Set.mem_singleton_iff] at hz
      subst hz; exact hs
    | some u =>
      simp only [hL, simulateQ_pure, StateT.run_pure, map_pure, support_pure,
        Set.mem_singleton_iff] at hz
      subst hz
      intro y i h' hy
      by_cases hyx : y = x
      · subst hyx
        simp only [Function.update_self, Option.some.injEq, Prod.mk.injEq] at hy
        obtain ⟨rfl, rfl⟩ := hy
        refine ⟨Nat.lt_succ_self _, fun y' h'' hy' => ?_⟩
        by_contra hne
        simp only [Function.update_of_ne hne] at hy'
        exact absurd (hs y' _ _ hy').1 (lt_irrefl _)
      · simp only [Function.update_of_ne hyx] at hy
        obtain ⟨hi, hu⟩ := hs y i h' hy
        refine ⟨Nat.lt_succ_of_lt hi, fun y' h'' hy' => ?_⟩
        by_cases hy'x : y' = x
        · subst hy'x
          simp only [Function.update_self, Option.some.injEq, Prod.mk.injEq] at hy'
          exact absurd hy'.1.symm (ne_of_lt hi)
        · simp only [Function.update_of_ne hy'x] at hy'
          exact hu y' h'' hy'
  · simp only [comb31, popImpl, StateT.run_mk] at hz
    erw [simulateQ_map, simulateQ_spec_query] at hz
    simp only [impl31] at hz
    subst hz
    exact hs

omit [SampleableType T] in
/-- **The popping simulation is the on-demand challenger**, through `proj31`. -/
theorem comb31_eqd {α : Type} (oa : OracleComp (specB AR X Hn T S) α) :
    ∀ s : PopSt X Hn × St31 AR,
      (fun z => (z.1, proj31 L z.2)) <$> (simulateQ (comb31 pre L) oa).run s =ᵈ
        (simulateQ (chImpl pre) oa).run (proj31 L s) := by
  induction oa using OracleComp.inductionOn with
  | pure x => intro s; simp only [simulateQ_pure, StateT.run_pure, map_pure]; exact EvalDistEq.rfl
  | query_bind q k ih =>
    intro s
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, map_bind]
    rw [← comb31_step pre L q s, bind_map_left]
    exact EvalDistEq.bind_congr_of_support _ fun z _ => ih z.1 z.2

end Def31Impl

section Def31Red

variable {DR : Type} [DecidableEq DR] {AR : DR → Type} [∀ d, SampleableType (AR d)]
  {X : Type} [DecidableEq X] {Hn T S : Type} [SampleableType T]
  {PK SK : Type} (tr : Trapdoor PK SK T S)

/-- The popping adversary's claims, named by index. -/
def mapcl (z : List (X × S) × PopSt X Hn × St31 AR) : List (ℕ × S) :=
  z.1.map fun p => (((z.2.1.tg p.1).map Prod.fst).getD 0, p.2)

/-- The joint run: key, adversary, targets, popping simulation against Def. 3.1's challenger. -/
def jointRun (n : ℕ) (B : PK → ProbComp (OracleComp (specB AR X Hn T S) (List (X × S)))) :
    ProbComp ((PK × SK) × List T × List (X × S) × PopSt X Hn × St31 AR) :=
  tr.keyGen >>= fun kp => B kp.1 >>= fun b => unifList T n >>= fun L =>
    (simulateQ (comb31 (tr.D kp.2) L) b).run (⟨0, fun _ => none⟩, st31) >>= fun z => pure (kp, L, z)

omit [DecidableEq DR] [∀ d, SampleableType (AR d)] [DecidableEq X] [SampleableType T] in
theorem wins_imp_win31 (ℓ : ℕ) (pk : PK) (L : List T) (z : List (X × S) × PopSt X Hn × St31 AR)
    (hinv : Inv31 z.2) (hw : Wins ℓ (goodPre tr.IsPre) pk z.1 (proj31 L z.2)) :
    Win31 tr ℓ (pk, L, mapcl z, z.2.2) := by
  obtain ⟨hlen, hnd, hiq, hgood⟩ := hw
  have hidx : ∀ p ∈ z.1, ∃ i h t, z.2.1.tg p.1 = some (i, h) ∧ L[i]? = some t ∧
      tr.IsPre pk p.2 t := by
    intro p hp
    obtain ⟨t, h, htg, hpre⟩ := hgood p hp
    simp only [proj31, Option.bind_eq_some_iff, Option.map_eq_some_iff, Prod.mk.injEq] at htg
    obtain ⟨⟨i, h'⟩, hi, t', ht', rfl, rfl⟩ := htg
    exact ⟨i, h', t', hi, ht', hpre⟩
  refine ⟨by simp [mapcl, hlen], ?_, hiq, ?_⟩
  · have : (mapcl z).map Prod.fst =
        (z.1.map Prod.fst).map fun x => ((z.2.1.tg x).map Prod.fst).getD 0 := by
      simp [mapcl]
    rw [this]
    refine hnd.map_on fun x hx y hy hxy => ?_
    obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hx
    obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hy
    obtain ⟨i, h, -, hpi, -, -⟩ := hidx p hp
    obtain ⟨j, h', -, hqj, -, -⟩ := hidx q hq
    simp only [hpi, hqj, Option.map_some, Option.getD_some] at hxy
    subst hxy
    exact ((hinv _ _ _ hpi).2 _ _ hqj).symm
  · intro p hp
    obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hp
    obtain ⟨i, h, t, hqi, hit, hpre⟩ := hidx q hq
    exact ⟨t, by simpa [hqi] using hit, hpre⟩

/-- **The on-demand OMPR game is no easier than Def. 3.1**: every on-demand adversary `B` (labelled
targets requested one by one) is matched by the Def. 3.1 adversary `popAdv B`, which is given all
`n` targets and pops them on request, with at least the same advantage. So `advOMPR` (the term of
PomFRIT's U1) is bounded by Def. 3.1's advantage of an explicit adversary. -/
theorem advOMPR_le_ompr31 (n ℓ : ℕ)
    (B : PK → ProbComp (OracleComp (specB AR X Hn T S) (List (X × S)))) :
    advOMPR tr n ℓ B ≤ advOMPR31 tr n ℓ (popAdv B) := by
  have h1 : omExp tr.keyGen tr.D n B =ᵈ
      (fun r => (r.1.1, r.2.2.1, proj31 r.2.1 r.2.2.2)) <$> jointRun tr n B := by
    simp only [omExp, jointRun, map_bind, map_pure]
    refine EvalDistEq.bind_right _ fun kp => EvalDistEq.bind_right _ fun b =>
      EvalDistEq.bind_right _ fun L => ?_
    have := (comb31_eqd (tr.D kp.2) L b (⟨0, fun _ => none⟩, st31)).symm.bind_left
      (fun r => pure (kp.1, r.1, r.2))
    simp only [bind_map_left] at this
    exact this
  have h2 : ompr31Exp tr n (popAdv B) =ᵈ
      (fun r => (r.1.1, r.2.1, mapcl r.2.2, r.2.2.2.2)) <$> jointRun tr n B := by
    simp only [ompr31Exp, jointRun, popAdv, map_bind, map_pure, bind_map_left, simulateQ_map,
      StateT.run_map, collapse31]
    refine EvalDistEq.bind_right _ fun kp => (eqd_swap _ _ _).trans ?_
    refine EvalDistEq.bind_right _ fun b => EvalDistEq.bind_right _ fun L => ?_
    exact EvalDistEq.rfl
  unfold advOMPR advOMPR31
  rw [h1.prEvent_eq, h2.prEvent_eq, prEvent_map, prEvent_map]
  refine prEvent_mono_of_support _ _ _ fun r hr hw => ?_
  simp only [jointRun, mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hr
  obtain ⟨kp, -, b, -, L, -, z, hz, rfl⟩ := hr
  have hinv := simulateQ_run_preservesInv (comb31 (tr.D kp.2) L) Inv31
    (comb31_inv (tr.D kp.2) L) b _ (fun x i h hx => by simp at hx) z hz
  exact wins_imp_win31 tr ℓ kp.1 L z hinv hw

end Def31Red

/-! ## Item 9: A-OMPI(q_T, Q) -/

section OMPI

variable {DR : Type} (AR : DR → Type) (T S : Type)

abbrev AnsI : DR ⊕ (Unit ⊕ ℕ) → Type := Sum.elim AR (Sum.elim (fun _ => Option T) fun _ => Option S)

/-- The A-OMPI adversary's oracles: the world, "new target" (`none` once the `q_T` targets are
used), and the index oracle `i ↦ D(y_i)` (`none` for an index not yet issued). -/
abbrev specI : OracleSpec (DR ⊕ (Unit ⊕ ℕ)) := OracleSpec.ofFn (AnsI AR T S)

/-- The A-OMPI challenger's state: the world's cache, the unused targets, the issued targets (in
order), the opened indices, the number of index queries. -/
structure OMPISt where
  ro : (specR AR).QueryCache
  rest : List T
  ys : List T
  opened : List ℕ
  oq : ℕ

end OMPI

section OMPIImpl

variable {DR : Type} [DecidableEq DR] {AR : DR → Type} [∀ d, SampleableType (AR d)]
  {T S : Type} [SampleableType T]

/-- **The A-OMPI challenger.** -/
def ompiImpl (D : T → S) : QueryImpl (specI AR T S) (StateT (OMPISt AR T) ProbComp)
  | .inl d => StateT.mk fun c =>
      (fun r => (r.1, { c with ro := r.2 })) <$> ((specR AR).randomOracle d).run c.ro
  | .inr (.inl ()) => StateT.mk fun c => pure <| match c.rest with
      | y :: r => (some y, { c with rest := r, ys := c.ys ++ [y] })
      | [] => (none, c)
  | .inr (.inr i) => StateT.mk fun c =>
      pure ((c.ys[i]?).map D, { c with opened := i :: c.opened, oq := c.oq + 1 })

/-- The initial state, with the target stream `L`. -/
def ompi0 (L : List T) : OMPISt AR T := ⟨∅, L, [], [], 0⟩

variable {PK SK : Type} (tr : Trapdoor PK SK T S)

/-- **The A-OMPI experiment** with `q_T` targets. -/
def ompiExp (qT : ℕ) (A : PK → ProbComp (OracleComp (specI AR T S) (ℕ × S))) :
    ProbComp (PK × (ℕ × S) × OMPISt AR T) := do
  let kp ← tr.keyGen
  let a ← A kp.1
  let L ← unifList T qT
  let r ← (simulateQ (ompiImpl (tr.D kp.2)) a).run (ompi0 L)
  pure (kp.1, r.1, r.2)

/-- **The A-OMPI win**: a preimage of an issued, unopened target, within `Q` index queries. -/
def OMPIWin (Q : ℕ) (r : PK × (ℕ × S) × OMPISt AR T) : Prop :=
  ∃ y, r.2.2.ys[r.2.1.1]? = some y ∧ r.2.1.1 ∉ r.2.2.opened ∧ tr.IsPre r.1 r.2.1.2 y ∧ r.2.2.oq ≤ Q

/-- **`Adv^{ompi}(q_T, Q)`.** -/
noncomputable def advOMPI (qT Q : ℕ) (A : PK → ProbComp (OracleComp (specI AR T S) (ℕ × S))) :
    ℝ≥0∞ :=
  Pr{let r ← ompiExp tr qT A}[OMPIWin tr Q r]

end OMPIImpl

/-! ## Semantic-oracle forgers -/

section Sem

variable {D : Type} (R : D → Type) (C Q T A V Out : Type) (H : Q → T) (pv : A → V)

/-- **A forger against a signing oracle in semantic form.** Given the oracle `σ : T → A` (queried
at `H q` for a query `q`) and coins `E : C`, it is a computation over the hash oracles
`OracleSpec.ofFn R` with an output, a signing log and a probe log. `reads`: against every table,
its result is the same for every `σ'` that agrees with `σ` on the signing log and has the same
view `pv` on the probe log. -/
structure SemForger where
  run : (T → A) → C → OracleComp (OracleSpec.ofFn R) (Out × List Q × List Q)
  reads : ∀ (σ σ' : T → A) (E : C) (g : (d : D) → R d),
    (∀ q ∈ (evalWithAnswerFn (QueryImpl.ofFn g) (run σ E)).2.1, σ' (H q) = σ (H q)) →
    (∀ q ∈ (evalWithAnswerFn (QueryImpl.ofFn g) (run σ E)).2.2, pv (σ' (H q)) = pv (σ (H q))) →
    evalWithAnswerFn (QueryImpl.ofFn g) (run σ' E) = evalWithAnswerFn (QueryImpl.ofFn g) (run σ E)

variable {R C Q T A V Out H pv}

/-- A forger that reads a coarser view of the probe answers reads any finer one. -/
def SemForger.refine {V' : Type} (B : SemForger R C Q T A V Out H pv) (pv' : A → V')
    (h : ∀ a b, pv' a = pv' b → pv a = pv b) : SemForger R C Q T A V' Out H pv' where
  run := B.run
  reads σ σ' E g hs hp := B.reads σ σ' E g hs fun q hq => h _ _ (hp q hq)

variable [DecidableEq D] [∀ d, SampleableType (R d)] [SampleableType C]

/-- **The advantage of a semantic forger** against the oracle `σ`: the probability of `Win` over
uniform coins and the lazy random oracle. -/
noncomputable def semAdv (σ : T → A) (B : SemForger R C Q T A V Out H pv)
    (Win : Out × List Q × List Q → Prop) : ℝ≥0∞ :=
  Pr{let E ← $ᵗ C; let r ← (simulateQ randomOracle (B.run σ E)).run' ∅}[Win r]

end Sem

/-! ## Oracle forgers are semantic forgers -/

section Oracle

variable {D : Type} {R : D → Type} {C Q T A V Out : Type} (H : Q → T) (pv : A → V)

/-- An oracle forger's oracles: the hashes `R` and the signer, answering `A` on queries `Q`. -/
abbrev specSig (R : D → Type) (Q A : Type) : OracleSpec (D ⊕ Q) :=
  OracleSpec.ofFn (Sum.elim R fun _ => A)

/-- The hashes forwarded, and the signer `q ↦ σ(H(q))`, logging the signing queries. -/
def sigImpl (σ : T → A) :
    QueryImpl (specSig R Q A) (StateT (List Q) (OracleComp (OracleSpec.ofFn R)))
  | .inl d => StateT.mk fun l => (fun a => (a, l)) <$>
      (liftM ((OracleSpec.ofFn R).query d) : OracleComp (OracleSpec.ofFn R) (R d))
  | .inr q => StateT.mk fun l => pure (σ (H q), l ++ [q])

variable {H}

theorem sigImpl_prefix (σ : T → A) (g : (d : D) → R d) {α : Type} :
    ∀ (oc : OracleComp (specSig R Q A) α) (l : List Q),
      l <+: (evalWithAnswerFn (QueryImpl.ofFn g) ((simulateQ (sigImpl H σ) oc).run l)).2 := by
  intro oc
  induction oc using OracleComp.inductionOn with
  | pure x => intro l; simp
  | query_bind t k ih =>
    intro l
    rcases t with d | q
    · simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, sigImpl, StateT.run_mk,
        evalWithAnswerFn_bind]
      exact ih _ l
    · simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, sigImpl, StateT.run_mk,
        evalWithAnswerFn_bind, evalWithAnswerFn_pure]
      exact (List.prefix_append l [q]).trans (ih _ _)

theorem sigImpl_reads (σ σ' : T → A) (g : (d : D) → R d) {α : Type} :
    ∀ (oc : OracleComp (specSig R Q A) α) (l : List Q),
      (∀ q ∈ (evalWithAnswerFn (QueryImpl.ofFn g) ((simulateQ (sigImpl H σ) oc).run l)).2,
        σ' (H q) = σ (H q)) →
      evalWithAnswerFn (QueryImpl.ofFn g) ((simulateQ (sigImpl H σ') oc).run l) =
        evalWithAnswerFn (QueryImpl.ofFn g) ((simulateQ (sigImpl H σ) oc).run l) := by
  intro oc
  induction oc using OracleComp.inductionOn with
  | pure x => intro l _; simp
  | query_bind t k ih =>
    intro l h
    rcases t with d | q
    · simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, sigImpl, StateT.run_mk,
        evalWithAnswerFn_bind] at h ⊢
      exact ih _ l h
    · simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, sigImpl, StateT.run_mk,
        evalWithAnswerFn_bind, evalWithAnswerFn_pure] at h ⊢
      have hq : σ' (H q) = σ (H q) :=
        h q ((sigImpl_prefix σ g _ _).subset (List.mem_append_right l (List.mem_singleton_self q)))
      rw [hq]
      exact ih _ _ h

/-- **An oracle forger as a semantic forger** (no probe): it gets the signer as an oracle, and its
signing log is the list of its signing queries, as the challenger records it. Its advantage is the
oracle game's (`semAdv` of `ofOracle B` is, by definition, the probability that `B` wins against
the logging signer). -/
def ofOracle (B : C → OracleComp (specSig R Q A) Out) : SemForger R C Q T A V Out H pv where
  run σ E := (fun r => (r.1, r.2, [])) <$> (simulateQ (sigImpl H σ) (B E)).run []
  reads σ σ' E g hs _ := by
    simp only [evalWithAnswerFn_map] at hs ⊢
    rw [sigImpl_reads σ σ' g (B E) [] hs]

end Oracle

/-! ## Items 10 and 11: CT-UF_K and CT-UF^open_K -/

section CTUF

variable {D : Type} {R : D → Type} {C : Type} {K : ℕ} {T A S Xc : Type}

/-- The `K` signers as one oracle on `(k, t)`. -/
def signers {SK : Type} (Dsk : SK → T → A) (sk : Fin K → SK) : Fin K × T → A :=
  fun p => Dsk (sk p.1) p.2

/-- A CT-UF forger's output: a forgery `(k, x*, s*)` and the openings of the signed targets (for
CT-UF^open; ignored by CT-UF). -/
abbrev CTOut (K : ℕ) (S Xc : Type) := Option (Fin K × Xc × S) × List Xc

/-- **A CT-UF forger** against `K` signers on arbitrary targets: its signing log is the list of
queried `(k, t)`; it has no probe. -/
abbrev CTForger (R : D → Type) (C : Type) (K : ℕ) (T A S Xc : Type) :=
  SemForger R C (Fin K × T) (Fin K × T) A Unit (CTOut K S Xc) id fun _ => ()

variable (V : Fin K → S → T → Prop) (Com : Xc → T) (DCom : Xc → Prop)

/-- **The CT-UF win** (item 10): `(k, x*, s*)` with `x* ∈ D_Com`, `P_k(s*) = Com(x*)`, and
`Com(x*)` never queried to any signer. -/
def CTWin (r : CTOut K S Xc × List (Fin K × T) × List (Fin K × T)) : Prop :=
  ∃ k x s, r.1.1 = some (k, x, s) ∧ DCom x ∧ V k s (Com x) ∧ ∀ q ∈ r.2.1, q.2 ≠ Com x

/-- **The CT-UF^open win** (item 11): the CT-UF win, and an opening in `D_Com` of every queried
target. -/
def CTOpenWin (r : CTOut K S Xc × List (Fin K × T) × List (Fin K × T)) : Prop :=
  CTWin V Com DCom r ∧ ∀ q ∈ r.2.1, ∃ x ∈ r.1.2, DCom x ∧ Com x = q.2


/-- **The CT-UF win with freshness up to a relation** `cls` (CT-UF^×, `uov-open-reductions.md`):
no signed target is in the class of `Com(x*)`. For UOV, `cls t t' ↔ ∃ μ ≠ 0, t = μ • t'` (the
public map is homogeneous quadratic and every `GF(256)` element is a square). -/
def CTXWin (cls : T → T → Prop) (r : CTOut K S Xc × List (Fin K × T) × List (Fin K × T)) : Prop :=
  ∃ k x s, r.1.1 = some (k, x, s) ∧ DCom x ∧ V k s (Com x) ∧ ∀ q ∈ r.2.1, ¬cls q.2 (Com x)

/-- With a reflexive class relation, a CT-UF^× win is a CT-UF win. -/
theorem ctWin_of_ctxWin {cls : T → T → Prop} (hrefl : ∀ t, cls t t)
    {r : CTOut K S Xc × List (Fin K × T) × List (Fin K × T)} (h : CTXWin V Com DCom cls r) :
    CTWin V Com DCom r := by
  obtain ⟨k, x, s, h1, h2, h3, h4⟩ := h
  exact ⟨k, x, s, h1, h2, h3, fun q hq he => h4 q hq (he ▸ hrefl _)⟩

variable [DecidableEq D] [∀ d, SampleableType (R d)] [SampleableType C]

/-- **`Adv^{ct-uf}_K`** at fixed keys (the signers `σ`, the verification `V`). -/
noncomputable def advCTUFAt (σ : Fin K × T → A) (B : CTForger R C K T A S Xc) : ℝ≥0∞ :=
  semAdv σ B (CTWin V Com DCom)

/-- **`Adv^{ct-uf-open}_K`** at fixed keys. -/
noncomputable def advCTUFOpenAt (σ : Fin K × T → A) (B : CTForger R C K T A S Xc) : ℝ≥0∞ :=
  semAdv σ B (CTOpenWin V Com DCom)


/-- **`Adv^{ct-uf-×}_K`** at fixed keys (freshness up to `cls`). -/
noncomputable def advCTUFXAt (cls : T → T → Prop) (σ : Fin K × T → A)
    (B : CTForger R C K T A S Xc) : ℝ≥0∞ :=
  semAdv σ B (CTXWin V Com DCom cls)

theorem advCTUFXAt_le {cls : T → T → Prop} (hrefl : ∀ t, cls t t) (σ : Fin K × T → A)
    (B : CTForger R C K T A S Xc) :
    advCTUFXAt V Com DCom cls σ B ≤ advCTUFAt V Com DCom σ B :=
  prEvent_bind_mono_of_support _ _ _ fun _ _ =>
    prEvent_mono _ _ _ fun _ h => ctWin_of_ctxWin V Com DCom hrefl h

/-- **The one-query forger of a rescaling attack**: it asks the signer of key `k` at `y` and
outputs `(k, x, resc s')` for the answer `s'`. -/
def scaleForger {S' : Type} (k : Fin K) (x : Xc) (y : T) (resc : S' → S) :
    CTForger R C K T (Option S') S Xc where
  run σ _ := pure (((σ (k, y)).map fun s' => (k, x, resc s'), []), [(k, y)], [])
  reads σ σ' E g hs _ := by
    simp only [evalWithAnswerFn_pure, List.mem_singleton, forall_eq] at hs ⊢
    simp only [id] at hs
    rw [hs]

/-- **CT-UF is broken by a rescaling attack** whenever the answer at a query `y ≠ Com(x)` can be
rescaled into a preimage of `Com(x)`: the forger `scaleForger` wins with probability 1. (For UOV,
`y = μ • Com(x)`, `resc s' = (μ⁻¹)^128 • s'`: `Spec.Pqov.ctuf_scaling_attack`; see
`Assumptions/UOVLinks.lean`, `ctuf_pqov_broken`.) -/
theorem advCTUFAt_scaleForger {S' : Type} (σ : Fin K × T → Option S') (k : Fin K) (x : Xc) (y : T)
    (resc : S' → S) (s' : S') (hσ : σ (k, y) = some s') (hD : DCom x) (hV : V k (resc s') (Com x))
    (hy : y ≠ Com x) :
    advCTUFAt V Com DCom σ (scaleForger (R := R) (C := C) k x y resc) = 1 := by
  have hw : CTWin V Com DCom ((((σ (k, y)).map fun s' => (k, x, resc s'), []), [(k, y)], []) :
      CTOut K S Xc × List (Fin K × T) × List (Fin K × T)) :=
    ⟨k, x, resc s', by simp [hσ], hD, hV, by simpa using hy⟩
  unfold advCTUFAt semAdv
  simp [scaleForger, hw]

/-- CT-UF^open is a restriction of CT-UF: the same forger wins less often. -/
theorem advCTUFOpenAt_le (σ : Fin K × T → A) (B : CTForger R C K T A S Xc) :
    advCTUFOpenAt V Com DCom σ B ≤ advCTUFAt V Com DCom σ B :=
  prEvent_bind_mono_of_support _ _ _ fun _ _ => prEvent_mono _ _ _ fun _ h => h.1

variable {PK SK : Type}

/-- **`Adv^{ct-uf}_K`** over `K` keys (`keys`, e.g. `K` independent runs of `keyGen`), the forger
chosen from the public keys. -/
noncomputable def advCTUF (keys : ProbComp (Fin K → PK × SK)) (P : PK → S → T → Prop)
    (Dsk : SK → T → A) (B : (Fin K → PK) → CTForger R C K T A S Xc) : ℝ≥0∞ :=
  Pr{let ks ← keys; let E ← $ᵗ C; let r ← (simulateQ randomOracle
    ((B fun k => (ks k).1).run (signers Dsk fun k => (ks k).2) E)).run' ∅}[
      CTWin (fun k => P (ks k).1) Com DCom r]

/-- **`Adv^{ct-uf-open}_K`** over `K` keys. -/
noncomputable def advCTUFOpen (keys : ProbComp (Fin K → PK × SK)) (P : PK → S → T → Prop)
    (Dsk : SK → T → A) (B : (Fin K → PK) → CTForger R C K T A S Xc) : ℝ≥0∞ :=
  Pr{let ks ← keys; let E ← $ᵗ C; let r ← (simulateQ randomOracle
    ((B fun k => (ks k).1).run (signers Dsk fun k => (ks k).2) E)).run' ∅}[
      CTOpenWin (fun k => P (ks k).1) Com DCom r]

theorem advCTUFOpen_le (keys : ProbComp (Fin K → PK × SK)) (P : PK → S → T → Prop)
    (Dsk : SK → T → A) (B : (Fin K → PK) → CTForger R C K T A S Xc) :
    advCTUFOpen Com DCom keys P Dsk B ≤ advCTUF Com DCom keys P Dsk B :=
  prEvent_bind_mono_of_support _ _ _ fun _ _ => prEvent_bind_mono_of_support _ _ _ fun _ _ =>
    prEvent_mono _ _ _ fun _ h => h.1

end CTUF

/-! ## Item 12: UF-Tag, and UF-Tag with a signability probe -/

section UFTag

variable {D : Type} {R : D → Type} {C Q T S S' : Type}

/-- **A UF-Tag forger with a signability probe**: the oracle `q ↦ σ(H(q))`; at the points of its
probe log it learns only whether `σ` succeeds. -/
abbrev ProbeForger (R : D → Type) (C Q T S S' : Type) (H : Q → T) :=
  SemForger R C Q T (Option S') Bool (Option (Q × S)) H Option.isSome

/-- **A UF-Tag forger** (no probe: the probe log is not read). -/
abbrev TagForger (R : D → Type) (C Q T S S' : Type) (H : Q → T) :=
  SemForger R C Q T (Option S') Unit (Option (Q × S)) H fun _ => ()

variable (V : S → T → Prop) (H : Q → T) (σ : T → Option S')

/-- **The UF-Tag win**: a preimage of `H(m*)` for an `m*` none of whose signing queries was
answered (`σ(H(m*))` failed). -/
def UFWin (r : Option (Q × S) × List Q × List Q) : Prop :=
  ∃ m s, r.1 = some (m, s) ∧ V s (H m) ∧ ∀ q ∈ r.2.1, q = m → σ (H m) = none

variable [DecidableEq D] [∀ d, SampleableType (R d)] [SampleableType C]

/-- **`Adv^{uf-tag}`** at a fixed key. -/
noncomputable def advUFTagAt (B : TagForger R C Q T S S' H) : ℝ≥0∞ :=
  semAdv σ B (UFWin V H σ)

/-- **`Adv^{uf-tag+probe}`** at a fixed key. -/
noncomputable def advUFTagProbeAt (B : ProbeForger R C Q T S S' H) : ℝ≥0∞ :=
  semAdv σ B (UFWin V H σ)

/-- A UF-Tag forger is a forger with a probe it does not read. -/
def TagForger.toProbe (B : TagForger R C Q T S S' H) : ProbeForger R C Q T S S' H :=
  B.refine Option.isSome fun _ _ _ => rfl

/-- **UF-Tag is UF-Tag with a probe restricted to forgers that do not read it.** -/
theorem advUFTagAt_eq_probe (B : TagForger R C Q T S S' H) :
    advUFTagAt V H σ B = advUFTagProbeAt V H σ B.toProbe := rfl

variable {PK SK : Type}

/-- **`Adv^{uf-tag+probe}`** over `keyGen`, with the public map `P` and the signer `Dsk`. -/
noncomputable def advUFTagProbe (keyGen : ProbComp (PK × SK)) (P : PK → S → T → Prop)
    (Dsk : SK → T → Option S') (B : PK → ProbeForger R C Q T S S' H) : ℝ≥0∞ :=
  Pr{let kp ← keyGen; let E ← $ᵗ C; let r ← (simulateQ randomOracle
    ((B kp.1).run (Dsk kp.2) E)).run' ∅}[UFWin (P kp.1) H (Dsk kp.2) r]

/-- **`Adv^{uf-tag}`** over `keyGen`. -/
noncomputable def advUFTag (keyGen : ProbComp (PK × SK)) (P : PK → S → T → Prop)
    (Dsk : SK → T → Option S') (B : PK → TagForger R C Q T S S' H) : ℝ≥0∞ :=
  advUFTagProbe H keyGen P Dsk fun pk => (B pk).toProbe

end UFTag

/-! ## n-target UOV from single-target UOV, by embedding -/

section NTarget

variable {PK SK T S : Type} (tr : Trapdoor PK SK T S) [SampleableType T]

/-- **The embedding at position `i`**: a single-target adversary that draws the other targets
itself and puts its own at `i`. -/
def embedAt {n : ℕ} (i : Fin n) (A : PK → (Fin n → T) → ProbComp S) (pk : PK) (t : T) :
    ProbComp S := do
  let ts ← unifVec T n
  A pk (Function.update ts i t)

lemma bind_unused {α β : Type} (mx : ProbComp α) (my : ProbComp β) :
    (mx >>= fun _ => my) =ᵈ my := by
  let : MeasurableSpace β := ⊤
  exact EvalDistEq.of_evalDist_eq (OracleComp.evalDist_bind_const mx my)

/-- **Replacing one coordinate of uniform targets by a fresh uniform target keeps them
uniform.** -/
theorem unifVec_update : ∀ {n : ℕ} (i : Fin n) {β : Type} (f : (Fin n → T) → ProbComp β),
    (do let t ← $ᵗ T; let ts ← unifVec T n; f (Function.update ts i t)) =ᵈ
      (do let ts ← unifVec T n; f ts)
  | 0, i, _, _ => i.elim0
  | n + 1, i, β, f => by
    refine Fin.cases ?_ (fun j => ?_) i
    · simp only [unifVec, bind_assoc, pure_bind, Fin.update_cons_zero]
      refine EvalDistEq.bind_right _ fun t => ?_
      exact bind_unused _ _
    · simp only [unifVec, bind_assoc, pure_bind, ← Fin.cons_update]
      refine (eqd_swap _ _ _).trans (EvalDistEq.bind_right _ fun a => ?_)
      exact unifVec_update j fun v => f (Fin.cons a v)

/-- The `n`-target experiment's outcome. -/
def nComp (n : ℕ) (A : PK → (Fin n → T) → ProbComp S) : ProbComp ((PK × SK) × (Fin n → T) × S) :=
  tr.keyGen >>= fun kp => unifVec T n >>= fun ts => A kp.1 ts >>= fun s => pure (kp, ts, s)

/-- The embedding's experiment, with the embedded vector as part of the outcome. -/
def eComp {n : ℕ} (i : Fin n) (A : PK → (Fin n → T) → ProbComp S) :
    ProbComp ((PK × SK) × (Fin n → T) × S) :=
  tr.keyGen >>= fun kp => ($ᵗ T) >>= fun t => unifVec T n >>= fun ts =>
    A kp.1 (Function.update ts i t) >>= fun s => pure (kp, Function.update ts i t, s)

/-- **`n`-target UOV is at most the sum of `n` single-target advantages** (of the embeddings),
so `Adv^{uov-n} ≤ n · max_i Adv^{uov}(embedAt i A)`. -/
theorem advUOVn_le_sum (n : ℕ) (A : PK → (Fin n → T) → ProbComp S) :
    advUOVn tr n A ≤ ∑ i : Fin n, advUOV tr (embedAt i A) := by
  have hm : advUOVn tr n A = Pr{let r ← nComp tr n A}[∃ i, tr.IsPre r.1.1 r.2.2 (r.2.1 i)] := by
    simp [advUOVn, nComp, map_bind]
  rw [hm]
  refine (prEvent_exists_le _ _).trans (Finset.sum_le_sum fun i _ => le_of_eq ?_)
  have hi : advUOV tr (embedAt i A) = Pr{let r ← eComp tr i A}[tr.IsPre r.1.1 r.2.2 (r.2.1 i)] := by
    simp [advUOV, embedAt, eComp, map_bind]
  rw [hi]
  refine (EvalDistEq.prEvent_eq ?_ _).symm
  unfold eComp nComp
  refine EvalDistEq.bind_right _ fun kp => ?_
  exact unifVec_update i fun ts => A kp.1 ts >>= fun s => pure (kp, ts, s)

end NTarget

/-! ## Sanity: the trivial attacks lose

Each win excludes the attack that returns an oracle answer: a one-more claim set needs more claims
than preimage queries, an A-OMPI or det-FDH forgery must be on an unopened index or unsigned
message, a CT-UF forgery on an unsigned target, a UF-Tag forgery on a pair whose signing query was
not answered. (That the games can be won at all, and that their hypotheses hold for the real
objects, is in `Audit/Nonvacuous.lean`.) -/

section Sanity

/-- An OMPR outcome with more than `ℓ` preimage queries is not a win. -/
theorem not_wins_of_iq {DR : Type} {AR : DR → Type} {X Hn G S PK : Type} (ℓ : ℕ)
    (good : PK → S → Option (G × Hn) → Prop) (pk : PK) (cl : List (X × S)) (c : Ch AR X Hn G)
    (h : ℓ < c.iq) : ¬Wins ℓ good pk cl c :=
  fun hw => absurd hw.2.2.1 (by omega)

/-- An A-OMPI forgery on an opened index is not a win. -/
theorem not_ompiWin_of_opened {DR : Type} {AR : DR → Type} {T S PK SK : Type}
    (tr : Trapdoor PK SK T S) (Q : ℕ) (r : PK × (ℕ × S) × OMPISt AR T)
    (h : r.2.1.1 ∈ r.2.2.opened) : ¬OMPIWin tr Q r :=
  fun ⟨_, _, hn, _⟩ => hn h

/-- A det-FDH forgery on a signed message is not a win. -/
theorem not_fdhWin_of_signed {DR : Type} {AR : DR → Type} {M T S PK SK : Type}
    (tr : Trapdoor PK SK T S) (qH qS : ℕ) (r : PK × (M × S) × T × FDHSt AR M T)
    (h : r.2.1.1 ∈ r.2.2.2.signed) : ¬FDHWin tr qH qS r :=
  fun hw => hw.1 h

/-- A CT-UF forgery whose commitment was signed (under any key) is not a win. -/
theorem not_ctWin_of_signed {K : ℕ} {T S Xc : Type} (V : Fin K → S → T → Prop) (Com : Xc → T)
    (DCom : Xc → Prop) (o : CTOut K S Xc) (log pl : List (Fin K × T))
    (h : ∀ k x s, o.1 = some (k, x, s) → ∃ q ∈ log, q.2 = Com x) :
    ¬CTWin V Com DCom (o, log, pl) := by
  rintro ⟨k, x, s, ho, -, -, hn⟩
  obtain ⟨q, hq, he⟩ := h k x s ho
  exact hn q hq he

/-- A UF-Tag forgery on a pair whose signing query was answered is not a win. -/
theorem not_ufWin_of_answered {Q T S S' : Type} (V : S → T → Prop) (H : Q → T)
    (σ : T → Option S') (m : Q) (s : S) (log pl : List Q) (hm : m ∈ log)
    (ha : (σ (H m)).isSome) : ¬UFWin V H σ (some (m, s), log, pl) := by
  rintro ⟨m', s', ho, -, hn⟩
  simp only [Option.some.injEq, Prod.mk.injEq] at ho
  obtain ⟨rfl, rfl⟩ := ho
  rw [hn m hm rfl] at ha
  exact absurd ha (by simp)

end Sanity

end VoleMole.Assumptions.UOV
