import VoleMole.Privacy.RatatouilleLean
import VoleMole.ZK.ReadsRO

/-!
# Ratatouille unlinkability in the random-oracle and ideal-cipher model

`Privacy.Ratatouille.unlinkability` (`Privacy/Ratatouille.lean`) assumes zero knowledge against
distinguishers that see the proofs only. Here the Issuer's guess also sees the random tables, as in
`ZK.Sim.zk_rom_ic_h23_num`, and the four proofs of the game (two issuance requests, two spends)
share them. The structure is `Privacy/MoussakaRO.lean`'s:

* **Tables**: `ShR = Tab2G pI × Tab5F × Cipher` (issuance and spend proofs both have
  `qsDegree = 9`), one `H₃` slice per proof (`SlicesR`). The Issuer (`AdversaryRO`) chooses its
  key, context, balance, responses and amounts without reading the tables (the zero-knowledge
  theorem is for statements fixed before the tables); its guess reads them, with a `Budget`.
* **The game** (`viewR`, `gameR`): each slot has an output on the tables the game runs on, an
  `H₂³` programming and its slice. Round 1's spend programs only if round 1 runs (`ok₁`), round 2's
  only if both rounds run, so that a programmed point never depends on a world's hidden choice.
* **The simulated world is `Ratatouille.view` for an adversary that sees the programmed tables**
  (`simGameR_iff`): the programmed tables are a function of the requests the Issuer sees and the
  simulator coins (`Vtab`: a simulation's programming reads its statement only when it produced a
  proof, `hprogI`, `hprogS`, and then the statement is in the request, `issueReqC_mk`,
  `parse_toBytes`). So `Ratatouille.simGame_iff`, `idealGame_iff` and `stage_ideal` apply verbatim
  to the adversary `A.at (Vtab co t) sl` (coins and tables fixed), and the hiding hop and the
  exchange of the nullifiers (`idealGameR_eq`) are those of `Ratatouille.unlinkability`, with the
  coins and the tables fixed.
* **The hops** (`hopI0R`, `hopI1R`, `hopS1R`, `hopS2R`, `Privacy.hop_ro`): each costs the
  zero-knowledge error at its reduction's budget and, except the first, a programming collision
  term (`deltaI1R`, `deltaS1R`, `deltaS2R`; bounded in `Privacy/RatatouilleDelta.lean`).

**`unlinkabilityRO`** (any proof systems) and **`unlinkabilityRO_lean`** (the Lean prover, SHAKE):

    |Pr[world (b₁, b₂)] − Pr[world (b₁', b₂')]| ≤ 8·εRO(q₃, q₅ + 3·624, q_E + 3·4607)
      + Σ over both worlds (δI₁ + δS₁ + δS₂) + 2·εhide.

**Cipher rows.** Everything here is stated for every type of cipher rows `R` (the shared
tables `ZK.Sim.ShG R p`, `ZK/ReadsRO.lean`) with `ZKRow R`; `unlinkabilityRO_leanG` is the generic
Lean-prover bound and `unlinkabilityRO_lean` its instance at function rows (`Blk → Blk`, the PRF
view); `Privacy/PermRO.lean` instantiates it at permutation rows (AES as uniformly random
permutations, the adversary reading whole rows: forward and inverse queries).
-/

open Finset

-- (The coin types are large products: their `Fintype` instances exceed the default size.)
set_option synthInstance.maxSize 1024

set_option linter.unusedSectionVars false

namespace VoleMole.Privacy.Ratatouille

open VoleMole.Spec.Ratatouille VoleMole.ZK.Sim

variable {Z : Sizes} {R : Type} [Fintype R] [Nonempty R]

/-! ## The model -/

/-- **The tables the four proofs share.** -/
abbrev ShR (R : Type) := ShG R pI

/-- The four proofs' `H₃` slices: issuance `0`, `1`; spend `1`, `2`. -/
abbrev SlicesR := Quad Tab3

/-- The round-1 and round-2 requests the Issuer's guess sees. -/
abbrev Rounds (Z : Sizes) :=
  Option (Except Error (SpendRequest Z) × Option (Except Error (SpendRequest Z)))

/-- **The malicious Issuer in the random-oracle model**: `Adversary`'s interaction, which does not
read the tables, and a guess that sees all of them. -/
structure AdversaryRO (R : Type) (Z : Sizes) where
  pk : PublicKey
  ctx : Context
  tInit : Credits
  respondIss : IssTr Z → Bool → Preimage
  d₁ : IssTr Z → Credits
  respond₁ : IssTr Z → Except Error (SpendRequest Z) → SpendResponse
  d₂ : IssTr Z → Except Error (SpendRequest Z) → Credits
  guess : IssTr Z → Rounds Z → SlicesR → ShR R → Prop

/-- The interaction as an `Adversary` (its guess is not used). -/
def AdversaryRO.base (A : AdversaryRO R Z) : Adversary Z :=
  ⟨A.pk, A.ctx, A.tInit, A.respondIss, A.d₁, A.respond₁, A.d₂, fun _ _ => True⟩

/-- **The adversary as an `Adversary` that sees the tables `V tr y` and the slices `sl`.** -/
def AdversaryRO.at (A : AdversaryRO R Z) (V : IssTr Z → Rounds Z → ShR R) (sl : SlicesR) : Adversary Z :=
  ⟨A.pk, A.ctx, A.tInit, A.respondIss, A.d₁, A.respond₁, A.d₂, fun tr y => A.guess tr y sl (V tr y)⟩

/-- **The Issuer's budget**: its guess reads each `H₃` slice at `q3` keys, `H₅` at `q5` and the
cipher at `qE` keys (each with everything else fixed), and `H₂³` freely. -/
structure AdversaryRO.Budget (A : AdversaryRO R Z) (q3 q5 qE : ℕ) : Prop where
  h30 : ∀ tr y (g₁ g₂ g₃ : Tab3) s, Rd3 (fun g => A.guess tr y ((g, g₁), (g₂, g₃)) s) q3
  h31 : ∀ tr y (g₀ g₂ g₃ : Tab3) s, Rd3 (fun g => A.guess tr y ((g₀, g), (g₂, g₃)) s) q3
  h32 : ∀ tr y (g₀ g₁ g₃ : Tab3) s, Rd3 (fun g => A.guess tr y ((g₀, g₁), (g, g₃)) s) q3
  h33 : ∀ tr y (g₀ g₁ g₂ : Tab3) s, Rd3 (fun g => A.guess tr y ((g₀, g₁), (g₂, g)) s) q3
  h5 : ∀ tr y sl, Rd5 (A.guess tr y sl) q5
  hE : ∀ tr y sl, RdE (A.guess tr y sl) qE

variable (A : AdversaryRO R Z)

/-- An issuance slot: its output on the tables, its programming, its `H₃` slice. -/
structure IssSlotR (R : Type) (Z : Sizes) where
  out : ShR R → IssOut Z TokenS
  prog : ShR R → ShR R
  slice : Tab3

/-- A spend slot: its output at a token and an amount on the tables, its programming (given
whether its round runs), its `H₃` slice. -/
structure SpSlotR (R : Type) (Z : Sizes) where
  out : TokenS → Credits → ShR R → SpOut Z TokenS
  prog : Bool → TokenS → Credits → ShR R → ShR R
  slice : Tab3

/-- **The view in world `(b₁, b₂)`** from four slots and the tables `t`: the issuances on `t`
programmed by the issuance slots; round 1 (and round 2) at `t` programmed by all slots, a spend
slot programming only if its round runs (decided on a provisional round 1 on the issuance tables:
a simulated round 1 does not read the tables). -/
def viewR (b₁ b₂ : Bool) (s₀ s₁ : IssSlotR R Z) (h₁ h₂ : SpSlotR R Z) (t : ShR R) : Prop :=
  let u := s₀.prog (s₁.prog t)
  let i₀ := s₀.out u
  let i₁ := s₁.out u
  let tr : IssTr Z := (i₀.req, i₁.req)
  let tk₀ := i₀.fin (A.respondIss tr false)
  let tk₁ := i₁.fin (A.respondIss tr true)
  let τ₁ := tokD (tokIface A.base) tk₀ tk₁ b₁
  let ok1 := ok₁ A.base (tokIface A.base) tr tk₀ tk₁
  let o₁' := h₁.out τ₁ (A.d₁ tr) u
  let ch' := o₁'.fin (A.respond₁ tr o₁'.req)
  let ok2' := ok₂ A.base (tokIface A.base) b₁ tr tk₀ tk₁ o₁'.req ch'
  let v := s₀.prog (s₁.prog (h₁.prog ok1 τ₁ (A.d₁ tr)
    (h₂.prog (ok1 && ok2') (cur₂ (tokIface A.base) b₁ b₂ tk₀ tk₁ ch') (A.d₂ tr o₁'.req) t)))
  let o₁ := h₁.out τ₁ (A.d₁ tr) v
  let ch := o₁.fin (A.respond₁ tr o₁.req)
  let o₂ := h₂.out (cur₂ (tokIface A.base) b₁ b₂ tk₀ tk₁ ch) (A.d₂ tr o₁.req) v
  A.guess tr (bif ok1 then
      some (o₁.req, bif ok₂ A.base (tokIface A.base) b₁ tr tk₀ tk₁ o₁.req ch then some o₂.req
        else none) else none)
    ((s₀.slice, s₁.slice), (h₁.slice, h₂.slice)) v

/-- The game with the slots drawn from their parts of the tape. -/
def gameR {T₀ T₁ T₂ T₃ : Type} (b₁ b₂ : Bool) (g₀ : T₀ → IssSlotR R Z) (g₁ : T₁ → IssSlotR R Z)
    (k₁ : T₂ → SpSlotR R Z) (k₂ : T₃ → SpSlotR R Z) (x : ((T₀ × T₁) × (T₂ × T₃)) × ShR R) : Prop :=
  viewR A b₁ b₂ (g₀ x.1.1.1) (g₁ x.1.1.2) (k₁ x.1.2.1) (k₂ x.1.2.2) x.2

/-! ## The slots -/

/-- An issuance prover of the random-oracle model: the proof (or `none`) of `w` for `x` with
randomness `ρ`, the proof's `H₃` slice and the shared tables. -/
abbrev ProverI (R : Type) (Z : Sizes) := IssueInstance → IssueWitness → Rho → Tab3 → ShR R → Option (IssueProof Z)

/-- A spend prover of the random-oracle model. -/
abbrev ProverS (R : Type) (Z : Sizes) := SpendInstance → SpendWitness → Rho → Tab3 → ShR R → Option (SpendProof Z)

/-- The issuance prover with the tables fixed, as the spec's primitives (the rest unused). -/
def primI (PI : ProverI R Z) (g : Tab3) (s : ShR R) : Prim Z Empty :=
  ⟨fun e => e.elim, fun e => e.elim, fun x w ρ => PI x w ρ g s, fun _ _ => true,
    fun _ _ _ => none, fun _ _ => true⟩

/-- The spend prover with the tables fixed, as the spec's primitives. -/
def primS (PS : ProverS R Z) (g : Tab3) (s : ShR R) : Prim Z Empty :=
  ⟨fun e => e.elim, fun e => e.elim, fun _ _ _ => none, fun _ _ => true,
    fun x w ρ => PS x w ρ g s, fun _ _ => true⟩

/-- The coins `(nf, r)` of an issuance or a spend. -/
abbrev NRR := Coins 24 × Coins 16

/-- A real slot's tape: `(nf, r)`, the prover's randomness and its `H₃` slice. -/
abbrev TRe := NRR × (Coins 16 × Tab3)

/-- **A real issuance**: the spec's `issue_request_with_seed` with the prover on the tables. -/
def issRealR (PI : ProverI R Z) (x : TRe) : IssSlotR R Z :=
  ⟨fun s => issOutOf A.base (issueOf (primI PI x.2.2 s) A.tInit A.ctx (vec x.1.1) (vec x.1.2)
    (vec x.2.1)), fun s => s, x.2.2⟩

/-- **A real spend**: the spec's `spend_request_with_seed` with the prover on the tables. -/
def spRealR (PS : ProverS R Z) (x : TRe) : SpSlotR R Z :=
  ⟨fun τ d s => spOutOf A.base (spendOf (primS PS x.2.2 s) A.pk (some τ) d A.ctx (vec x.1.1)
    (vec x.1.2) (vec x.2.1)).2, fun _ _ _ s => s, x.2.2⟩

/-- **The real game in the random-oracle model.** -/
def realGameR (PI : ProverI R Z) (PS : ProverS R Z) (b₁ b₂ : Bool) :
    ((TRe × TRe) × (TRe × TRe)) × ShR R → Prop :=
  gameR A b₁ b₂ (issRealR A PI) (issRealR A PI) (spRealR A PS) (spRealR A PS)

variable {CI CS : Type} (simI : IssueInstance → CI → Option (IssueProof Z))
  (simS : SpendInstance → CS → Option (SpendProof Z))
  (progI : IssueInstance → CI → ShR R → ShR R) (progS : SpendInstance → CS → ShR R → ShR R)

/-- The issuance instance of the coins `(nf, r)`. -/
def xIOf (n : NRR) : IssueInstance := ⟨com (vec n.1) A.ctx A.tInit (vec n.2), A.tInit, A.ctx⟩

/-- The spend instance of the coins `(nf', r')` at a token and an amount (the Client's new balance
`t'` from its check; `0` where the check fails and nothing is proved). -/
def xSOf (n : NRR) (τ : TokenS) (d : Credits) : SpendInstance :=
  ⟨A.pk, τ.nf, d, com (vec n.1) A.ctx ((clientCheck τ.t τ.x d).getD 0) (vec n.2), A.ctx⟩

/-- **A simulated issuance**: the simulated request, and the programming (none if `T_init = 0`:
nothing is proved). -/
def issSimR (x : NRR × (CI × Tab3)) : IssSlotR R Z :=
  ⟨fun _ => issSim A.base simI (x.1.1, x.1.2, x.2.1),
    fun s => if A.tInit = 0 then s else progI (xIOf A x.1) x.2.1 s, x.2.2⟩

/-- **A simulated spend**: the Client's checks and a simulated proof, and the programming if its
round runs. -/
def spSimR (x : NRR × (CS × Tab3)) : SpSlotR R Z :=
  ⟨fun τ d _ => spSim A.base simS (x.1.1, x.1.2, x.2.1) τ d,
    fun ok τ d s => if ok = true then progS (xSOf A x.1 τ d) x.2.1 s else s, x.2.2⟩

/-- The simulated tapes. -/
abbrev TIsR (CI : Type) := NRR × (CI × Tab3)
abbrev TSsR (CS : Type) := NRR × (CS × Tab3)

/-- The game with all four proofs simulated. -/
def simGameR (b₁ b₂ : Bool) : ((TIsR CI × TIsR CI) × (TSsR CS × TSsR CS)) × ShR R → Prop :=
  gameR A b₁ b₂ (issSimR A simI progI) (issSimR A simI progI) (spSimR A simS progS)
    (spSimR A simS progS)

/-! ## The simulated world as `Ratatouille.view` for an adversary that sees the tables -/

/-- A commitment where none is needed. -/
def dummyC : Commitment := Vector.ofFn fun _ => 0

/-- **An issuance simulation's programming from its request**: the instance's commitment is the
request's (a simulation that produced no proof programs independently of the instance,
`hprogI`). -/
def progIm (c : CI) (req : Except Error (IssueRequest Z)) (s : ShR R) : ShR R :=
  if A.tInit = 0 then s else match req with
    | .ok q => progI ⟨issueReqC q, A.tInit, A.ctx⟩ c s
    | .error _ => progI ⟨dummyC, A.tInit, A.ctx⟩ c s

/-- **A spend simulation's programming from its request** (the instance is the request's
nullifier, amount and new commitment). -/
def progSm (c : CS) (rq : Except Error (SpendRequest Z)) (s : ShR R) : ShR R :=
  match rq with
  | .ok q => progS ⟨A.pk, (SpendReq.parse q).nf, (SpendReq.parse q).d, (SpendReq.parse q).cNext,
      A.ctx⟩ c s
  | .error _ => progS ⟨A.pk, nf0, 0, dummyC, A.ctx⟩ c s

/-- **The programmed tables as a function of what the Issuer sees** (the requests and the rounds)
and of the simulator coins: the issuances' programming, round 1's if it runs, round 2's if it
runs. -/
def Vtab (co : (CI × CI) × (CS × CS)) (t : ShR R) (tr : IssTr Z) (y : Rounds Z) : ShR R :=
  progIm A progI co.1.1 tr.1 (progIm A progI co.1.2 tr.2 (match y with
    | none => t
    | some (rq, y₂) => progSm A progS co.2.1 rq (match y₂ with
      | none => t
      | some r₂ => progSm A progS co.2.2 r₂ t)))

lemma ok_of_ok₁ {B : Adversary Z} {tr : IssTr Z} {tk₀ tk₁ : Option TokenS} (b₁ : Bool)
    (h : ok₁ B (tokIface B) tr tk₀ tk₁ = true) :
    (tokIface B).ok (tokD (tokIface B) tk₀ tk₁ b₁) (B.d₁ tr) = true := by
  unfold ok₁ at h
  simp only [Bool.and_eq_true] at h
  cases b₁
  · exact h.1.2
  · exact h.2

lemma ok_of_ok₂ {B : Adversary Z} {tr : IssTr Z} {tk₀ tk₁ ch : Option TokenS}
    {rq : Except Error (SpendRequest Z)} (b₁ b₂ : Bool)
    (h : ok₂ B (tokIface B) b₁ tr tk₀ tk₁ rq ch = true) :
    (tokIface B).ok (cur₂ (tokIface B) b₁ b₂ tk₀ tk₁ ch) (B.d₂ tr rq) = true := by
  unfold ok₂ at h
  simp only [Bool.and_eq_true] at h
  unfold cur₂
  cases b₂ == b₁
  · exact h.2
  · exact h.1.2

/-- **The view's tables are `Vtab` of what the Issuer sees**, for slots whose outputs do not read
the tables and whose programming is the one of their requests. -/
theorem viewR_tab (b₁ b₂ : Bool) (i₀ i₁ : IssOut Z TokenS) (P₀ P₁ : ShR R → ShR R)
    (o₁ o₂ : TokenS → Credits → SpOut Z TokenS) (Q₁ Q₂ : Bool → TokenS → Credits → ShR R → ShR R)
    (co : (CI × CI) × (CS × CS)) (t : ShR R)
    (hP₀ : ∀ s, P₀ s = progIm A progI co.1.1 i₀.req s)
    (hP₁ : ∀ s, P₁ s = progIm A progI co.1.2 i₁.req s)
    (hQ₁ : ∀ τ d s, (tokIface A.base).ok τ d = true →
      Q₁ true τ d s = progSm A progS co.2.1 (o₁ τ d).req s)
    (hQ₁' : ∀ τ d s, Q₁ false τ d s = s)
    (hQ₂ : ∀ τ d s, (tokIface A.base).ok τ d = true →
      Q₂ true τ d s = progSm A progS co.2.2 (o₂ τ d).req s)
    (hQ₂' : ∀ τ d s, Q₂ false τ d s = s) :
    let tr : IssTr Z := (i₀.req, i₁.req)
    let tk₀ := i₀.fin (A.respondIss tr false)
    let tk₁ := i₁.fin (A.respondIss tr true)
    let τ₁ := tokD (tokIface A.base) tk₀ tk₁ b₁
    let ok1 := ok₁ A.base (tokIface A.base) tr tk₀ tk₁
    let O₁ := o₁ τ₁ (A.d₁ tr)
    let ch := O₁.fin (A.respond₁ tr O₁.req)
    let ok2 := ok₂ A.base (tokIface A.base) b₁ tr tk₀ tk₁ O₁.req ch
    let O₂ := o₂ (cur₂ (tokIface A.base) b₁ b₂ tk₀ tk₁ ch) (A.d₂ tr O₁.req)
    P₀ (P₁ (Q₁ ok1 τ₁ (A.d₁ tr) (Q₂ (ok1 && ok2) (cur₂ (tokIface A.base) b₁ b₂ tk₀ tk₁ ch)
        (A.d₂ tr O₁.req) t))) =
      Vtab A progI progS co t tr (bif ok1 then some (O₁.req, bif ok2 then some O₂.req else none)
        else none) := by
  intro tr tk₀ tk₁ τ₁ ok1 O₁ ch ok2 O₂
  unfold Vtab
  rw [hP₀, hP₁]
  congr 2
  cases h1 : ok1
  · simp only [Bool.false_and, hQ₁', hQ₂', Bool.cond_false]
  · simp only [Bool.true_and, Bool.cond_true]
    rw [hQ₁ τ₁ (A.d₁ tr) _ (ok_of_ok₁ (B := A.base) b₁ h1)]
    congr 1
    cases h2 : ok2
    · simp only [hQ₂', Bool.cond_false]
    · simp only [Bool.cond_true]
      exact hQ₂ (cur₂ (tokIface A.base) b₁ b₂ tk₀ tk₁ ch) (A.d₂ tr O₁.req) t
        (ok_of_ok₂ (B := A.base) b₁ b₂ h2)

/-- **The simulated view is `Ratatouille.view` for the adversary that sees `V` and `sl`**, when
`V` of what the Issuer sees is the view's tables. -/
theorem viewR_eq_view (b₁ b₂ : Bool) (i₀ i₁ : IssOut Z TokenS) (P₀ P₁ : ShR R → ShR R) (g₀ g₁ g₂ g₃ : Tab3)
    (o₁ o₂ : TokenS → Credits → SpOut Z TokenS) (Q₁ Q₂ : Bool → TokenS → Credits → ShR R → ShR R)
    (t : ShR R) (V : IssTr Z → Rounds Z → ShR R)
    (hV : let tr : IssTr Z := (i₀.req, i₁.req)
      let tk₀ := i₀.fin (A.respondIss tr false)
      let tk₁ := i₁.fin (A.respondIss tr true)
      let τ₁ := tokD (tokIface A.base) tk₀ tk₁ b₁
      let ok1 := ok₁ A.base (tokIface A.base) tr tk₀ tk₁
      let O₁ := o₁ τ₁ (A.d₁ tr)
      let ch := O₁.fin (A.respond₁ tr O₁.req)
      let ok2 := ok₂ A.base (tokIface A.base) b₁ tr tk₀ tk₁ O₁.req ch
      let O₂ := o₂ (cur₂ (tokIface A.base) b₁ b₂ tk₀ tk₁ ch) (A.d₂ tr O₁.req)
      P₀ (P₁ (Q₁ ok1 τ₁ (A.d₁ tr) (Q₂ (ok1 && ok2) (cur₂ (tokIface A.base) b₁ b₂ tk₀ tk₁ ch)
          (A.d₂ tr O₁.req) t))) =
        V tr (bif ok1 then some (O₁.req, bif ok2 then some O₂.req else none) else none)) :
    viewR A b₁ b₂ ⟨fun _ => i₀, P₀, g₀⟩ ⟨fun _ => i₁, P₁, g₁⟩ ⟨fun τ d _ => o₁ τ d, Q₁, g₂⟩
        ⟨fun τ d _ => o₂ τ d, Q₂, g₃⟩ t ↔
      view (A.at V ((g₀, g₁), (g₂, g₃))) (tokIface A.base) b₁ b₂ i₀ i₁ o₁ o₂ := by
  simp only [viewR, view, stage₁, stage₂, stage₃, AdversaryRO.at]
  rw [hV]
  rfl

variable {A simI simS progI progS} in
lemma issSim_prog (hprogI : ∀ x x' c, simI x c = none → progI x c = progI x' c) (n : NRR) (c : CI)
    (s : ShR R) : (if A.tInit = 0 then s else progI (xIOf A n) c s) =
      progIm A progI c (issSim A.base simI (n.1, n.2, c)).req s := by
  unfold progIm
  by_cases hT : A.tInit = 0
  · simp only [hT, ↓reduceIte]
  · simp only [hT, ↓reduceIte]
    have hT' : A.base.tInit ≠ 0 := hT
    unfold issSim issueSim issOutOf
    simp only [hT', ↓reduceIte]
    cases h : simI ⟨com (vec n.1) A.base.ctx A.base.tInit (vec n.2), A.base.tInit, A.base.ctx⟩ c with
    | none => exact congrFun (hprogI (xIOf A n) ⟨dummyC, A.tInit, A.ctx⟩ c h) s
    | some pf => simp only [issueReqC_mk]; rfl

variable {A simI simS progI progS} in
lemma spSim_prog (hprogS : ∀ x x' c, simS x c = none → progS x c = progS x' c) (n : NRR) (c : CS)
    (τ : TokenS) (d : Credits) (hok : (tokIface A.base).ok τ d = true) (s : ShR R) :
    progS (xSOf A n τ d) c s = progSm A progS c (spSim A.base simS (n.1, n.2, c) τ d).req s := by
  simp only [tokIface, Bool.and_eq_true, decide_eq_true_eq] at hok
  obtain ⟨hv, hc⟩ := hok
  obtain ⟨t', ht'⟩ := Option.isSome_iff_exists.1 hc
  have hx : xSOf A n τ d = ⟨A.pk, τ.nf, d, com (vec n.1) A.ctx t' (vec n.2), A.ctx⟩ := by
    simp only [xSOf, ht', Option.getD_some]
  rw [hx]
  unfold spSim spendSim spOutOf progSm
  simp only [show τ.Valid A.base.pk A.base.ctx from hv, not_true_eq_false, ↓reduceIte, ht']
  cases h : simS ⟨A.base.pk, τ.nf, d, com (vec n.1) A.base.ctx t' (vec n.2), A.base.ctx⟩ c with
  | none => exact congrFun (hprogS _ ⟨A.pk, nf0, 0, dummyC, A.ctx⟩ c h) s
  | some pf => simp only [parse_toBytes]; rfl

/-- The simulated tape, regrouped as `Ratatouille`'s, the coins, the slices and the tables. -/
def tapeOfR (x : ((TIsR CI × TIsR CI) × (TSsR CS × TSsR CS)) × ShR R) : SimTape CI CS :=
  (((x.1.1.1.1.1, x.1.1.1.1.2, x.1.1.1.2.1), (x.1.1.2.1.1, x.1.1.2.1.2, x.1.1.2.2.1)),
    ((x.1.2.1.1.1, x.1.2.1.1.2, x.1.2.1.2.1), (x.1.2.2.1.1, x.1.2.2.1.2, x.1.2.2.2.1)))

def coinsOfR (x : ((TIsR CI × TIsR CI) × (TSsR CS × TSsR CS)) × ShR R) : (CI × CI) × (CS × CS) :=
  ((x.1.1.1.2.1, x.1.1.2.2.1), (x.1.2.1.2.1, x.1.2.2.2.1))

def slicesOfR (x : ((TIsR CI × TIsR CI) × (TSsR CS × TSsR CS)) × ShR R) : SlicesR :=
  ((x.1.1.1.2.2, x.1.1.2.2.2), (x.1.2.1.2.2, x.1.2.2.2.2))

/-- **The simulated game is `Ratatouille.simGame` for the adversary that sees the programmed
tables** (`Vtab` of the coins and the tables). -/
theorem simGameR_iff (hprogI : ∀ x x' c, simI x c = none → progI x c = progI x' c)
    (hprogS : ∀ x x' c, simS x c = none → progS x c = progS x' c) (b₁ b₂ : Bool)
    (x : ((TIsR CI × TIsR CI) × (TSsR CS × TSsR CS)) × ShR R) :
    simGameR A simI simS progI progS b₁ b₂ x ↔
      simGame (A.at (Vtab A progI progS (coinsOfR x) x.2) (slicesOfR x)) simI simS b₁ b₂
        (tapeOfR x) :=
  viewR_eq_view A b₁ b₂ (issSim A.base simI (x.1.1.1.1.1, x.1.1.1.1.2, x.1.1.1.2.1))
    (issSim A.base simI (x.1.1.2.1.1, x.1.1.2.1.2, x.1.1.2.2.1))
    (fun s => if A.tInit = 0 then s else progI (xIOf A x.1.1.1.1) x.1.1.1.2.1 s)
    (fun s => if A.tInit = 0 then s else progI (xIOf A x.1.1.2.1) x.1.1.2.2.1 s)
    x.1.1.1.2.2 x.1.1.2.2.2 x.1.2.1.2.2 x.1.2.2.2.2
    (fun τ d => spSim A.base simS (x.1.2.1.1.1, x.1.2.1.1.2, x.1.2.1.2.1) τ d)
    (fun τ d => spSim A.base simS (x.1.2.2.1.1, x.1.2.2.1.2, x.1.2.2.2.1) τ d)
    (fun ok τ d s => if ok = true then progS (xSOf A x.1.2.1.1 τ d) x.1.2.1.2.1 s else s)
    (fun ok τ d s => if ok = true then progS (xSOf A x.1.2.2.1 τ d) x.1.2.2.2.1 s else s) x.2 _
    (viewR_tab A progI progS b₁ b₂ _ _ _ _
      (fun τ d => spSim A.base simS (x.1.2.1.1.1, x.1.2.1.1.2, x.1.2.1.2.1) τ d)
      (fun τ d => spSim A.base simS (x.1.2.2.1.1, x.1.2.2.1.2, x.1.2.2.2.1) τ d)
      (fun ok τ d s => if ok = true then progS (xSOf A x.1.2.1.1 τ d) x.1.2.1.2.1 s else s)
      (fun ok τ d s => if ok = true then progS (xSOf A x.1.2.2.1 τ d) x.1.2.2.2.1 s else s)
      (coinsOfR x) x.2
      (fun s => issSim_prog hprogI x.1.1.1.1 x.1.1.1.2.1 s)
      (fun s => issSim_prog hprogI x.1.1.2.1 x.1.1.2.2.1 s)
      (fun τ d s h => spSim_prog hprogS x.1.2.1.1 x.1.2.1.2.1 τ d h s) (fun _ _ _ => rfl)
      (fun τ d s h => spSim_prog hprogS x.1.2.2.1 x.1.2.2.2.1 τ d h s) (fun _ _ _ => rfl))

/-! ## The hiding hop and the ideal world -/

/-- The simulator coins, the slices and the tables, fixed in the reductions. -/
abbrev KR (R : Type) (CI CS : Type) := ((CI × CI) × (CS × CS)) × (SlicesR × ShR R)

/-- **The reduction to hiding**: `Ratatouille.reduction` for the Issuer that sees the tables
programmed with the coins `K.1` on the tables `K.2.2`, and the slices `K.2.1`. -/
def reductionR (b₁ b₂ : Bool) (K : KR R CI CS) : Quad Nullifier → Quad (Credits → Commitment) → Prop :=
  reduction (A.at (Vtab A progI progS K.1 K.2.2) K.2.1) simI simS b₁ b₂ K.1

/-- The ideal world: uniform commitments. -/
def idealGameR (b₁ b₂ : Bool) (y : UTape × KR R CI CS) : Prop :=
  reductionR A simI simS progI progS b₁ b₂ y.2 (hideIdeal y.1).1 (hideIdeal y.1).2

/-- Regroup the simulated tape as the hiding tape and the rest. -/
def regroupR : ((TIsR CI × TIsR CI) × (TSsR CS × TSsR CS)) × ShR R ≃ HTape × KR R CI CS where
  toFun x := (((x.1.1.1.1, x.1.1.2.1), (x.1.2.1.1, x.1.2.2.1)), (coinsOfR x, (slicesOfR x, x.2)))
  invFun y := ((((y.1.1.1, (y.2.1.1.1, y.2.2.1.1.1)), (y.1.1.2, (y.2.1.1.2, y.2.2.1.1.2))),
    ((y.1.2.1, (y.2.1.2.1, y.2.2.1.2.1)), (y.1.2.2, (y.2.1.2.2, y.2.2.1.2.2)))), y.2.2.2)
  left_inv _ := rfl
  right_inv _ := rfl

theorem hiding_hopR [Fintype CI] [Nonempty CI] [Fintype CS] [Nonempty CS]
    (hprogI : ∀ x x' c, simI x c = none → progI x c = progI x' c)
    (hprogS : ∀ x x' c, simS x c = none → progS x c = progS x' c) (b₁ b₂ : Bool) {εhide : ℝ}
    (hhide : ∀ K, hidingAdv A.ctx (reductionR A simI simS progI progS b₁ b₂ K) ≤ εhide) :
    |pr _ (simGameR A simI simS progI progS b₁ b₂) -
      pr _ (idealGameR A simI simS progI progS b₁ b₂)| ≤ εhide := by
  rw [← pr_equiv regroupR.symm (simGameR A simI simS progI progS b₁ b₂),
    pr_congr fun y => (simGameR_iff A simI simS progI progS hprogI hprogS b₁ b₂ (regroupR.symm y)).trans
      (simGame_iff _ simI simS b₁ b₂ _)]
  exact abs_pr_prod_sub_le' _ _ fun K => hhide K

/-- Permute the nullifiers of the first three slots of an ideal tape. -/
def permU (e : (Coins 24 × Coins 24 × Coins 24) ≃ (Coins 24 × Coins 24 × Coins 24)) :
    UTape ≃ UTape where
  toFun u :=
    let z := e (u.1.1.1, u.1.2.1, u.2.1.1)
    (((z.1, u.1.1.2), (z.2.1, u.1.2.2)), ((z.2.2, u.2.1.2), u.2.2))
  invFun u :=
    let z := e.symm (u.1.1.1, u.1.2.1, u.2.1.1)
    (((z.1, u.1.1.2), (z.2.1, u.1.2.2)), ((z.2.2, u.2.1.2), u.2.2))
  left_inv u := by simp
  right_inv u := by simp

/-- **In the ideal world the four worlds coincide**, for every simulator coins, slices and
tables (`Ratatouille.idealGame_eq`, with the coins and the tables fixed). -/
theorem idealGameR_eq [Fintype CI] [Nonempty CI] [Fintype CS] [Nonempty CS] (b₁ b₂ : Bool) :
    pr _ (idealGameR A simI simS progI progS b₁ b₂) =
      pr _ (idealGameR A simI simS progI progS false false) := by
  have key : ∀ K : KR R CI CS, pr UTape (fun u => idealGameR A simI simS progI progS b₁ b₂ (u, K)) =
      pr UTape (fun u => idealGameR A simI simS progI progS false false (u, K)) := by
    intro K
    set A' := A.at (Vtab A progI progS K.1 K.2.2) K.2.1
    have e (c₁ c₂ : Bool) (u : UTape) : idealGameR A simI simS progI progS c₁ c₂ (u, K) ↔
        idealW A' simI simS (bif c₁ then vec u.1.2.1 else vec u.1.1.1)
          (bif c₂ == c₁ then vec u.2.1.1 else bif c₁ then vec u.1.1.1 else vec u.1.2.1)
          (vec u.1.1.2) (vec u.1.2.2) (vec u.2.1.2) (vec u.2.2.2) K.1 :=
      idealGame_iff A' simI simS c₁ c₂ (u, K.1)
    rw [pr_congr (e b₁ b₂), pr_congr (e false false)]
    cases b₁ <;> cases b₂ <;>
      simp only [Bool.true_beq, Bool.false_beq, Bool.not_true, Bool.not_false, Bool.cond_true,
        Bool.cond_false]
    · rw [← pr_equiv (permU (⟨fun z => (z.1, z.2.2, z.2.1), fun z => (z.1, z.2.2, z.2.1),
        fun _ => rfl, fun _ => rfl⟩ : (Coins 24 × Coins 24 × Coins 24) ≃ _))
        (fun u => idealW A' simI simS (vec u.1.1.1) (vec u.2.1.1) (vec u.1.1.2) (vec u.1.2.2)
          (vec u.2.1.2) (vec u.2.2.2) K.1)]
      exact pr_congr fun _ => Iff.rfl
    · rw [← pr_equiv (permU (⟨fun z => (z.2.1, z.2.2, z.1), fun z => (z.2.2, z.1, z.2.1),
        fun _ => rfl, fun _ => rfl⟩ : (Coins 24 × Coins 24 × Coins 24) ≃ _))
        (fun u => idealW A' simI simS (vec u.1.1.1) (vec u.2.1.1) (vec u.1.1.2) (vec u.1.2.2)
          (vec u.2.1.2) (vec u.2.2.2) K.1)]
      exact pr_congr fun _ => Iff.rfl
    · rw [← pr_equiv (permU (⟨fun z => (z.2.1, z.1, z.2.2), fun z => (z.2.1, z.1, z.2.2),
        fun _ => rfl, fun _ => rfl⟩ : (Coins 24 × Coins 24 × Coins 24) ≃ _))
        (fun u => idealW A' simI simS (vec u.1.1.1) (vec u.2.1.1) (vec u.1.1.2) (vec u.1.2.2)
          (vec u.2.1.2) (vec u.2.2.2) K.1)]
      exact pr_congr fun _ => Iff.rfl
  have h := abs_pr_prod_sub_le' (fun y : UTape × KR R CI CS => idealGameR A simI simS progI progS b₁ b₂ y)
    (fun y : UTape × KR R CI CS => idealGameR A simI simS progI progS false false y) (ε := 0)
    fun K => by rw [key K, sub_self, abs_zero]
  rw [abs_nonpos_iff, sub_eq_zero] at h
  exact h

/-! ## The reads of the game's parts -/

/-- The rounds the Issuer sees, from the issuance outputs and the two spend outputs. -/
def guessY (b₁ : Bool) (i₀ i₁ : IssOut Z TokenS) (O₁ O₂ : SpOut Z TokenS) : Rounds Z :=
  bif ok₁ A.base (tokIface A.base) (i₀.req, i₁.req) (i₀.fin (A.respondIss (i₀.req, i₁.req) false))
      (i₁.fin (A.respondIss (i₀.req, i₁.req) true)) then
    some (O₁.req, bif ok₂ A.base (tokIface A.base) b₁ (i₀.req, i₁.req)
        (i₀.fin (A.respondIss (i₀.req, i₁.req) false)) (i₁.fin (A.respondIss (i₀.req, i₁.req) true))
        O₁.req (O₁.fin (A.respond₁ (i₀.req, i₁.req) O₁.req)) then some O₂.req else none)
  else none

/-- Round 1's token. -/
def τ₁Of (b₁ : Bool) (i₀ i₁ : IssOut Z TokenS) : TokenS :=
  tokD (tokIface A.base) (i₀.fin (A.respondIss (i₀.req, i₁.req) false))
    (i₁.fin (A.respondIss (i₀.req, i₁.req) true)) b₁

/-- Round 2's token. -/
def τ₂Of (b₁ b₂ : Bool) (i₀ i₁ : IssOut Z TokenS) (O₁ : SpOut Z TokenS) : TokenS :=
  cur₂ (tokIface A.base) b₁ b₂ (i₀.fin (A.respondIss (i₀.req, i₁.req) false))
    (i₁.fin (A.respondIss (i₀.req, i₁.req) true)) (O₁.fin (A.respond₁ (i₀.req, i₁.req) O₁.req))


/-- The output of a real spend that passes the Client's checks: the nullifier, amount and new
commitment, and the prover's proof. -/
def spOfProof (x : NRR) (τ : TokenS) (d t' : Credits) (o : Option (SpendProof Z)) : SpOut Z TokenS :=
  spOutOf A.base (match o with
    | none => .error .runtime
    | some pf => .ok (⟨vec x.1, t', vec x.2, com (vec x.1) A.ctx t' (vec x.2)⟩,
        SpendReq.toBytes ⟨τ.nf, d, com (vec x.1) A.ctx t' (vec x.2), pf⟩))

/-- The spend witness of the coins `(nf', r')` at a token, an amount and the new balance. -/
def wSOf (x : NRR) (τ : TokenS) (t' : Credits) : SpendWitness :=
  ⟨τ.t, τ.r, τ.x, τ.s, vec x.1, t', vec x.2⟩


section GameReads

variable {A} {q3 q5 qE r5 rE : ℕ}

/-- A real issuance's output reads what its prover reads. -/
lemma rd5_issRealR {PI : ProverI R Z} (hPI : ∀ x w ρ g, Rd5 (PI x w ρ g) r5) (x : TRe) :
    Rd5 (issRealR A PI x).out r5 := by
  by_cases hT : A.tInit = 0
  · have : (issRealR A PI x).out = fun _ => issOutOf A.base (.error .invalidArgument) := by
      funext s
      simp [issRealR, issueOf, hT]
    rw [this]; exact (Rd5.const _).mono (Nat.zero_le _)
  · have hT' : A.base.tInit ≠ 0 := hT
    have : (issRealR A PI x).out = fun s => issOutOf A.base (match PI (xIOf A x.1)
        ⟨vec x.1.1, vec x.1.2⟩ (vec x.2.1) x.2.2 s with
      | none => .error .runtime
      | some pf => .ok (⟨vec x.1.1, vec x.1.2, A.tInit, com (vec x.1.1) A.ctx A.tInit (vec x.1.2)⟩,
          issueReqBytes (com (vec x.1.1) A.ctx A.tInit (vec x.1.2)) pf)) := by
      funext s
      simp only [issRealR, issueOf, hT, ↓reduceIte]
      rfl
    rw [this]
    exact (hPI (xIOf A x.1) ⟨vec x.1.1, vec x.1.2⟩ (vec x.2.1) x.2.2).map fun o =>
      issOutOf A.base (match o with
        | none => .error .runtime
        | some pf => .ok (⟨vec x.1.1, vec x.1.2, A.tInit, com (vec x.1.1) A.ctx A.tInit (vec x.1.2)⟩,
            issueReqBytes (com (vec x.1.1) A.ctx A.tInit (vec x.1.2)) pf))

lemma rdE_issRealR {PI : ProverI R Z} (hPI : ∀ x w ρ g, RdE (PI x w ρ g) rE) (x : TRe) :
    RdE (issRealR A PI x).out rE := by
  by_cases hT : A.tInit = 0
  · have : (issRealR A PI x).out = fun _ => issOutOf A.base (.error .invalidArgument) := by
      funext s
      simp [issRealR, issueOf, hT]
    rw [this]; exact (RdE.const _).mono (Nat.zero_le _)
  · have hT' : A.base.tInit ≠ 0 := hT
    have : (issRealR A PI x).out = fun s => issOutOf A.base (match PI (xIOf A x.1)
        ⟨vec x.1.1, vec x.1.2⟩ (vec x.2.1) x.2.2 s with
      | none => .error .runtime
      | some pf => .ok (⟨vec x.1.1, vec x.1.2, A.tInit, com (vec x.1.1) A.ctx A.tInit (vec x.1.2)⟩,
          issueReqBytes (com (vec x.1.1) A.ctx A.tInit (vec x.1.2)) pf)) := by
      funext s
      simp only [issRealR, issueOf, hT, ↓reduceIte]
      rfl
    rw [this]
    exact (hPI (xIOf A x.1) ⟨vec x.1.1, vec x.1.2⟩ (vec x.2.1) x.2.2).map fun o =>
      issOutOf A.base (match o with
        | none => .error .runtime
        | some pf => .ok (⟨vec x.1.1, vec x.1.2, A.tInit, com (vec x.1.1) A.ctx A.tInit (vec x.1.2)⟩,
            issueReqBytes (com (vec x.1.1) A.ctx A.tInit (vec x.1.2)) pf))

/-- **A real spend's output**: an error if the Client's checks fail, else `spOfProof` of the
prover's proof. -/
lemma spRealR_out (PS : ProverS R Z) (x : TRe) (τ : TokenS) (d : Credits) (s : ShR R) :
    (spRealR A PS x).out τ d s = if τ.Valid A.pk A.ctx then
      (match clientCheck τ.t τ.x d with
        | none => spOutOf A.base (.error .invalidArgument)
        | some t' => spOfProof A x.1 τ d t' (PS ⟨A.pk, τ.nf, d, com (vec x.1.1) A.ctx t' (vec x.1.2), A.ctx⟩
            (wSOf x.1 τ t') (vec x.2.1) x.2.2 s))
      else spOutOf A.base (.error .invalidArgument) := by
  simp only [spRealR, spendOf]
  by_cases hv : τ.Valid A.pk A.ctx
  · simp only [not_true_eq_false, ↓reduceIte, hv]
    cases clientCheck τ.t τ.x d with
    | none => rfl
    | some t' =>
      simp only [primS]
      unfold spOfProof wSOf
      cases PS ⟨A.pk, τ.nf, d, com (vec x.1.1) A.ctx t' (vec x.1.2), A.ctx⟩
        ⟨τ.t, τ.r, τ.x, τ.s, vec x.1.1, t', vec x.1.2⟩ (vec x.2.1) x.2.2 s <;> rfl
  · simp only [not_false_eq_true, ↓reduceIte, hv]

lemma rd5_spRealR {PS : ProverS R Z} (hPS : ∀ x w ρ g, Rd5 (PS x w ρ g) r5) (x : TRe) (τ : TokenS)
    (d : Credits) : Rd5 ((spRealR A PS x).out τ d) r5 := by
  have e : (spRealR A PS x).out τ d = fun s => _ := funext (spRealR_out (A := A) PS x τ d)
  rw [e]
  split_ifs
  · split
    · exact (Rd5.const _).mono (Nat.zero_le _)
    · exact (hPS _ _ _ _).map _
  · exact (Rd5.const _).mono (Nat.zero_le _)

lemma rdE_spRealR {PS : ProverS R Z} (hPS : ∀ x w ρ g, RdE (PS x w ρ g) rE) (x : TRe) (τ : TokenS)
    (d : Credits) : RdE ((spRealR A PS x).out τ d) rE := by
  have e : (spRealR A PS x).out τ d = fun s => _ := funext (spRealR_out (A := A) PS x τ d)
  rw [e]
  split_ifs
  · split
    · exact (RdE.const _).mono (Nat.zero_le _)
    · exact (hPS _ _ _ _).map _
  · exact (RdE.const _).mono (Nat.zero_le _)

lemma Rd5.bind4 {p : VoleMole.Verifier.Params} {Y₀ Y₁ Y₂ Y₃ X : Sort*} {m₀ : ShG R p → Y₀} {m₁ : ShG R p → Y₁}
    {m₂ : Y₀ → Y₁ → ShG R p → Y₂} {m₃ : Y₀ → Y₁ → Y₂ → ShG R p → Y₃} {f : Y₀ → Y₁ → Y₂ → Y₃ → ShG R p → X}
    {a₀ a₁ a₂ a₃ b : ℕ} (h₀ : Rd5 m₀ a₀) (h₁ : Rd5 m₁ a₁) (h₂ : ∀ y₀ y₁, Rd5 (m₂ y₀ y₁) a₂)
    (h₃ : ∀ y₀ y₁ y₂, Rd5 (m₃ y₀ y₁ y₂) a₃) (hf : ∀ y₀ y₁ y₂ y₃, Rd5 (f y₀ y₁ y₂ y₃) b) :
    Rd5 (fun s => f (m₀ s) (m₁ s) (m₂ (m₀ s) (m₁ s) s) (m₃ (m₀ s) (m₁ s) (m₂ (m₀ s) (m₁ s) s) s) s)
      (a₀ + (a₁ + (a₂ + (a₃ + b)))) :=
  h₀.bind fun y₀ => h₁.bind (f := fun y₁ s => f y₀ y₁ (m₂ y₀ y₁ s) (m₃ y₀ y₁ (m₂ y₀ y₁ s) s) s)
    fun y₁ => (h₂ y₀ y₁).bind (f := fun y₂ s => f y₀ y₁ y₂ (m₃ y₀ y₁ y₂ s) s)
      fun y₂ => (h₃ y₀ y₁ y₂).bind (f := fun y₃ s => f y₀ y₁ y₂ y₃ s) fun y₃ => hf y₀ y₁ y₂ y₃

lemma RdE.bind4 {p : VoleMole.Verifier.Params} {Y₀ Y₁ Y₂ Y₃ X : Sort*} {m₀ : ShG R p → Y₀} {m₁ : ShG R p → Y₁}
    {m₂ : Y₀ → Y₁ → ShG R p → Y₂} {m₃ : Y₀ → Y₁ → Y₂ → ShG R p → Y₃} {f : Y₀ → Y₁ → Y₂ → Y₃ → ShG R p → X}
    {a₀ a₁ a₂ a₃ b : ℕ} (h₀ : RdE m₀ a₀) (h₁ : RdE m₁ a₁) (h₂ : ∀ y₀ y₁, RdE (m₂ y₀ y₁) a₂)
    (h₃ : ∀ y₀ y₁ y₂, RdE (m₃ y₀ y₁ y₂) a₃) (hf : ∀ y₀ y₁ y₂ y₃, RdE (f y₀ y₁ y₂ y₃) b) :
    RdE (fun s => f (m₀ s) (m₁ s) (m₂ (m₀ s) (m₁ s) s) (m₃ (m₀ s) (m₁ s) (m₂ (m₀ s) (m₁ s) s) s) s)
      (a₀ + (a₁ + (a₂ + (a₃ + b)))) :=
  h₀.bind fun y₀ => h₁.bind (f := fun y₁ s => f y₀ y₁ (m₂ y₀ y₁ s) (m₃ y₀ y₁ (m₂ y₀ y₁ s) s) s)
    fun y₁ => (h₂ y₀ y₁).bind (f := fun y₂ s => f y₀ y₁ y₂ (m₃ y₀ y₁ y₂ s) s)
      fun y₂ => (h₃ y₀ y₁ y₂).bind (f := fun y₃ s => f y₀ y₁ y₂ y₃ s) fun y₃ => hf y₀ y₁ y₂ y₃

/-- **The view, with slots that do not program, reads what its slots and the guess read.** -/
lemma rd5_viewR (hA : A.Budget q3 q5 qE) (b₁ b₂ : Bool) (o₀ o₁ : ShR R → IssOut Z TokenS)
    (g₀ g₁ g₂ g₃ : Tab3) (k₁ k₂ : TokenS → Credits → ShR R → SpOut Z TokenS) {a₀ a₁ c₁ c₂ : ℕ}
    (h₀ : Rd5 o₀ a₀) (h₁ : Rd5 o₁ a₁) (hk₁ : ∀ τ d, Rd5 (k₁ τ d) c₁)
    (hk₂ : ∀ τ d, Rd5 (k₂ τ d) c₂) :
    Rd5 (fun u => viewR A b₁ b₂ ⟨o₀, fun t => t, g₀⟩ ⟨o₁, fun t => t, g₁⟩
      ⟨k₁, fun _ _ _ t => t, g₂⟩ ⟨k₂, fun _ _ _ t => t, g₃⟩ u) (a₀ + (a₁ + (c₁ + (c₂ + q5)))) :=
  Rd5.bind4 (m₂ := fun i₀ i₁ u => k₁ (τ₁Of A b₁ i₀ i₁) (A.d₁ (i₀.req, i₁.req)) u)
    (m₃ := fun i₀ i₁ O₁ u => k₂ (τ₂Of A b₁ b₂ i₀ i₁ O₁) (A.d₂ (i₀.req, i₁.req) O₁.req) u)
    (f := fun i₀ i₁ O₁ O₂ u => A.guess (i₀.req, i₁.req) (guessY A b₁ i₀ i₁ O₁ O₂)
      ((g₀, g₁), (g₂, g₃)) u)
    h₀ h₁ (fun _ _ => hk₁ _ _) (fun _ _ _ => hk₂ _ _) fun _ _ _ _ => hA.h5 _ _ _

lemma rdE_viewR (hA : A.Budget q3 q5 qE) (b₁ b₂ : Bool) (o₀ o₁ : ShR R → IssOut Z TokenS)
    (g₀ g₁ g₂ g₃ : Tab3) (k₁ k₂ : TokenS → Credits → ShR R → SpOut Z TokenS) {a₀ a₁ c₁ c₂ : ℕ}
    (h₀ : RdE o₀ a₀) (h₁ : RdE o₁ a₁) (hk₁ : ∀ τ d, RdE (k₁ τ d) c₁)
    (hk₂ : ∀ τ d, RdE (k₂ τ d) c₂) :
    RdE (fun u => viewR A b₁ b₂ ⟨o₀, fun t => t, g₀⟩ ⟨o₁, fun t => t, g₁⟩
      ⟨k₁, fun _ _ _ t => t, g₂⟩ ⟨k₂, fun _ _ _ t => t, g₃⟩ u) (a₀ + (a₁ + (c₁ + (c₂ + qE)))) :=
  RdE.bind4 (m₂ := fun i₀ i₁ u => k₁ (τ₁Of A b₁ i₀ i₁) (A.d₁ (i₀.req, i₁.req)) u)
    (m₃ := fun i₀ i₁ O₁ u => k₂ (τ₂Of A b₁ b₂ i₀ i₁ O₁) (A.d₂ (i₀.req, i₁.req) O₁.req) u)
    (f := fun i₀ i₁ O₁ O₂ u => A.guess (i₀.req, i₁.req) (guessY A b₁ i₀ i₁ O₁ O₂)
      ((g₀, g₁), (g₂, g₃)) u)
    h₀ h₁ (fun _ _ => hk₁ _ _) (fun _ _ _ => hk₂ _ _) fun _ _ _ _ => hA.hE _ _ _

lemma rd3_viewR0 (hA : A.Budget q3 q5 qE) (b₁ b₂ : Bool) (o₀ : ShR R → IssOut Z TokenS)
    (P₀ : ShR R → ShR R) (s₁ : IssSlotR R Z) (h₁ h₂ : SpSlotR R Z) (u : ShR R) :
    Rd3 (fun g => viewR A b₁ b₂ ⟨o₀, P₀, g⟩ s₁ h₁ h₂ u) q3 := by
  simp only [viewR]; exact hA.h30 _ _ _ _ _ _

lemma rd3_viewR1 (hA : A.Budget q3 q5 qE) (b₁ b₂ : Bool) (s₀ : IssSlotR R Z)
    (o₁ : ShR R → IssOut Z TokenS) (P₁ : ShR R → ShR R) (h₁ h₂ : SpSlotR R Z) (u : ShR R) :
    Rd3 (fun g => viewR A b₁ b₂ s₀ ⟨o₁, P₁, g⟩ h₁ h₂ u) q3 := by
  simp only [viewR]; exact hA.h31 _ _ _ _ _ _

lemma rd3_viewR2 (hA : A.Budget q3 q5 qE) (b₁ b₂ : Bool) (s₀ s₁ : IssSlotR R Z)
    (k₁ : TokenS → Credits → ShR R → SpOut Z TokenS) (Q₁ : Bool → TokenS → Credits → ShR R → ShR R)
    (h₂ : SpSlotR R Z) (u : ShR R) :
    Rd3 (fun g => viewR A b₁ b₂ s₀ s₁ ⟨k₁, Q₁, g⟩ h₂ u) q3 := by
  simp only [viewR]; exact hA.h32 _ _ _ _ _ _

lemma rd3_viewR3 (hA : A.Budget q3 q5 qE) (b₁ b₂ : Bool) (s₀ s₁ : IssSlotR R Z) (h₁ : SpSlotR R Z)
    (k₂ : TokenS → Credits → ShR R → SpOut Z TokenS) (Q₂ : Bool → TokenS → Credits → ShR R → ShR R)
    (u : ShR R) :
    Rd3 (fun g => viewR A b₁ b₂ s₀ s₁ h₁ ⟨k₂, Q₂, g⟩ u) q3 := by
  simp only [viewR]; exact hA.h33 _ _ _ _ _ _

end GameReads

/-! ## The slots' outputs, unfolded -/

/-- An issuance output from the prover's proof (for `T_init ≠ 0`). -/
def ΦI (n : NRR) (o : Option (IssueProof Z)) : IssOut Z TokenS :=
  issOutOf A.base (match o with
    | none => .error .runtime
    | some pf => .ok (⟨vec n.1, vec n.2, A.tInit, com (vec n.1) A.ctx A.tInit (vec n.2)⟩,
        issueReqBytes (com (vec n.1) A.ctx A.tInit (vec n.2)) pf))

variable {A} in
lemma issRealR_out_zero {PI : ProverI R Z} (hT : A.tInit = 0) (x : TRe) (s : ShR R) :
    (issRealR A PI x).out s = issOutOf A.base (.error .invalidArgument) := by
  simp [issRealR, issueOf, hT]

variable {A simI} in
lemma issSim_zero (hT : A.tInit = 0) (n : NRR) (c : CI) :
    issSim A.base simI (n.1, n.2, c) = issOutOf A.base (.error .invalidArgument) := by
  have hT' : A.base.tInit = 0 := hT
  simp [issSim, issueSim, hT']

variable {A} in
lemma issRealR_out_ne {PI : ProverI R Z} (hT : A.tInit ≠ 0) (x : TRe) (s : ShR R) :
    (issRealR A PI x).out s = ΦI A x.1 (PI (xIOf A x.1) ⟨vec x.1.1, vec x.1.2⟩ (vec x.2.1) x.2.2 s) := by
  simp only [issRealR, issueOf, hT, ↓reduceIte]
  rfl

variable {A simI} in
lemma issSim_ne (hT : A.tInit ≠ 0) (n : NRR) (c : CI) :
    issSim A.base simI (n.1, n.2, c) = ΦI A n (simI (xIOf A n) c) := by
  have hT' : A.base.tInit ≠ 0 := hT
  simp only [issSim, issueSim, hT', ↓reduceIte]
  rfl

variable {A} in
lemma spRealR_out_ok {PS : ProverS R Z} (x : TRe) {τ : TokenS} {d t' : Credits}
    (hv : τ.Valid A.pk A.ctx) (hc : clientCheck τ.t τ.x d = some t') (s : ShR R) :
    (spRealR A PS x).out τ d s =
      spOfProof A x.1 τ d t' (PS (xSOf A x.1 τ d) (wSOf x.1 τ t') (vec x.2.1) x.2.2 s) := by
  rw [spRealR_out]
  simp only [hv, ↓reduceIte, hc, xSOf, Option.getD_some]

variable {A simS} in
lemma spSim_ok (n : NRR) (c : CS) {τ : TokenS} {d t' : Credits} (hv : τ.Valid A.pk A.ctx)
    (hc : clientCheck τ.t τ.x d = some t') :
    spSim A.base simS (n.1, n.2, c) τ d = spOfProof A n τ d t' (simS (xSOf A n τ d) c) := by
  simp only [spSim, spendSim, show τ.Valid A.base.pk A.base.ctx from hv, not_true_eq_false,
    ↓reduceIte, hc, xSOf, Option.getD_some]
  rfl

lemma valid_of_ok {B : Adversary Z} {τ : TokenS} {d : Credits} (h : (tokIface B).ok τ d = true) :
    τ.Valid B.pk B.ctx ∧ ∃ t', clientCheck τ.t τ.x d = some t' := by
  simp only [tokIface, Bool.and_eq_true, decide_eq_true_eq] at h
  exact ⟨h.1, Option.isSome_iff_exists.1 h.2⟩

/-- The spend relation at a token that passes the Client's checks. -/
lemma spendRel_of (n : NRR) {τ : TokenS} {d t' : Credits} (hv : τ.Valid A.pk A.ctx)
    (hc : clientCheck τ.t τ.x d = some t') : SpendRel (xSOf A n τ d) (wSOf n τ t') := by
  refine ⟨hv, ?_, ?_⟩
  · simp only [xSOf, wSOf, hc, Option.getD_some]
  · have := clientCheck_eq hc
    simp only [xSOf, wSOf] at this ⊢
    omega

/-! ## The hybrids' contexts -/

/-- A slot with a fixed output and no programming. -/
def fakeI (o : IssOut Z TokenS) (g : Tab3) : IssSlotR R Z := ⟨fun _ => o, fun t => t, g⟩
def fakeS (o : SpOut Z TokenS) (g : Tab3) : SpSlotR R Z := ⟨fun _ _ _ => o, fun _ _ _ t => t, g⟩

/-- A simulated slot whose programming is already applied. -/
def noProgI (x : TIsR CI) : IssSlotR R Z := ⟨fun _ => issSim A.base simI (x.1.1, x.1.2, x.2.1), fun t => t, x.2.2⟩
def noProgS (x : TSsR CS) : SpSlotR R Z :=
  ⟨fun τ d _ => spSim A.base simS (x.1.1, x.1.2, x.2.1) τ d, fun _ _ _ t => t, x.2.2⟩

/-- An issuance slot's programming. -/
abbrev PIR (n : NRR) (c : CI) (s : ShR R) : ShR R := if A.tInit = 0 then s else progI (xIOf A n) c s

variable (PI : ProverI R Z) (PS : ProverS R Z)

/-- The tape regroupings around each slot. -/
def eqv0R {N Q T₁ T₂ S : Type} : (N × (T₁ × T₂)) × (Q × S) ≃ (((N × Q) × T₁) × T₂) × S where
  toFun z := ((((z.1.1, z.2.1), z.1.2.1), z.1.2.2), z.2.2)
  invFun y := ((y.1.1.1.1, (y.1.1.2, y.1.2)), (y.1.1.1.2, y.2))
  left_inv _ := rfl
  right_inv _ := rfl

def eqv1R {T₀ N Q T₂ S : Type} : (T₀ × (N × T₂)) × (Q × S) ≃ ((T₀ × (N × Q)) × T₂) × S where
  toFun z := (((z.1.1, (z.1.2.1, z.2.1)), z.1.2.2), z.2.2)
  invFun y := ((y.1.1.1, (y.1.1.2.1, y.1.2)), (y.1.1.2.2, y.2))
  left_inv _ := rfl
  right_inv _ := rfl

def eqv2R {T₀₁ N T₃ Q S : Type} : ((T₀₁ × N) × T₃) × (Q × S) ≃ (T₀₁ × ((N × Q) × T₃)) × S where
  toFun z := ((z.1.1.1, ((z.1.1.2, z.2.1), z.1.2)), z.2.2)
  invFun y := (((y.1.1, y.1.2.1.1), y.1.2.2), (y.1.2.1.2, y.2))
  left_inv _ := rfl
  right_inv _ := rfl

def eqv3R {T₀₁ T₂ N Q S : Type} : ((T₀₁ × T₂) × N) × (Q × S) ≃ (T₀₁ × (T₂ × (N × Q))) × S where
  toFun z := ((z.1.1.1, (z.1.1.2, (z.1.2, z.2.1))), z.2.2)
  invFun y := (((y.1.1, y.1.2.1), y.1.2.2.1), (y.1.2.2.2, y.2))
  left_inv _ := rfl
  right_inv _ := rfl

/-- The rest of the game around issuance `0`'s output. -/
def F0R (b₁ b₂ : Bool) (γ : NRR × (TRe × (TRe × TRe))) (o : IssOut Z TokenS) (g : Tab3) (u : ShR R) :
    Prop :=
  viewR A b₁ b₂ (fakeI o g) (issRealR A PI γ.2.1) (spRealR A PS γ.2.2.1) (spRealR A PS γ.2.2.2) u

/-- The rest of the game around issuance `1`'s output. -/
def F1R (b₁ b₂ : Bool) (γ : TIsR CI × (NRR × (TRe × TRe))) (o : IssOut Z TokenS) (g : Tab3) (u : ShR R) :
    Prop :=
  viewR A b₁ b₂ (noProgI A simI γ.1) (fakeI o g) (spRealR A PS γ.2.2.1) (spRealR A PS γ.2.2.2) u

/-- **The collision term of hop 1**: issuance `1`'s real proof on the tables programmed by
issuance `0`'s simulation differs from the one on the original tables. -/
noncomputable def deltaI1R [Fintype CI] : ℝ :=
  pr ((TIsR CI × (NRR × (TRe × TRe))) × ((Coins 16 × Tab3) × ShR R)) fun z =>
    (issRealR A PI (z.1.2.1, z.2.1)).out (PIR A progI z.1.1.1 z.1.1.2.1 z.2.2) ≠
      (issRealR A PI (z.1.2.1, z.2.1)).out z.2.2

/-- The issuance outputs of a spend hop's context. -/
abbrev i₀R {α : Type} (γ : (TIsR CI × TIsR CI) × α) : IssOut Z TokenS :=
  issSim A.base simI (γ.1.1.1.1, γ.1.1.1.2, γ.1.1.2.1)
abbrev i₁R {α : Type} (γ : (TIsR CI × TIsR CI) × α) : IssOut Z TokenS :=
  issSim A.base simI (γ.1.2.1.1, γ.1.2.1.2, γ.1.2.2.1)

/-- Round 1 runs. -/
abbrev ok1R {α : Type} (γ : (TIsR CI × TIsR CI) × α) : Bool :=
  ok₁ A.base (tokIface A.base) ((i₀R A simI γ).req, (i₁R A simI γ).req)
    ((i₀R A simI γ).fin (A.respondIss ((i₀R A simI γ).req, (i₁R A simI γ).req) false))
    ((i₁R A simI γ).fin (A.respondIss ((i₀R A simI γ).req, (i₁R A simI γ).req) true))

/-- The issuance programming of a spend hop's context. -/
abbrev PI2R {α : Type} (γ : (TIsR CI × TIsR CI) × α) (s : ShR R) : ShR R :=
  PIR A progI γ.1.1.1 γ.1.1.2.1 (PIR A progI γ.1.2.1 γ.1.2.2.1 s)

/-- The rest of the game around round 1's output: issuances simulated, round 2 real. -/
def FS1R (b₁ b₂ : Bool) (γ : ((TIsR CI × TIsR CI) × NRR) × TRe) (o : SpOut Z TokenS) (g : Tab3)
    (u : ShR R) : Prop :=
  viewR A b₁ b₂ (noProgI A simI γ.1.1.1) (noProgI A simI γ.1.1.2) (fakeS o g) (spRealR A PS γ.2) u

/-- **The collision term of hop S1**: round 1's real proof on the tables programmed by the
issuance simulations differs from the one on the original tables. -/
noncomputable def deltaS1R [Fintype CI] (b₁ : Bool) : ℝ :=
  pr ((((TIsR CI × TIsR CI) × NRR) × TRe) × ((Coins 16 × Tab3) × ShR R)) fun z =>
    (spRealR A PS (z.1.1.2, z.2.1)).out (τ₁Of A b₁ (i₀R A simI z.1.1) (i₁R A simI z.1.1))
        (A.d₁ ((i₀R A simI z.1.1).req, (i₁R A simI z.1.1).req)) (PI2R A progI z.1.1 z.2.2) ≠
      (spRealR A PS (z.1.1.2, z.2.1)).out (τ₁Of A b₁ (i₀R A simI z.1.1) (i₁R A simI z.1.1))
        (A.d₁ ((i₀R A simI z.1.1).req, (i₁R A simI z.1.1).req)) z.2.2

/-- Round 1's simulated output in a round-2 hop's context. -/
abbrev O₁R (b₁ : Bool) (γ : ((TIsR CI × TIsR CI) × TSsR CS) × NRR) : SpOut Z TokenS :=
  spSim A.base simS (γ.1.2.1.1, γ.1.2.1.2, γ.1.2.2.1) (τ₁Of A b₁ (i₀R A simI γ.1) (i₁R A simI γ.1))
    (A.d₁ ((i₀R A simI γ.1).req, (i₁R A simI γ.1).req))

/-- Round 2 runs (given round 1). -/
abbrev ok2R (b₁ : Bool) (γ : ((TIsR CI × TIsR CI) × TSsR CS) × NRR) : Bool :=
  ok₂ A.base (tokIface A.base) b₁ ((i₀R A simI γ.1).req, (i₁R A simI γ.1).req)
    ((i₀R A simI γ.1).fin (A.respondIss ((i₀R A simI γ.1).req, (i₁R A simI γ.1).req) false))
    ((i₁R A simI γ.1).fin (A.respondIss ((i₀R A simI γ.1).req, (i₁R A simI γ.1).req) true))
    (O₁R A simI simS b₁ γ).req ((O₁R A simI simS b₁ γ).fin
      (A.respond₁ ((i₀R A simI γ.1).req, (i₁R A simI γ.1).req) (O₁R A simI simS b₁ γ).req))

/-- The programming before round 2's: the issuances and round 1. -/
def LS2R (b₁ : Bool) (γ : ((TIsR CI × TIsR CI) × TSsR CS) × NRR) (s : ShR R) : ShR R :=
  PI2R A progI γ.1 (if ok1R A simI γ.1 = true then
    progS (xSOf A γ.1.2.1 (τ₁Of A b₁ (i₀R A simI γ.1) (i₁R A simI γ.1))
      (A.d₁ ((i₀R A simI γ.1).req, (i₁R A simI γ.1).req))) γ.1.2.2.1 s else s)

/-- Round 2's token and amount in its hop's context. -/
abbrev τ₂R (b₁ b₂ : Bool) (γ : ((TIsR CI × TIsR CI) × TSsR CS) × NRR) : TokenS :=
  τ₂Of A b₁ b₂ (i₀R A simI γ.1) (i₁R A simI γ.1) (O₁R A simI simS b₁ γ)
abbrev d₂R (b₁ : Bool) (γ : ((TIsR CI × TIsR CI) × TSsR CS) × NRR) : Credits :=
  A.d₂ ((i₀R A simI γ.1).req, (i₁R A simI γ.1).req) (O₁R A simI simS b₁ γ).req

/-- The rest of the game around round 2's output: everything else simulated. -/
def FS2R (b₁ b₂ : Bool) (γ : ((TIsR CI × TIsR CI) × TSsR CS) × NRR) (o : SpOut Z TokenS) (g : Tab3)
    (u : ShR R) : Prop :=
  viewR A b₁ b₂ (noProgI A simI γ.1.1.1) (noProgI A simI γ.1.1.2) (noProgS A simS γ.1.2) (fakeS o g) u

/-- **The collision term of hop S2**: round 2's real proof on the tables programmed by the other
three simulations differs from the one on the original tables. -/
noncomputable def deltaS2R [Fintype CI] [Fintype CS] (b₁ b₂ : Bool) : ℝ :=
  pr ((((TIsR CI × TIsR CI) × TSsR CS) × NRR) × ((Coins 16 × Tab3) × ShR R)) fun z =>
    (spRealR A PS (z.1.2, z.2.1)).out (τ₂R A simI simS b₁ b₂ z.1) (d₂R A simI simS b₁ z.1)
        (LS2R A simI progI progS b₁ z.1 z.2.2) ≠
      (spRealR A PS (z.1.2, z.2.1)).out (τ₂R A simI simS b₁ b₂ z.1) (d₂R A simI simS b₁ z.1) z.2.2

/-! ## The four hops -/

section Hops

variable {A PI PS simI simS progI progS} {q3 q5 qE r5 rE m5 mE : ℕ}

theorem hopI0R [Fintype CI] [Nonempty CI] (hA : A.Budget q3 q5 qE)
    (hPI5 : ∀ x w ρ g, Rd5 (PI x w ρ g) r5) (hPIE : ∀ x w ρ g, RdE (PI x w ρ g) rE)
    (hPS5 : ∀ x w ρ g, Rd5 (PS x w ρ g) r5) (hPSE : ∀ x w ρ g, RdE (PS x w ρ g) rE)
    {ε : ℝ} (hε : 0 ≤ ε) (hI : ZeroKnowledgeRO IssueRel
      (fun x w (ρ : Coins 16) g s => PI x w (vec ρ) g s) simI progI
      (Budget pI q3 (0 + (r5 + (r5 + (r5 + q5)))) (0 + (rE + (rE + (rE + qE))))) ε) (b₁ b₂ : Bool) :
    |pr _ (gameR A b₁ b₂ (issRealR A PI) (issRealR A PI) (spRealR A PS) (spRealR A PS)) -
      pr _ (gameR A b₁ b₂ (issSimR A simI progI) (issRealR A PI) (spRealR A PS) (spRealR A PS))| ≤
      ε := by
  have h := hop_ro (Γ := NRR × (TRe × (TRe × TRe))) (ρ := Coins 16) (G := Tab3) (C := CI) (S := ShR R)
    (fun γ ρ g s => (issRealR A PI (γ.1, (ρ, g))).out s)
    (fun γ c => issSim A.base simI (γ.1.1, γ.1.2, c)) (fun γ c s => PIR A progI γ.1 c s)
    (fun _ s => s) (F0R A PI PS b₁ b₂) (ε := ε) fun γ => ?_
  · have hδ : pr ((NRR × (TRe × (TRe × TRe))) × ((Coins 16 × Tab3) × ShR R)) (fun z =>
        (issRealR A PI (z.1.1, (z.2.1.1, z.2.1.2))).out z.2.2 ≠
          (issRealR A PI (z.1.1, (z.2.1.1, z.2.1.2))).out z.2.2) = 0 := by
      rw [pr_congr (Q := fun _ => False) fun z => by simp, pr_const]
      simp
    rw [hδ, add_zero] at h
    rw [← pr_equiv eqv0R (gameR A b₁ b₂ (issRealR A PI) (issRealR A PI) (spRealR A PS)
        (spRealR A PS)), ← pr_equiv eqv0R (gameR A b₁ b₂ (issSimR A simI progI) (issRealR A PI)
        (spRealR A PS) (spRealR A PS))]
    exact le_of_eq_of_le (congrArg₂ (fun a c => |a - c|) (pr_congr fun z => Iff.rfl)
      (pr_congr fun z => Iff.rfl)) h
  · by_cases hT : A.tInit = 0
    · simp only [issRealR_out_zero hT, issSim_zero hT, PIR, hT, ↓reduceIte]
      exact (hop_ro_unused (ρ := Coins 16) (C := CI) (fun g u => F0R A PI PS b₁ b₂ γ
        (issOutOf A.base (.error .invalidArgument)) g u)).trans hε
    · simp only [issRealR_out_ne hT, issSim_ne hT, PIR, hT, ↓reduceIte]
      exact hI (xIOf A γ.1) ⟨vec γ.1.1, vec γ.1.2⟩ rfl
        (fun o g s => F0R A PI PS b₁ b₂ γ (ΦI A γ.1 o) g s)
        ⟨fun o s => rd3_viewR0 hA b₁ b₂ _ _ _ _ _ _,
          fun o g => rd5_viewR hA b₁ b₂ (fun _ => ΦI A γ.1 o) (issRealR A PI γ.2.1).out g
            γ.2.1.2.2 γ.2.2.1.2.2 γ.2.2.2.2.2 (spRealR A PS γ.2.2.1).out (spRealR A PS γ.2.2.2).out
            (Rd5.const _) (rd5_issRealR hPI5 _) (rd5_spRealR hPS5 _) (rd5_spRealR hPS5 _),
          fun o g => rdE_viewR hA b₁ b₂ (fun _ => ΦI A γ.1 o) (issRealR A PI γ.2.1).out g
            γ.2.1.2.2 γ.2.2.1.2.2 γ.2.2.2.2.2 (spRealR A PS γ.2.2.1).out (spRealR A PS γ.2.2.2).out
            (RdE.const _) (rdE_issRealR hPIE _) (rdE_spRealR hPSE _) (rdE_spRealR hPSE _)⟩

lemma isProg_PIR (hpI : ∀ x c, IsProg (progI x c) m5 mE) (n : NRR) (c : CI) :
    IsProg (PIR A progI n c) m5 mE :=
  IsProg.ite _ (IsProg.id.mono (Nat.zero_le _) (Nat.zero_le _)) (hpI _ _)

theorem hopI1R [Fintype CI] [Nonempty CI] (hA : A.Budget q3 q5 qE)
    (hPS5 : ∀ x w ρ g, Rd5 (PS x w ρ g) r5) (hPSE : ∀ x w ρ g, RdE (PS x w ρ g) rE)
    (hpI : ∀ x c, IsProg (progI x c) m5 mE)
    {ε : ℝ} (hε : 0 ≤ ε) (hI : ZeroKnowledgeRO IssueRel
      (fun x w (ρ : Coins 16) g s => PI x w (vec ρ) g s) simI progI
      (Budget pI q3 (0 + (0 + (r5 + (r5 + q5))) + m5) (0 + (0 + (rE + (rE + qE))) + mE)) ε)
    (b₁ b₂ : Bool) :
    |pr _ (gameR A b₁ b₂ (issSimR A simI progI) (issRealR A PI) (spRealR A PS) (spRealR A PS)) -
      pr _ (gameR A b₁ b₂ (issSimR A simI progI) (issSimR A simI progI) (spRealR A PS)
        (spRealR A PS))| ≤ ε + deltaI1R A progI PI := by
  have h := hop_ro (Γ := TIsR CI × (NRR × (TRe × TRe))) (ρ := Coins 16) (G := Tab3) (C := CI)
    (S := ShR R) (fun γ ρ g s => (issRealR A PI (γ.2.1, (ρ, g))).out s)
    (fun γ c => issSim A.base simI (γ.2.1.1, γ.2.1.2, c)) (fun γ c s => PIR A progI γ.2.1 c s)
    (fun γ s => PIR A progI γ.1.1 γ.1.2.1 s) (F1R A simI PS b₁ b₂) (ε := ε) fun γ => ?_
  · rw [← pr_equiv eqv1R (gameR A b₁ b₂ (issSimR A simI progI) (issRealR A PI) (spRealR A PS)
        (spRealR A PS)), ← pr_equiv eqv1R (gameR A b₁ b₂ (issSimR A simI progI)
        (issSimR A simI progI) (spRealR A PS) (spRealR A PS))]
    exact le_of_eq_of_le (congrArg₂ (fun a c => |a - c|) (pr_congr fun z => Iff.rfl)
      (pr_congr fun z => Iff.rfl)) h
  · by_cases hT : A.tInit = 0
    · simp only [issRealR_out_zero hT, issSim_zero hT, PIR, hT, ↓reduceIte]
      exact (hop_ro_unused (ρ := Coins 16) (C := CI) (fun g u => F1R A simI PS b₁ b₂ γ
        (issOutOf A.base (.error .invalidArgument)) g u)).trans hε
    · have hL : IsProg (progI (xIOf A γ.1.1) γ.1.2.1) m5 mE := hpI _ _
      simp only [issRealR_out_ne hT, issSim_ne hT, PIR, hT, ↓reduceIte]
      exact hI (xIOf A γ.2.1) ⟨vec γ.2.1.1, vec γ.2.1.2⟩ rfl
        (fun o g s => F1R A simI PS b₁ b₂ γ (ΦI A γ.2.1 o) g (progI (xIOf A γ.1.1) γ.1.2.1 s))
        ⟨fun o s => rd3_viewR1 hA b₁ b₂ _ _ _ _ _ _,
          fun o g => (rd5_viewR hA b₁ b₂ (noProgI A simI γ.1).out (fun _ => ΦI A γ.2.1 o) γ.1.2.2 g
            γ.2.2.1.2.2 γ.2.2.2.2.2 (spRealR A PS γ.2.2.1).out (spRealR A PS γ.2.2.2).out
            (Rd5.const _) (Rd5.const _) (rd5_spRealR hPS5 _) (rd5_spRealR hPS5 _)).comp_prog hL,
          fun o g => (rdE_viewR hA b₁ b₂ (noProgI A simI γ.1).out (fun _ => ΦI A γ.2.1 o) γ.1.2.2 g
            γ.2.2.1.2.2 γ.2.2.2.2.2 (spRealR A PS γ.2.2.1).out (spRealR A PS γ.2.2.2).out
            (RdE.const _) (RdE.const _) (rdE_spRealR hPSE _) (rdE_spRealR hPSE _)).comp_prog hL⟩

theorem hopS1R [Fintype CI] [Nonempty CI] [Fintype CS] [Nonempty CS] (hA : A.Budget q3 q5 qE)
    (hPS5 : ∀ x w ρ g, Rd5 (PS x w ρ g) r5) (hPSE : ∀ x w ρ g, RdE (PS x w ρ g) rE)
    (hpI : ∀ x c, IsProg (progI x c) m5 mE)
    {ε : ℝ} (hε : 0 ≤ ε) (hS : ZeroKnowledgeRO SpendRel
      (fun x w (ρ : Coins 16) g s => PS x w (vec ρ) g s) simS progS
      (Budget pS q3 (0 + (0 + (0 + (r5 + q5))) + (m5 + m5)) (0 + (0 + (0 + (rE + qE))) + (mE + mE))) ε)
    (b₁ b₂ : Bool) :
    |pr _ (gameR A b₁ b₂ (issSimR A simI progI) (issSimR A simI progI) (spRealR A PS)
        (spRealR A PS)) -
      pr _ (gameR A b₁ b₂ (issSimR A simI progI) (issSimR A simI progI) (spSimR A simS progS)
        (spRealR A PS))| ≤ ε + deltaS1R A simI progI PS b₁ := by
  have h := hop_ro (Γ := ((TIsR CI × TIsR CI) × NRR) × TRe) (ρ := Coins 16) (G := Tab3) (C := CS)
    (S := ShR R)
    (fun γ ρ g s => (spRealR A PS (γ.1.2, (ρ, g))).out (τ₁Of A b₁ (i₀R A simI γ.1) (i₁R A simI γ.1))
      (A.d₁ ((i₀R A simI γ.1).req, (i₁R A simI γ.1).req)) s)
    (fun γ c => spSim A.base simS (γ.1.2.1, γ.1.2.2, c) (τ₁Of A b₁ (i₀R A simI γ.1) (i₁R A simI γ.1))
      (A.d₁ ((i₀R A simI γ.1).req, (i₁R A simI γ.1).req)))
    (fun γ c s => if ok1R A simI γ.1 = true then
      progS (xSOf A γ.1.2 (τ₁Of A b₁ (i₀R A simI γ.1) (i₁R A simI γ.1))
        (A.d₁ ((i₀R A simI γ.1).req, (i₁R A simI γ.1).req))) c s else s)
    (fun γ s => PI2R A progI γ.1 s) (FS1R A simI PS b₁ b₂) (ε := ε) fun γ => ?_
  · rw [← pr_equiv eqv2R (gameR A b₁ b₂ (issSimR A simI progI) (issSimR A simI progI)
        (spRealR A PS) (spRealR A PS)), ← pr_equiv eqv2R (gameR A b₁ b₂ (issSimR A simI progI)
        (issSimR A simI progI) (spSimR A simS progS) (spRealR A PS))]
    exact le_of_eq_of_le (congrArg₂ (fun a c => |a - c|) (pr_congr fun z => Iff.rfl)
      (pr_congr fun z => Iff.rfl)) h
  · have hL : IsProg (PI2R A progI γ.1) (m5 + m5) (mE + mE) :=
      (isProg_PIR hpI _ _).comp (isProg_PIR hpI _ _)
    cases hok : ok1R A simI γ.1
    · -- Round 1 does not run: its output is not read.
      have e : ∀ o g u, FS1R A simI PS b₁ b₂ γ o g u ↔
          FS1R A simI PS b₁ b₂ γ (spOutOf A.base (.error .invalidArgument)) g u := fun o g u => by
        simp only [FS1R, viewR, fakeS, noProgI, spRealR, hok, Bool.cond_false]
      simp only [Bool.false_eq_true, ↓reduceIte]
      exact le_of_eq_of_le (congrArg₂ (fun x y => |x - y|) (pr_congr fun a => e _ _ _)
        (pr_congr fun a => e _ _ _)) ((hop_ro_unused (ρ := Coins 16) (C := CS) (fun g u =>
          FS1R A simI PS b₁ b₂ γ (spOutOf A.base (.error .invalidArgument)) g
            (PI2R A progI γ.1 u))).trans hε)
    · obtain ⟨hv, t', hc⟩ := valid_of_ok (τ := τ₁Of A b₁ (i₀R A simI γ.1) (i₁R A simI γ.1))
        (d := A.d₁ ((i₀R A simI γ.1).req, (i₁R A simI γ.1).req)) (ok_of_ok₁ (B := A.base) b₁ hok)
      simp only [↓reduceIte, spRealR_out_ok _ hv hc, spSim_ok _ _ hv hc]
      exact hS _ _ (spendRel_of A γ.1.2 hv hc)
        (fun o g s => FS1R A simI PS b₁ b₂ γ (spOfProof A γ.1.2 (τ₁Of A b₁ (i₀R A simI γ.1)
          (i₁R A simI γ.1)) (A.d₁ ((i₀R A simI γ.1).req, (i₁R A simI γ.1).req)) t' o) g
          (PI2R A progI γ.1 s))
        ⟨fun o s => rd3_viewR2 hA b₁ b₂ _ _ _ _ _ _,
          fun o g => (rd5_viewR hA b₁ b₂ (noProgI A simI γ.1.1.1).out (noProgI A simI γ.1.1.2).out
            γ.1.1.1.2.2 γ.1.1.2.2.2 g γ.2.2.2 _ (spRealR A PS γ.2).out
            (Rd5.const _) (Rd5.const _) (fun _ _ => Rd5.const _) (rd5_spRealR hPS5 _)).comp_prog hL,
          fun o g => (rdE_viewR hA b₁ b₂ (noProgI A simI γ.1.1.1).out (noProgI A simI γ.1.1.2).out
            γ.1.1.1.2.2 γ.1.1.2.2.2 g γ.2.2.2 _ (spRealR A PS γ.2).out
            (RdE.const _) (RdE.const _) (fun _ _ => RdE.const _) (rdE_spRealR hPSE _)).comp_prog hL⟩

theorem hopS2R [Fintype CI] [Nonempty CI] [Fintype CS] [Nonempty CS] (hA : A.Budget q3 q5 qE)
    (hpI : ∀ x c, IsProg (progI x c) m5 mE) (hpS : ∀ x c, IsProg (progS x c) m5 mE)
    {ε : ℝ} (hε : 0 ≤ ε) (hS : ZeroKnowledgeRO SpendRel
      (fun x w (ρ : Coins 16) g s => PS x w (vec ρ) g s) simS progS
      (Budget pS q3 (0 + (0 + (0 + (0 + q5))) + (m5 + (m5 + m5)))
        (0 + (0 + (0 + (0 + qE))) + (mE + (mE + mE)))) ε) (b₁ b₂ : Bool) :
    |pr _ (gameR A b₁ b₂ (issSimR A simI progI) (issSimR A simI progI) (spSimR A simS progS)
        (spRealR A PS)) -
      pr _ (simGameR A simI simS progI progS b₁ b₂)| ≤
      ε + deltaS2R A simI simS progI progS PS b₁ b₂ := by
  have h := hop_ro (Γ := ((TIsR CI × TIsR CI) × TSsR CS) × NRR) (ρ := Coins 16) (G := Tab3)
    (C := CS) (S := ShR R)
    (fun γ ρ g s => (spRealR A PS (γ.2, (ρ, g))).out (τ₂R A simI simS b₁ b₂ γ)
      (d₂R A simI simS b₁ γ) s)
    (fun γ c => spSim A.base simS (γ.2.1, γ.2.2, c) (τ₂R A simI simS b₁ b₂ γ) (d₂R A simI simS b₁ γ))
    (fun γ c s => if (ok1R A simI γ.1 && ok2R A simI simS b₁ γ) = true then
      progS (xSOf A γ.2 (τ₂R A simI simS b₁ b₂ γ) (d₂R A simI simS b₁ γ)) c s else s)
    (LS2R A simI progI progS b₁) (FS2R A simI simS b₁ b₂) (ε := ε) fun γ => ?_
  · rw [← pr_equiv eqv3R (gameR A b₁ b₂ (issSimR A simI progI) (issSimR A simI progI)
        (spSimR A simS progS) (spRealR A PS)),
      ← pr_equiv eqv3R (simGameR A simI simS progI progS b₁ b₂)]
    exact le_of_eq_of_le (congrArg₂ (fun a c => |a - c|) (pr_congr fun z => Iff.rfl)
      (pr_congr fun z => Iff.rfl)) h
  · have hL : IsProg (LS2R A simI progI progS b₁ γ) (m5 + (m5 + m5)) (mE + (mE + mE)) :=
      (isProg_PIR hpI _ _).comp ((isProg_PIR hpI _ _).comp (IsProg.ite _ (hpS _ _)
        (IsProg.id.mono (Nat.zero_le _) (Nat.zero_le _))))
    cases hok : (ok1R A simI γ.1 && ok2R A simI simS b₁ γ)
    · -- Round 2 does not run: its output is not read.
      have e : ∀ o g u, FS2R A simI simS b₁ b₂ γ o g u ↔
          FS2R A simI simS b₁ b₂ γ (spOutOf A.base (.error .invalidArgument)) g u := fun o g u => by
        rcases Bool.and_eq_false_iff.1 hok with h1 | h2
        · simp only [FS2R, viewR, fakeS, noProgI, noProgS, h1, Bool.cond_false]
        · simp only [ok2R, O₁R, τ₁Of] at h2
          simp only [FS2R, viewR, fakeS, noProgI, noProgS, h2, Bool.cond_false]
      simp only [Bool.false_eq_true, ↓reduceIte]
      exact le_of_eq_of_le (congrArg₂ (fun x y => |x - y|) (pr_congr fun a => e _ _ _)
        (pr_congr fun a => e _ _ _)) ((hop_ro_unused (ρ := Coins 16) (C := CS) (fun g u =>
          FS2R A simI simS b₁ b₂ γ (spOutOf A.base (.error .invalidArgument)) g
            (LS2R A simI progI progS b₁ γ u))).trans hε)
    · obtain ⟨h1, h2⟩ := Bool.and_eq_true_iff.1 hok
      obtain ⟨hv, t', hc⟩ := valid_of_ok (τ := τ₂R A simI simS b₁ b₂ γ) (d := d₂R A simI simS b₁ γ)
        (ok_of_ok₂ (B := A.base) b₁ b₂ h2)
      simp only [↓reduceIte, spRealR_out_ok _ hv hc, spSim_ok _ _ hv hc]
      exact hS _ _ (spendRel_of A γ.2 hv hc)
        (fun o g s => FS2R A simI simS b₁ b₂ γ (spOfProof A γ.2 (τ₂R A simI simS b₁ b₂ γ)
          (d₂R A simI simS b₁ γ) t' o) g (LS2R A simI progI progS b₁ γ s))
        ⟨fun o s => rd3_viewR3 hA b₁ b₂ _ _ _ _ _ _,
          fun o g => (rd5_viewR hA b₁ b₂ (noProgI A simI γ.1.1.1).out (noProgI A simI γ.1.1.2).out
            γ.1.1.1.2.2 γ.1.1.2.2.2 γ.1.2.2.2 g (noProgS A simS γ.1.2).out _
            (Rd5.const _) (Rd5.const _) (fun _ _ => Rd5.const _) (fun _ _ => Rd5.const _)).comp_prog hL,
          fun o g => (rdE_viewR hA b₁ b₂ (noProgI A simI γ.1.1.1).out (noProgI A simI γ.1.1.2).out
            γ.1.1.1.2.2 γ.1.1.2.2.2 γ.1.2.2.2 g (noProgS A simS γ.1.2).out _
            (RdE.const _) (RdE.const _) (fun _ _ => RdE.const _) (fun _ _ => RdE.const _)).comp_prog hL⟩

end Hops

/-! ## Unlinkability in the random-oracle model -/

variable {A PI PS simI simS progI progS} in
/-- **Theorem 2 in the random-oracle and ideal-cipher model, for any proof systems.** The real
game runs the spec with every proof computed on the shared tables, and the Issuer's guess sees all
tables (budget `q₃, q₅, q_E`). If the issuance and spend proofs are `ZeroKnowledgeRO` (errors
`εI`, `εS` as functions of the budgets), their real provers read `H₅` and the cipher at `r₅`,
`r_E` keys, their programmings at `m₅`, `m_E` keys, a simulation that produces no proof
programs independently of its instance (`hprogI`, `hprogS`), and the hiding reductions
(simulator coins and tables fixed) have advantage `≤ εhide`, then any two worlds differ by at
most the zero-knowledge errors at the reductions' budgets and the collision terms of both worlds,
plus `2εhide`. -/
theorem unlinkabilityRO [Fintype CI] [Nonempty CI] [Fintype CS] [Nonempty CS]
    {q3 q5 qE r5 rE m5 mE : ℕ} {εI εS : ℕ → ℕ → ℕ → ℝ} {εhide : ℝ}
    (hA : A.Budget q3 q5 qE)
    (hPI5 : ∀ x w ρ g, Rd5 (PI x w ρ g) r5) (hPIE : ∀ x w ρ g, RdE (PI x w ρ g) rE)
    (hPS5 : ∀ x w ρ g, Rd5 (PS x w ρ g) r5) (hPSE : ∀ x w ρ g, RdE (PS x w ρ g) rE)
    (hpI : ∀ x c, IsProg (progI x c) m5 mE) (hpS : ∀ x c, IsProg (progS x c) m5 mE)
    (hprogI : ∀ x x' c, simI x c = none → progI x c = progI x' c)
    (hprogS : ∀ x x' c, simS x c = none → progS x c = progS x' c)
    (hI : ∀ a c, ZeroKnowledgeRO IssueRel (fun x w (ρ : Coins 16) g s => PI x w (vec ρ) g s) simI
      progI (Budget pI q3 a c) (εI q3 a c))
    (hS : ∀ a c, ZeroKnowledgeRO SpendRel (fun x w (ρ : Coins 16) g s => PS x w (vec ρ) g s) simS
      progS (Budget pS q3 a c) (εS q3 a c))
    (hεI : ∀ a c, 0 ≤ εI q3 a c) (hεS : ∀ a c, 0 ≤ εS q3 a c)
    (hhide : ∀ b₁ b₂ K, hidingAdv A.ctx (reductionR A simI simS progI progS b₁ b₂ K) ≤ εhide)
    (b₁ b₂ b₁' b₂' : Bool) :
    |pr _ (realGameR A PI PS b₁ b₂) - pr _ (realGameR A PI PS b₁' b₂')| ≤
      2 * (εI q3 (0 + (r5 + (r5 + (r5 + q5)))) (0 + (rE + (rE + (rE + qE)))) +
          εI q3 (0 + (0 + (r5 + (r5 + q5))) + m5) (0 + (0 + (rE + (rE + qE))) + mE) +
          εS q3 (0 + (0 + (0 + (r5 + q5))) + (m5 + m5)) (0 + (0 + (0 + (rE + qE))) + (mE + mE)) +
          εS q3 (0 + (0 + (0 + (0 + q5))) + (m5 + (m5 + m5)))
            (0 + (0 + (0 + (0 + qE))) + (mE + (mE + mE)))) +
        2 * deltaI1R A progI PI +
        (deltaS1R A simI progI PS b₁ + deltaS1R A simI progI PS b₁') +
        (deltaS2R A simI simS progI progS PS b₁ b₂ + deltaS2R A simI simS progI progS PS b₁' b₂') +
        2 * εhide := by
  have hw (c₁ c₂ : Bool) : |pr _ (realGameR A PI PS c₁ c₂) -
      pr _ (idealGameR A simI simS progI progS c₁ c₂)| ≤
      εI q3 (0 + (r5 + (r5 + (r5 + q5)))) (0 + (rE + (rE + (rE + qE)))) +
        (εI q3 (0 + (0 + (r5 + (r5 + q5))) + m5) (0 + (0 + (rE + (rE + qE))) + mE) +
          deltaI1R A progI PI) +
        (εS q3 (0 + (0 + (0 + (r5 + q5))) + (m5 + m5)) (0 + (0 + (0 + (rE + qE))) + (mE + mE)) +
          deltaS1R A simI progI PS c₁) +
        (εS q3 (0 + (0 + (0 + (0 + q5))) + (m5 + (m5 + m5)))
            (0 + (0 + (0 + (0 + qE))) + (mE + (mE + mE))) +
          deltaS2R A simI simS progI progS PS c₁ c₂) + εhide := by
    have h1 := hopI0R (A := A) (PI := PI) (PS := PS) (simI := simI) (progI := progI) hA hPI5 hPIE
      hPS5 hPSE (hεI _ _) (hI _ _) c₁ c₂
    have h2 := hopI1R (A := A) (PI := PI) (PS := PS) (simI := simI) (progI := progI) hA hPS5 hPSE
      hpI (hεI _ _) (hI _ _) c₁ c₂
    have h3 := hopS1R (A := A) (PS := PS) (simI := simI) (simS := simS) (progI := progI)
      (progS := progS) hA hPS5 hPSE hpI (hεS _ _) (hS _ _) c₁ c₂
    have h4 := hopS2R (A := A) (PS := PS) (simI := simI) (simS := simS) (progI := progI)
      (progS := progS) hA hpI hpS (hεS _ _) (hS _ _) c₁ c₂
    have h5 := hiding_hopR A simI simS progI progS hprogI hprogS c₁ c₂ (hhide c₁ c₂)
    unfold realGameR
    set p0 := pr _ (gameR A c₁ c₂ (issRealR A PI) (issRealR A PI) (spRealR A PS) (spRealR A PS))
    set p1 := pr _ (gameR A c₁ c₂ (issSimR A simI progI) (issRealR A PI) (spRealR A PS)
      (spRealR A PS))
    set p2 := pr _ (gameR A c₁ c₂ (issSimR A simI progI) (issSimR A simI progI) (spRealR A PS)
      (spRealR A PS))
    set p3 := pr _ (gameR A c₁ c₂ (issSimR A simI progI) (issSimR A simI progI)
      (spSimR A simS progS) (spRealR A PS))
    set p4 := pr _ (simGameR A simI simS progI progS c₁ c₂)
    set p5 := pr _ (idealGameR A simI simS progI progS c₁ c₂)
    have := abs_sub_le p0 p1 p5
    have := abs_sub_le p1 p2 p5
    have := abs_sub_le p2 p3 p5
    have := abs_sub_le p3 p4 p5
    linarith
  have h := hw b₁ b₂
  have h' := hw b₁' b₂'
  rw [idealGameR_eq] at h h'
  rw [abs_sub_comm] at h'
  have := abs_sub_le (pr _ (realGameR A PI PS b₁ b₂))
    (pr _ (idealGameR A simI simS progI progS false false)) (pr _ (realGameR A PI PS b₁' b₂'))
  linarith

/-! ## With the Lean prover -/

section Lean

open VoleMole.Verifier VoleMole.Verifier.Bridge

variable [CipherRow R]

/-- **The Lean issuance prover in the random-oracle model** (`ZK.Sim.realROb` with SHAKE for the
hashes that are not tables), as the spec's proof. -/
noncomputable def leanPIR : ProverI R Sizes.labelRows := fun x w ρ g s =>
  vecOf _ (realROb pI Hashes.shake (stI x) (encI x w) (bOf ρ) g s)

/-- The Lean spend prover in the random-oracle model. -/
noncomputable def leanPSR : ProverS R Sizes.labelRows := fun x w ρ g s =>
  vecOf _ (realROb pS Hashes.shake (stS x) (encS x w) (bOf ρ) g s)

/-- The simulators, as the spec's proofs. -/
def leanSimIR (_ : IssueInstance) (c : SimCoins pI) : Option (IssueProof Sizes.labelRows) :=
  vecOf _ (simulate pI c)
def leanSimSR (_ : SpendInstance) (c : SimCoins pS) : Option (SpendProof Sizes.labelRows) :=
  vecOf _ (simulate pS c)

/-- The simulators' programmings (`ZK.Sim.progRO`). -/
noncomputable def leanProgIR (x : IssueInstance) (c : SimCoins pI) : ShR R → ShR R :=
  progRO pI Hashes.shake (stI x) c
noncomputable def leanProgSR (x : SpendInstance) (c : SimCoins pS) : ShR R → ShR R :=
  progRO pS Hashes.shake (stS x) c

lemma vecOf_none_simulate {p : Params} {n : ℕ} (hn : p.proofBytes = n) {c : SimCoins p}
    (h : vecOf n (simulate p c) = none) : ∃ e, simulate p c = .error e := by
  cases hs : simulate p c with
  | error e => exact ⟨e, rfl⟩
  | ok b =>
    rw [hs] at h
    simp only [vecOf, simulate_ok_size hs, hn, ↓reduceDIte, reduceCtorEq] at h

lemma leanProgIR_none (x x' : IssueInstance) (c : SimCoins pI) (h : leanSimIR x c = none) :
    leanProgIR (R := R) x c = leanProgIR x' c := by
  obtain ⟨e, he⟩ := vecOf_none_simulate (by decide) h
  exact progRO_of_error (R := R) _ he _ _

lemma leanProgSR_none (x x' : SpendInstance) (c : SimCoins pS) (h : leanSimSR x c = none) :
    leanProgSR (R := R) x c = leanProgSR x' c := by
  obtain ⟨e, he⟩ := vecOf_none_simulate (by decide) h
  exact progRO_of_error (R := R) _ he _ _

/-- **Zero knowledge of the Lean issuance prover in the random-oracle model** (cipher rows `R`,
error `ZKRow.εz R pI`). -/
theorem leanPIR_zkRO [ZKRow R] (q3 q5 qE : ℕ) : ZeroKnowledgeRO IssueRel
    (fun x w (ρ : Coins 16) g (s : ShR R) => leanPIR x w (vec ρ) g s) leanSimIR leanProgIR
    (Budget pI q3 q5 qE) (ZKRow.εz R pI q3 q5 qE) := by
  have h := (lean_zeroKnowledgeROG (R := R) Hashes.shake pI stI (fun _ => rfl) rfl encI IssueRel
    csI zkHypI hashesWF_shake (smallParams_of_le (by decide) (by decide)) q3 q5 qE).transfer
    id (fun _ w => w) (fun _ _ h => h) (vecOf Sizes.labelRows.issue)
    (Adm' := Budget pI q3 q5 qE) (fun D hD => Budget.comp _ hD)
  have e : (fun x w (ρ : Coins 16) g (s : ShR R) => leanPIR x w (vec ρ) g s) =
      fun x w r g s => vecOf _ (realRO pI Hashes.shake (stI (id x)) (encI (id x) w) r g s) := by
    funext x w ρ g s
    simp only [leanPIR, realRO, bOf_vec, id]
  rw [e]
  exact h

/-- **Zero knowledge of the Lean spend prover in the random-oracle model.** -/
theorem leanPSR_zkRO [ZKRow R] (q3 q5 qE : ℕ) : ZeroKnowledgeRO SpendRel
    (fun x w (ρ : Coins 16) g (s : ShR R) => leanPSR x w (vec ρ) g s) leanSimSR leanProgSR
    (Budget pS q3 q5 qE) (ZKRow.εz R pS q3 q5 qE) := by
  have h := (lean_zeroKnowledgeROG (R := R) Hashes.shake pS stS (fun _ => rfl) rfl encS SpendRel
    csS zkHypS hashesWF_shake (smallParams_of_le (by decide) (by decide)) q3 q5 qE).transfer
    id (fun _ w => w) (fun _ _ h => h) (vecOf Sizes.labelRows.spend)
    (Adm' := Budget pS q3 q5 qE) (fun D hD => Budget.comp _ hD)
  have e : (fun x w (ρ : Coins 16) g (s : ShR R) => leanPSR x w (vec ρ) g s) =
      fun x w r g s => vecOf _ (realRO pS Hashes.shake (stS (id x)) (encS (id x) w) r g s) := by
    funext x w ρ g s
    simp only [leanPSR, realRO, bOf_vec, id]
  rw [e]
  exact h

/-- **Theorem 2 with the Lean prover, for every type of cipher rows** (`ZKRow R`): any two
worlds differ by at most

    4·εz(pI; q₃, q₅ + 3·624, q_E + 3·4607) + 4·εz(pS; q₃, q₅ + 3·624, q_E + 3·4607)
      + 2·δI₁ + Σ_w (δS₁ w + δS₂ w) + 2·εhide. -/
theorem unlinkabilityRO_leanG [ZKRow R] (A : AdversaryRO R Sizes.labelRows) {q3 q5 qE : ℕ}
    {εhide : ℝ} (hA : A.Budget q3 q5 qE)
    (hhide : ∀ b₁ b₂ K, hidingAdv A.ctx
      (reductionR A leanSimIR leanSimSR leanProgIR leanProgSR b₁ b₂ K) ≤ εhide)
    (b₁ b₂ b₁' b₂' : Bool) :
    |pr _ (realGameR A leanPIR leanPSR b₁ b₂) - pr _ (realGameR A leanPIR leanPSR b₁' b₂')| ≤
      4 * ZKRow.εz R pI q3 (q5 + 1872) (qE + 13821) +
        4 * ZKRow.εz R pS q3 (q5 + 1872) (qE + 13821) + 2 * deltaI1R A leanProgIR leanPIR +
        (deltaS1R A leanSimIR leanProgIR leanPSR b₁ + deltaS1R A leanSimIR leanProgIR leanPSR b₁') +
        (deltaS2R A leanSimIR leanSimSR leanProgIR leanProgSR leanPSR b₁ b₂ +
          deltaS2R A leanSimIR leanSimSR leanProgIR leanProgSR leanPSR b₁' b₂') +
        2 * εhide := by
  have hPI5 : ∀ x w ρ g, Rd5 (leanPIR (R := R) x w ρ g) 624 := fun x w ρ g =>
    (realROb_rd5 (p := pI) (Hb := Hashes.shake) (st := stI x) (w := encI x w) (bOf ρ) g).map (vecOf Sizes.labelRows.issue)
  have hPIE : ∀ x w ρ g, RdE (leanPIR (R := R) x w ρ g) 4607 := fun x w ρ g =>
    (realROb_rdE (p := pI) (st := stI x) (w := encI x w) hashesWF_shake (bOf ρ) g).map (vecOf Sizes.labelRows.issue)
  have hPS5 : ∀ x w ρ g, Rd5 (leanPSR (R := R) x w ρ g) 624 := fun x w ρ g =>
    (realROb_rd5 (p := pS) (Hb := Hashes.shake) (st := stS x) (w := encS x w) (bOf ρ) g).map (vecOf Sizes.labelRows.spend)
  have hPSE : ∀ x w ρ g, RdE (leanPSR (R := R) x w ρ g) 4607 := fun x w ρ g =>
    (realROb_rdE (p := pS) (st := stS x) (w := encS x w) hashesWF_shake (bOf ρ) g).map (vecOf Sizes.labelRows.spend)
  have h := unlinkabilityRO (A := A) (PI := leanPIR) (PS := leanPSR) (simI := leanSimIR)
    (simS := leanSimSR) (progI := leanProgIR) (progS := leanProgSR) (εI := ZKRow.εz R pI)
    (εS := ZKRow.εz R pS)
    hA hPI5 hPIE hPS5 hPSE (fun x c => progRO_isProg c) (fun x c => progRO_isProg c)
    leanProgIR_none leanProgSR_none (fun a c => leanPIR_zkRO q3 a c) (fun a c => leanPSR_zkRO q3 a c)
    (fun a c => ZKRow.εz_nonneg _ _ _ _) (fun a c => ZKRow.εz_nonneg _ _ _ _) hhide b₁ b₂ b₁' b₂'
  have m : ∀ (p : Params) a c, a ≤ q5 + 1872 → c ≤ qE + 13821 →
      ZKRow.εz R p q3 a c ≤ ZKRow.εz R p q3 (q5 + 1872) (qE + 13821) :=
    fun p a c ha hc => ZKRow.εz_mono p le_rfl ha hc
  have m1 := m pI (0 + (624 + (624 + (624 + q5)))) (0 + (4607 + (4607 + (4607 + qE)))) (by omega)
    (by omega)
  have m2 := m pI (0 + (0 + (624 + (624 + q5))) + 312) (0 + (0 + (4607 + (4607 + qE))) + 4607)
    (by omega) (by omega)
  have m3 := m pS (0 + (0 + (0 + (624 + q5))) + (312 + 312))
    (0 + (0 + (0 + (4607 + qE))) + (4607 + 4607)) (by omega) (by omega)
  have m4 := m pS (0 + (0 + (0 + (0 + q5))) + (312 + (312 + 312)))
    (0 + (0 + (0 + (0 + qE))) + (4607 + (4607 + 4607))) (by omega) (by omega)
  linarith

/-- **Theorem 2 with the Lean prover, in the random-oracle and ideal-cipher model.** The real
game runs the spec with the Lean prover (dedicated label rows), `H₃`, `H₂³`, `H₅` uniform tables,
the cipher a uniform table, SHAKE for the other hashes; the Issuer's guess sees every table,
reading each `H₃` slice at `q₃` keys, `H₅` at `q₅`, the cipher at `q_E` keys and `H₂³` freely (its
interaction does not read them). Any two worlds differ by at most

    8·εRO(q₃, q₅ + 3·624, q_E + 3·4607) + 2·δI₁ + Σ_w (δS₁ w + δS₂ w) + 2·εhide.

(`unlinkabilityRO_leanG` at function rows.) -/
theorem unlinkabilityRO_lean (A : AdversaryRO (Blk → Blk) Sizes.labelRows) {q3 q5 qE : ℕ}
    {εhide : ℝ} (hA : A.Budget q3 q5 qE)
    (hhide : ∀ b₁ b₂ K, hidingAdv A.ctx
      (reductionR A leanSimIR leanSimSR leanProgIR leanProgSR b₁ b₂ K) ≤ εhide)
    (b₁ b₂ b₁' b₂' : Bool) :
    |pr _ (realGameR A leanPIR leanPSR b₁ b₂) - pr _ (realGameR A leanPIR leanPSR b₁' b₂')| ≤
      8 * εRO q3 (q5 + 1872) (qE + 13821) + 2 * deltaI1R A leanProgIR leanPIR +
        (deltaS1R A leanSimIR leanProgIR leanPSR b₁ + deltaS1R A leanSimIR leanProgIR leanPSR b₁') +
        (deltaS2R A leanSimIR leanSimSR leanProgIR leanProgSR leanPSR b₁ b₂ +
          deltaS2R A leanSimIR leanSimSR leanProgIR leanProgSR leanPSR b₁' b₂') +
        2 * εhide :=
  (unlinkabilityRO_leanG A hA hhide b₁ b₂ b₁' b₂').trans (le_of_eq (by
    rw [ZKRow.εz_fn, ZKRow.εz_fn]
    ring))

end Lean

end VoleMole.Privacy.Ratatouille
