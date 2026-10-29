import VoleMole.Privacy.MoussakaLean
import VoleMole.ZK.ReadsRO

/-!
# Moussaka issuer hiding and unlinkability in the random-oracle and ideal-cipher model

`Privacy.Moussaka.anonymity` (`Privacy/Moussaka.lean`) assumes zero knowledge against
distinguishers that see the proofs only. Here the adversary also sees the random tables the
proofs are computed with, as in `ZK.Sim.zk_rom_ic_h23_num`, and all four proofs of the game (two
issuance requests, two redemptions) **share** them.

## The model

* **Tables.** `ShM = Tab2G pI × Tab5F × Cipher`: `H₂³` on every grinding point (one table for the
  issuance and the redemption proofs: both have `qsDegree = 9`, so the same prefix length), `H₅` on
  every `37`-byte input, the cipher of the whole BAVC and VOLE expansion. Each proof has its own
  `H₃` slice (`Tab3`, `H₃` at its seed inputs `wPrefix ‖ μ₁ ‖ ρ ‖ 3`): a global `H₃` restricted to
  the four proofs' slices is four independent tables as long as the four `(μ₁, wPrefix)` differ,
  which the game does not enforce (two Clients with equal `(nf, r)`); this modelling step is the
  one place a global `H₃` would add a collision term (`≤ 2⁻¹⁹²`, on paper).
* **Adversary** (`AdversaryRO`): Moussaka's colluding adversary (`Adversary`'s contexts, keys,
  responses and choices) whose final guess also sees all tables, with a budget `Budget q₃ q₅ q_E`:
  it reads each `H₃` slice at `q₃` keys, `H₅` at `q₅`, the cipher at `q_E` (adaptively), and `H₂³`
  freely. **Its earlier choices (responses, Anchor Sets, digests) do not read the tables**: the
  zero-knowledge theorem is for a statement fixed before the tables, and the redemption
  statements are the adversary's choices. Lifting this needs an adaptive-statement version of
  `zk_rom_ic_h23` (open).
* **The game** (`viewRO`, `gameRO`): each proof slot has an output on the tables the game runs on,
  an `H₂³` programming (the identity for a real proof) and its `H₃` slice. The issuance outputs
  are computed on the tables programmed by the issuance slots, the redemption outputs on the tables
  programmed by all slots, and the redemptions (and their programming) happen only if §6's rule
  allows them (`allOk`), as in `Moussaka.view`. With real slots this is the spec's game with every
  hash and the cipher a uniform table (`realGameRO`).

## The hybrids

Issuance `0`, issuance `1`, redemption left, redemption right are replaced in that order
(`Privacy.hop_ro`): the statement of each replaced proof is then fixed by the coins of the
simulated ones (simulated proofs do not depend on the tables). Each hop costs

* the zero-knowledge error at the budget of its reduction: the adversary's budget plus the reads of
  the proofs it still runs for real (`r₅`, `r_E` each: `624`, `4607` for the Lean prover,
  `ZK.Sim.realRO_rd5`, `realRO_rdE`) plus the reads of the programmings it applies (`m₅`, `m_E`
  each: `312`, `4607`, `ZK.Sim.progRO_isProg`);
* **a programming collision term** `δ`: the probability that the proof being replaced, run for
  real, reads `H₂³` differently on the tables the earlier simulations programmed than on the
  original ones (`δI₁`, `δL`, `δR`; the first hop has none). These are explicit probabilities of
  the game, bounded in `Privacy/MoussakaDelta.lean` (`deltaI1_le`, `deltaL_le`, `deltaR_le`,
  `anonymityRO_lean_num`; `lean/docs/zk.md` §10.2).

Then the view is a function of the commitments, the nullifiers, the simulator coins and the
tables (`hviewRO`, `simGameRO_iff`); hiding (`hidingAdv` for the reduction `reductionRO` with the
simulator coins and the tables fixed) and the exchange of the fresh nullifiers finish as in
`Moussaka.anonymity`.

**`anonymityRO`**: the two worlds differ by at most the sum over both worlds of the four
zero-knowledge errors and three collision terms, plus `2εhide`. **`anonymityRO_lean`**: the Lean
prover and simulator (`ZK.Sim.realRO`, `progRO`) with SHAKE: every zero-knowledge error is
`εRO q₃ (q₅ + 1872) (q_E + 13821)`, so the bound is

    8·εRO(q₃, q₅ + 3·624, q_E + 3·4607) + 2·δI₁ + Σ_b (δL b + δR b) + 2·εhide.

**Cipher rows.** Everything here is stated for every type of cipher rows `R` (the shared
tables `ZK.Sim.ShG R p`, `ZK/ReadsRO.lean`) with `ZKRow R`; `anonymityRO_leanG` is the generic
Lean-prover bound and `anonymityRO_lean` its instance at function rows (`Blk → Blk`, the PRF
view); `Privacy/PermRO.lean` instantiates it at permutation rows (AES as uniformly random
permutations, the adversary reading whole rows: forward and inverse queries).
-/

open Finset

-- (The coin types are large products: their `Fintype` instances exceed the default size.)
set_option synthInstance.maxSize 1024

set_option linter.unusedSectionVars false

namespace VoleMole.Privacy.Moussaka

open VoleMole.Spec VoleMole.Spec.Moussaka VoleMole.ZK.Sim

-- `Com` evaluates Keccak-p[800]; nothing below needs to unfold it.
attribute [local irreducible] com UOVKey.eval

/-! ## The model -/

/-- **The tables the four proofs share**: `H₂³` (issuance and redemption have the same prefix
length), `H₅`, the cipher. -/
abbrev ShM (R : Type) := ShG R pI

variable {R : Type} [Fintype R] [Nonempty R]

/-- The four proofs' `H₃` slices: issuance `0`, `1`; redemption left, right. -/
abbrev Slices := (Tab3 × Tab3) × (Tab3 × Tab3)

/-- **The colluding adversary in the random-oracle model**: `Adversary`'s interaction, which does
not read the tables, and a guess that sees all of them. -/
structure AdversaryRO (R : Type) where
  ctxIss : Coins ctxBytes
  ctxRed : Coins ctxBytes
  pk : Bool → UOVKey
  respond : Bytes → Bytes → Bool → Coins uovN
  choose : Bytes → Bytes → Bool → AnchorSet × Bytes
  guess : Bytes → Bytes → Option (Except Error Bytes × Except Error Bytes) → Slices → ShM R → Prop

/-- The interaction of `A` as an `Adversary` (its guess is not used). -/
def AdversaryRO.base (A : AdversaryRO R) : Adversary :=
  ⟨A.ctxIss, A.ctxRed, A.pk, A.respond, A.choose, fun _ _ _ => True⟩

/-- **The adversary's budget**: its guess reads each `H₃` slice at `q3` keys, `H₅` at `q5` and the
cipher at `qE` keys (each with everything else fixed), and `H₂³` freely. -/
structure AdversaryRO.Budget (A : AdversaryRO R) (q3 q5 qE : ℕ) : Prop where
  h30 : ∀ q₀ q₁ y (g₁ gL gR : Tab3) s, Rd3 (fun g => A.guess q₀ q₁ y ((g, g₁), (gL, gR)) s) q3
  h31 : ∀ q₀ q₁ y (g₀ gL gR : Tab3) s, Rd3 (fun g => A.guess q₀ q₁ y ((g₀, g), (gL, gR)) s) q3
  h3L : ∀ q₀ q₁ y (g₀ g₁ gR : Tab3) s, Rd3 (fun g => A.guess q₀ q₁ y ((g₀, g₁), (g, gR)) s) q3
  h3R : ∀ q₀ q₁ y (g₀ g₁ gL : Tab3) s, Rd3 (fun g => A.guess q₀ q₁ y ((g₀, g₁), (gL, g)) s) q3
  h5 : ∀ q₀ q₁ y sl, Rd5 (A.guess q₀ q₁ y sl) q5
  hE : ∀ q₀ q₁ y sl, RdE (A.guess q₀ q₁ y sl) qE

variable (A : AdversaryRO R) (idx : AnchorSet → UOVKey → ℕ)

/-- An issuance slot: its output on the tables, its programming, its `H₃` slice. -/
structure IssSlot (R : Type) where
  out : ShM R → PendingToken × Bytes
  prog : ShM R → ShM R
  slice : Tab3

/-- A redemption slot: its output at a redemption point on the tables, its programming (given
whether the redemptions happen at all), its `H₃` slice. -/
structure RedSlot (R : Type) where
  out : RedeemPt → ShM R → Except Error Bytes
  prog : Bool → RedeemPt → ShM R → ShM R
  slice : Tab3

/-- The guess, given the issuance outputs, the redemption outputs, the slices and the tables
`v` the adversary sees. -/
def postRO (i₀ i₁ : PendingToken × Bytes) (oL oR : Except Error Bytes) (sl : Slices) (v : ShM R) :
    Prop :=
  A.guess i₀.2 i₁.2 (bif allOk A.base idx i₀ i₁ then some (oL, oR) else none) sl v

/-- **The view in world `b`** from four slots and the tables `t`: the issuance outputs on `t`
programmed by the issuance slots; the redemptions run (and the adversary looks) at `t` programmed
by all four slots, a redemption slot programming only if §6's rule allows the redemptions. -/
def viewRO (b : Bool) (s₀ s₁ : IssSlot R) (sL sR : RedSlot R) (t : ShM R) : Prop :=
  let u := s₀.prog (s₁.prog t)
  let i₀ := s₀.out u
  let i₁ := s₁.out u
  let ok := allOk A.base idx i₀ i₁
  let v := s₀.prog (s₁.prog (sL.prog ok (pt A.base idx b i₀ i₁ false)
    (sR.prog ok (pt A.base idx b i₀ i₁ true) t)))
  postRO A idx i₀ i₁ (sL.out (pt A.base idx b i₀ i₁ false) v) (sR.out (pt A.base idx b i₀ i₁ true) v)
    ((s₀.slice, s₁.slice), (sL.slice, sR.slice)) v

/-- The game with the slots drawn by `g₀ g₁ gL gR` from their parts of the tape. -/
def gameRO {T₀ T₁ TL TR : Type} (b : Bool) (g₀ : T₀ → IssSlot R) (g₁ : T₁ → IssSlot R)
    (gL : TL → RedSlot R) (gR : TR → RedSlot R) (x : ((T₀ × T₁) × (TL × TR)) × ShM R) : Prop :=
  viewRO A idx b (g₀ x.1.1.1) (g₁ x.1.1.2) (gL x.1.2.1) (gR x.1.2.2) x.2

/-! ## The slots -/

/-- A proof system of the random-oracle model: `P w x ρ g s` is the proof of `w` for `x` with
randomness `ρ`, the proof's `H₃` slice `g` and the shared tables `s`. -/
abbrev ProverRO (R : Type) (I : Type) := Bytes → I → Bytes → Tab3 → ShM R → Bytes

/-- The proof system with the tables fixed, as the spec's `NIZK` (the verifier is not used). -/
def nizkAt {I : Type} (P : ProverRO R I) (g : Tab3) (s : ShM R) : NIZK I :=
  ⟨fun w x rho => P w x rho g s, fun _ _ => true⟩

/-- The issuance coins `(nf, r)`. -/
abbrev NR := Coins nfBytes × Coins rBytes

/-- The commitment and the issuance instance of the coins `(nf, r)`. -/
def tOf (x : NR) : Bytes := com (List.ofFn x.1) A.base.ci A.base.cr (List.ofFn x.2)

def xIOf (x : NR) : IssueInstance := ⟨tOf A x, A.base.ci⟩

def wIOf (x : NR) : Bytes := encodeIssueWitness (List.ofFn x.1) A.base.ci A.base.cr (List.ofFn x.2)

/-- The pending token of the coins `(nf, r)`. -/
def pendOf (x : NR) : PendingToken := ⟨List.ofFn x.1, List.ofFn x.2, A.base.ci, A.base.cr, tOf A x⟩

/-- **A real issuance**: the spec's `issue_request` with the prover on the tables. -/
def issRealRO (PI : ProverRO R IssueInstance) (x : NR × (Coins proveSeedBytes × Tab3)) : IssSlot R :=
  ⟨fun s => issueRequestOf (nizkAt PI x.2.2 s) A.base.ci A.base.cr (List.ofFn x.1.1)
      (List.ofFn x.1.2) (List.ofFn x.2.1), fun s => s, x.2.2⟩

/-- **A real redemption**: the spec's `redeem_request` with the prover on the tables. -/
def redRealRO (PR : ProverRO R RedeemInstance) (x : Coins proveSeedBytes × Tab3) : RedSlot R :=
  ⟨fun p s => redeemRequestOf (nizkAt PR x.2 s) p.tok p.anchors p.i A.base.ci A.base.cr p.cd
      (List.ofFn x.1), fun _ _ s => s, x.2⟩

variable {CI CR : Type} (simI : IssueInstance → CI → Bytes) (simR : RedeemInstance → CR → Bytes)
  (progI : IssueInstance → CI → ShM R → ShM R) (progR : RedeemInstance → CR → ShM R → ShM R)

/-- A simulated issuance request (`Moussaka.issSim`). -/
def issSimOut (x : NR × CI) : PendingToken × Bytes := (pendOf A x.1, tOf A x.1 ++ simI (xIOf A x.1) x.2)

@[simp] lemma issSimOut_t (x : NR × CI) : (issSimOut A simI x).1.t = tOf A x.1 := rfl

lemma issSimOut_eq (x : NR × CI) : issSimOut A simI x = issSim A.base simI (x.1.1, x.1.2, x.2) := rfl

/-- **A simulated issuance**: the simulated request, and the simulator's programming. -/
def issSimRO (x : NR × (CI × Tab3)) : IssSlot R :=
  ⟨fun _ => issSimOut A simI (x.1, x.2.1), progI (xIOf A x.1) x.2.1, x.2.2⟩

/-- The redemption instance at a redemption point. -/
def xROf (p : RedeemPt) : RedeemInstance := ⟨p.anchors.keys, p.tok.nf, A.base.ci, A.base.cr, p.cd⟩

/-- **A simulated redemption**: the Client's checks, a simulated proof, the programming. -/
def redSimRO (x : CR × Tab3) : RedSlot R :=
  ⟨fun p _ => redSim A.base simR x.1 p, fun ok p s => if ok = true then progR (xROf A p) x.1 s else s,
    x.2⟩

/-- The real issuance tape: `(nf, r)`, the prover's randomness and its `H₃` slice. -/
abbrev TIr := NR × (Coins proveSeedBytes × Tab3)
/-- The real redemption tape. -/
abbrev TRr := Coins proveSeedBytes × Tab3

/-- **The real game in the random-oracle model**: the spec's protocol with every proof computed on
the shared uniform tables. -/
def realGameRO (PI : ProverRO R IssueInstance) (PR : ProverRO R RedeemInstance) (b : Bool) :
    ((TIr × TIr) × (TRr × TRr)) × ShM R → Prop :=
  gameRO A idx b (issRealRO A PI) (issRealRO A PI) (redRealRO A PR) (redRealRO A PR)

/-! ## The redemption points when §6's rule allows the redemptions -/

section Points

variable (B : Adversary)

lemma okAt_of_allOk {i₀ i₁ : PendingToken × Bytes} (h : allOk B idx i₀ i₁ = true) (c side : Bool) :
    okAt B idx i₀ i₁ c side = true := by
  unfold allOk at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨-, -⟩, h1⟩, h2⟩, h3⟩, h4⟩ := h
  cases c <;> cases side <;> assumption

lemma tok_isSome_of_allOk {i₀ i₁ : PendingToken × Bytes} (h : allOk B idx i₀ i₁ = true) (c : Bool) :
    (tok B i₀ i₁ c).isSome = true := by
  unfold allOk at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨h0, h1⟩, -⟩, -⟩, -⟩, -⟩ := h
  cases c <;> assumption

/-- With the redemptions allowed, Client `c`'s token carries its pending token's nullifier. -/
lemma tokD_nf_of_allOk {i₀ i₁ : PendingToken × Bytes} (h : allOk B idx i₀ i₁ = true) (c : Bool) :
    (tokD B i₀ i₁ c).nf = (bif c then i₁ else i₀).1.nf := by
  have hs := tok_isSome_of_allOk idx B h c
  unfold tokD
  unfold tok at hs ⊢
  unfold finalizeIssue at hs ⊢
  split_ifs at hs ⊢
  · rfl
  · simp at hs

lemma pt_nf_of_allOk {i₀ i₁ : PendingToken × Bytes} (h : allOk B idx i₀ i₁ = true) (b side : Bool) :
    (pt B idx b i₀ i₁ side).tok.nf = (bif b ^^ side then i₁ else i₀).1.nf :=
  tokD_nf_of_allOk idx B h _

/-- With the redemptions allowed, the Client's check passes at both redemption points. -/
lemma redeemOk_pt_of_allOk {i₀ i₁ : PendingToken × Bytes} (h : allOk B idx i₀ i₁ = true)
    (b side : Bool) :
    redeemOk B.ci B.cr (pt B idx b i₀ i₁ side).tok (pt B idx b i₀ i₁ side).anchors
      (pt B idx b i₀ i₁ side).i = true :=
  okAt_of_allOk idx B h _ _

end Points

/-! ## All proofs simulated: the view is a function of the commitments and nullifiers -/

/-- The simulated issuance tape: `(nf, r)`, the simulator coins and the proof's `H₃` slice. -/
abbrev TIs (CI : Type) := NR × (CI × Tab3)
/-- The simulated redemption tape. -/
abbrev TRs (CR : Type) := CR × Tab3

/-- The game with all four proofs simulated. -/
def simGameRO (b : Bool) : ((TIs CI × TIs CI) × (TRs CR × TRs CR)) × ShM R → Prop :=
  gameRO A idx b (issSimRO A simI progI) (issSimRO A simI progI) (redSimRO A simR progR)
    (redSimRO A simR progR)

/-- The redemption instance of side `side` in world `b`, from the requests and the nullifiers. -/
def xSide (b : Bool) (q₀ q₁ n₀ n₁ : Bytes) (side : Bool) : RedeemInstance :=
  ⟨(A.choose q₀ q₁ side).1.keys, bif b ^^ side then n₁ else n₀, A.base.ci, A.base.cr,
    (A.choose q₀ q₁ side).2⟩

/-- **The simulated view** as a function of the commitments `t₀, t₁`, the nullifiers `n₀, n₁`
revealed at redemption, the simulator coins, the slices and the tables `s`: the openings enter
nothing. -/
def hviewRO (b : Bool) (t₀ t₁ n₀ n₁ : Bytes) (cI₀ cI₁ : CI) (cL cR : CR) (sl : Slices) (s : ShM R) :
    Prop :=
  let q₀ := t₀ ++ simI ⟨t₀, A.base.ci⟩ cI₀
  let q₁ := t₁ ++ simI ⟨t₁, A.base.ci⟩ cI₁
  let u := progI ⟨t₀, A.base.ci⟩ cI₀ (progI ⟨t₁, A.base.ci⟩ cI₁ s)
  let v := if allOkT A.base idx q₀ q₁ t₀ t₁ = true then
    progI ⟨t₀, A.base.ci⟩ cI₀ (progI ⟨t₁, A.base.ci⟩ cI₁
      (progR (xSide A b q₀ q₁ n₀ n₁ false) cL (progR (xSide A b q₀ q₁ n₀ n₁ true) cR s)))
    else u
  A.guess q₀ q₁ (bif allOkT A.base idx q₀ q₁ t₀ t₁ then
    some (ySim A.base simR b q₀ q₁ n₀ n₁ cL false, ySim A.base simR b q₀ q₁ n₀ n₁ cR true)
    else none) sl v

/-- **`allOk` is `allOkT`** for honest pending tokens (`t = Com(nf, ·, r)`): the first step of
`post_redSim`, recomputed. -/
lemma allOk_eq_allOkT (B : Adversary) (i₀ i₁ : PendingToken × Bytes)
    (h₀ : i₀.1.t = com i₀.1.nf B.ci B.cr i₀.1.r) (h₁ : i₁.1.t = com i₁.1.nf B.ci B.cr i₁.1.r) :
    allOk B idx i₀ i₁ = allOkT B idx i₀.2 i₁.2 i₀.1.t i₁.1.t := by
  have htok (c : Bool) (hc : finT B i₀.2 i₁.2 i₀.1.t i₁.1.t c = true) : tokD B i₀ i₁ c =
      ⟨(bif c then i₁ else i₀).1.nf, (bif c then i₁ else i₀).1.r, resp B i₀.2 i₁.2 c⟩ := by
    unfold tokD
    rw [tok_of_fin B i₀ i₁ c]
    simp only [hc, ↓reduceIte]
    rfl
  have hok (c side : Bool) (hc : finT B i₀.2 i₁.2 i₀.1.t i₁.1.t c = true) :
      okAt B idx i₀ i₁ c side = okT B idx i₀.2 i₁.2 i₀.1.t i₁.1.t c side := by
    unfold okAt okT redeemOk
    rw [htok c hc]
    cases c <;> simp only [Bool.cond_false, Bool.cond_true, ← h₀, ← h₁]
  unfold allOk allOkT
  rw [tok_of_fin B i₀ i₁ false, tok_of_fin B i₀ i₁ true]
  cases e₀ : finT B i₀.2 i₁.2 i₀.1.t i₁.1.t false
  · simp
  · cases e₁ : finT B i₀.2 i₁.2 i₀.1.t i₁.1.t true
    · simp
    · simp [hok _ _ e₀, hok _ _ e₁]

/-- `allOk` on simulated issuance outputs is `allOkT` on the requests and commitments. -/
lemma allOk_issSim (x₀ x₁ : NR × CI) :
    allOk A.base idx (issSimOut A simI x₀) (issSimOut A simI x₁) =
      allOkT A.base idx (issSimOut A simI x₀).2 (issSimOut A simI x₁).2 (tOf A x₀.1) (tOf A x₁.1) :=
  allOk_eq_allOkT idx A.base _ _ rfl rfl


/-- **The view with simulated redemptions**, for issuance slots with honest pending tokens that
do not depend on the tables: a function of the requests, commitments and nullifiers. -/
theorem viewRO_redSim (b : Bool) (i₀ i₁ : PendingToken × Bytes) (P₀ P₁ : ShM R → ShM R) (g₀ g₁ : Tab3)
    (xL xR : CR × Tab3) (s : ShM R) (h₀ : i₀.1.t = com i₀.1.nf A.base.ci A.base.cr i₀.1.r)
    (h₁ : i₁.1.t = com i₁.1.nf A.base.ci A.base.cr i₁.1.r) :
    viewRO A idx b ⟨fun _ => i₀, P₀, g₀⟩ ⟨fun _ => i₁, P₁, g₁⟩ (redSimRO A simR progR xL)
        (redSimRO A simR progR xR) s ↔
      A.guess i₀.2 i₁.2 (bif allOkT A.base idx i₀.2 i₁.2 i₀.1.t i₁.1.t then
          some (ySim A.base simR b i₀.2 i₁.2 i₀.1.nf i₁.1.nf xL.1 false,
            ySim A.base simR b i₀.2 i₁.2 i₀.1.nf i₁.1.nf xR.1 true) else none)
        ((g₀, g₁), (xL.2, xR.2))
        (if allOkT A.base idx i₀.2 i₁.2 i₀.1.t i₁.1.t = true then
          P₀ (P₁ (progR (xSide A b i₀.2 i₁.2 i₀.1.nf i₁.1.nf false) xL.1
            (progR (xSide A b i₀.2 i₁.2 i₀.1.nf i₁.1.nf true) xR.1 s)))
          else P₀ (P₁ s)) := by
  have hall := allOk_eq_allOkT idx A.base i₀ i₁ h₀ h₁
  simp only [viewRO, postRO, redSimRO]
  rw [hall]
  cases hC : allOkT A.base idx i₀.2 i₁.2 i₀.1.t i₁.1.t
  · simp only [Bool.false_eq_true, ↓reduceIte, Bool.cond_false]
  · have hA : allOk A.base idx i₀ i₁ = true := by rw [hall, hC]
    have hx (side : Bool) : xROf A (pt A.base idx b i₀ i₁ side) =
        xSide A b i₀.2 i₁.2 i₀.1.nf i₁.1.nf side := by
      simp only [xROf, xSide, pt_nf_of_allOk idx A.base hA]
      cases b <;> cases side <;> rfl
    have hy (side : Bool) (c : CR) : redSim A.base simR c (pt A.base idx b i₀ i₁ side) =
        ySim A.base simR b i₀.2 i₁.2 i₀.1.nf i₁.1.nf c side := by
      rw [redSim_of_ok A.base simR c _ (redeemOk_pt_of_allOk idx A.base hA b side)]
      have := hx side
      simp only [xROf] at this
      rw [this, pt_nf_of_allOk idx A.base hA]
      unfold ySim xSide
      cases b <;> cases side <;> rfl
    simp only [↓reduceIte, Bool.cond_true, hx, hy]

theorem simGameRO_iff (b : Bool) (x : ((TIs CI × TIs CI) × (TRs CR × TRs CR)) × ShM R) :
    simGameRO A idx simI simR progI progR b x ↔
      hviewRO A idx simI simR progI progR b (tOf A x.1.1.1.1) (tOf A x.1.1.2.1)
        (List.ofFn x.1.1.1.1.1) (List.ofFn x.1.1.2.1.1) x.1.1.1.2.1 x.1.1.2.2.1 x.1.2.1.1 x.1.2.2.1
        ((x.1.1.1.2.2, x.1.1.2.2.2), (x.1.2.1.2, x.1.2.2.2)) x.2 :=
  viewRO_redSim A idx simR progR b (issSimOut A simI (x.1.1.1.1, x.1.1.1.2.1))
    (issSimOut A simI (x.1.1.2.1, x.1.1.2.2.1)) _ _ _ _ x.1.2.1 x.1.2.2 x.2 rfl rfl

/-! ## The hiding hop and the ideal world -/

/-- **The reduction to hiding**: the adversary, with the simulator coins, the slices and the tables
fixed, run on the commitments and nullifiers it is given. -/
def reductionRO (b : Bool) (c : ((CI × CI) × (CR × CR)) × (Slices × ShM R))
    (z : Bytes × Bytes × Bytes × Bytes) : Prop :=
  hviewRO A idx simI simR progI progR b z.1 z.2.1 z.2.2.1 z.2.2.2 c.1.1.1 c.1.1.2 c.1.2.1 c.1.2.2
    c.2.1 c.2.2

/-- The game after the hiding hop: fresh nullifiers are revealed at redemption. -/
def idealGameRO (b : Bool)
    (x : (HTape × (Coins nfBytes × Coins nfBytes)) × (((CI × CI) × (CR × CR)) × (Slices × ShM R))) :
    Prop :=
  reductionRO A idx simI simR progI progR b x.2 (hideIdeal A.base.ci A.base.cr x.1)

/-- Regroup the simulated game's tape as the hiding tape and the rest. -/
def regroupRO : ((TIs CI × TIs CI) × (TRs CR × TRs CR)) × ShM R ≃
    HTape × (((CI × CI) × (CR × CR)) × (Slices × ShM R)) where
  toFun x := ((x.1.1.1.1, x.1.1.2.1), ((x.1.1.1.2.1, x.1.1.2.2.1), (x.1.2.1.1, x.1.2.2.1)),
    ((x.1.1.1.2.2, x.1.1.2.2.2), (x.1.2.1.2, x.1.2.2.2)), x.2)
  invFun y := ((((y.1.1, y.2.1.1.1, y.2.2.1.1.1), (y.1.2, y.2.1.1.2, y.2.2.1.1.2)),
    ((y.2.1.2.1, y.2.2.1.2.1), (y.2.1.2.2, y.2.2.1.2.2))), y.2.2.2)
  left_inv _ := rfl
  right_inv _ := rfl

theorem hiding_hopRO [Fintype CI] [Nonempty CI] [Fintype CR] [Nonempty CR] (b : Bool) {εhide : ℝ}
    (hhide : ∀ c, hidingAdv A.base.ci A.base.cr (reductionRO A idx simI simR progI progR b c) ≤
      εhide) :
    |pr _ (simGameRO A idx simI simR progI progR b) -
      pr _ (idealGameRO A idx simI simR progI progR b)| ≤ εhide := by
  rw [← pr_equiv regroupRO.symm (simGameRO A idx simI simR progI progR b),
    pr_congr fun y => simGameRO_iff A idx simI simR progI progR b (regroupRO.symm y)]
  exact abs_pr_prod_sub_le' _ _ fun c => hhide c

/-- Exchange the fresh nullifiers. -/
def swapNRO : (HTape × (Coins nfBytes × Coins nfBytes)) × (((CI × CI) × (CR × CR)) × (Slices × ShM R)) ≃
    (HTape × (Coins nfBytes × Coins nfBytes)) × (((CI × CI) × (CR × CR)) × (Slices × ShM R)) where
  toFun x := ((x.1.1, (x.1.2.2, x.1.2.1)), x.2)
  invFun x := ((x.1.1, (x.1.2.2, x.1.2.1)), x.2)
  left_inv _ := rfl
  right_inv _ := rfl

/-- **After the hiding hop the worlds coincide**, tables included: world `b` reveals (and the
simulators program at) the fresh `n_b` on the left and `n_{¬b}` on the right. -/
theorem idealGameRO_eq [Fintype CI] [Fintype CR] :
    pr _ (idealGameRO A idx simI simR progI progR false) =
      pr _ (idealGameRO A idx simI simR progI progR true) := by
  rw [← pr_equiv swapNRO]
  exact pr_congr fun x => Iff.rfl

/-! ## The reads of the game's parts -/

section GameReads

variable {A idx} {r5 rE : ℕ}

lemma issRealRO_out (PI : ProverRO R IssueInstance) (x : TIr) (u : ShM R) :
    (issRealRO A PI x).out u =
      (pendOf A x.1, tOf A x.1 ++ PI (wIOf A x.1) (xIOf A x.1) (List.ofFn x.2.1) x.2.2 u) := rfl

lemma rd5_issReal {PI : ProverRO R IssueInstance} (hPI : ∀ w x rho g, Rd5 (PI w x rho g) r5)
    (x : TIr) : Rd5 (fun u => (issRealRO A PI x).out u) r5 :=
  (hPI (wIOf A x.1) (xIOf A x.1) (List.ofFn x.2.1) x.2.2).map fun π => (pendOf A x.1, tOf A x.1 ++ π)

lemma rdE_issReal {PI : ProverRO R IssueInstance} (hPI : ∀ w x rho g, RdE (PI w x rho g) rE)
    (x : TIr) : RdE (fun u => (issRealRO A PI x).out u) rE :=
  (hPI (wIOf A x.1) (xIOf A x.1) (List.ofFn x.2.1) x.2.2).map fun π => (pendOf A x.1, tOf A x.1 ++ π)

lemma rd5_redReal {PR : ProverRO R RedeemInstance} (hPR : ∀ w x rho g, Rd5 (PR w x rho g) r5)
    (x : TRr) (p : RedeemPt) : Rd5 (fun u => (redRealRO A PR x).out p u) r5 := by
  simp only [redRealRO, redeemRequestOf, nizkAt]
  split
  · exact (Rd5.const _).mono (Nat.zero_le _)
  · split_ifs
    · exact (hPR _ _ _ _).map fun π => (Except.ok (p.tok.nf ++ π) : Except Error Bytes)
    · exact (Rd5.const _).mono (Nat.zero_le _)

lemma rdE_redReal {PR : ProverRO R RedeemInstance} (hPR : ∀ w x rho g, RdE (PR w x rho g) rE)
    (x : TRr) (p : RedeemPt) : RdE (fun u => (redRealRO A PR x).out p u) rE := by
  simp only [redRealRO, redeemRequestOf, nizkAt]
  split
  · exact (RdE.const _).mono (Nat.zero_le _)
  · split_ifs
    · exact (hPR _ _ _ _).map fun π => (Except.ok (p.tok.nf ++ π) : Except Error Bytes)
    · exact (RdE.const _).mono (Nat.zero_le _)

variable {q3 q5 qE : ℕ}

lemma rd5_postRO (hA : A.Budget q3 q5 qE) (i₀ i₁ : PendingToken × Bytes)
    {yL yR : ShM R → Except Error Bytes} {a a' : ℕ} (hL : Rd5 yL a) (hR : Rd5 yR a') (sl : Slices) :
    Rd5 (fun u => postRO A idx i₀ i₁ (yL u) (yR u) sl u) (a + a' + q5) :=
  (hL.bind (f := fun y u => (y, yR u)) fun y => hR.map fun z => (y, z)).bind
    (f := fun y u => A.guess i₀.2 i₁.2 (bif allOk A.base idx i₀ i₁ then some y else none) sl u)
    fun _ => hA.h5 _ _ _ _

lemma rdE_postRO (hA : A.Budget q3 q5 qE) (i₀ i₁ : PendingToken × Bytes)
    {yL yR : ShM R → Except Error Bytes} {a a' : ℕ} (hL : RdE yL a) (hR : RdE yR a') (sl : Slices) :
    RdE (fun u => postRO A idx i₀ i₁ (yL u) (yR u) sl u) (a + a' + qE) :=
  (hL.bind (f := fun y u => (y, yR u)) fun y => hR.map fun z => (y, z)).bind
    (f := fun y u => A.guess i₀.2 i₁.2 (bif allOk A.base idx i₀ i₁ then some y else none) sl u)
    fun _ => hA.hE _ _ _ _

/-- A redemption output that does not read the tables. -/
lemma rd5_const_out (y : RedeemPt → Except Error Bytes) (p : RedeemPt) :
    Rd5 (fun _ : ShM R => y p) 0 := Rd5.const _

lemma rdE_const_out (y : RedeemPt → Except Error Bytes) (p : RedeemPt) :
    RdE (fun _ : ShM R => y p) 0 := RdE.const _

end GameReads

/-! ## The relations at the game's instances -/

lemma issueRelW_of (n : NR) : IssueRelW (xIOf A n) (wIOf A n) :=
  ⟨⟨_, _, _, by simp [nfBytes], by simp [rBytes], by simp [Adversary.cr, AdversaryRO.base, ctxBytes],
    rfl, rfl⟩, by simp [xIOf, Adversary.ci, AdversaryRO.base, ctxBytes]⟩

/-! ## The hybrids' contexts -/

variable (PI : ProverRO R IssueInstance) (PR : ProverRO R RedeemInstance)

/-- The tape regrouped around issuance `0`'s proof. -/
def eqv0 {N Q T₁ T₂ S : Type} : (N × (T₁ × T₂)) × (Q × S) ≃ (((N × Q) × T₁) × T₂) × S where
  toFun z := ((((z.1.1, z.2.1), z.1.2.1), z.1.2.2), z.2.2)
  invFun y := ((y.1.1.1.1, (y.1.1.2, y.1.2)), (y.1.1.1.2, y.2))
  left_inv _ := rfl
  right_inv _ := rfl

/-- The tape regrouped around issuance `1`'s proof. -/
def eqv1 {T₀ N Q T₂ S : Type} : (T₀ × (N × T₂)) × (Q × S) ≃ ((T₀ × (N × Q)) × T₂) × S where
  toFun z := (((z.1.1, (z.1.2.1, z.2.1)), z.1.2.2), z.2.2)
  invFun y := ((y.1.1.1, (y.1.1.2.1, y.1.2)), (y.1.1.2.2, y.2))
  left_inv _ := rfl
  right_inv _ := rfl

/-- The tape regrouped around the left redemption's proof. -/
def eqvL {T₀₁ Q T₃ S : Type} : (T₀₁ × T₃) × (Q × S) ≃ (T₀₁ × (Q × T₃)) × S where
  toFun z := ((z.1.1, (z.2.1, z.1.2)), z.2.2)
  invFun y := ((y.1.1, y.1.2.2), (y.1.2.1, y.2))
  left_inv _ := rfl
  right_inv _ := rfl

/-- The tape regrouped around the right redemption's proof. -/
def eqvR {T₀₁ T₂ Q S : Type} : (T₀₁ × T₂) × (Q × S) ≃ (T₀₁ × (T₂ × Q)) × S where
  toFun z := ((z.1.1, (z.1.2, z.2.1)), z.2.2)
  invFun y := ((y.1.1, y.1.2.1), (y.1.2.2, y.2))
  left_inv _ := rfl
  right_inv _ := rfl

/-- The rest of the game around issuance `0`'s proof `o` (slice `g`), on the tables `u`: issuance
`1` and both redemptions real. -/
def F0 (b : Bool) (γ : NR × (TIr × (TRr × TRr))) (o : Bytes) (g : Tab3) (u : ShM R) : Prop :=
  postRO A idx (pendOf A γ.1, tOf A γ.1 ++ o) ((issRealRO A PI γ.2.1).out u)
    ((redRealRO A PR γ.2.2.1).out (pt A.base idx b (pendOf A γ.1, tOf A γ.1 ++ o)
      ((issRealRO A PI γ.2.1).out u) false) u)
    ((redRealRO A PR γ.2.2.2).out (pt A.base idx b (pendOf A γ.1, tOf A γ.1 ++ o)
      ((issRealRO A PI γ.2.1).out u) true) u)
    ((g, γ.2.1.2.2), (γ.2.2.1.2, γ.2.2.2.2)) u

/-- The rest of the game around issuance `1`'s proof: issuance `0` simulated (its programming
applied to the tables `u` already), both redemptions real. -/
def F1 (b : Bool) (γ : TIs CI × (NR × (TRr × TRr))) (o : Bytes) (g : Tab3) (u : ShM R) : Prop :=
  postRO A idx (issSimOut A simI (γ.1.1, γ.1.2.1)) (pendOf A γ.2.1, tOf A γ.2.1 ++ o)
    ((redRealRO A PR γ.2.2.1).out (pt A.base idx b (issSimOut A simI (γ.1.1, γ.1.2.1))
      (pendOf A γ.2.1, tOf A γ.2.1 ++ o) false) u)
    ((redRealRO A PR γ.2.2.2).out (pt A.base idx b (issSimOut A simI (γ.1.1, γ.1.2.1))
      (pendOf A γ.2.1, tOf A γ.2.1 ++ o) true) u)
    ((γ.1.2.2, g), (γ.2.2.1.2, γ.2.2.2.2)) u

/-- **The collision term of hop 1**: issuance `1`'s real proof on the tables programmed by
issuance `0`'s simulation differs from the proof on the original tables. -/
noncomputable def deltaI1 [Fintype CI] : ℝ :=
  pr ((TIs CI × (NR × (TRr × TRr))) × ((Coins proveSeedBytes × Tab3) × ShM R)) fun z =>
    PI (wIOf A z.1.2.1) (xIOf A z.1.2.1) (List.ofFn z.2.1.1) z.2.1.2
        (progI (xIOf A z.1.1.1) z.1.1.2.1 z.2.2) ≠
      PI (wIOf A z.1.2.1) (xIOf A z.1.2.1) (List.ofFn z.2.1.1) z.2.1.2 z.2.2

/-- The redemption witness at a redemption point. -/
def wROf (p : RedeemPt) : Bytes :=
  encodeRedeemWitness p.tok.nf A.base.ci A.base.cr p.tok.r p.tok.s p.i

/-- The issuance outputs of a hop context. -/
abbrev i₀Of {α : Type} (γ : (TIs CI × TIs CI) × α) : PendingToken × Bytes :=
  issSimOut A simI (γ.1.1.1, γ.1.1.2.1)
abbrev i₁Of {α : Type} (γ : (TIs CI × TIs CI) × α) : PendingToken × Bytes :=
  issSimOut A simI (γ.1.2.1, γ.1.2.2.1)

/-- The issuance programming of a hop context. -/
abbrev PIOf {α : Type} (γ : (TIs CI × TIs CI) × α) (s : ShM R) : ShM R :=
  progI (xIOf A γ.1.1.1) γ.1.1.2.1 (progI (xIOf A γ.1.2.1) γ.1.2.2.1 s)

/-- The rest of the game around the left redemption's output `o`: issuances simulated, the right
redemption real. -/
def FL (b : Bool) (γ : (TIs CI × TIs CI) × TRr) (o : Except Error Bytes) (g : Tab3) (u : ShM R) :
    Prop :=
  postRO A idx (i₀Of A simI γ) (i₁Of A simI γ) o
    ((redRealRO A PR γ.2).out (pt A.base idx b (i₀Of A simI γ) (i₁Of A simI γ) true) u)
    ((γ.1.1.2.2, γ.1.2.2.2), (g, γ.2.2)) u

/-- **The collision term of hop L**: the left redemption's real proof on the tables programmed by
the issuance simulations differs from the one on the original tables. -/
noncomputable def deltaL [Fintype CI] (b : Bool) : ℝ :=
  pr (((TIs CI × TIs CI) × TRr) × ((Coins proveSeedBytes × Tab3) × ShM R)) fun z =>
    (redRealRO A PR z.2.1).out (pt A.base idx b (i₀Of A simI z.1) (i₁Of A simI z.1) false)
        (PIOf A progI z.1 z.2.2) ≠
      (redRealRO A PR z.2.1).out (pt A.base idx b (i₀Of A simI z.1) (i₁Of A simI z.1) false) z.2.2

/-- The programming before the right redemption's: the issuances and the left redemption. -/
def LR (b : Bool) (γ : (TIs CI × TIs CI) × TRs CR) (s : ShM R) : ShM R :=
  PIOf A progI γ (if allOk A.base idx (i₀Of A simI γ) (i₁Of A simI γ) = true then
    progR (xROf A (pt A.base idx b (i₀Of A simI γ) (i₁Of A simI γ) false)) γ.2.1 s else s)

/-- The rest of the game around the right redemption's output: the other three simulated. -/
def FR (b : Bool) (γ : (TIs CI × TIs CI) × TRs CR) (o : Except Error Bytes) (g : Tab3) (u : ShM R) :
    Prop :=
  postRO A idx (i₀Of A simI γ) (i₁Of A simI γ)
    (redSim A.base simR γ.2.1 (pt A.base idx b (i₀Of A simI γ) (i₁Of A simI γ) false)) o
    ((γ.1.1.2.2, γ.1.2.2.2), (γ.2.2, g)) u

/-- **The collision term of hop R**: the right redemption's real proof on the tables programmed by
the other three simulations differs from the one on the original tables. -/
noncomputable def deltaR [Fintype CI] [Fintype CR] (b : Bool) : ℝ :=
  pr (((TIs CI × TIs CI) × TRs CR) × ((Coins proveSeedBytes × Tab3) × ShM R)) fun z =>
    (redRealRO A PR z.2.1).out (pt A.base idx b (i₀Of A simI z.1) (i₁Of A simI z.1) true)
        (LR A idx simI progI progR b z.1 z.2.2) ≠
      (redRealRO A PR z.2.1).out (pt A.base idx b (i₀Of A simI z.1) (i₁Of A simI z.1) true) z.2.2

/-- **At a redemption point that passes the Client's check** the witness satisfies the
redemption relation, and the real and simulated redemptions are the nullifier and a proof. -/
lemma redeem_facts (p : RedeemPt) (hr : p.tok.r.length = rBytes) (hs : p.tok.s.length = uovN)
    (hn : p.tok.nf.length = nfBytes) (hok : redeemOk A.base.ci A.base.cr p.tok p.anchors p.i = true) :
    RedeemRelW (xROf A p) (wROf A p) ∧
      (∀ (x : TRr) u, (redRealRO A PR x).out p u =
        .ok (p.tok.nf ++ PR (wROf A p) (xROf A p) (List.ofFn x.1) x.2 u)) ∧
      ∀ c, redSim A.base simR c p = .ok (p.tok.nf ++ simR (xROf A p) c) := by
  unfold redeemOk at hok
  split at hok
  · cases hok
  · rename_i pk hk
    simp only [decide_eq_true_eq] at hok
    refine ⟨⟨⟨_, _, _, pk, hr, hs, hk, rfl, hok⟩, p.anchors.valid.2.1, hn,
      by simp [xROf, Adversary.ci, AdversaryRO.base, ctxBytes],
      by simp [xROf, Adversary.cr, AdversaryRO.base, ctxBytes]⟩, fun x u => ?_, fun c => ?_⟩
    · simp only [redRealRO, redeemRequestOf, nizkAt, hk, hok, ↓reduceIte]
      rfl
    · exact redSim_of_ok A.base simR c p (by unfold redeemOk; rw [hk]; simp [hok])

/-- The simulated issuance outputs are well formed. -/
lemma issSimOut_wf (x : NR × CI) :
    (issSimOut A simI x).1.r.length = rBytes ∧ (issSimOut A simI x).1.nf.length = nfBytes := by
  simp [issSimOut, pendOf, rBytes, nfBytes]

/-! ## The four hops -/

section Hops

variable {A idx PI PR simI progI} {q3 q5 qE r5 rE m5 mE : ℕ}

theorem hop0RO [Fintype CI] [Nonempty CI] (hA : A.Budget q3 q5 qE)
    (hPI5 : ∀ w x rho g, Rd5 (PI w x rho g) r5) (hPIE : ∀ w x rho g, RdE (PI w x rho g) rE)
    (hPR5 : ∀ w x rho g, Rd5 (PR w x rho g) r5) (hPRE : ∀ w x rho g, RdE (PR w x rho g) rE)
    {ε : ℝ} (hI : ZeroKnowledgeRO IssueRelW
      (fun x w (ρ : Coins proveSeedBytes) g s => PI w x (List.ofFn ρ) g s) simI progI
      (Budget pI q3 (r5 + (r5 + r5 + q5)) (rE + (rE + rE + qE))) ε) (b : Bool) :
    |pr _ (gameRO A idx b (issRealRO A PI) (issRealRO A PI) (redRealRO A PR) (redRealRO A PR)) -
      pr _ (gameRO A idx b (issSimRO A simI progI) (issRealRO A PI) (redRealRO A PR)
        (redRealRO A PR))| ≤ ε := by
  have h := hop_ro (Γ := NR × (TIr × (TRr × TRr))) (ρ := Coins proveSeedBytes) (G := Tab3)
    (C := CI) (S := ShM R) (fun γ ρ g s => PI (wIOf A γ.1) (xIOf A γ.1) (List.ofFn ρ) g s)
    (fun γ c => simI (xIOf A γ.1) c) (fun γ c => progI (xIOf A γ.1) c) (fun _ s => s)
    (F0 A idx PI PR b) (ε := ε) fun γ => hI (xIOf A γ.1) (wIOf A γ.1) (issueRelW_of A γ.1)
      (fun o g s => F0 A idx PI PR b γ o g s)
      ⟨fun o s => hA.h30 _ _ _ _ _ _ _,
        fun o g => (rd5_issReal hPI5 γ.2.1).bind fun i =>
          rd5_postRO (idx := idx) hA (pendOf A γ.1, tOf A γ.1 ++ o) i
            (rd5_redReal hPR5 γ.2.2.1 (pt A.base idx b (pendOf A γ.1, tOf A γ.1 ++ o) i false))
            (rd5_redReal hPR5 γ.2.2.2 (pt A.base idx b (pendOf A γ.1, tOf A γ.1 ++ o) i true))
            ((g, γ.2.1.2.2), (γ.2.2.1.2, γ.2.2.2.2)),
        fun o g => (rdE_issReal hPIE γ.2.1).bind fun i =>
          rdE_postRO (idx := idx) hA (pendOf A γ.1, tOf A γ.1 ++ o) i
            (rdE_redReal hPRE γ.2.2.1 (pt A.base idx b (pendOf A γ.1, tOf A γ.1 ++ o) i false))
            (rdE_redReal hPRE γ.2.2.2 (pt A.base idx b (pendOf A γ.1, tOf A γ.1 ++ o) i true))
            ((g, γ.2.1.2.2), (γ.2.2.1.2, γ.2.2.2.2))⟩
  have hδ : pr ((NR × (TIr × (TRr × TRr))) × ((Coins proveSeedBytes × Tab3) × ShM R)) (fun z =>
      PI (wIOf A z.1.1) (xIOf A z.1.1) (List.ofFn z.2.1.1) z.2.1.2 z.2.2 ≠
        PI (wIOf A z.1.1) (xIOf A z.1.1) (List.ofFn z.2.1.1) z.2.1.2 z.2.2) = 0 := by
    rw [pr_congr (Q := fun _ => False) fun z => by simp, pr_const]
    simp
  rw [hδ, add_zero] at h
  rw [← pr_equiv eqv0 (gameRO A idx b (issRealRO A PI) (issRealRO A PI) (redRealRO A PR)
      (redRealRO A PR)), ← pr_equiv eqv0 (gameRO A idx b (issSimRO A simI progI) (issRealRO A PI)
      (redRealRO A PR) (redRealRO A PR))]
  refine le_of_eq_of_le (congrArg₂ (fun a c => |a - c|) (pr_congr fun z => ?_) (pr_congr fun z => ?_)) h
  · exact Iff.rfl
  · exact Iff.rfl

theorem hop1RO [Fintype CI] [Nonempty CI] (hA : A.Budget q3 q5 qE)
    (hPR5 : ∀ w x rho g, Rd5 (PR w x rho g) r5) (hPRE : ∀ w x rho g, RdE (PR w x rho g) rE)
    (hpI : ∀ x c, IsProg (progI x c) m5 mE)
    {ε : ℝ} (hI : ZeroKnowledgeRO IssueRelW
      (fun x w (ρ : Coins proveSeedBytes) g s => PI w x (List.ofFn ρ) g s) simI progI
      (Budget pI q3 (r5 + r5 + q5 + m5) (rE + rE + qE + mE)) ε) (b : Bool) :
    |pr _ (gameRO A idx b (issSimRO A simI progI) (issRealRO A PI) (redRealRO A PR)
        (redRealRO A PR)) -
      pr _ (gameRO A idx b (issSimRO A simI progI) (issSimRO A simI progI) (redRealRO A PR)
        (redRealRO A PR))| ≤ ε + deltaI1 A progI PI := by
  have h := hop_ro (Γ := TIs CI × (NR × (TRr × TRr))) (ρ := Coins proveSeedBytes) (G := Tab3)
    (C := CI) (S := ShM R) (fun γ ρ g s => PI (wIOf A γ.2.1) (xIOf A γ.2.1) (List.ofFn ρ) g s)
    (fun γ c => simI (xIOf A γ.2.1) c) (fun γ c => progI (xIOf A γ.2.1) c)
    (fun γ s => progI (xIOf A γ.1.1) γ.1.2.1 s)
    (F1 A idx simI PR b) (ε := ε) fun γ => hI (xIOf A γ.2.1) (wIOf A γ.2.1) (issueRelW_of A γ.2.1)
      (fun o g s => F1 A idx simI PR b γ o g (progI (xIOf A γ.1.1) γ.1.2.1 s))
      ⟨fun o s => hA.h31 _ _ _ _ _ _ _,
        fun o g => (rd5_postRO (idx := idx) hA _ _ (rd5_redReal hPR5 _ _) (rd5_redReal hPR5 _ _) _).comp_prog
          (hpI _ _),
        fun o g => (rdE_postRO (idx := idx) hA _ _ (rdE_redReal hPRE _ _) (rdE_redReal hPRE _ _) _).comp_prog
          (hpI _ _)⟩
  rw [← pr_equiv eqv1 (gameRO A idx b (issSimRO A simI progI) (issRealRO A PI) (redRealRO A PR)
      (redRealRO A PR)), ← pr_equiv eqv1 (gameRO A idx b (issSimRO A simI progI)
      (issSimRO A simI progI) (redRealRO A PR) (redRealRO A PR))]
  exact le_of_eq_of_le (congrArg₂ (fun a c => |a - c|) (pr_congr fun z => Iff.rfl)
    (pr_congr fun z => Iff.rfl)) h

theorem hopLRO [Fintype CI] [Nonempty CI] [Fintype CR] [Nonempty CR] (hA : A.Budget q3 q5 qE)
    (hPR5 : ∀ w x rho g, Rd5 (PR w x rho g) r5) (hPRE : ∀ w x rho g, RdE (PR w x rho g) rE)
    (hpI : ∀ x c, IsProg (progI x c) m5 mE)
    {ε : ℝ} (hε : 0 ≤ ε) (hR : ZeroKnowledgeRO RedeemRelW
      (fun x w (ρ : Coins proveSeedBytes) g s => PR w x (List.ofFn ρ) g s) simR progR
      (Budget pR q3 (0 + r5 + q5 + (m5 + m5)) (0 + rE + qE + (mE + mE))) ε) (b : Bool) :
    |pr _ (gameRO A idx b (issSimRO A simI progI) (issSimRO A simI progI) (redRealRO A PR)
        (redRealRO A PR)) -
      pr _ (gameRO A idx b (issSimRO A simI progI) (issSimRO A simI progI)
        (redSimRO A simR progR) (redRealRO A PR))| ≤ ε + deltaL A idx simI progI PR b := by
  have h := hop_ro (Γ := (TIs CI × TIs CI) × TRr) (ρ := Coins proveSeedBytes) (G := Tab3)
    (C := CR) (S := ShM R)
    (fun γ ρ g s => (redRealRO A PR (ρ, g)).out
      (pt A.base idx b (i₀Of A simI γ) (i₁Of A simI γ) false) s)
    (fun γ c => redSim A.base simR c (pt A.base idx b (i₀Of A simI γ) (i₁Of A simI γ) false))
    (fun γ c s => if allOk A.base idx (i₀Of A simI γ) (i₁Of A simI γ) = true then
      progR (xROf A (pt A.base idx b (i₀Of A simI γ) (i₁Of A simI γ) false)) c s else s)
    (fun γ s => PIOf A progI γ s) (FL A idx simI PR b) (ε := ε) fun γ => ?_
  · rw [← pr_equiv eqvL (gameRO A idx b (issSimRO A simI progI) (issSimRO A simI progI)
        (redRealRO A PR) (redRealRO A PR)), ← pr_equiv eqvL (gameRO A idx b (issSimRO A simI progI)
        (issSimRO A simI progI) (redSimRO A simR progR) (redRealRO A PR))]
    exact le_of_eq_of_le (congrArg₂ (fun a c => |a - c|) (pr_congr fun z => Iff.rfl)
      (pr_congr fun z => Iff.rfl)) h
  · set p := pt A.base idx b (i₀Of A simI γ) (i₁Of A simI γ) false with hp
    cases hok : allOk A.base idx (i₀Of A simI γ) (i₁Of A simI γ)
    · -- The redemptions do not happen: this proof is not read.
      have e : ∀ o g u, FL A idx simI PR b γ o g u ↔ A.guess (i₀Of A simI γ).2 (i₁Of A simI γ).2
          none ((γ.1.1.2.2, γ.1.2.2.2), (g, γ.2.2)) u := fun o g u => by
        simp only [FL, postRO, hok, Bool.cond_false]
      simp only [Bool.false_eq_true, ↓reduceIte]
      rw [pr_congr fun a => e _ _ _, pr_congr fun a => e _ _ _]
      exact (hop_ro_unused (ρ := Coins proveSeedBytes) (C := CR) (fun g u =>
        A.guess (i₀Of A simI γ).2 (i₁Of A simI γ).2 none ((γ.1.1.2.2, γ.1.2.2.2), (g, γ.2.2))
          (PIOf A progI γ u))).trans hε
    · have hwf := tokD_wf A.base (i₀ := i₀Of A simI γ) (i₁ := i₁Of A simI γ)
        (issSimOut_wf A simI _) (issSimOut_wf A simI _) (b ^^ false)
      obtain ⟨hrel, hreal, hsim⟩ := redeem_facts A simR PR p hwf.1 hwf.2.1 hwf.2.2
        (redeemOk_pt_of_allOk idx A.base hok b false)
      simp only [↓reduceIte]
      refine le_of_eq_of_le (congrArg₂ (fun x y => |x - y|) (pr_congr fun a => ?_)
        (pr_congr fun a => ?_)) (hR (xROf A p) (wROf A p) hrel
        (fun o g s => FL A idx simI PR b γ (.ok (p.tok.nf ++ o)) g (PIOf A progI γ s))
        ⟨fun o s => hA.h3L _ _ _ _ _ _ _,
          fun o g => (rd5_postRO (idx := idx) hA _ _ (Rd5.const _) (rd5_redReal hPR5 _ _) _).comp_prog
            ((hpI _ _).comp (hpI _ _)),
          fun o g => (rdE_postRO (idx := idx) hA _ _ (RdE.const _) (rdE_redReal hPRE _ _) _).comp_prog
            ((hpI _ _).comp (hpI _ _))⟩)
      · rw [hreal]
      · rw [hsim]

theorem hopRRO [Fintype CI] [Nonempty CI] [Fintype CR] [Nonempty CR] (hA : A.Budget q3 q5 qE)
    (hpI : ∀ x c, IsProg (progI x c) m5 mE) (hpR : ∀ x c, IsProg (progR x c) m5 mE)
    {ε : ℝ} (hε : 0 ≤ ε) (hR : ZeroKnowledgeRO RedeemRelW
      (fun x w (ρ : Coins proveSeedBytes) g s => PR w x (List.ofFn ρ) g s) simR progR
      (Budget pR q3 (0 + 0 + q5 + (m5 + (m5 + m5))) (0 + 0 + qE + (mE + (mE + mE)))) ε)
    (b : Bool) :
    |pr _ (gameRO A idx b (issSimRO A simI progI) (issSimRO A simI progI)
        (redSimRO A simR progR) (redRealRO A PR)) -
      pr _ (simGameRO A idx simI simR progI progR b)| ≤
      ε + deltaR A idx simI progI progR PR b := by
  have h := hop_ro (Γ := (TIs CI × TIs CI) × TRs CR) (ρ := Coins proveSeedBytes) (G := Tab3)
    (C := CR) (S := ShM R)
    (fun γ ρ g s => (redRealRO A PR (ρ, g)).out
      (pt A.base idx b (i₀Of A simI γ) (i₁Of A simI γ) true) s)
    (fun γ c => redSim A.base simR c (pt A.base idx b (i₀Of A simI γ) (i₁Of A simI γ) true))
    (fun γ c s => if allOk A.base idx (i₀Of A simI γ) (i₁Of A simI γ) = true then
      progR (xROf A (pt A.base idx b (i₀Of A simI γ) (i₁Of A simI γ) true)) c s else s)
    (LR A idx simI progI progR b) (FR A idx simI simR b) (ε := ε) fun γ => ?_
  · rw [← pr_equiv eqvR (gameRO A idx b (issSimRO A simI progI) (issSimRO A simI progI)
        (redSimRO A simR progR) (redRealRO A PR)), ← pr_equiv eqvR (simGameRO A idx simI simR
        progI progR b)]
    exact le_of_eq_of_le (congrArg₂ (fun a c => |a - c|) (pr_congr fun z => Iff.rfl)
      (pr_congr fun z => Iff.rfl)) h
  · set p := pt A.base idx b (i₀Of A simI γ) (i₁Of A simI γ) true with hp
    have hL : IsProg (LR A idx simI progI progR b γ) (m5 + (m5 + m5)) (mE + (mE + mE)) :=
      (hpI _ _).comp ((hpI _ _).comp (IsProg.ite _ (hpR _ _) (IsProg.id.mono (Nat.zero_le _)
        (Nat.zero_le _))))
    cases hok : allOk A.base idx (i₀Of A simI γ) (i₁Of A simI γ)
    · have e : ∀ o g u, FR A idx simI simR b γ o g u ↔ A.guess (i₀Of A simI γ).2
          (i₁Of A simI γ).2 none ((γ.1.1.2.2, γ.1.2.2.2), (γ.2.2, g)) u := fun o g u => by
        simp only [FR, postRO, hok, Bool.cond_false]
      simp only [Bool.false_eq_true, ↓reduceIte]
      rw [pr_congr fun a => e _ _ _, pr_congr fun a => e _ _ _]
      exact (hop_ro_unused (ρ := Coins proveSeedBytes) (C := CR) (fun g u =>
        A.guess (i₀Of A simI γ).2 (i₁Of A simI γ).2 none ((γ.1.1.2.2, γ.1.2.2.2), (γ.2.2, g))
          (LR A idx simI progI progR b γ u))).trans hε
    · have hwf := tokD_wf A.base (i₀ := i₀Of A simI γ) (i₁ := i₁Of A simI γ)
        (issSimOut_wf A simI _) (issSimOut_wf A simI _) (b ^^ true)
      obtain ⟨hrel, hreal, hsim⟩ := redeem_facts A simR PR p hwf.1 hwf.2.1 hwf.2.2
        (redeemOk_pt_of_allOk idx A.base hok b true)
      simp only [↓reduceIte]
      refine le_of_eq_of_le (congrArg₂ (fun x y => |x - y|) (pr_congr fun a => ?_)
        (pr_congr fun a => ?_)) (hR (xROf A p) (wROf A p) hrel
        (fun o g s => FR A idx simI simR b γ (.ok (p.tok.nf ++ o)) g (LR A idx simI progI progR b γ s))
        ⟨fun o s => hA.h3R _ _ _ _ _ _ _,
          fun o g => (rd5_postRO (idx := idx) hA _ _ (Rd5.const _) (Rd5.const _) _).comp_prog
            hL,
          fun o g => (rdE_postRO (idx := idx) hA _ _ (RdE.const _) (RdE.const _) _).comp_prog
            hL⟩)
      · rw [hreal]
      · rw [hsim]

end Hops

/-! ## Issuer hiding and unlinkability in the random-oracle model -/

variable {A idx PI PR simI simR progI progR} in
/-- **Theorem 4(a) in the random-oracle and ideal-cipher model, for any proof systems.** The real
game runs the spec with every proof computed on the shared tables, and the adversary's guess sees
all tables (budget `q₃, q₅, q_E`). If the issuance and redemption proofs are `ZeroKnowledgeRO`
(errors `εI`, `εR` as functions of the budgets), their real provers read `H₅` and the cipher at
`r₅`, `r_E` keys, their programmings at `m₅`, `m_E` keys (`IsProg`), and the hiding reductions
(simulator coins and tables fixed) have advantage `≤ εhide`, then the worlds differ by at most
twice the four zero-knowledge errors at the reductions' budgets, plus the collision terms of both
worlds (`deltaI1`, `deltaL`, `deltaR`), plus `2εhide`. -/
theorem anonymityRO [Fintype CI] [Nonempty CI] [Fintype CR] [Nonempty CR]
    {q3 q5 qE r5 rE m5 mE : ℕ} {εI εR : ℕ → ℕ → ℕ → ℝ} {εhide : ℝ}
    (hA : A.Budget q3 q5 qE)
    (hPI5 : ∀ w x rho g, Rd5 (PI w x rho g) r5) (hPIE : ∀ w x rho g, RdE (PI w x rho g) rE)
    (hPR5 : ∀ w x rho g, Rd5 (PR w x rho g) r5) (hPRE : ∀ w x rho g, RdE (PR w x rho g) rE)
    (hpI : ∀ x c, IsProg (progI x c) m5 mE) (hpR : ∀ x c, IsProg (progR x c) m5 mE)
    (hI : ∀ a c, ZeroKnowledgeRO IssueRelW
      (fun x w (ρ : Coins proveSeedBytes) g s => PI w x (List.ofFn ρ) g s) simI progI
      (Budget pI q3 a c) (εI q3 a c))
    (hR : ∀ a c, ZeroKnowledgeRO RedeemRelW
      (fun x w (ρ : Coins proveSeedBytes) g s => PR w x (List.ofFn ρ) g s) simR progR
      (Budget pR q3 a c) (εR q3 a c))
    (hεR : ∀ a c, 0 ≤ εR q3 a c)
    (hhide : ∀ b c, hidingAdv A.base.ci A.base.cr (reductionRO A idx simI simR progI progR b c) ≤
      εhide) :
    |pr _ (realGameRO A idx PI PR false) - pr _ (realGameRO A idx PI PR true)| ≤
      2 * (εI q3 (r5 + (r5 + r5 + q5)) (rE + (rE + rE + qE)) +
          εI q3 (r5 + r5 + q5 + m5) (rE + rE + qE + mE) +
          εR q3 (0 + r5 + q5 + (m5 + m5)) (0 + rE + qE + (mE + mE)) +
          εR q3 (0 + 0 + q5 + (m5 + (m5 + m5))) (0 + 0 + qE + (mE + (mE + mE)))) +
        2 * deltaI1 A progI PI +
        (deltaL A idx simI progI PR false + deltaL A idx simI progI PR true) +
        (deltaR A idx simI progI progR PR false + deltaR A idx simI progI progR PR true) +
        2 * εhide := by
  have hw (b : Bool) : |pr _ (realGameRO A idx PI PR b) - pr _ (idealGameRO A idx simI simR progI progR b)| ≤
      εI q3 (r5 + (r5 + r5 + q5)) (rE + (rE + rE + qE)) +
        (εI q3 (r5 + r5 + q5 + m5) (rE + rE + qE + mE) + deltaI1 A progI PI) +
        (εR q3 (0 + r5 + q5 + (m5 + m5)) (0 + rE + qE + (mE + mE)) +
          deltaL A idx simI progI PR b) +
        (εR q3 (0 + 0 + q5 + (m5 + (m5 + m5))) (0 + 0 + qE + (mE + (mE + mE))) +
          deltaR A idx simI progI progR PR b) + εhide := by
    have h1 := hop0RO (idx := idx) (simI := simI) (progI := progI) hA hPI5 hPIE hPR5 hPRE (hI _ _) b
    have h2 := hop1RO (idx := idx) (PI := PI) hA hPR5 hPRE hpI (hI _ _) b
    have h3 := hopLRO (idx := idx) (simI := simI) (simR := simR) (progR := progR) hA hPR5 hPRE hpI (hεR _ _) (hR _ _) b
    have h4 := hopRRO (idx := idx) (simI := simI) (simR := simR) (progR := progR) (PR := PR) hA hpI hpR (hεR _ _) (hR _ _) b
    have h5 := hiding_hopRO A idx simI simR progI progR b (hhide b)
    unfold realGameRO
    set p0 := pr _ (gameRO A idx b (issRealRO A PI) (issRealRO A PI) (redRealRO A PR) (redRealRO A PR))
    set p1 := pr _ (gameRO A idx b (issSimRO A simI progI) (issRealRO A PI) (redRealRO A PR)
      (redRealRO A PR))
    set p2 := pr _ (gameRO A idx b (issSimRO A simI progI) (issSimRO A simI progI) (redRealRO A PR)
      (redRealRO A PR))
    set p3 := pr _ (gameRO A idx b (issSimRO A simI progI) (issSimRO A simI progI)
      (redSimRO A simR progR) (redRealRO A PR))
    set p4 := pr _ (simGameRO A idx simI simR progI progR b)
    set p5 := pr _ (idealGameRO A idx simI simR progI progR b)
    have := abs_sub_le p0 p1 p5
    have := abs_sub_le p1 p2 p5
    have := abs_sub_le p2 p3 p5
    have := abs_sub_le p3 p4 p5
    linarith
  have h0 := hw false
  have h1 := hw true
  rw [idealGameRO_eq] at h0
  rw [abs_sub_comm] at h1
  have := abs_sub_le (pr _ (realGameRO A idx PI PR false))
    (pr _ (idealGameRO A idx simI simR progI progR true)) (pr _ (realGameRO A idx PI PR true))
  linarith

/-! ## With the Lean prover -/

section Lean

open VoleMole.Verifier VoleMole.Verifier.Bridge

variable [CipherRow R]

/-- **The Lean issuance prover in the random-oracle model** (`ZK.Sim.realROb` with SHAKE for the
hashes that are not tables), its output as the spec's proof bytes. -/
noncomputable def leanPI : ProverRO R IssueInstance := fun w x rho g s =>
  toL ((realROb pI Hashes.shake (stI x) (toBA w) (toBA rho) g s).toOption.getD .empty)

/-- The Lean redemption prover in the random-oracle model. -/
noncomputable def leanPR : ProverRO R RedeemInstance := fun w x rho g s =>
  toL ((realROb pR Hashes.shake (stR x) (toBA w) (toBA rho) g s).toOption.getD .empty)

/-- The issuance simulator's programming (`ZK.Sim.progRO`). -/
noncomputable def leanProgI (x : IssueInstance) (c : SimCoins pI) : ShM R → ShM R :=
  progRO pI Hashes.shake (stI x) c

/-- The redemption simulator's programming. -/
noncomputable def leanProgR (x : RedeemInstance) (c : SimCoins pR) : ShM R → ShM R :=
  progRO pR Hashes.shake (stR x) c

lemma leanPI_ofFn (w : Bytes) (x : IssueInstance) (ρ : Coins proveSeedBytes) (g : Tab3) (s : ShM R) :
    leanPI w x (List.ofFn ρ) g s =
      toL ((realRO pI Hashes.shake (stI x) (toBA w) ρ g s).toOption.getD .empty) := by
  simp only [leanPI, realRO, toBA_ofFn]

lemma leanPR_ofFn (w : Bytes) (x : RedeemInstance) (ρ : Coins proveSeedBytes) (g : Tab3) (s : ShM R) :
    leanPR w x (List.ofFn ρ) g s =
      toL ((realRO pR Hashes.shake (stR x) (toBA w) ρ g s).toOption.getD .empty) := by
  simp only [leanPR, realRO, toBA_ofFn]

/-- **Zero knowledge of the Lean issuance prover in the random-oracle model** (cipher rows `R`,
error `ZKRow.εz R pI`). -/
theorem leanPI_zkRO [ZKRow R] (q3 q5 qE : ℕ) : ZeroKnowledgeRO IssueRelW
    (fun x w (ρ : Coins proveSeedBytes) g (s : ShM R) => leanPI w x (List.ofFn ρ) g s) (leanSim pI)
    leanProgI (Budget pI q3 q5 qE) (ZKRow.εz R pI q3 q5 qE) := by
  have h := (lean_zeroKnowledgeROG (R := R) Hashes.shake pI stI (fun _ => rfl) rfl
    (fun _ w => toBA w) IssueRelW csI zkHypI hashesWF_shake
    (smallParams_of_le (by decide) (by decide)) q3 q5 qE).transfer
    id (fun _ w => w) (fun _ _ h => h) (fun o => toL (o.toOption.getD .empty))
    (fun D hD => Budget.comp _ hD)
  have e : (fun x w (ρ : Coins proveSeedBytes) g (s : ShM R) => leanPI w x (List.ofFn ρ) g s) =
      fun x w r g s => toL ((realRO pI Hashes.shake (stI (id x)) (toBA w) r g s).toOption.getD .empty) := by
    funext x w ρ g s
    exact leanPI_ofFn w x ρ g s
  rw [e]
  exact h

/-- **Zero knowledge of the Lean redemption prover in the random-oracle model.** -/
theorem leanPR_zkRO [ZKRow R] (q3 q5 qE : ℕ) : ZeroKnowledgeRO RedeemRelW
    (fun x w (ρ : Coins proveSeedBytes) g (s : ShM R) => leanPR w x (List.ofFn ρ) g s) (leanSim pR)
    leanProgR (Budget pR q3 q5 qE) (ZKRow.εz R pR q3 q5 qE) := by
  have h := (lean_zeroKnowledgeROG (R := R) Hashes.shake pR stR (fun _ => rfl) rfl
    (fun _ w => toBA w) RedeemRelW csR zkHypR hashesWF_shake
    (smallParams_of_le (by decide) (by decide)) q3 q5 qE).transfer
    id (fun _ w => w) (fun _ _ h => h) (fun o => toL (o.toOption.getD .empty))
    (fun D hD => Budget.comp _ hD)
  have e : (fun x w (ρ : Coins proveSeedBytes) g (s : ShM R) => leanPR w x (List.ofFn ρ) g s) =
      fun x w r g s => toL ((realRO pR Hashes.shake (stR (id x)) (toBA w) r g s).toOption.getD .empty) := by
    funext x w ρ g s
    exact leanPR_ofFn w x ρ g s
  rw [e]
  exact h

/-- **Theorem 4(a) with the Lean prover, for every type of cipher rows** (`ZKRow R`): the
issuance and redemption errors are `ZKRow.εz R pI`, `ZKRow.εz R pR` at the reductions' budgets,
four of each:

    4·εz(pI; q₃, q₅ + 3·624, q_E + 3·4607) + 4·εz(pR; q₃, q₅ + 3·624, q_E + 3·4607)
      + 2·δI₁ + Σ_b (δL b + δR b) + 2·εhide. -/
theorem anonymityRO_leanG [ZKRow R] (A : AdversaryRO R) (idx : AnchorSet → UOVKey → ℕ)
    {q3 q5 qE : ℕ} {εhide : ℝ} (hA : A.Budget q3 q5 qE)
    (hhide : ∀ b c, hidingAdv A.base.ci A.base.cr
      (reductionRO A idx (leanSim pI) (leanSim pR) leanProgI leanProgR b c) ≤ εhide) :
    |pr _ (realGameRO A idx leanPI leanPR false) - pr _ (realGameRO A idx leanPI leanPR true)| ≤
      4 * ZKRow.εz R pI q3 (q5 + 1872) (qE + 13821) +
        4 * ZKRow.εz R pR q3 (q5 + 1872) (qE + 13821) + 2 * deltaI1 A leanProgI leanPI +
        (deltaL A idx (leanSim pI) leanProgI leanPR false +
          deltaL A idx (leanSim pI) leanProgI leanPR true) +
        (deltaR A idx (leanSim pI) leanProgI leanProgR leanPR false +
          deltaR A idx (leanSim pI) leanProgI leanProgR leanPR true) +
        2 * εhide := by
  have hPI5 : ∀ w x rho g, Rd5 (leanPI (R := R) w x rho g) 624 := fun w x rho g =>
    (realROb_rd5 (p := pI) (Hb := Hashes.shake) (st := stI x) (w := toBA w) (toBA rho) g).map
      fun o => toL (o.toOption.getD .empty)
  have hPIE : ∀ w x rho g, RdE (leanPI (R := R) w x rho g) 4607 := fun w x rho g =>
    (realROb_rdE (p := pI) (st := stI x) (w := toBA w) hashesWF_shake (toBA rho) g).map
      fun o => toL (o.toOption.getD .empty)
  have hPR5 : ∀ w x rho g, Rd5 (leanPR (R := R) w x rho g) 624 := fun w x rho g =>
    (realROb_rd5 (p := pR) (Hb := Hashes.shake) (st := stR x) (w := toBA w) (toBA rho) g).map
      fun o => toL (o.toOption.getD .empty)
  have hPRE : ∀ w x rho g, RdE (leanPR (R := R) w x rho g) 4607 := fun w x rho g =>
    (realROb_rdE (p := pR) (st := stR x) (w := toBA w) hashesWF_shake (toBA rho) g).map
      fun o => toL (o.toOption.getD .empty)
  have h := anonymityRO (A := A) (idx := idx) (PI := leanPI) (PR := leanPR) (simI := leanSim pI)
    (simR := leanSim pR) (progI := leanProgI) (progR := leanProgR) (εI := ZKRow.εz R pI)
    (εR := ZKRow.εz R pR)
    hA hPI5 hPIE hPR5 hPRE (fun x c => progRO_isProg c) (fun x c => progRO_isProg c)
    (fun a c => leanPI_zkRO q3 a c) (fun a c => leanPR_zkRO q3 a c)
    (fun a c => ZKRow.εz_nonneg _ _ _ _) hhide
  have m : ∀ (p : Params) a c, a ≤ q5 + 1872 → c ≤ qE + 13821 →
      ZKRow.εz R p q3 a c ≤ ZKRow.εz R p q3 (q5 + 1872) (qE + 13821) :=
    fun p a c ha hc => ZKRow.εz_mono p le_rfl ha hc
  have m1 := m pI (624 + (624 + 624 + q5)) (4607 + (4607 + 4607 + qE)) (by omega) (by omega)
  have m2 := m pI (624 + 624 + q5 + 312) (4607 + 4607 + qE + 4607) (by omega) (by omega)
  have m3 := m pR (0 + 624 + q5 + (312 + 312)) (0 + 4607 + qE + (4607 + 4607)) (by omega) (by omega)
  have m4 := m pR (0 + 0 + q5 + (312 + (312 + 312))) (0 + 0 + qE + (4607 + (4607 + 4607))) (by omega)
    (by omega)
  linarith

/-- **Theorem 4(a) with the Lean prover, in the random-oracle and ideal-cipher model.** The
real game runs the spec with the Lean prover and verifier statements (dedicated label rows),
`H₃`, `H₂³`, `H₅` uniform tables, the cipher a uniform table, SHAKE for the other hashes; the
adversary's guess sees every table, reading each `H₃` slice at `q₃` keys, `H₅` at `q₅`, the cipher
at `q_E` keys and `H₂³` freely (its interaction does not read them). Then the two worlds differ by
at most

    8·εRO(q₃, q₅ + 3·624, q_E + 3·4607) + 2·δI₁ + Σ_b (δL b + δR b) + 2·εhide,

`εRO q₃ q₅ q_E = q₃·2⁻¹²⁸ + 2⁻¹¹³ + 221·(4607 + q_E + 4607)·2⁻¹²⁸ + (q₅ + 1)·2⁻¹²⁸`, the `δ` the
explicit programming-collision probabilities of the hybrids and `εhide` the hiding advantage of
the reductions (simulator coins and tables fixed). (`anonymityRO_leanG` at function rows.) -/
theorem anonymityRO_lean (A : AdversaryRO (Blk → Blk)) (idx : AnchorSet → UOVKey → ℕ)
    {q3 q5 qE : ℕ} {εhide : ℝ} (hA : A.Budget q3 q5 qE)
    (hhide : ∀ b c, hidingAdv A.base.ci A.base.cr
      (reductionRO A idx (leanSim pI) (leanSim pR) leanProgI leanProgR b c) ≤ εhide) :
    |pr _ (realGameRO A idx leanPI leanPR false) - pr _ (realGameRO A idx leanPI leanPR true)| ≤
      8 * εRO q3 (q5 + 1872) (qE + 13821) + 2 * deltaI1 A leanProgI leanPI +
        (deltaL A idx (leanSim pI) leanProgI leanPR false +
          deltaL A idx (leanSim pI) leanProgI leanPR true) +
        (deltaR A idx (leanSim pI) leanProgI leanProgR leanPR false +
          deltaR A idx (leanSim pI) leanProgI leanProgR leanPR true) +
        2 * εhide :=
  (anonymityRO_leanG A idx hA hhide).trans (le_of_eq (by
    rw [ZKRow.εz_fn, ZKRow.εz_fn]
    ring))

end Lean

end VoleMole.Privacy.Moussaka
