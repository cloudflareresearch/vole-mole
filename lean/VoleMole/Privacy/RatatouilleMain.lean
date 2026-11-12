import VoleMole.ZK.MainGame
import VoleMole.Privacy.RatatouilleLean

/-!
# Ratatouille unlinkability on `main` (no dedicated label rows), under (PU)

`Privacy.Ratatouille.unlinkability` (Theorem 2) assumes per-proof zero knowledge, which holds only
with the label-row fix. On `main` an issuance proof and the spend of the same token share the
opening `r` as the first 16 witness bytes (`ZK/Relations.lean`, `ratatouille_main_zk`), and a
spend's change token carries a fresh opening that the next spend proves with. Here the theorem is
proved for `main`'s layout with the joint hop of `ZK/MainGame.lean`, as `Privacy/MoussakaMain.lean`
does for Moussaka.

## The game (`realMainR`)

The malicious Issuer of `Ratatouille.Adversary` (key, context, initial balance, responses, refunds
and amounts chosen from the transcripts without reading the tables), whose guess also sees each
proof's `H₃`, `H₅` and cipher tables (`VisR`). The four proofs (two issuances, round 1's spend,
round 2's spend) are the executable prover in the model of `zk_rom_ic` for `main`'s statements
(`stI`, `stS` with `pIr`, `pSr`: `labelRows = false`; proof sizes `Sizes.main`), run as in
`Spec/Ratatouille.lean` (`issueM`, `spendM`: the Client's checks unchanged), and the guess as in
`Ratatouille.view`.

## The bound (`unlinkability_main`)

    |Pr[world (b₁, b₂)] − Pr[world (b₁', b₂')]|
      ≤ 8·(q₃·2⁻¹²⁸ + 221·(4607 + q_E)·2⁻¹²⁸) + 15·(PU(b₁, b₂) + PU(b₁', b₂')) + 2·εhide

with `PU` (`puTermR`) the (PU) event on simulated proofs (the guess's `H₅` read set on some
proof's table contains a candidate for that proof's witness prefix: an issued token's or a change
token's opening) and `εhide` the hiding of `Com` for `Ratatouille.reduction` of the Issuer at fixed
tables.
-/

open Finset

-- (The coin types are large products: their `Fintype` instances exceed the default size.)
set_option synthInstance.maxSize 1024

set_option linter.unusedSectionVars false
set_option linter.constructorNameAsVariable false

namespace VoleMole.Privacy.Ratatouille

open VoleMole.Spec.Ratatouille VoleMole.ZK.Sim VoleMole.Privacy.MainChain
open VoleMole.Verifier VoleMole.Verifier.Bridge

attribute [local irreducible] simulate proveIdeal proveE firstHit

/-! ## `main`'s statements -/

abbrev pIr : Params := { witnessBytes := 240, qsDegree := 9, labelRows := false }
abbrev pSr : Params := { witnessBytes := 847, qsDegree := 9, labelRows := false }

lemma mainP_pIr : MainP pIr := ⟨rfl, by decide⟩
lemma mainP_pSr : MainP pSr := ⟨rfl, by decide⟩
lemma small_pIr : SmallParams pIr := smallParams_of_le (by decide) (by decide)
lemma small_pSr : SmallParams pSr := smallParams_of_le (by decide) (by decide)

theorem zkHypIr (x : IssueInstance) (w : IssueWitness) (h : IssueRel x w) :
    ZKHyp CrtGen.tables (withP (stI x) pIr) (encI x w) (csI x) :=
  let z := zkHypI x w h
  { hvals := z.hvals, hdeg := z.hdeg, hd := z.hd, hd' := z.hd', hsat := z.hsat, hw := z.hw,
    hnm := z.hnm, hT := z.hT, hI := z.hI }

theorem zkHypSr (x : SpendInstance) (w : SpendWitness) (h : SpendRel x w) :
    ZKHyp CrtGen.tables (withP (stS x) pSr) (encS x w) (csS x) :=
  let z := zkHypS x w h
  { hvals := z.hvals, hdeg := z.hdeg, hd := z.hd, hd' := z.hd', hsat := z.hsat, hw := z.hw,
    hnm := z.hnm, hT := z.hT, hI := z.hI }

/-! ## The adversary and the game -/

/-- The four proofs' tables: issuance 0, 1, round 1's spend, round 2's spend. -/
abbrev VisR := Vis pIr × Vis pIr × Vis pSr × Vis pSr

/-- The guess's input: the issuance transcript and the spends. -/
abbrev GIn := IssTr Sizes.main ×
  Option (Except Error (SpendRequest Sizes.main) × Option (Except Error (SpendRequest Sizes.main)))

/-- **The malicious Issuer on `main`**: `Adversary`'s interaction (not reading the tables) and a
guess that also sees the four proofs' tables, with `H₅` read sets `R₁ … R₄`. -/
structure AdversaryRM where
  pk : PublicKey
  ctx : Context
  tInit : Credits
  respondIss : IssTr Sizes.main → Bool → Preimage
  d₁ : IssTr Sizes.main → Credits
  respond₁ : IssTr Sizes.main → Except Error (SpendRequest Sizes.main) → SpendResponse
  d₂ : IssTr Sizes.main → Except Error (SpendRequest Sizes.main) → Credits
  guess : GIn → VisR → Prop
  R₁ : GIn → VisR → Finset (SKey pIr)
  R₂ : GIn → VisR → Finset (SKey pIr)
  R₃ : GIn → VisR → Finset (SKey pSr)
  R₄ : GIn → VisR → Finset (SKey pSr)

namespace AdversaryRM

variable (A : AdversaryRM)

/-- The Issuer with its guess at fixed tables. -/
def atV (v : VisR) : Adversary Sizes.main :=
  ⟨A.pk, A.ctx, A.tInit, A.respondIss, A.d₁, A.respond₁, A.d₂, fun tr y => A.guess (tr, y) v⟩

/-- Its interaction (the guess is not used). -/
def int : Adversary Sizes.main :=
  ⟨A.pk, A.ctx, A.tInit, A.respondIss, A.d₁, A.respond₁, A.d₂, fun _ _ => True⟩

/-- **The guess's budget**: each proof's `H₃` table at `q3` and cipher at `qE` keys. -/
structure Budget (q3 qE : ℕ) : Prop where
  b₁ : ∀ g v₂ v₃ v₄, RdV q3 qE fun v₁ => A.guess g (v₁, v₂, v₃, v₄)
  b₂ : ∀ g v₁ v₃ v₄, RdV q3 qE fun v₂ => A.guess g (v₁, v₂, v₃, v₄)
  b₃ : ∀ g v₁ v₂ v₄, RdV q3 qE fun v₃ => A.guess g (v₁, v₂, v₃, v₄)
  b₄ : ∀ g v₁ v₂ v₃, RdV q3 qE fun v₄ => A.guess g (v₁, v₂, v₃, v₄)

/-- **Consistent `H₅` read sets** (`ZK.Sim.VCons` for the guess, its other input fixed). -/
def Cons : Prop :=
  ∀ g, VCons (S := Unit) (fun _ _ _ _ _ v₁ v₂ v₃ v₄ => A.guess g (v₁, v₂, v₃, v₄))
    (fun _ _ _ _ _ v₁ v₂ v₃ v₄ => A.R₁ g (v₁, v₂, v₃, v₄))
    (fun _ _ _ _ _ v₁ v₂ v₃ v₄ => A.R₂ g (v₁, v₂, v₃, v₄))
    (fun _ _ _ _ _ v₁ v₂ v₃ v₄ => A.R₃ g (v₁, v₂, v₃, v₄))
    (fun _ _ _ _ _ v₁ v₂ v₃ v₄ => A.R₄ g (v₁, v₂, v₃, v₄))

end AdversaryRM

variable (A : AdversaryRM)

/-- The four `(nf, r)`: issuance 0, 1; round 1's and round 2's new token. -/
abbrev SecR := Quad (Coins 24 × Coins 16)

/-- A proof as the spec's `n`-byte string (none if it was not made or failed). -/
def pfR (n : ℕ) (o : Option Out) : Option (Spec.Ratatouille.Bytes n) :=
  match o with
  | some e => vecOf n e
  | none => none

/-- The issuance statement and witness (none if `T_init = 0`: the Client throws). -/
def issStmtR (x : Coins 24 × Coins 16) : Option SW :=
  if A.tInit = 0 then none else
  some (stI ⟨com (vec x.1) A.ctx A.tInit (vec x.2), A.tInit, A.ctx⟩,
    encI ⟨com (vec x.1) A.ctx A.tInit (vec x.2), A.tInit, A.ctx⟩ ⟨vec x.1, vec x.2⟩)

/-- `issue_request_with_seed` with the proof `o` (`issueOf`). -/
def issueM (nf : Nullifier) (r : Opening) (o : Option Out) :
    Except Error (PendingTokenS × IssueRequest Sizes.main) :=
  if A.tInit = 0 then .error .invalidArgument else
  match pfR _ o with
  | none => .error .runtime
  | some pf => .ok (⟨nf, r, A.tInit, com nf A.ctx A.tInit r⟩, issueReqBytes (com nf A.ctx A.tInit r) pf)

/-- The issuance slot's output. -/
def issO (x : Coins 24 × Coins 16) (o : Option Out) : IssOut Sizes.main TokenS :=
  issOutOf A.int (issueM A (vec x.1) (vec x.2) o)

/-- The spend statement and witness, when the Client's checks pass (`spendOf`). -/
def spStmt (τ : TokenS) (d : Credits) (x : Coins 24 × Coins 16) : Option SW :=
  if ¬ τ.Valid A.pk A.ctx then none else
  match clientCheck τ.t τ.x d with
  | none => none
  | some t' =>
    some (stS ⟨A.pk, τ.nf, d, com (vec x.1) A.ctx t' (vec x.2), A.ctx⟩,
      encS ⟨A.pk, τ.nf, d, com (vec x.1) A.ctx t' (vec x.2), A.ctx⟩
        ⟨τ.t, τ.r, τ.x, τ.s, vec x.1, t', vec x.2⟩)

/-- `spend_request_with_seed` with the proof `o`. -/
def spendM (τ : TokenS) (d : Credits) (nf' : Nullifier) (r' : Opening) (o : Option Out) :
    Except Error (PendingSpendS × SpendRequest Sizes.main) :=
  if ¬ τ.Valid A.pk A.ctx then .error .invalidArgument else
  match clientCheck τ.t τ.x d with
  | none => .error .invalidArgument
  | some t' =>
    match pfR _ o with
    | none => .error .runtime
    | some pf => .ok (⟨nf', t', r', com nf' A.ctx t' r'⟩,
        SpendReq.toBytes ⟨τ.nf, d, com nf' A.ctx t' r', pf⟩)

/-- The spend slot's output. -/
def spO (τ : TokenS) (d : Credits) (x : Coins 24 × Coins 16) (o : Option Out) : SpOut Sizes.main TokenS :=
  spOutOf A.int (spendM A τ d (vec x.1) (vec x.2) o)

/-- The issuance transcript. -/
def trₘ (s : SecR) (o₁ o₂ : Option Out) : IssTr Sizes.main := ((issO A s.1.1 o₁).req, (issO A s.1.2 o₂).req)

/-- Client `c`'s issued token. -/
def tkₘ (s : SecR) (o₁ o₂ : Option Out) (c : Bool) : Option TokenS :=
  (bif c then issO A s.1.2 o₂ else issO A s.1.1 o₁).fin (A.respondIss (trₘ A s o₁ o₂) c)

/-- Round 1's spender's token. -/
def τ₁ₘ (b₁ : Bool) (s : SecR) (o₁ o₂ : Option Out) : TokenS :=
  tokD (tokIface A.int) (tkₘ A s o₁ o₂ false) (tkₘ A s o₁ o₂ true) b₁

/-- Round 1's spend. -/
def sp₁ₘ (b₁ : Bool) (s : SecR) (o₁ o₂ o₃ : Option Out) : SpOut Sizes.main TokenS :=
  spO A (τ₁ₘ A b₁ s o₁ o₂) (A.d₁ (trₘ A s o₁ o₂)) s.2.1 o₃

/-- Round 1's change token. -/
def chₘ (b₁ : Bool) (s : SecR) (o₁ o₂ o₃ : Option Out) : Option TokenS :=
  (sp₁ₘ A b₁ s o₁ o₂ o₃).fin (A.respond₁ (trₘ A s o₁ o₂) (sp₁ₘ A b₁ s o₁ o₂ o₃).req)

/-- Round 2's spender's token. -/
def τ₂ₘ (b₁ b₂ : Bool) (s : SecR) (o₁ o₂ o₃ : Option Out) : TokenS :=
  cur₂ (tokIface A.int) b₁ b₂ (tkₘ A s o₁ o₂ false) (tkₘ A s o₁ o₂ true) (chₘ A b₁ s o₁ o₂ o₃)

/-- Round 2's amount. -/
def d₂ₘ (b₁ : Bool) (s : SecR) (o₁ o₂ o₃ : Option Out) : Credits :=
  A.d₂ (trₘ A s o₁ o₂) (sp₁ₘ A b₁ s o₁ o₂ o₃).req

/-- **The game of world `(b₁, b₂)`**, as four proofs in sequence. -/
def gameₘ (b₁ b₂ : Bool) : Game SecR Out SW SW SW SW where
  σ₁ s := issStmtR A s.1.1
  σ₂ s _ := issStmtR A s.1.2
  σ₃ s o₁ o₂ := spStmt A (τ₁ₘ A b₁ s o₁ o₂) (A.d₁ (trₘ A s o₁ o₂)) s.2.1
  σ₄ s o₁ o₂ o₃ := spStmt A (τ₂ₘ A b₁ b₂ s o₁ o₂ o₃) (d₂ₘ A b₁ s o₁ o₂ o₃) s.2.2

/-- The guess's input in world `(b₁, b₂)` (`stage₃`). -/
def gR (b₁ b₂ : Bool) (s : SecR) (o₁ o₂ o₃ o₄ : Option Out) : GIn :=
  let I := tokIface A.int
  let tr := trₘ A s o₁ o₂
  let tk₀ := tkₘ A s o₁ o₂ false
  let tk₁ := tkₘ A s o₁ o₂ true
  let rq := (sp₁ₘ A b₁ s o₁ o₂ o₃).req
  let ch := chₘ A b₁ s o₁ o₂ o₃
  (tr, bif ok₁ A.int I tr tk₀ tk₁ then
    some (rq, bif ok₂ A.int I b₁ tr tk₀ tk₁ rq ch then
      some (spO A (τ₂ₘ A b₁ b₂ s o₁ o₂ o₃) (d₂ₘ A b₁ s o₁ o₂ o₃) s.2.2 o₄).req else none) else none)

/-- **The final event of world `(b₁, b₂)`.** -/
def evR (b₁ b₂ : Bool) : Ev SecR Out (Vis pIr) (Vis pIr) (Vis pSr) (Vis pSr) :=
  fun s o₁ o₂ o₃ o₄ v₁ v₂ v₃ v₄ => A.guess (gR A b₁ b₂ s o₁ o₂ o₃ o₄) (v₁, v₂, v₃, v₄)

def rR₁ (b₁ b₂ : Bool) : RSet SecR Out (Vis pIr) (Vis pIr) (Vis pSr) (Vis pSr) (SKey pIr) :=
  fun s o₁ o₂ o₃ o₄ v₁ v₂ v₃ v₄ => A.R₁ (gR A b₁ b₂ s o₁ o₂ o₃ o₄) (v₁, v₂, v₃, v₄)
def rR₂ (b₁ b₂ : Bool) : RSet SecR Out (Vis pIr) (Vis pIr) (Vis pSr) (Vis pSr) (SKey pIr) :=
  fun s o₁ o₂ o₃ o₄ v₁ v₂ v₃ v₄ => A.R₂ (gR A b₁ b₂ s o₁ o₂ o₃ o₄) (v₁, v₂, v₃, v₄)
def rR₃ (b₁ b₂ : Bool) : RSet SecR Out (Vis pIr) (Vis pIr) (Vis pSr) (Vis pSr) (SKey pSr) :=
  fun s o₁ o₂ o₃ o₄ v₁ v₂ v₃ v₄ => A.R₃ (gR A b₁ b₂ s o₁ o₂ o₃ o₄) (v₁, v₂, v₃, v₄)
def rR₄ (b₁ b₂ : Bool) : RSet SecR Out (Vis pIr) (Vis pIr) (Vis pSr) (Vis pSr) (SKey pSr) :=
  fun s o₁ o₂ o₃ o₄ v₁ v₂ v₃ v₄ => A.R₄ (gR A b₁ b₂ s o₁ o₂ o₃ o₄) (v₁, v₂, v₃, v₄)

variable [HasPrg]

/-- **The real game on `main`** in world `(b₁, b₂)`: the executable prover (`main`'s statements) in
the model of `zk_rom_ic`, SHAKE for the hashes that are not tables. -/
noncomputable def realMainR (b₁ b₂ : Bool) : ℝ :=
  pr _ (ev (gameₘ A b₁ b₂) (realSlot Hashes.shake CrtGen.tables pIr)
    (realSlot Hashes.shake CrtGen.tables pIr) (realSlot Hashes.shake CrtGen.tables pSr)
    (realSlot Hashes.shake CrtGen.tables pSr) (evR A b₁ b₂))

/-- **The (PU) term of world `(b₁, b₂)`** (`ZK.Sim.predAll` on simulated proofs). -/
noncomputable def puTermR (b₁ b₂ : Bool) : ℝ :=
  pr _ (ev (gameₘ A b₁ b₂) (simP pIr) (simP pIr) (simP pSr) (simP pSr)
    (predAll Hashes.shake CrtGen.tables mainP_pIr mainP_pIr mainP_pSr mainP_pSr
      (rR₁ A b₁ b₂) (rR₂ A b₁ b₂) (rR₃ A b₁ b₂) (rR₄ A b₁ b₂)))

/-! ## The hypotheses of the joint hop -/

lemma issStmtR_valid (x : Coins 24 × Coins 16) : ∀ y ∈ issStmtR A x, ValidZK CrtGen.tables pIr y := by
  intro y hy
  unfold issStmtR at hy
  split_ifs at hy
  · cases hy
  · cases hy
    refine ⟨_, zkHypIr _ _ ?_⟩
    rfl

lemma spStmt_valid (τ : TokenS) (d : Credits) (x : Coins 24 × Coins 16) :
    ∀ y ∈ spStmt A τ d x, ValidZK CrtGen.tables pSr y := by
  intro y hy
  unfold spStmt at hy
  split_ifs at hy with hv
  · cases hc : clientCheck τ.t τ.x d with
    | none => rw [hc] at hy; cases hy
    | some t' =>
      rw [hc] at hy
      cases hy
      exact ⟨_, zkHypSr _ _ ⟨hv, rfl, by
        have := clientCheck_eq hc; simp only at this ⊢; omega⟩⟩
  · cases hy

lemma vcons_evR (hC : A.Cons) (b₁ b₂ : Bool) :
    VCons (evR A b₁ b₂) (rR₁ A b₁ b₂) (rR₂ A b₁ b₂) (rR₃ A b₁ b₂) (rR₄ A b₁ b₂) := by
  refine ⟨fun s o₁ o₂ o₃ o₄ v₁ v₂ v₃ v₄ g h => ?_, fun s o₁ o₂ o₃ o₄ v₁ v₂ v₃ v₄ g h => ?_,
    fun s o₁ o₂ o₃ o₄ v₁ v₂ v₃ v₄ g h => ?_, fun s o₁ o₂ o₃ o₄ v₁ v₂ v₃ v₄ g h => ?_⟩
  · exact (hC (gR A b₁ b₂ s o₁ o₂ o₃ o₄)).c₁ () o₁ o₂ o₃ o₄ v₁ v₂ v₃ v₄ g h
  · exact (hC (gR A b₁ b₂ s o₁ o₂ o₃ o₄)).c₂ () o₁ o₂ o₃ o₄ v₁ v₂ v₃ v₄ g h
  · exact (hC (gR A b₁ b₂ s o₁ o₂ o₃ o₄)).c₃ () o₁ o₂ o₃ o₄ v₁ v₂ v₃ v₄ g h
  · exact (hC (gR A b₁ b₂ s o₁ o₂ o₃ o₄)).c₄ () o₁ o₂ o₃ o₄ v₁ v₂ v₃ v₄ g h

/-- **The joint hop in each world**: real against simulated, `4·εRF + 15·PU`. -/
theorem real_sim_mainR {q3 qE : ℕ} (hA : A.Budget q3 qE) (hC : A.Cons) (b₁ b₂ : Bool) :
    |realMainR A b₁ b₂ - pr _ (ev (gameₘ A b₁ b₂) (simSlot pIr) (simSlot pIr) (simSlot pSr)
      (simSlot pSr) (evR A b₁ b₂))| ≤ 4 * εRF q3 qE + 15 * puTermR A b₁ b₂ :=
  main_chain_le Hashes.shake CrtGen.tables mainP_pIr mainP_pIr mainP_pSr mainP_pSr (gameₘ A b₁ b₂)
    (evR A b₁ b₂) (rR₁ A b₁ b₂) (rR₂ A b₁ b₂) (rR₃ A b₁ b₂) (rR₄ A b₁ b₂) (vcons_evR A hC b₁ b₂)
    small_pIr small_pIr small_pSr small_pSr q3 qE
    (fun _ _ _ _ _ v₂ v₃ v₄ => hA.b₁ _ v₂ v₃ v₄) (fun _ _ _ _ _ v₁ v₃ v₄ => hA.b₂ _ v₁ v₃ v₄)
    (fun _ _ _ _ _ v₁ v₂ v₄ => hA.b₃ _ v₁ v₂ v₄) (fun _ _ _ _ _ v₁ v₂ v₃ => hA.b₄ _ v₁ v₂ v₃)
    (fun s => issStmtR_valid A s.1.1) (fun s _ => issStmtR_valid A s.1.2)
    (fun s _ _ => spStmt_valid A _ _ s.2.1) (fun s _ _ _ => spStmt_valid A _ _ s.2.2)

/-! ## With all proofs simulated: the game of `Ratatouille.unlinkability` at fixed tables -/

/-- The simulated issuance proof (the simulator ignores the instance). -/
noncomputable def simIR (_ : IssueInstance) (c : SimCoins pIr) : Option (IssueProof Sizes.main) :=
  vecOf _ (simulate pIr c)

/-- The simulated spend proof. -/
noncomputable def simSR (_ : SpendInstance) (c : SimCoins pSr) : Option (SpendProof Sizes.main) :=
  vecOf _ (simulate pSr c)

lemma issueM_sim (x : Coins 24 × Coins 16) (c : SimCoins pIr) :
    issueM A (vec x.1) (vec x.2) ((issStmtR A x).map fun _ => simulate pIr c) =
      issueSim simIR A.tInit A.ctx (vec x.1) (vec x.2) c := by
  unfold issueM issStmtR issueSim
  split_ifs
  · rfl
  · simp only [Option.map_some, pfR, simIR]
    rcases vecOf _ (simulate pIr c) with _ | pf <;> rfl

lemma spendM_sim (τ : TokenS) (d : Credits) (x : Coins 24 × Coins 16) (c : SimCoins pSr) :
    spendM A τ d (vec x.1) (vec x.2) ((spStmt A τ d x).map fun _ => simulate pSr c) =
      spendSim simSR A.pk τ d A.ctx (vec x.1) (vec x.2) c := by
  unfold spendM spStmt spendSim
  split_ifs
  · rcases hc : clientCheck τ.t τ.x d with _ | t'
    · rfl
    · simp only [Option.map_some, pfR, simSR]
      rcases vecOf _ (simulate pSr c) with _ | pf <;> rfl
  · rfl

/-- The simulated game's tape, regrouped: the tables, then `Ratatouille.simGame`'s tape. -/
def regroupₘ : SecR × (simSlot pIr).K × (simSlot pIr).K × (simSlot pSr).K × (simSlot pSr).K ≃
    VisR × SimTape (SimCoins pIr) (SimCoins pSr) where
  toFun x := ((x.2.1.2, x.2.2.1.2, x.2.2.2.1.2, x.2.2.2.2.2),
    (((x.1.1.1.1, x.1.1.1.2, x.2.1.1), (x.1.1.2.1, x.1.1.2.2, x.2.2.1.1)),
      ((x.1.2.1.1, x.1.2.1.2, x.2.2.2.1.1), (x.1.2.2.1, x.1.2.2.2, x.2.2.2.2.1))))
  invFun y := ((((y.2.1.1.1, y.2.1.1.2.1), (y.2.1.2.1, y.2.1.2.2.1)),
      ((y.2.2.1.1, y.2.2.1.2.1), (y.2.2.2.1, y.2.2.2.2.1))),
    (y.2.1.1.2.2, y.1.1), (y.2.1.2.2.2, y.1.2.1), (y.2.2.1.2.2, y.1.2.2.1), (y.2.2.2.2.2, y.1.2.2.2))
  left_inv _ := rfl
  right_inv _ := rfl

/-- **With all four proofs simulated, the game is `Ratatouille.simGame` of the Issuer at the
tables.** -/
theorem sim_eqR (b₁ b₂ : Bool) :
    pr _ (ev (gameₘ A b₁ b₂) (simSlot pIr) (simSlot pIr) (simSlot pSr) (simSlot pSr) (evR A b₁ b₂)) =
      @pr (VisR × SimTape (SimCoins pIr) (SimCoins pSr)) (@instFintypeProd _ _ _ _)
        (fun z => simGame (A.atV z.1) simIR simSR b₁ b₂ z.2) := by
  rw [← @pr_equiv _ _ _ (@instFintypeProd _ _ _ _) regroupₘ]
  refine pr_congr fun x => ?_
  simp only [ev, gameₘ, evR, gR, Slot.out, simSlot, trₘ, tkₘ, τ₁ₘ, sp₁ₘ, chₘ, τ₂ₘ, d₂ₘ, spO, issO,
    issueM_sim A, spendM_sim A]
  rfl

/-! ## Unlinkability on `main` -/

/-- **Theorem 2 on `main` (no label rows), under (PU).** For the malicious Issuer with the tables
(`H₃` and cipher budgets `q3`, `qE`, consistent `H₅` read sets), if every hiding reduction of the
Issuer at fixed tables has advantage at most `εhide`, any two worlds of the real game on `main`
differ by at most

    8·εRF(q3, qE) + 15·(puTermR (b₁, b₂) + puTermR (b₁', b₂')) + 2·εhide. -/
theorem unlinkability_main {q3 qE : ℕ} (hA : A.Budget q3 qE) (hC : A.Cons) {εhide : ℝ}
    (hhide : ∀ v b₁ b₂ co, hidingAdv (A.atV v).ctx (reduction (A.atV v) simIR simSR b₁ b₂ co) ≤ εhide)
    (b₁ b₂ b₁' b₂' : Bool) :
    |realMainR A b₁ b₂ - realMainR A b₁' b₂'| ≤
      8 * εRF q3 qE + 15 * (puTermR A b₁ b₂ + puTermR A b₁' b₂') + 2 * εhide := by
  have r0 := real_sim_mainR A hA hC b₁ b₂
  have r1 := real_sim_mainR A hA hC b₁' b₂'
  rw [sim_eqR] at r0 r1
  have h0 := avg_close (fun v => simGame (A.atV v) simIR simSR b₁ b₂)
    (fun v => idealGame (A.atV v) simIR simSR b₁ b₂)
    fun v => hiding_hop (A.atV v) simIR simSR b₁ b₂ (hhide v b₁ b₂)
  have h1 := avg_close (fun v => simGame (A.atV v) simIR simSR b₁' b₂')
    (fun v => idealGame (A.atV v) simIR simSR b₁' b₂')
    fun v => hiding_hop (A.atV v) simIR simSR b₁' b₂' (hhide v b₁' b₂')
  have e0 := avg_eq (fun v => idealGame (A.atV v) simIR simSR b₁ b₂)
    (fun v => idealGame (A.atV v) simIR simSR false false) fun v => idealGame_eq (A.atV v) simIR simSR b₁ b₂
  have e1 := avg_eq (fun v => idealGame (A.atV v) simIR simSR b₁' b₂')
    (fun v => idealGame (A.atV v) simIR simSR false false) fun v => idealGame_eq (A.atV v) simIR simSR b₁' b₂'
  beta_reduce at h0 h1 e0 e1
  have := abs_sub_le_iff.1 r0; have := abs_sub_le_iff.1 r1; have := abs_sub_le_iff.1 h0
  have := abs_sub_le_iff.1 h1
  rw [abs_sub_le_iff]
  constructor <;> linarith

end VoleMole.Privacy.Ratatouille
