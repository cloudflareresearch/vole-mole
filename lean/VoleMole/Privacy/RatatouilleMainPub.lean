import VoleMole.Privacy.RatatouilleMain
import VoleMole.Privacy.PUKeccak
import VoleMole.ZK.MainPU

/-!
# Ratatouille on `main`: the simulated game as a function of public values

`unlinkability_main` (`Privacy/RatatouilleMain.lean`) leaves the term `puTermR`: an event of the
game with all four proofs simulated. To turn it into the advantage of predictors in the game
`Privacy.PU.puAdv`, everything the event reads must be written as a function of the commitments,
the nullifiers, the simulators' coins and the tables. This file does that, for the per-proof-table
game (`Privacy/RatatouilleMainPU.lean`) and the shared-table game
(`Privacy/RatatouilleMainShared.lean`).

* **The values of the game** (`vTr`, `vTk`, `vτ₁`, `vOk₁`, `vCh`, `vOk₂`, `vτ₂`, `vG`): what
  `Ratatouille.view` computes from two issuances and round 1's spend, for any token type, as
  functions (the issuance transcript, the tokens, the refusal tests, the guess's input). A token
  map that commutes with the slots preserves them (`vTk_map` … `vG_map`: the content of
  `Ratatouille.view_map`, value by value).
* **The public world** (`iP`, `trP`, `τ₁P`, `d₁P`, `cr₁P`, `oP`, `ok₂P`, `τ₂P`, `d₂P`, `yP`,
  `gP`, `stIP`, `st₃P`, `st₄P`): these values for `Ratatouille.pubIss`/`pubSp` (tokens without
  openings), from the nullifiers, the two issued commitments `t₀, t₁` (values), the commitment
  functions `cf₂, cf₃` of the two spends' new tokens and the simulators' coins.
* **The simulated game is the public world** (`trₘ_pub` … `gR_pub`, `issStmtR_pub`,
  `spStmt_pub`, `σ₃_pub`, `σ₄_pub`): with the proofs simulated, the guess's input is `gP`, the
  statements of the four proofs are `stIP t₀`, `stIP t₁`, `st₃P`, `st₄P`, and their witness
  prefixes are the openings: of the issued token (issuance), of Client `b₁`'s issued token
  (round 1's spend, if the round runs), and of round 1's change token or Client `!b₁`'s issued
  token (round 2's spend, if it runs).
* **Each commitment column is used at one credit** (`oP_const`, `gP_const`, …): the issued
  commitments at `T_init` (by definition of `iP`), and round 1's new commitment at
  `cr₁P = clientCheck(τ₁.t, τ₁.x, d₁)`, a function of the issuance part alone. So the public world
  with `cf₂` is the public world with the constant `cf₂ cr₁P`, and the (PU) game for the change
  token's opening is the game for `PU.comCredit` with the issuance part in the public input
  (`comCh`).
-/

open Finset

-- (The coin types are large products: their `Fintype` instances exceed the default size.)
set_option synthInstance.maxSize 1024

set_option linter.unusedSectionVars false
set_option linter.constructorNameAsVariable false

namespace VoleMole.Privacy.Ratatouille

open VoleMole.Spec.Ratatouille VoleMole.ZK.Sim VoleMole.Privacy.MainChain
open VoleMole.Verifier VoleMole.Verifier.Bridge VoleMole.Privacy.PU

attribute [local irreducible] simulate proveIdeal proveE firstHit

/-! ## The values of the game, for any token type -/

section Vals

variable {Z : Sizes} (B : Adversary Z) {Tok : Type} (I : Iface Tok)

/-- What the guess gets after the issuance transcript. -/
abbrev Rounds' (Z : Sizes) :=
  Option (Except Error (SpendRequest Z) × Option (Except Error (SpendRequest Z)))

/-- The issuance transcript. -/
def vTr (i₀ i₁ : IssOut Z Tok) : IssTr Z := (i₀.req, i₁.req)

/-- Client `c`'s issued token. -/
def vTk (i₀ i₁ : IssOut Z Tok) (c : Bool) : Option Tok :=
  (bif c then i₁ else i₀).fin (B.respondIss (vTr i₀ i₁) c)

/-- Round 1's spender's token. -/
def vτ₁ (b₁ : Bool) (i₀ i₁ : IssOut Z Tok) : Tok :=
  tokD I (vTk B i₀ i₁ false) (vTk B i₀ i₁ true) b₁

/-- Round 1 runs. -/
def vOk₁ (i₀ i₁ : IssOut Z Tok) : Bool :=
  ok₁ B I (vTr i₀ i₁) (vTk B i₀ i₁ false) (vTk B i₀ i₁ true)

/-- Round 1's change token, from the spend `o`. -/
def vCh (i₀ i₁ : IssOut Z Tok) (o : SpOut Z Tok) : Option Tok :=
  o.fin (B.respond₁ (vTr i₀ i₁) o.req)

/-- Round 2 runs. -/
def vOk₂ (b₁ : Bool) (i₀ i₁ : IssOut Z Tok) (o : SpOut Z Tok) : Bool :=
  ok₂ B I b₁ (vTr i₀ i₁) (vTk B i₀ i₁ false) (vTk B i₀ i₁ true) o.req (vCh B i₀ i₁ o)

/-- Round 2's spender's token. -/
def vτ₂ (b₁ b₂ : Bool) (i₀ i₁ : IssOut Z Tok) (o : SpOut Z Tok) : Tok :=
  cur₂ I b₁ b₂ (vTk B i₀ i₁ false) (vTk B i₀ i₁ true) (vCh B i₀ i₁ o)

/-- **The guess's input**, from the issuances, round 1's spend `o` and round 2's request `y`. -/
def vG (b₁ : Bool) (i₀ i₁ : IssOut Z Tok) (o : SpOut Z Tok) (y : Except Error (SpendRequest Z)) :
    IssTr Z × Rounds' Z :=
  (vTr i₀ i₁, bif vOk₁ B I i₀ i₁ then
    some (o.req, bif vOk₂ B I b₁ i₀ i₁ o then some y else none) else none)

lemma vG_of_not_ok₁ (b₁ : Bool) (i₀ i₁ : IssOut Z Tok) (o : SpOut Z Tok)
    (y : Except Error (SpendRequest Z)) (h : vOk₁ B I i₀ i₁ = false) :
    vG B I b₁ i₀ i₁ o y = (vTr i₀ i₁, none) := by
  unfold vG
  rw [h]
  rfl

lemma vG_of_not_ok₂ (b₁ : Bool) (i₀ i₁ : IssOut Z Tok) (o : SpOut Z Tok)
    (y : Except Error (SpendRequest Z)) (h₁ : vOk₁ B I i₀ i₁ = true)
    (h : vOk₂ B I b₁ i₀ i₁ o = false) :
    vG B I b₁ i₀ i₁ o y = (vTr i₀ i₁, some (o.req, none)) := by
  unfold vG
  rw [h₁, h]
  rfl

lemma vG_of_ok (b₁ : Bool) (i₀ i₁ : IssOut Z Tok) (o : SpOut Z Tok)
    (y : Except Error (SpendRequest Z)) (h₁ : vOk₁ B I i₀ i₁ = true)
    (h : vOk₂ B I b₁ i₀ i₁ o = true) :
    vG B I b₁ i₀ i₁ o y = (vTr i₀ i₁, some (o.req, some y)) := by
  unfold vG
  rw [h₁, h]
  rfl

/-- The guess's input when round 2's request is not shown. -/
def vG' (i₀ i₁ : IssOut Z Tok) (o : SpOut Z Tok) : IssTr Z × Rounds' Z :=
  (vTr i₀ i₁, bif vOk₁ B I i₀ i₁ then some (o.req, none) else none)

lemma vG_eq_vG' (b₁ : Bool) (i₀ i₁ : IssOut Z Tok) (o : SpOut Z Tok)
    (y : Except Error (SpendRequest Z))
    (h : (vOk₁ B I i₀ i₁ && vOk₂ B I b₁ i₀ i₁ o) = false) :
    vG B I b₁ i₀ i₁ o y = vG' B I i₀ i₁ o := by
  unfold vG vG'
  cases h₁ : vOk₁ B I i₀ i₁
  · rfl
  · rw [h₁, Bool.true_and] at h
    rw [h]
    rfl

/-! ### Token maps -/

variable {Tok' : Type} (I' : Iface Tok') (π : Tok → Tok')

/-- An issuance slot is the image of another under a token map. -/
structure IssMap (i : IssOut Z Tok) (i' : IssOut Z Tok') : Prop where
  req : i'.req = i.req
  fin : ∀ s, i'.fin s = (i.fin s).map π

/-- A spend is the image of another under a token map. -/
structure SpMap (o : SpOut Z Tok) (o' : SpOut Z Tok') : Prop where
  req : o'.req = o.req
  fin : ∀ r, o'.fin r = (o.fin r).map π

variable {π} {i₀ i₁ : IssOut Z Tok} {i₀' i₁' : IssOut Z Tok'} {o : SpOut Z Tok}
  {o' : SpOut Z Tok'}

lemma vTr_map (h₀ : IssMap π i₀ i₀') (h₁ : IssMap π i₁ i₁') : vTr i₀' i₁' = vTr i₀ i₁ := by
  unfold vTr
  rw [h₀.req, h₁.req]

lemma vTk_map (h₀ : IssMap π i₀ i₀') (h₁ : IssMap π i₁ i₁') (c : Bool) :
    vTk B i₀' i₁' c = (vTk B i₀ i₁ c).map π := by
  unfold vTk
  rw [vTr_map h₀ h₁]
  cases c
  · exact h₀.fin _
  · exact h₁.fin _

lemma vτ₁_map (hd : π I.dflt = I'.dflt) (h₀ : IssMap π i₀ i₀') (h₁ : IssMap π i₁ i₁')
    (b₁ : Bool) : vτ₁ B I' b₁ i₀' i₁' = π (vτ₁ B I b₁ i₀ i₁) := by
  unfold vτ₁
  rw [vTk_map B h₀ h₁, vTk_map B h₀ h₁]
  exact tokD_map I I' π hd _ _ _

lemma vOk₁_map (hd : π I.dflt = I'.dflt) (hok : ∀ τ d, I'.ok (π τ) d = I.ok τ d)
    (h₀ : IssMap π i₀ i₀') (h₁ : IssMap π i₁ i₁') : vOk₁ B I' i₀' i₁' = vOk₁ B I i₀ i₁ := by
  unfold vOk₁
  rw [vTr_map h₀ h₁, vTk_map B h₀ h₁, vTk_map B h₀ h₁]
  exact ok₁_map B I I' π hd hok _ _ _

lemma vCh_map (h₀ : IssMap π i₀ i₀') (h₁ : IssMap π i₁ i₁') (ho : SpMap π o o') :
    vCh B i₀' i₁' o' = (vCh B i₀ i₁ o).map π := by
  unfold vCh
  rw [vTr_map h₀ h₁, ho.req, ho.fin]

lemma vOk₂_map (hd : π I.dflt = I'.dflt) (hok : ∀ τ d, I'.ok (π τ) d = I.ok τ d)
    (h₀ : IssMap π i₀ i₀') (h₁ : IssMap π i₁ i₁') (ho : SpMap π o o') (b₁ : Bool) :
    vOk₂ B I' b₁ i₀' i₁' o' = vOk₂ B I b₁ i₀ i₁ o := by
  unfold vOk₂
  rw [vTr_map h₀ h₁, vTk_map B h₀ h₁, vTk_map B h₀ h₁, ho.req, vCh_map B h₀ h₁ ho]
  exact ok₂_map B I I' π hd hok _ _ _ _ _ _

lemma vτ₂_map (hd : π I.dflt = I'.dflt) (h₀ : IssMap π i₀ i₀') (h₁ : IssMap π i₁ i₁')
    (ho : SpMap π o o') (b₁ b₂ : Bool) :
    vτ₂ B I' b₁ b₂ i₀' i₁' o' = π (vτ₂ B I b₁ b₂ i₀ i₁ o) := by
  unfold vτ₂
  rw [vTk_map B h₀ h₁, vTk_map B h₀ h₁, vCh_map B h₀ h₁ ho]
  exact cur₂_map I I' π hd _ _ _ _ _

end Vals

/-! ## Openings of the spec's tokens and witness prefixes -/

lemma getD_of_take' {l : List UInt8} {r : Coins 16} (h : l.take 16 = List.ofFn r) (k : Fin 16) :
    l.getD k.1 0 = r k := by
  have h1 : (l.take 16)[k.1]? = l[k.1]? := List.getElem?_take_of_lt k.2
  rw [List.getD_eq_getElem?_getD, ← h1, h, List.getElem?_ofFn]
  simp

lemma toList_vec {n : ℕ} (r : Coins n) : (vec r).toList = List.ofFn r := Vector.toList_ofFn

/-- **The issuance witness starts with the opening** (`issue.hpp:94-105`). -/
lemma wPre_encI (x : IssueInstance) (nf : Nullifier) (r : Coins 16) :
    wPre (encI x ⟨nf, vec r⟩) = r := by
  funext k
  show (toBA _).get! k.1 = r k
  rw [toBA_get!]
  refine getD_of_take' ?_ k
  rw [encodeIssueWitness, List.append_assoc, toList_vec]
  exact List.take_left' (by simp)

/-- **The spend witness starts with the opening of the token spent** (`spend.hpp:231-268`). -/
lemma wPre_encS (x : SpendInstance) (w : SpendWitness) (r : Coins 16) (hr : w.r = vec r) :
    wPre (encS x w) = r := by
  funext k
  show (toBA _).get! k.1 = r k
  rw [toBA_get!]
  refine getD_of_take' ?_ k
  simp only [encodeSpendWitness, List.append_assoc, hr, toList_vec]
  exact List.take_left' (by simp)

variable (A : AdversaryRM)

/-- **An issued token keeps the opening of its request.** -/
lemma issO_fin_r (x : Coins 24 × Coins 16) (o : Option Out) (resp : Preimage) (τ : TokenS)
    (h : (issO A x o).fin resp = some τ) : τ.r = vec x.2 := by
  unfold issO issOutOf at h
  simp only at h
  generalize hm : issueM A (vec x.1) (vec x.2) o = m at h
  rcases m with e | q
  · cases h
  · have hq : q.1.r = vec x.2 := by
      unfold issueM at hm
      split_ifs at hm
      split at hm
      · cases hm
      · rw [← Except.ok.inj hm]
    simp only [finalizeIssue] at h
    split_ifs at h
    rw [← Option.some.inj h]
    exact hq

/-- **A change token has the opening drawn for it.** -/
lemma spO_fin_r (τ : TokenS) (d : Credits) (x : Coins 24 × Coins 16) (o : Option Out)
    (resp : SpendResponse) (τ' : TokenS) (h : (spO A τ d x o).fin resp = some τ') :
    τ'.r = vec x.2 := by
  unfold spO spOutOf at h
  simp only at h
  generalize hm : spendM A τ d (vec x.1) (vec x.2) o = m at h
  rcases m with e | q
  · cases h
  · have hq : q.1.r = vec x.2 := by
      unfold spendM at hm
      split_ifs at hm
      split at hm
      · cases hm
      · split at hm
        · cases hm
        · rw [← Except.ok.inj hm]
    simp only [finalizeSpend] at h
    split_ifs at h
    rw [← Option.some.inj h]
    exact hq

/-! ## The spec's game as values -/

/-- Round 1 runs (the spec's world). -/
def ok₁ₘ (s : SecR) (o₁ o₂ : Option Out) : Bool :=
  vOk₁ A.int (tokIface A.int) (issO A s.1.1 o₁) (issO A s.1.2 o₂)

/-- Round 2 runs (the spec's world). -/
def ok₂ₘ (b₁ : Bool) (s : SecR) (o₁ o₂ o₃ : Option Out) : Bool :=
  vOk₂ A.int (tokIface A.int) b₁ (issO A s.1.1 o₁) (issO A s.1.2 o₂) (sp₁ₘ A b₁ s o₁ o₂ o₃)

lemma gR_eq (b₁ b₂ : Bool) (s : SecR) (o₁ o₂ o₃ o₄ : Option Out) :
    gR A b₁ b₂ s o₁ o₂ o₃ o₄ = vG A.int (tokIface A.int) b₁ (issO A s.1.1 o₁) (issO A s.1.2 o₂)
      (sp₁ₘ A b₁ s o₁ o₂ o₃)
      (spO A (τ₂ₘ A b₁ b₂ s o₁ o₂ o₃) (d₂ₘ A b₁ s o₁ o₂ o₃) s.2.2 o₄).req := rfl

/-- The guess's input when round 2's request is not shown. -/
def gR' (b₁ : Bool) (s : SecR) (o₁ o₂ o₃ : Option Out) : GIn :=
  vG' A.int (tokIface A.int) (issO A s.1.1 o₁) (issO A s.1.2 o₂) (sp₁ₘ A b₁ s o₁ o₂ o₃)

lemma gR_of_not_ok₁ (b₁ b₂ : Bool) (s : SecR) (o₁ o₂ o₃ o₄ : Option Out)
    (h : ok₁ₘ A s o₁ o₂ = false) : gR A b₁ b₂ s o₁ o₂ o₃ o₄ = (trₘ A s o₁ o₂, none) :=
  vG_of_not_ok₁ A.int (tokIface A.int) b₁ _ _ _ _ h

lemma gR_eq_gR' (b₁ b₂ : Bool) (s : SecR) (o₁ o₂ o₃ o₄ : Option Out)
    (h : (ok₁ₘ A s o₁ o₂ && ok₂ₘ A b₁ s o₁ o₂ o₃) = false) :
    gR A b₁ b₂ s o₁ o₂ o₃ o₄ = gR' A b₁ s o₁ o₂ o₃ :=
  vG_eq_vG' A.int (tokIface A.int) b₁ _ _ _ _ h

/-- Client `c`'s opening. -/
def rIss (s : SecR) (c : Bool) : Coins 16 := (bif c then s.1.2 else s.1.1).2

/-- **If round 1 runs, its spender's token has Client `b₁`'s opening.** -/
lemma τ₁ₘ_r (b₁ : Bool) (s : SecR) (o₁ o₂ : Option Out) (h : ok₁ₘ A s o₁ o₂ = true) :
    (τ₁ₘ A b₁ s o₁ o₂).r = vec (rIss s b₁) := by
  unfold ok₁ₘ vOk₁ ok₁ at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨h0, h1⟩, -⟩, -⟩ := h
  obtain ⟨τ₀, hτ₀⟩ := Option.isSome_iff_exists.1 h0
  obtain ⟨τ₁, hτ₁⟩ := Option.isSome_iff_exists.1 h1
  have e₀ : tkₘ A s o₁ o₂ false = some τ₀ := hτ₀
  have e₁ : tkₘ A s o₁ o₂ true = some τ₁ := hτ₁
  unfold τ₁ₘ tokD
  rw [e₀, e₁]
  cases b₁
  · exact issO_fin_r A s.1.1 o₁ _ τ₀ hτ₀
  · exact issO_fin_r A s.1.2 o₂ _ τ₁ hτ₁

/-- **If both rounds run, round 2's spender's token has the opening of round 1's change token
(`b₂ = b₁`) or of Client `!b₁`'s issued token.** -/
lemma τ₂ₘ_r (b₁ b₂ : Bool) (s : SecR) (o₁ o₂ o₃ : Option Out) (h : ok₁ₘ A s o₁ o₂ = true)
    (h₂ : ok₂ₘ A b₁ s o₁ o₂ o₃ = true) :
    (τ₂ₘ A b₁ b₂ s o₁ o₂ o₃).r = vec (bif b₂ == b₁ then s.2.1.2 else rIss s (!b₁)) := by
  unfold ok₁ₘ vOk₁ ok₁ at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨h0, h1⟩, -⟩, -⟩ := h
  obtain ⟨τ₀, hτ₀⟩ := Option.isSome_iff_exists.1 h0
  obtain ⟨τ₁, hτ₁⟩ := Option.isSome_iff_exists.1 h1
  have e₀ : tkₘ A s o₁ o₂ false = some τ₀ := hτ₀
  have e₁ : tkₘ A s o₁ o₂ true = some τ₁ := hτ₁
  unfold ok₂ₘ vOk₂ ok₂ at h₂
  simp only [Bool.and_eq_true] at h₂
  obtain ⟨⟨hc, -⟩, -⟩ := h₂
  obtain ⟨τc, hτc⟩ := Option.isSome_iff_exists.1 hc
  have ec : chₘ A b₁ s o₁ o₂ o₃ = some τc := hτc
  unfold τ₂ₘ cur₂ tokD
  rw [e₀, e₁, ec]
  cases b₂ == b₁
  · cases b₁
    · exact issO_fin_r A s.1.2 o₂ _ τ₁ hτ₁
    · exact issO_fin_r A s.1.1 o₁ _ τ₀ hτ₀
  · exact spO_fin_r A _ _ s.2.1 o₃ _ τc hτc

/-! ## The public world -/

variable [HasPrg]

/-- The simulators' coins of the four proofs. -/
abbrev CoR := (SimCoins pIr × SimCoins pIr) × (SimCoins pSr × SimCoins pSr)

/-- **A simulated issuance in the public world**, with the commitment `t`. -/
noncomputable def iP (n : Nullifier) (t : Commitment) (c : SimCoins pIr) :
    IssOut Sizes.main PubTok :=
  pubIss A.int simIR (fun _ => t) n c

/-- The issuance transcript. -/
noncomputable def trP (n : Nullifier × Nullifier) (t : Commitment × Commitment)
    (c : SimCoins pIr × SimCoins pIr) : IssTr Sizes.main :=
  vTr (iP A n.1 t.1 c.1) (iP A n.2 t.2 c.2)

/-- Round 1 runs. -/
noncomputable def ok₁P (n : Nullifier × Nullifier) (t : Commitment × Commitment)
    (c : SimCoins pIr × SimCoins pIr) : Bool :=
  vOk₁ A.int (pubIface A.int) (iP A n.1 t.1 c.1) (iP A n.2 t.2 c.2)

/-- Round 1's spender's token, without its opening. -/
noncomputable def τ₁P (b₁ : Bool) (n : Nullifier × Nullifier) (t : Commitment × Commitment)
    (c : SimCoins pIr × SimCoins pIr) : PubTok :=
  vτ₁ A.int (pubIface A.int) b₁ (iP A n.1 t.1 c.1) (iP A n.2 t.2 c.2)

/-- Round 1's amount. -/
noncomputable def d₁P (n : Nullifier × Nullifier) (t : Commitment × Commitment)
    (c : SimCoins pIr × SimCoins pIr) : Credits :=
  A.d₁ (trP A n t c)

/-- **The credit of round 1's change token**: `clientCheck(τ₁.t, τ₁.x, d₁)`, a function of the
issuance part (zero if the Client's check fails: the commitment is then not used). -/
noncomputable def cr₁P (b₁ : Bool) (n : Nullifier × Nullifier) (t : Commitment × Commitment)
    (c : SimCoins pIr × SimCoins pIr) : Credits :=
  (clientCheck (τ₁P A b₁ n t c).t (τ₁P A b₁ n t c).x (d₁P A n t c)).getD 0

/-- Round 1's spend, with the new token's commitment function `cf₂`. -/
noncomputable def oP (b₁ : Bool) (n : Quad Nullifier) (t : Commitment × Commitment)
    (cf₂ : Credits → Commitment) (co : CoR) : SpOut Sizes.main PubTok :=
  pubSp A.int simSR cf₂ n.2.1 co.2.1 (τ₁P A b₁ n.1 t co.1) (d₁P A n.1 t co.1)

/-- Round 2 runs. -/
noncomputable def ok₂P (b₁ : Bool) (n : Quad Nullifier) (t : Commitment × Commitment)
    (cf₂ : Credits → Commitment) (co : CoR) : Bool :=
  vOk₂ A.int (pubIface A.int) b₁ (iP A n.1.1 t.1 co.1.1) (iP A n.1.2 t.2 co.1.2)
    (oP A b₁ n t cf₂ co)

/-- Round 2's spender's token, without its opening. -/
noncomputable def τ₂P (b₁ b₂ : Bool) (n : Quad Nullifier) (t : Commitment × Commitment)
    (cf₂ : Credits → Commitment) (co : CoR) : PubTok :=
  vτ₂ A.int (pubIface A.int) b₁ b₂ (iP A n.1.1 t.1 co.1.1) (iP A n.1.2 t.2 co.1.2)
    (oP A b₁ n t cf₂ co)

/-- Round 2's amount. -/
noncomputable def d₂P (b₁ : Bool) (n : Quad Nullifier) (t : Commitment × Commitment)
    (cf₂ : Credits → Commitment) (co : CoR) : Credits :=
  A.d₂ (trP A n.1 t co.1) (oP A b₁ n t cf₂ co).req

/-- Round 2's request. -/
noncomputable def yP (b₁ b₂ : Bool) (n : Quad Nullifier) (t : Commitment × Commitment)
    (cf₂ cf₃ : Credits → Commitment) (co : CoR) : Except Error (SpendRequest Sizes.main) :=
  (pubSp A.int simSR cf₃ n.2.2 co.2.2 (τ₂P A b₁ b₂ n t cf₂ co) (d₂P A b₁ n t cf₂ co)).req

/-- **The guess's input with all proofs simulated**, from the nullifiers, the issued commitments,
the commitment functions of the spends' new tokens and the simulators' coins. -/
noncomputable def gP (b₁ b₂ : Bool) (n : Quad Nullifier) (t : Commitment × Commitment)
    (cf₂ cf₃ : Credits → Commitment) (co : CoR) : GIn :=
  vG A.int (pubIface A.int) b₁ (iP A n.1.1 t.1 co.1.1) (iP A n.1.2 t.2 co.1.2)
    (oP A b₁ n t cf₂ co) (yP A b₁ b₂ n t cf₂ cf₃ co)

/-- The statement of an issuance proof with commitment `t` (none if `T_init = 0`). -/
def stIP (t : Commitment) : Option Statement :=
  if A.tInit = 0 then none else some (stI ⟨t, A.tInit, A.ctx⟩)

/-- The statement of a spend of the public token `τ` (none if the Client's checks fail). -/
def stSP (τ : PubTok) (d : Credits) (cf : Credits → Commitment) : Option Statement :=
  if ¬ uovEval A.pk τ.s = tag τ.c τ.x then none else
  match clientCheck τ.t τ.x d with
  | none => none
  | some t' => some (stS ⟨A.pk, τ.nf, d, cf t', A.ctx⟩)

/-- **The statement of round 1's spend proof**, if the round runs. -/
noncomputable def st₃P (b₁ : Bool) (n : Quad Nullifier) (t : Commitment × Commitment)
    (cf₂ : Credits → Commitment) (co : CoR) : Option Statement :=
  bif ok₁P A n.1 t co.1 then stSP A (τ₁P A b₁ n.1 t co.1) (d₁P A n.1 t co.1) cf₂ else none

/-- **The statement of round 2's spend proof**, if both rounds run. -/
noncomputable def st₄P (b₁ b₂ : Bool) (n : Quad Nullifier) (t : Commitment × Commitment)
    (cf₂ cf₃ : Credits → Commitment) (co : CoR) : Option Statement :=
  bif ok₁P A n.1 t co.1 && ok₂P A b₁ n t cf₂ co then
    stSP A (τ₂P A b₁ b₂ n t cf₂ co) (d₂P A b₁ n t cf₂ co) cf₃ else none

/-! ## Each commitment column is used at one credit -/

/-- **A public spend reads its commitment function at one credit**: the Client's
`clientCheck(τ.t, τ.x, d)`. -/
lemma pubSp_const {Z : Sizes} {CS : Type} (B : Adversary Z)
    (simS : SpendInstance → CS → Option (SpendProof Z)) (cf : Credits → Commitment)
    (n : Nullifier) (c : CS) (τ : PubTok) (d : Credits) :
    pubSp B simS cf n c τ d =
      pubSp B simS (fun _ => cf ((clientCheck τ.t τ.x d).getD 0)) n c τ d := by
  unfold pubSp
  split_ifs
  · rcases hc : clientCheck τ.t τ.x d with _ | t'
    · rfl
    · rfl
  · rfl

lemma stSP_const (τ : PubTok) (d : Credits) (cf : Credits → Commitment) :
    stSP A τ d cf = stSP A τ d (fun _ => cf ((clientCheck τ.t τ.x d).getD 0)) := by
  unfold stSP
  split_ifs
  · rcases hc : clientCheck τ.t τ.x d with _ | t'
    · rfl
    · rfl
  · rfl

/-- **Round 1's spend uses `cf₂` at the credit `cr₁P` only.** -/
lemma oP_const (b₁ : Bool) (n : Quad Nullifier) (t : Commitment × Commitment)
    (cf₂ : Credits → Commitment) (co : CoR) :
    oP A b₁ n t cf₂ co = oP A b₁ n t (fun _ => cf₂ (cr₁P A b₁ n.1 t co.1)) co :=
  pubSp_const A.int simSR cf₂ _ _ _ _

lemma ok₂P_const (b₁ : Bool) (n : Quad Nullifier) (t : Commitment × Commitment)
    (cf₂ : Credits → Commitment) (co : CoR) :
    ok₂P A b₁ n t cf₂ co = ok₂P A b₁ n t (fun _ => cf₂ (cr₁P A b₁ n.1 t co.1)) co := by
  unfold ok₂P
  rw [oP_const]

lemma τ₂P_const (b₁ b₂ : Bool) (n : Quad Nullifier) (t : Commitment × Commitment)
    (cf₂ : Credits → Commitment) (co : CoR) :
    τ₂P A b₁ b₂ n t cf₂ co = τ₂P A b₁ b₂ n t (fun _ => cf₂ (cr₁P A b₁ n.1 t co.1)) co := by
  unfold τ₂P
  rw [oP_const]

lemma d₂P_const (b₁ : Bool) (n : Quad Nullifier) (t : Commitment × Commitment)
    (cf₂ : Credits → Commitment) (co : CoR) :
    d₂P A b₁ n t cf₂ co = d₂P A b₁ n t (fun _ => cf₂ (cr₁P A b₁ n.1 t co.1)) co := by
  unfold d₂P
  rw [oP_const]

lemma yP_const (b₁ b₂ : Bool) (n : Quad Nullifier) (t : Commitment × Commitment)
    (cf₂ cf₃ : Credits → Commitment) (co : CoR) :
    yP A b₁ b₂ n t cf₂ cf₃ co =
      yP A b₁ b₂ n t (fun _ => cf₂ (cr₁P A b₁ n.1 t co.1)) cf₃ co := by
  unfold yP
  rw [τ₂P_const, d₂P_const]

/-- **The guess's input uses `cf₂` at the credit `cr₁P` only.** -/
lemma gP_const (b₁ b₂ : Bool) (n : Quad Nullifier) (t : Commitment × Commitment)
    (cf₂ cf₃ : Credits → Commitment) (co : CoR) :
    gP A b₁ b₂ n t cf₂ cf₃ co =
      gP A b₁ b₂ n t (fun _ => cf₂ (cr₁P A b₁ n.1 t co.1)) cf₃ co := by
  unfold gP
  rw [oP_const, yP_const]

lemma st₃P_const (b₁ : Bool) (n : Quad Nullifier) (t : Commitment × Commitment)
    (cf₂ : Credits → Commitment) (co : CoR) :
    st₃P A b₁ n t cf₂ co = st₃P A b₁ n t (fun _ => cf₂ (cr₁P A b₁ n.1 t co.1)) co := by
  unfold st₃P
  rw [stSP_const]
  rfl

lemma st₄P_const (b₁ b₂ : Bool) (n : Quad Nullifier) (t : Commitment × Commitment)
    (cf₂ cf₃ : Credits → Commitment) (co : CoR) :
    st₄P A b₁ b₂ n t cf₂ cf₃ co =
      st₄P A b₁ b₂ n t (fun _ => cf₂ (cr₁P A b₁ n.1 t co.1)) cf₃ co := by
  unfold st₄P
  rw [ok₂P_const, τ₂P_const, d₂P_const]

/-! ## The simulated game is the public world -/

/-- The nullifiers. -/
def nS (s : SecR) : Quad Nullifier := ((vec s.1.1.1, vec s.1.2.1), (vec s.2.1.1, vec s.2.2.1))

/-- **The commitment of an issued token**: `Com(nf, ctx, T_init, r)`. -/
def comI (n : Coins 24) (r : Coins 16) : Commitment := com (vec n) A.ctx A.tInit (vec r)

/-- The two issued commitments. -/
def tS (s : SecR) : Commitment × Commitment := (comI A s.1.1.1 s.1.1.2, comI A s.1.2.1 s.1.2.2)

/-- The commitment function `t ↦ Com(nf, ctx, t, r)` of a spend's new token. -/
def cfS (x : Coins 24 × Coins 16) : Credits → Commitment := comFn A.int (vec x.1) (vec x.2)

/-- **A public issuance reads its commitment function at `T_init` only.** -/
lemma pubIss_const {Z : Sizes} {CI : Type} (B : Adversary Z)
    (simI : IssueInstance → CI → Option (IssueProof Z)) (cf : Credits → Commitment)
    (n : Nullifier) (c : CI) :
    pubIss B simI cf n c = pubIss B simI (fun _ => cf B.tInit) n c := rfl

lemma comFn_tInit (n : Coins 24) (r : Coins 16) :
    comFn A.int (vec n) (vec r) A.int.tInit = comI A n r := rfl

/-- A simulated issuance of the spec's world is `iP` at its commitment. -/
lemma issO_pub (x : Coins 24 × Coins 16) (c : SimCoins pIr) (o : Option Out)
    (ho : o = (issStmtR A x).map fun _ => simulate pIr c) :
    IssMap (pubOf A.int) (issO A x o) (iP A (vec x.1) (comI A x.1 x.2) c) := by
  have e : issO A x o = issSim A.int simIR (x.1, x.2, c) := by
    unfold issO
    rw [ho, issueM_sim]
    rfl
  have e' : iP A (vec x.1) (comI A x.1 x.2) c =
      pubIss A.int simIR (comFn A.int (vec x.1) (vec x.2)) (vec x.1) c := by
    rw [pubIss_const, comFn_tInit]
    rfl
  rw [e, e']
  exact ⟨(issSim_pub A.int simIR (x.1, x.2, c)).1, (issSim_pub A.int simIR (x.1, x.2, c)).2⟩

/-- A simulated spend of the spec's world is the public spend of the token's public part. -/
lemma spO_pub (τ : TokenS) (d : Credits) (x : Coins 24 × Coins 16) (c : SimCoins pSr)
    (o : Option Out) (ho : o = (spStmt A τ d x).map fun _ => simulate pSr c) :
    SpMap (pubOf A.int) (spO A τ d x o)
      (pubSp A.int simSR (cfS A x) (vec x.1) c (pubOf A.int τ) d) := by
  have e : spO A τ d x o = spSim A.int simSR (x.1, x.2, c) τ d := by
    unfold spO
    rw [ho, spendM_sim]
    rfl
  rw [e]
  exact ⟨(spSim_pub A.int simSR (x.1, x.2, c) τ d).1, (spSim_pub A.int simSR (x.1, x.2, c) τ d).2⟩

/-- **An issuance statement is public, and its witness prefix is the opening.** -/
lemma issStmtR_pub (x : Coins 24 × Coins 16) :
    (issStmtR A x).map Prod.fst = stIP A (comI A x.1 x.2) ∧
      ∀ y ∈ issStmtR A x, wPre y.2 = x.2 := by
  unfold issStmtR stIP
  split_ifs
  · exact ⟨rfl, fun y hy => by cases hy⟩
  · refine ⟨rfl, fun y hy => ?_⟩
    cases hy
    exact wPre_encI _ _ _

/-- **A spend statement is public, and its witness prefix is the opening of the token spent.** -/
lemma spStmt_pub (τ : TokenS) (d : Credits) (x : Coins 24 × Coins 16) :
    (spStmt A τ d x).map Prod.fst = stSP A (pubOf A.int τ) d (cfS A x) ∧
      ∀ y ∈ spStmt A τ d x, ∀ r : Coins 16, τ.r = vec r → wPre y.2 = r := by
  unfold spStmt stSP
  by_cases hv : τ.Valid A.pk A.ctx
  · have hv' : uovEval A.pk (pubOf A.int τ).s = tag (pubOf A.int τ).c (pubOf A.int τ).x := hv
    simp only [hv, hv', not_true_eq_false, ↓reduceIte]
    cases hc : clientCheck τ.t τ.x d with
    | none =>
      have hc' : clientCheck (pubOf A.int τ).t (pubOf A.int τ).x d = none := hc
      rw [hc']
      exact ⟨rfl, fun y hy => by cases hy⟩
    | some t' =>
      have hc' : clientCheck (pubOf A.int τ).t (pubOf A.int τ).x d = some t' := hc
      rw [hc']
      refine ⟨rfl, fun y hy r hr => ?_⟩
      cases hy
      exact wPre_encS _ _ r hr
  · have hv' : ¬ uovEval A.pk (pubOf A.int τ).s = tag (pubOf A.int τ).c (pubOf A.int τ).x := hv
    simp only [hv, hv', not_false_eq_true, ↓reduceIte]
    exact ⟨rfl, fun y hy => by cases hy⟩

section Sim

variable (b₁ b₂ : Bool) (s : SecR) (co : CoR) (o₁ o₂ o₃ o₄ : Option Out)
  (h₁ : o₁ = (issStmtR A s.1.1).map fun _ => simulate pIr co.1.1)
  (h₂ : o₂ = (issStmtR A s.1.2).map fun _ => simulate pIr co.1.2)
include h₁ h₂

lemma trₘ_pub : trₘ A s o₁ o₂ = trP A (nS s).1 (tS A s) co.1 :=
  (vTr_map (issO_pub A s.1.1 co.1.1 o₁ h₁) (issO_pub A s.1.2 co.1.2 o₂ h₂)).symm

lemma ok₁ₘ_pub : ok₁ₘ A s o₁ o₂ = ok₁P A (nS s).1 (tS A s) co.1 :=
  (vOk₁_map A.int (tokIface A.int) (pubIface A.int) rfl (tokIface_ok A.int)
    (issO_pub A s.1.1 co.1.1 o₁ h₁) (issO_pub A s.1.2 co.1.2 o₂ h₂)).symm

lemma τ₁ₘ_pub : pubOf A.int (τ₁ₘ A b₁ s o₁ o₂) = τ₁P A b₁ (nS s).1 (tS A s) co.1 :=
  (vτ₁_map A.int (tokIface A.int) (pubIface A.int) rfl
    (issO_pub A s.1.1 co.1.1 o₁ h₁) (issO_pub A s.1.2 co.1.2 o₂ h₂) b₁).symm

lemma d₁ₘ_pub : A.d₁ (trₘ A s o₁ o₂) = d₁P A (nS s).1 (tS A s) co.1 := by
  unfold d₁P
  rw [trₘ_pub A s co o₁ o₂ h₁ h₂]

/-- **The statement of round 1's spend proof is public.** -/
lemma σ₃_pub (h : ok₁ₘ A s o₁ o₂ = true) :
    (spStmt A (τ₁ₘ A b₁ s o₁ o₂) (A.d₁ (trₘ A s o₁ o₂)) s.2.1).map Prod.fst =
      st₃P A b₁ (nS s) (tS A s) (cfS A s.2.1) co := by
  unfold st₃P
  rw [← ok₁ₘ_pub A s co o₁ o₂ h₁ h₂, h, (spStmt_pub A _ _ _).1, τ₁ₘ_pub A b₁ s co o₁ o₂ h₁ h₂,
    d₁ₘ_pub A s co o₁ o₂ h₁ h₂]
  rfl

/-- **The witness prefix of round 1's spend proof is Client `b₁`'s opening**, if the round
runs. -/
lemma σ₃_wPre (h : ok₁ₘ A s o₁ o₂ = true) :
    ∀ y ∈ spStmt A (τ₁ₘ A b₁ s o₁ o₂) (A.d₁ (trₘ A s o₁ o₂)) s.2.1, wPre y.2 = rIss s b₁ :=
  fun y hy => (spStmt_pub A _ _ _).2 y hy _ (τ₁ₘ_r A b₁ s o₁ o₂ h)

variable (h₃ : ok₁ₘ A s o₁ o₂ = true →
  o₃ = (spStmt A (τ₁ₘ A b₁ s o₁ o₂) (A.d₁ (trₘ A s o₁ o₂)) s.2.1).map fun _ => simulate pSr co.2.1)
include h₃

lemma sp₁ₘ_pub (h : ok₁ₘ A s o₁ o₂ = true) :
    SpMap (pubOf A.int) (sp₁ₘ A b₁ s o₁ o₂ o₃) (oP A b₁ (nS s) (tS A s) (cfS A s.2.1) co) := by
  have e := spO_pub A (τ₁ₘ A b₁ s o₁ o₂) (A.d₁ (trₘ A s o₁ o₂)) s.2.1 co.2.1 o₃ (h₃ h)
  have e' : pubSp A.int simSR (cfS A s.2.1) (vec s.2.1.1) co.2.1 (pubOf A.int (τ₁ₘ A b₁ s o₁ o₂))
      (A.d₁ (trₘ A s o₁ o₂)) = oP A b₁ (nS s) (tS A s) (cfS A s.2.1) co := by
    unfold oP
    rw [τ₁ₘ_pub A b₁ s co o₁ o₂ h₁ h₂, d₁ₘ_pub A s co o₁ o₂ h₁ h₂]
    rfl
  rw [e'] at e
  exact e

lemma ok₂ₘ_pub (h : ok₁ₘ A s o₁ o₂ = true) :
    ok₂ₘ A b₁ s o₁ o₂ o₃ = ok₂P A b₁ (nS s) (tS A s) (cfS A s.2.1) co :=
  (vOk₂_map A.int (tokIface A.int) (pubIface A.int) rfl (tokIface_ok A.int)
    (issO_pub A s.1.1 co.1.1 o₁ h₁) (issO_pub A s.1.2 co.1.2 o₂ h₂)
    (sp₁ₘ_pub A b₁ s co o₁ o₂ o₃ h₁ h₂ h₃ h) b₁).symm

lemma τ₂ₘ_pub (h : ok₁ₘ A s o₁ o₂ = true) :
    pubOf A.int (τ₂ₘ A b₁ b₂ s o₁ o₂ o₃) = τ₂P A b₁ b₂ (nS s) (tS A s) (cfS A s.2.1) co :=
  (vτ₂_map A.int (tokIface A.int) (pubIface A.int) rfl
    (issO_pub A s.1.1 co.1.1 o₁ h₁) (issO_pub A s.1.2 co.1.2 o₂ h₂)
    (sp₁ₘ_pub A b₁ s co o₁ o₂ o₃ h₁ h₂ h₃ h) b₁ b₂).symm

lemma d₂ₘ_pub (h : ok₁ₘ A s o₁ o₂ = true) :
    d₂ₘ A b₁ s o₁ o₂ o₃ = d₂P A b₁ (nS s) (tS A s) (cfS A s.2.1) co := by
  unfold d₂ₘ d₂P
  rw [trₘ_pub A s co o₁ o₂ h₁ h₂, (sp₁ₘ_pub A b₁ s co o₁ o₂ o₃ h₁ h₂ h₃ h).req]

/-- **The statement of round 2's spend proof is public.** -/
lemma σ₄_pub (h : ok₁ₘ A s o₁ o₂ = true) (h' : ok₂ₘ A b₁ s o₁ o₂ o₃ = true) :
    (spStmt A (τ₂ₘ A b₁ b₂ s o₁ o₂ o₃) (d₂ₘ A b₁ s o₁ o₂ o₃) s.2.2).map Prod.fst =
      st₄P A b₁ b₂ (nS s) (tS A s) (cfS A s.2.1) (cfS A s.2.2) co := by
  unfold st₄P
  rw [← ok₁ₘ_pub A s co o₁ o₂ h₁ h₂, ← ok₂ₘ_pub A b₁ s co o₁ o₂ o₃ h₁ h₂ h₃ h, h, h',
    (spStmt_pub A _ _ _).1, τ₂ₘ_pub A b₁ b₂ s co o₁ o₂ o₃ h₁ h₂ h₃ h,
    d₂ₘ_pub A b₁ s co o₁ o₂ o₃ h₁ h₂ h₃ h]
  rfl

/-- **The witness prefix of round 2's spend proof** is the opening of round 1's change token
(`b₂ = b₁`) or of Client `!b₁`'s issued token, if both rounds run. -/
lemma σ₄_wPre (h : ok₁ₘ A s o₁ o₂ = true) (h' : ok₂ₘ A b₁ s o₁ o₂ o₃ = true) :
    ∀ y ∈ spStmt A (τ₂ₘ A b₁ b₂ s o₁ o₂ o₃) (d₂ₘ A b₁ s o₁ o₂ o₃) s.2.2,
      wPre y.2 = bif b₂ == b₁ then s.2.1.2 else rIss s (!b₁) :=
  fun y hy => (spStmt_pub A _ _ _).2 y hy _ (τ₂ₘ_r A b₁ b₂ s o₁ o₂ o₃ h h')

variable (h₄ : ok₁ₘ A s o₁ o₂ = true → ok₂ₘ A b₁ s o₁ o₂ o₃ = true →
  o₄ = (spStmt A (τ₂ₘ A b₁ b₂ s o₁ o₂ o₃) (d₂ₘ A b₁ s o₁ o₂ o₃) s.2.2).map
    fun _ => simulate pSr co.2.2)
include h₄

/-- **With all proofs simulated, the guess's input is public**: `gP` at the nullifiers, the issued
commitments and the commitment functions of the spends' new tokens. -/
theorem gR_pub : gR A b₁ b₂ s o₁ o₂ o₃ o₄ =
    gP A b₁ b₂ (nS s) (tS A s) (cfS A s.2.1) (cfS A s.2.2) co := by
  rw [gR_eq]
  unfold gP
  have hi₀ : IssMap (pubOf A.int) (issO A s.1.1 o₁) (iP A (nS s).1.1 (tS A s).1 co.1.1) :=
    issO_pub A s.1.1 co.1.1 o₁ h₁
  have hi₁ : IssMap (pubOf A.int) (issO A s.1.2 o₂) (iP A (nS s).1.2 (tS A s).2 co.1.2) :=
    issO_pub A s.1.2 co.1.2 o₂ h₂
  have hk : vOk₁ A.int (pubIface A.int) (iP A (nS s).1.1 (tS A s).1 co.1.1)
      (iP A (nS s).1.2 (tS A s).2 co.1.2) = ok₁ₘ A s o₁ o₂ :=
    (ok₁ₘ_pub A s co o₁ o₂ h₁ h₂).symm
  cases h : ok₁ₘ A s o₁ o₂
  · rw [vG_of_not_ok₁ _ _ _ _ _ _ _ h, vG_of_not_ok₁ _ _ _ _ _ _ _ (hk.trans h),
      vTr_map hi₀ hi₁]
  · have ho := sp₁ₘ_pub A b₁ s co o₁ o₂ o₃ h₁ h₂ h₃ h
    have hk₂ : vOk₂ A.int (pubIface A.int) b₁ (iP A (nS s).1.1 (tS A s).1 co.1.1)
        (iP A (nS s).1.2 (tS A s).2 co.1.2) (oP A b₁ (nS s) (tS A s) (cfS A s.2.1) co) =
        ok₂ₘ A b₁ s o₁ o₂ o₃ := (ok₂ₘ_pub A b₁ s co o₁ o₂ o₃ h₁ h₂ h₃ h).symm
    cases h' : ok₂ₘ A b₁ s o₁ o₂ o₃
    · rw [vG_of_not_ok₂ _ _ _ _ _ _ _ h h', vG_of_not_ok₂ _ _ _ _ _ _ _ (hk.trans h)
        (hk₂.trans h'), vTr_map hi₀ hi₁, ho.req]
    · rw [vG_of_ok _ _ _ _ _ _ _ h h', vG_of_ok _ _ _ _ _ _ _ (hk.trans h) (hk₂.trans h'),
        vTr_map hi₀ hi₁, ho.req]
      have e := (spO_pub A (τ₂ₘ A b₁ b₂ s o₁ o₂ o₃) (d₂ₘ A b₁ s o₁ o₂ o₃) s.2.2 co.2.2 o₄
        (h₄ h h')).req
      rw [← e]
      unfold yP
      rw [τ₂ₘ_pub A b₁ b₂ s co o₁ o₂ o₃ h₁ h₂ h₃ h, d₂ₘ_pub A b₁ s co o₁ o₂ o₃ h₁ h₂ h₃ h]
      rfl

end Sim

/-! ## The commitment of the change token, at a credit in the public part -/

/-- What the credit of round 1's change token depends on: the two issued tokens' `(nf, r)` and
the issuance simulators' coins. -/
abbrev BCh := ((Coins 24 × Coins 16) × (Coins 24 × Coins 16)) × (SimCoins pIr × SimCoins pIr)

/-- **The credit of round 1's change token**, from the issuance part. -/
noncomputable def crCh (b₁ : Bool) (b : BCh) : Credits :=
  cr₁P A b₁ (vec b.1.1.1, vec b.1.2.1) (comI A b.1.1.1 b.1.1.2, comI A b.1.2.1 b.1.2.2) b.2

/-- **The commitment of round 1's change token**: `PU.comCredit` with the issuance part in the
public input: `Com(nf', ctx, crCh b, r')`. -/
noncomputable def comCh (b₁ : Bool) : Coins 24 × BCh → Coins 16 → Commitment :=
  comCredit A.ctx (crCh A b₁)

end VoleMole.Privacy.Ratatouille
