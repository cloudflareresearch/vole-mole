import VoleMole.Privacy.MoussakaUnboundMain
import VoleMole.Privacy.MoussakaMainPU

/-!
# Unbound Moussaka on `main`: the (PU) term as the advantage of explicit predictors

`anonymityU_main` (`Privacy/MoussakaUnboundMain.lean`) bounds Theorem U5(a) on `main` by
`8·εRF + 15·(puTermU 0 + puTermU 1) + 2·εprf`, with `puTermU b` an event of the game with all four
proofs simulated. Here that event is reduced to the game `Privacy.PU.puAdv` for the unbound
commitment `UCom`, as `Privacy/MoussakaMainPU.lean` does for `Com`.

**`UCom` as a (PU) commitment.** `UCom(nf_key, ctx_iss, r)` is one truncated call of
Keccak-p[800,12] on a state with `r` at bytes `7 … 22` (`ucom_eq_comP`: it is
`PU.comP PU.kp800 (XU ctx_iss) (PU.trunc 45 55)`), injective in `r` (`XU_injective`). The public
part is the key `nf_key`: the predictor is given it, so it can compute every nullifier
`Derive(nf_key, ctx_red)` the view reveals. In the ideal-permutation model, a predictor with `q`
forward and inverse queries and `c` candidates has advantage at most
`(c + q)/(2¹²⁸ − q) + q/(2⁴⁴⁰ − q)` (`puAdvPerm_unbound_le`), as for `Com`.

**The predictors** (`predU`, `predU₀`, `predU₁`). With all proofs simulated, the guess's input is
a function of the commitments `t₀, t₁`, the keys `k₀, k₁` (through the nullifiers), the simulators'
coins and the tables (`yU_sim`, from `MoussakaUnbound.post_redSim`); so are the redemption
statements (`redStmtU_fin`) and the candidate sets `candJ`. For Client `c`, `predU b … c` is the
union of the candidates of its issuance proof and, when the game's rule lets the redemptions run
(`allOkT`), of each query answered by Client `c` (`who b q = c`): at most `3·(q₅ + 1)` candidates
(`card_predU_le`). Every proof has the Client's opening `r_c` as witness prefix
(`wPre_issueWitnessU`, `wPre_redeemWitnessU`).

**The reduction** (`puTermU_le`): if every `H₅` read set has at most `q₅` keys,

    puTermU b ≤ puAdv UCom (predU₀ b) + puAdv UCom (predU₁ b) + 2·(q₅ + 1)·2⁻¹²⁸,

the last term for the redemption proofs that are computed but not shown (a dummy token's, or both
when the rule refuses), bounded through the simulator's uniform `d` (`pr_d3_le`, `pr_d4_le`).

**`anonymityU_main_pu`**: Theorem U5(a) on `main` with two redemption queries,

    8·εRF(q₃, q_E) + 15·(Σ_{b, c} puAdv UCom (predU_c b) + 4·(q₅ + 1)·2⁻¹²⁸) + 2·εprf.
-/

open Finset

-- (The coin types are large products: their `Fintype` instances exceed the default size.)
set_option synthInstance.maxSize 1024

set_option linter.unusedSectionVars false
-- (The ideal-permutation bound has `2⁴⁴⁰`.)
set_option exponentiation.threshold 600
set_option linter.constructorNameAsVariable false

namespace VoleMole.Privacy.MoussakaUnbound

open VoleMole.Spec VoleMole.Spec.MoussakaUnbound VoleMole.ZK.Sim VoleMole.Privacy.MainChain
open VoleMole.Verifier VoleMole.Verifier.Bridge VoleMole.Privacy.PU
open VoleMole.Spec.Moussaka (NIZK AnchorSet Error ctxBytes proveSeedBytes rBytes nfBytes maxAnchors)
open VoleMole.Privacy.Moussaka (pf getD_of_take)

-- `UCom` and `Derive` evaluate Keccak-p[800]; nothing below needs to unfold them.
attribute [local irreducible] derive UOVKey.eval
attribute [local irreducible] simulate proveIdeal proveE firstHit

/-! ## `UCom` as a (PU) commitment -/

/-- **`encode_unbound_com_state(nf_key, ctx_iss, r)` as a state**, for the key `k` and the opening
`r`. -/
def XU (ci : Spec.Bytes) (k : Coins nfKeyBytes) (r : Coins 16) : KState :=
  fun i => (ucomState (List.ofFn k) ci (List.ofFn r))[i]

lemma toSt_XU (ci : Spec.Bytes) (k : Coins nfKeyBytes) (r : Coins 16) :
    toSt (XU ci k r) = ucomState (List.ofFn k) ci (List.ofFn r) := by
  apply Vector.ext
  intro i hi
  simp [toSt, XU]

/-- **`UCom` is one truncated call of Keccak-p[800,12]**:
`UCom(k, ctx_iss, r) = trunc 45 55 (kp800 (XU ci k r))`. -/
theorem ucom_eq_comP (ci : Spec.Bytes) (k : Coins nfKeyBytes) (r : Coins 16) :
    ucom (List.ofFn k) ci (List.ofFn r) = List.ofFn (comP kp800 (XU ci) (trunc 45 55) k r) := by
  unfold ucom comP
  rw [← toSt_XU]
  apply List.ext_getElem
  · rw [List.length_take, Vector.length_toList, List.length_ofFn]
    rfl
  · intro i h1 h2
    rw [List.getElem_take, Vector.getElem_toList, List.getElem_ofFn]
    rfl

/-- The opening is bytes `7 … 22` of the state. -/
lemma XU_apply_r (ci : Spec.Bytes) (k : Coins nfKeyBytes) (r : Coins 16) (j : Fin 16) :
    XU ci k r ⟨7 + j.1, by omega⟩ = r j := by
  have hj := j.2
  show (Arith.MoussakaUnbound.encodeUnboundComState (fn (List.ofFn k)) (fn ci)
    (fn (List.ofFn r)))[7 + j.1] = r j
  unfold Arith.MoussakaUnbound.encodeUnboundComState
  rw [Vector.getElem_ofFn]
  have h1 : ¬ (7 + j.1 < 7) := by omega
  have h2 : 7 + j.1 < 23 := by omega
  simp only [h1, h2, ite_false, ite_true, Nat.add_sub_cancel_left, fn, List.getD_eq_getElem?_getD,
    List.getElem?_ofFn, hj, dite_true, Option.getD_some]

/-- **The encoding is injective in the opening.** -/
theorem XU_injective (ci : Spec.Bytes) (k : Coins nfKeyBytes) : Function.Injective (XU ci k) := by
  intro r r' h
  funext j
  rw [← XU_apply_r ci k r j, ← XU_apply_r ci k r' j, h]

/-- **(PU) for unbound Moussaka's `UCom` in the ideal-permutation model.** With a uniform
permutation of the 800-bit state in place of Keccak-p[800,12], a predictor of the 128-bit opening
with at most `q` forward and inverse queries and at most `c` candidates has advantage at most

    (c + q) / (2¹²⁸ − q) + q / (2⁴⁴⁰ − q). -/
theorem puAdvPerm_unbound_le {Aux : Type} [Fintype Aux] [Nonempty Aux] (ci : Spec.Bytes)
    (A : Coins nfKeyBytes → Coins 45 → Aux → PTree KState (Finset (Coins 16)))
    {q c : ℕ} (hA : ∀ n t a, (A n t a).Bound q) (hc : ∀ n t a π, ((A n t a).run π).card ≤ c)
    (hq : q < 2 ^ 128) :
    puAdvPerm (XU ci) (trunc 45 55) A ≤
      (c + q) / (2 ^ 128 - q : ℝ) + q / (2 ^ 440 - q : ℝ) := by
  have hR : Fintype.card (Coins 16) = 2 ^ 128 :=
    (card_coins 16).trans (by norm_num)
  have hm : ∀ t : Coins 45,
      (2 ^ 8) ^ 55 ≤ (univ.filter fun y : KState => trunc 45 55 y = t).card := by
    intro t
    rw [card_fiber_trunc 45 55 t, Prob.card_uint8]
  have := puAdvPerm_le (XU ci) (XU_injective ci) (trunc 45 55) A hA hc hm
    (by rw [hR]; exact hq) (lt_of_lt_of_le hq (by
      rw [← pow_mul]; exact Nat.pow_le_pow_right (by norm_num) (by norm_num)))
  rw [hR] at this
  have e : (((2 ^ 8) ^ 55 : ℕ) : ℝ) = 2 ^ 440 := by
    rw [Nat.cast_pow, Nat.cast_pow, Nat.cast_ofNat, ← pow_mul]
  rw [e] at this
  simpa only [Nat.cast_pow, Nat.cast_ofNat] using this

attribute [local irreducible] ucom

/-! ## Witness prefixes -/

/-- **The unbound issuance witness starts with the opening.** -/
lemma wPre_issueWitnessU (k ci : Bytes) (r : Coins 16) :
    wPre (toBA (encodeIssueWitness k ci (List.ofFn r))) = r := by
  funext j
  show (toBA _).get! j.1 = r j
  rw [toBA_get!]
  refine getD_of_take ?_ j
  unfold encodeIssueWitness
  rw [List.append_assoc, List.take_append_of_le_length (by simp), List.take_of_length_le (by simp)]

/-- **The unbound redemption witness starts with the opening.** -/
lemma wPre_redeemWitnessU (k ci cr s : Bytes) (i : ℕ) (r : Coins 16) :
    wPre (toBA (encodeRedeemWitness k ci cr (List.ofFn r) s i)) = r := by
  funext j
  show (toBA _).get! j.1 = r j
  rw [toBA_get!]
  refine getD_of_take ?_ j
  unfold encodeRedeemWitness
  simp only [List.append_assoc]
  rw [List.take_append_of_le_length (by simp), List.take_of_length_le (by simp)]

/-! ## The simulated game as a function of the commitments and the keys -/

variable (A : AdversaryUM)

/-- `UCom` on the Clients' coins, with the adversary's `ctx_iss`. -/
def comU (k : Coins nfKeyBytes) (r : Coins rBytes) : Bytes := ucom (List.ofFn k) A.int.ci (List.ofFn r)

/-- **`UCom` is `PU.comP` at Keccak-p[800,12]**: the (PU) game for the unbound commitment is the
game of `Privacy/PU.lean` with `kp800` for the permutation. -/
theorem puAdv_comU_eq {Aux : Type} [Fintype Aux]
    (P : Coins nfKeyBytes → Bytes → Aux → Finset (Coins rBytes)) :
    puAdv (comU A) P = puAdv (comP kp800 (XU A.int.ci) (trunc 45 55))
      (fun n t a => P n (List.ofFn t) a) := by
  unfold puAdv
  refine pr_congr fun z => ?_
  rw [comU, ucom_eq_comP]

/-- Client `c`'s opening. -/
def rOfU (s : SecU) (c : Bool) : Coins rBytes := (bif c then s.2 else s.1).2

/-- Client `c`'s key. -/
def kOfU (s : SecU) (c : Bool) : Bytes := List.ofFn (bif c then s.2 else s.1).1

lemma tUM_eq (s : SecU) (c : Bool) : tUM A s c = comU A (bif c then s.2 else s.1).1 (rOfU s c) := rfl

/-- The four simulators' coins and tables (the tape of the simulated game without the secret). -/
abbrev AuxU := (SimCoins pIu × Vis pIu) × (SimCoins pIu × Vis pIu) × (SimCoins pRu × Vis pRu) ×
  (SimCoins pRu × Vis pRu)

variable [HasPrg]

/-- A simulated issuance request. -/
noncomputable def reqU (t : Bytes) (c : SimCoins pIu) : Bytes := t ++ pf (some (simulate pIu c))

/-- The tables. -/
def visU (k : AuxU) : VisU := (k.1.2, k.2.1.2, k.2.2.1.2, k.2.2.2.2)

/-- The nullifier table of the keys `k₀, k₁`: `c, ctx ↦ Derive(k_c, ctx)`. -/
def tabU (k₀ k₁ : Bytes) : Bool → Coins ctxBytes → Bytes :=
  fun c ctx => bif c then derive k₁ (List.ofFn ctx) else derive k₀ (List.ofFn ctx)

/-- **The guess's third input with all proofs simulated**, from the commitments, the keys and the
simulators' coins. -/
noncomputable def ySimU (b : Bool) (t₀ t₁ k₀ k₁ : Bytes) (k : AuxU) :
    Option (Fin 2 → Except Error Bytes) :=
  bif allOkT A.int (reqU t₀ k.1.1) (reqU t₁ k.2.1.1) t₀ t₁ then
    some ![ySim A.int simRU b (tabU k₀ k₁) (A.queries (reqU t₀ k.1.1) (reqU t₁ k.2.1.1) 0)
        k.2.2.1.1,
      ySim A.int simRU b (tabU k₀ k₁) (A.queries (reqU t₀ k.1.1) (reqU t₁ k.2.1.1) 1) k.2.2.2.1]
  else none

/-- The redemption instance of query `j` in world `b`, from the requests and the keys. -/
def xQU (b : Bool) (q₀ q₁ k₀ k₁ : Bytes) (j : Fin 2) : RedeemInstance :=
  ⟨(A.queries q₀ q₁ j).anchors.keys, tabU k₀ k₁ (who b (A.queries q₀ q₁ j)) (A.queries q₀ q₁ j).ctxRed,
    A.int.ci, List.ofFn (A.queries q₀ q₁ j).ctxRed, (A.queries q₀ q₁ j).cd⟩

/-- **The candidate sets of the four simulated proofs**, from the commitments, the keys, the
simulators' coins and the tables. -/
noncomputable def candU₁ (b : Bool) (t₀ t₁ k₀ k₁ : Bytes) (k : AuxU) : Finset (Coins rBytes) :=
  candJ Hashes.shake CrtGen.tables mainP_pIu (stI ⟨t₀, A.int.ci⟩)
    (A.R₁ (reqU t₀ k.1.1) (reqU t₁ k.2.1.1) (ySimU A b t₀ t₁ k₀ k₁ k) (visU k)) k.1.1

noncomputable def candU₂ (b : Bool) (t₀ t₁ k₀ k₁ : Bytes) (k : AuxU) : Finset (Coins rBytes) :=
  candJ Hashes.shake CrtGen.tables mainP_pIu (stI ⟨t₁, A.int.ci⟩)
    (A.R₂ (reqU t₀ k.1.1) (reqU t₁ k.2.1.1) (ySimU A b t₀ t₁ k₀ k₁ k) (visU k)) k.2.1.1

noncomputable def candU₃ (b : Bool) (t₀ t₁ k₀ k₁ : Bytes) (k : AuxU) : Finset (Coins rBytes) :=
  candJ Hashes.shake CrtGen.tables mainP_pRu
    (stR (xQU A b (reqU t₀ k.1.1) (reqU t₁ k.2.1.1) k₀ k₁ 0))
    (A.R₃ (reqU t₀ k.1.1) (reqU t₁ k.2.1.1) (ySimU A b t₀ t₁ k₀ k₁ k) (visU k)) k.2.2.1.1

noncomputable def candU₄ (b : Bool) (t₀ t₁ k₀ k₁ : Bytes) (k : AuxU) : Finset (Coins rBytes) :=
  candJ Hashes.shake CrtGen.tables mainP_pRu
    (stR (xQU A b (reqU t₀ k.1.1) (reqU t₁ k.2.1.1) k₀ k₁ 1))
    (A.R₄ (reqU t₀ k.1.1) (reqU t₁ k.2.1.1) (ySimU A b t₀ t₁ k₀ k₁ k) (visU k)) k.2.2.2.1

/-- Query `j`'s answering Client, from the requests. -/
noncomputable def whoU (b : Bool) (t₀ t₁ : Bytes) (k : AuxU) (j : Fin 2) : Bool :=
  who b (A.queries (reqU t₀ k.1.1) (reqU t₁ k.2.1.1) j)

/-- **The predictor for Client `c`'s opening in world `b`**: the candidates of its issuance proof
and, if the redemptions run (`allOkT`), of each query it answers. -/
noncomputable def predU (b : Bool) (t₀ t₁ k₀ k₁ : Bytes) (k : AuxU) (c : Bool) :
    Finset (Coins rBytes) :=
  (bif c then candU₂ A b t₀ t₁ k₀ k₁ k else candU₁ A b t₀ t₁ k₀ k₁ k) ∪
    (bif allOkT A.int (reqU t₀ k.1.1) (reqU t₁ k.2.1.1) t₀ t₁ then
      ((if whoU A b t₀ t₁ k 0 = c then candU₃ A b t₀ t₁ k₀ k₁ k else ∅) ∪
        (if whoU A b t₀ t₁ k 1 = c then candU₄ A b t₀ t₁ k₀ k₁ k else ∅))
    else ∅)

/-- **At most `3·(q₅ + 1)` candidates**, if every read set has at most `q₅` keys. -/
theorem card_predU_le {q5 : ℕ}
    (h₁ : ∀ q₀ q₁ y v, (A.R₁ q₀ q₁ y v).card ≤ q5) (h₂ : ∀ q₀ q₁ y v, (A.R₂ q₀ q₁ y v).card ≤ q5)
    (h₃ : ∀ q₀ q₁ y v, (A.R₃ q₀ q₁ y v).card ≤ q5) (h₄ : ∀ q₀ q₁ y v, (A.R₄ q₀ q₁ y v).card ≤ q5)
    (b : Bool) (t₀ t₁ k₀ k₁ : Bytes) (k : AuxU) (c : Bool) :
    (predU A b t₀ t₁ k₀ k₁ k c).card ≤ 3 * (q5 + 1) := by
  have e₁ : (candU₁ A b t₀ t₁ k₀ k₁ k).card ≤ q5 + 1 :=
    (card_candJ_le Hashes.shake CrtGen.tables mainP_pIu _ _ _).trans (Nat.succ_le_succ (h₁ _ _ _ _))
  have e₂ : (candU₂ A b t₀ t₁ k₀ k₁ k).card ≤ q5 + 1 :=
    (card_candJ_le Hashes.shake CrtGen.tables mainP_pIu _ _ _).trans (Nat.succ_le_succ (h₂ _ _ _ _))
  have e₃ : (candU₃ A b t₀ t₁ k₀ k₁ k).card ≤ q5 + 1 :=
    (card_candJ_le Hashes.shake CrtGen.tables mainP_pRu _ _ _).trans (Nat.succ_le_succ (h₃ _ _ _ _))
  have e₄ : (candU₄ A b t₀ t₁ k₀ k₁ k).card ≤ q5 + 1 :=
    (card_candJ_le Hashes.shake CrtGen.tables mainP_pRu _ _ _).trans (Nat.succ_le_succ (h₄ _ _ _ _))
  unfold predU
  generalize candU₁ A b t₀ t₁ k₀ k₁ k = C₁ at e₁ ⊢
  generalize candU₂ A b t₀ t₁ k₀ k₁ k = C₂ at e₂ ⊢
  generalize candU₃ A b t₀ t₁ k₀ k₁ k = C₃ at e₃ ⊢
  generalize candU₄ A b t₀ t₁ k₀ k₁ k = C₄ at e₄ ⊢
  generalize allOkT A.int (reqU t₀ k.1.1) (reqU t₁ k.2.1.1) t₀ t₁ = ok
  refine (Finset.card_union_le _ _).trans ?_
  have a : (bif c then C₂ else C₁).card ≤ q5 + 1 := by
    cases c
    · exact e₁
    · exact e₂
  have a₃ : (if whoU A b t₀ t₁ k 0 = c then C₃ else ∅).card ≤ q5 + 1 := by
    split_ifs
    · exact e₃
    · exact Nat.zero_le _
  have a₄ : (if whoU A b t₀ t₁ k 1 = c then C₄ else ∅).card ≤ q5 + 1 := by
    split_ifs
    · exact e₄
    · exact Nat.zero_le _
  have a' : (bif ok then ((if whoU A b t₀ t₁ k 0 = c then C₃ else ∅) ∪
      (if whoU A b t₀ t₁ k 1 = c then C₄ else ∅)) else ∅).card ≤ 2 * (q5 + 1) := by
    cases ok
    · exact Nat.zero_le _
    · exact (Finset.card_union_le _ _).trans (by omega)
  exact (Nat.add_le_add a a').trans (by omega)

/-! ## The simulated game, rewritten -/

lemma fin2_eta {X : Type*} (f : Fin 2 → X) : ![f 0, f 1] = f := by
  funext j; fin_cases j <;> rfl

/-- **With all proofs simulated, the guess's third input is a function of the commitments, the
keys and the simulators' coins** (`MoussakaUnbound.post_redSim`, for the adversary whose guess
compares its input with `ySimU`). -/
theorem yU_sim (b : Bool) (s : SecU) (k : AuxU) :
    yU A b s (some (simulate pIu k.1.1)) (some (simulate pIu k.2.1.1))
      ((redStmtU A (ptU A b s (some (simulate pIu k.1.1)) (some (simulate pIu k.2.1.1))
        0)).map fun _ => simulate pRu k.2.2.1.1)
      ((redStmtU A (ptU A b s (some (simulate pIu k.1.1)) (some (simulate pIu k.2.1.1))
        1)).map fun _ => simulate pRu k.2.2.2.1) =
      ySimU A b (tUM A s false) (tUM A s true) (kOfU s false) (kOfU s true) k := by
  unfold yU
  rw [redOutU_sim A (visU k), redOutU_sim A (visU k)]
  let A' : Adversary 2 := ⟨A.ctxIss, A.pk, A.respond, A.queries, fun _ _ y =>
    y = ySimU A b (tUM A s false) (tUM A s true) (kOfU s false) (kOfU s true) k⟩
  have h := (post_redSim A' simRU b (issU A s false (some (simulate pIu k.1.1)))
    (issU A s true (some (simulate pIu k.2.1.1))) ![k.2.2.1.1, k.2.2.2.1] rfl rfl).2
  have e : (fun j => redSim A' simRU (![k.2.2.1.1, k.2.2.2.1] j)
      (pt A' b (issU A s false (some (simulate pIu k.1.1))) (issU A s true (some (simulate pIu k.2.1.1)))
        j)) = ![redSim (A.atV (visU k)) simRU k.2.2.1.1
          (ptU A b s (some (simulate pIu k.1.1)) (some (simulate pIu k.2.1.1)) 0),
        redSim (A.atV (visU k)) simRU k.2.2.2.1
          (ptU A b s (some (simulate pIu k.1.1)) (some (simulate pIu k.2.1.1)) 1)] := by
    rw [← fin2_eta (fun j => redSim A' simRU (![k.2.2.1.1, k.2.2.2.1] j)
      (pt A' b (issU A s false (some (simulate pIu k.1.1))) (issU A s true (some (simulate pIu k.2.1.1)))
        j))]
    rfl
  have h2 := h (by
    show (bif allOkT A' _ _ _ _ then some _ else none) = _
    unfold ySimU
    congr 1
    congr 1
    rw [← fin2_eta (fun j => ySim A' simRU b _ (A'.queries _ _ j) (![k.2.2.1.1, k.2.2.2.1] j))]
    rfl)
  unfold post at h2
  rw [e] at h2
  exact h2

/-- **A redemption statement of a finalized token**: its instance is public (`xQU`), and its
witness prefix is the answering Client's opening. -/
theorem redStmtU_fin (b : Bool) (s : SecU) (k : AuxU) (j : Fin 2)
    (hf : finT A.int (reqU (tUM A s false) k.1.1) (reqU (tUM A s true) k.2.1.1) (tUM A s false)
      (tUM A s true) (whoU A b (tUM A s false) (tUM A s true) k j) = true) (y : SW)
    (hy : redStmtU A (ptU A b s (some (simulate pIu k.1.1)) (some (simulate pIu k.2.1.1)) j) =
      some y) :
    y.1 = stR (xQU A b (reqU (tUM A s false) k.1.1) (reqU (tUM A s true) k.2.1.1) (kOfU s false)
      (kOfU s true) j) ∧ wPre y.2 = rOfU s (whoU A b (tUM A s false) (tUM A s true) k j) := by
  set i₀ := issU A s false (some (simulate pIu k.1.1)) with hi₀
  set i₁ := issU A s true (some (simulate pIu k.2.1.1)) with hi₁
  set c := whoU A b (tUM A s false) (tUM A s true) k j with hc
  have hf' : finT A.int i₀.2 i₁.2 i₀.1.t i₁.1.t c = true := hf
  have htok : tokD A.int i₀ i₁ c = ⟨kOfU s c, List.ofFn (rOfU s c), resp A.int i₀.2 i₁.2 c⟩ := by
    unfold tokD
    rw [tok_of_fin A.int i₀ i₁ c]
    simp only [hf', ↓reduceIte, Option.getD_some]
    cases c <;> rfl
  have hP : ptU A b s (some (simulate pIu k.1.1)) (some (simulate pIu k.2.1.1)) j =
      ⟨⟨kOfU s c, List.ofFn (rOfU s c), resp A.int i₀.2 i₁.2 c⟩,
        (A.int.queries i₀.2 i₁.2 j).anchors, List.ofFn (A.int.queries i₀.2 i₁.2 j).ctxRed,
        (A.int.queries i₀.2 i₁.2 j).cd⟩ := by
    unfold ptU pt
    rw [← htok]
    rfl
  rw [hP] at hy
  unfold redStmtU at hy
  cases hfi : findIssuer (A.int.queries i₀.2 i₁.2 j).anchors (ucom (kOfU s c) A.int.ci
    (List.ofFn (rOfU s c))) (resp A.int i₀.2 i₁.2 c) with
  | none => rw [hfi] at hy; cases hy
  | some i =>
    rw [hfi] at hy
    cases hy
    refine ⟨?_, wPre_redeemWitnessU _ _ _ _ _ _⟩
    refine congrArg stR ?_
    unfold xRU xQU tabU kOfU
    rw [show who b (A.queries (reqU (tUM A s false) k.1.1) (reqU (tUM A s true) k.2.1.1) j) = c
      from rfl]
    cases c <;> rfl

/-! ## The hidden redemption proofs -/

/-- The witness prefix of query `j`'s redemption statement (zero if there is none). -/
noncomputable def hidRU (b : Bool) (j : Fin 2) (s : SecU) (c₁ c₂ : SimCoins pIu) : Bytes 16 :=
  match redStmtU A (ptU A b s (some (simulate pIu c₁)) (some (simulate pIu c₂)) j) with
  | some y => wPre y.2
  | none => fun _ => 0

/-- The candidates for the label offset of that proof, from a read set, the simulator's shared
tape and its corrections. -/
noncomputable def hidGU (b : Bool) (j : Fin 2) (s : SecU) (c₁ c₂ : SimCoins pIu)
    (S5 : Finset (SKey pRu)) (sh : Shared) (c : Bytes (16 * pRu.correctionBytes)) : Finset W128 :=
  match redStmtU A (ptU A b s (some (simulate pIu c₁)) (some (simulate pIu c₂)) j) with
  | some y => guessSet Hashes.shake CrtGen.tables (withP y.1 pRu) S5 sh (fieldsCD c (zeroB _))
  | none => ∅

lemma card_hidGU_le (b : Bool) (j : Fin 2) (s : SecU) (c₁ c₂ : SimCoins pIu)
    (S5 : Finset (SKey pRu)) (sh : Shared) (c : Bytes (16 * pRu.correctionBytes)) :
    (hidGU A b j s c₁ c₂ S5 sh c).card ≤ S5.card + 1 := by
  unfold hidGU
  split
  · exact card_guessSet_le _ _ _ _ _ _
  · exact Nat.zero_le _

/-- **The prediction of a redemption proof, with `d` separated**: the target and the candidates do
not read the simulator's `d`. -/
lemma predJ_hidU (b : Bool) (j : Fin 2) (s : SecU) (c₁ c₂ : SimCoins pIu) (S5 : Finset (SKey pRu))
    (k : SimCoins pRu × Vis pRu) :
    predJ Hashes.shake CrtGen.tables mainP_pRu S5 ((simP pRu).obs
      (redStmtU A (ptU A b s (some (simulate pIu c₁)) (some (simulate pIu c₂)) j)) k) →
    thetaMain (pre16 mainP_pRu.hw k.1.2.2.2.2.1) (hidRU A b j s c₁ c₂) ∈
      hidGU A b j s c₁ c₂ S5 k.1.1 k.1.2.1 := by
  unfold hidRU hidGU
  generalize redStmtU A (ptU A b s (some (simulate pIu c₁)) (some (simulate pIu c₂)) j) = y
  cases y with
  | none => exact fun h => (predJ_simP_none _ _ _ _ _ h).elim
  | some y =>
    intro h
    rw [predJ_simP, mem_candJ] at h
    have e := guessSet_fieldsCD Hashes.shake CrtGen.tables y.1 S5 k.1.1 k.1.2.1 (zeroB _)
      k.1.2.2.2.2.1
    show _ ∈ guessSet Hashes.shake CrtGen.tables (withP y.1 pRu) S5 k.1.1
      (fieldsCD k.1.2.1 (zeroB _))
    rw [e]
    exact h

/-! ## The reduction -/

/-- The event of `puTermU`, unfolded. -/
lemma puEvU_iff (b : Bool) (x : SecU × AuxU) :
    ev (gameU A b) (simP pIu) (simP pIu) (simP pRu) (simP pRu)
      (predAll Hashes.shake CrtGen.tables mainP_pIu mainP_pIu mainP_pRu mainP_pRu
        (rU₁ A b) (rU₂ A b) (rU₃ A b) (rU₄ A b)) x ↔
    (predJ Hashes.shake CrtGen.tables mainP_pIu
        (A.R₁ (reqU (tUM A x.1 false) x.2.1.1) (reqU (tUM A x.1 true) x.2.2.1.1)
          (ySimU A b (tUM A x.1 false) (tUM A x.1 true) (kOfU x.1 false) (kOfU x.1 true) x.2)
          (visU x.2))
        ((simP pIu).obs (some (issStmtU A x.1 false)) x.2.1) ∨
      predJ Hashes.shake CrtGen.tables mainP_pIu
        (A.R₂ (reqU (tUM A x.1 false) x.2.1.1) (reqU (tUM A x.1 true) x.2.2.1.1)
          (ySimU A b (tUM A x.1 false) (tUM A x.1 true) (kOfU x.1 false) (kOfU x.1 true) x.2)
          (visU x.2))
        ((simP pIu).obs (some (issStmtU A x.1 true)) x.2.2.1) ∨
      predJ Hashes.shake CrtGen.tables mainP_pRu
        (A.R₃ (reqU (tUM A x.1 false) x.2.1.1) (reqU (tUM A x.1 true) x.2.2.1.1)
          (ySimU A b (tUM A x.1 false) (tUM A x.1 true) (kOfU x.1 false) (kOfU x.1 true) x.2)
          (visU x.2))
        ((simP pRu).obs (redStmtU A (ptU A b x.1 (some (simulate pIu x.2.1.1))
          (some (simulate pIu x.2.2.1.1)) 0)) x.2.2.2.1) ∨
      predJ Hashes.shake CrtGen.tables mainP_pRu
        (A.R₄ (reqU (tUM A x.1 false) x.2.1.1) (reqU (tUM A x.1 true) x.2.2.1.1)
          (ySimU A b (tUM A x.1 false) (tUM A x.1 true) (kOfU x.1 false) (kOfU x.1 true) x.2)
          (visU x.2))
        ((simP pRu).obs (redStmtU A (ptU A b x.1 (some (simulate pIu x.2.1.1))
          (some (simulate pIu x.2.2.1.1)) 1)) x.2.2.2.2)) := by
  rw [← yU_sim A b x.1 x.2]
  exact Iff.rfl

/-- The event that Client `c`'s opening is among its predictor's candidates. -/
def winU (b c : Bool) (x : SecU × AuxU) : Prop :=
  rOfU x.1 c ∈ predU A b (tUM A x.1 false) (tUM A x.1 true) (kOfU x.1 false) (kOfU x.1 true) x.2 c

/-- The hidden redemption of query `0`: its `d` makes the dummy or real target a candidate. -/
def hidEvU₃ (b : Bool) (x : SecU × AuxU) : Prop :=
  thetaMain (pre16 mainP_pRu.hw x.2.2.2.1.1.2.2.2.2.1) (hidRU A b 0 x.1 x.2.1.1 x.2.2.1.1) ∈
    hidGU A b 0 x.1 x.2.1.1 x.2.2.1.1
      (A.R₃ (reqU (tUM A x.1 false) x.2.1.1) (reqU (tUM A x.1 true) x.2.2.1.1) none (visU x.2))
      x.2.2.2.1.1.1 x.2.2.2.1.1.2.1

/-- The hidden redemption of query `1`. -/
def hidEvU₄ (b : Bool) (x : SecU × AuxU) : Prop :=
  thetaMain (pre16 mainP_pRu.hw x.2.2.2.2.1.2.2.2.2.1) (hidRU A b 1 x.1 x.2.1.1 x.2.2.1.1) ∈
    hidGU A b 1 x.1 x.2.1.1 x.2.2.1.1
      (A.R₄ (reqU (tUM A x.1 false) x.2.1.1) (reqU (tUM A x.1 true) x.2.2.1.1) none (visU x.2))
      x.2.2.2.2.1.1 x.2.2.2.2.1.2.1

/-- With the rule passing, both tokens finalized. -/
lemma fin_of_allOkT {q₀ q₁ t₀ t₁ : Bytes} (h : allOkT A.int q₀ q₁ t₀ t₁ = true) (c : Bool) :
    finT A.int q₀ q₁ t₀ t₁ c = true := by
  unfold allOkT at h
  simp only [Bool.and_eq_true] at h
  cases c
  · exact h.1.1.1
  · exact h.1.1.2

set_option maxRecDepth 8192 in
/-- A shown redemption is a prediction of its answering Client's opening. -/
lemma win_of_shown (b : Bool) (s : SecU) (k : AuxU) (j : Fin 2)
    (hok : allOkT A.int (reqU (tUM A s false) k.1.1) (reqU (tUM A s true) k.2.1.1) (tUM A s false)
      (tUM A s true) = true) (S5 : Finset (SKey pRu)) (kj : SimCoins pRu × Vis pRu)
    (hS : S5 = (if j = 0 then A.R₃ else A.R₄) (reqU (tUM A s false) k.1.1)
      (reqU (tUM A s true) k.2.1.1)
      (ySimU A b (tUM A s false) (tUM A s true) (kOfU s false) (kOfU s true) k) (visU k))
    (hk : kj.1 = if j = 0 then k.2.2.1.1 else k.2.2.2.1)
    (h : predJ Hashes.shake CrtGen.tables mainP_pRu S5 ((simP pRu).obs
      (redStmtU A (ptU A b s (some (simulate pIu k.1.1)) (some (simulate pIu k.2.1.1)) j)) kj)) :
    winU A b false (s, k) ∨ winU A b true (s, k) := by
  rcases hy : redStmtU A (ptU A b s (some (simulate pIu k.1.1)) (some (simulate pIu k.2.1.1)) j)
    with _ | y
  · rw [hy] at h
    exact (predJ_simP_none _ _ _ _ _ h).elim
  · rw [hy, predJ_simP] at h
    obtain ⟨h1, h2⟩ := redStmtU_fin A b s k j (fin_of_allOkT A hok _) y hy
    rw [h1, h2] at h
    have hin : rOfU s (whoU A b (tUM A s false) (tUM A s true) k j) ∈ predU A b (tUM A s false)
        (tUM A s true) (kOfU s false) (kOfU s true) k (whoU A b (tUM A s false) (tUM A s true) k j) := by
      unfold predU
      refine Finset.mem_union_right _ ?_
      rw [hok]
      fin_cases j
      · refine Finset.mem_union_left _ ?_
        simp only [Fin.zero_eta, Fin.isValue, ↓reduceIte] at hS hk ⊢
        rw [hS, hk] at h
        exact h
      · refine Finset.mem_union_right _ ?_
        simp only [Fin.mk_one, Fin.isValue, one_ne_zero, ↓reduceIte] at hS hk ⊢
        rw [hS, hk] at h
        exact h
    generalize whoU A b (tUM A s false) (tUM A s true) k j = c at hin
    cases c
    · exact Or.inl hin
    · exact Or.inr hin

-- (The defeq checks on the nested tape exceed the default recursion depth.)
set_option maxRecDepth 8192 in
/-- **The (PU) event implies a prediction or a hit of a hidden proof's `d`.** -/
theorem puEvU_imp (b : Bool) (x : SecU × AuxU)
    (h : ev (gameU A b) (simP pIu) (simP pIu) (simP pRu) (simP pRu)
      (predAll Hashes.shake CrtGen.tables mainP_pIu mainP_pIu mainP_pRu mainP_pRu
        (rU₁ A b) (rU₂ A b) (rU₃ A b) (rU₄ A b)) x) :
    (winU A b false x ∨ winU A b true x) ∨ hidEvU₃ A b x ∨ hidEvU₄ A b x := by
  rw [puEvU_iff] at h
  obtain ⟨s, k⟩ := x
  dsimp only at h ⊢
  have hY : allOkT A.int (reqU (tUM A s false) k.1.1) (reqU (tUM A s true) k.2.1.1)
      (tUM A s false) (tUM A s true) = false →
      ySimU A b (tUM A s false) (tUM A s true) (kOfU s false) (kOfU s true) k = none := by
    intro hok
    unfold ySimU
    rw [hok]
    rfl
  rcases h with h | h | h | h
  · -- issuance of Client `false`
    rw [predJ_simP] at h
    refine Or.inl (Or.inl ?_)
    unfold winU predU
    refine Finset.mem_union_left _ ?_
    have hw : wPre (issStmtU A s false).2 = rOfU s false := wPre_issueWitnessU _ _ _
    rw [hw] at h
    exact h
  · -- issuance of Client `true`
    rw [predJ_simP] at h
    refine Or.inl (Or.inr ?_)
    unfold winU predU
    refine Finset.mem_union_left _ ?_
    have hw : wPre (issStmtU A s true).2 = rOfU s true := wPre_issueWitnessU _ _ _
    rw [hw] at h
    exact h
  · -- query `0`
    cases hok : allOkT A.int (reqU (tUM A s false) k.1.1) (reqU (tUM A s true) k.2.1.1)
      (tUM A s false) (tUM A s true)
    · rw [hY hok] at h
      exact Or.inr (Or.inl (predJ_hidU A b 0 s k.1.1 k.2.1.1 _ k.2.2.1 h))
    · exact Or.inl (win_of_shown A b s k 0 hok _ k.2.2.1 rfl rfl h)
  · -- query `1`
    cases hok : allOkT A.int (reqU (tUM A s false) k.1.1) (reqU (tUM A s true) k.2.1.1)
      (tUM A s false) (tUM A s true)
    · rw [hY hok] at h
      exact Or.inr (Or.inr (predJ_hidU A b 1 s k.1.1 k.2.1.1 _ k.2.2.2 h))
    · exact Or.inl (win_of_shown A b s k 1 hok _ k.2.2.2 rfl rfl h)

/-- **The predictor for Client `false`** in the game `PU.puAdv`: public part `nf_key₀`,
commitment `t₀`, auxiliary coins the other Client's `(nf_key₁, r₁)`, the simulators' coins and the
tables. -/
noncomputable def predU₀ (b : Bool) (n : Coins nfKeyBytes) (t : Bytes)
    (a : (Coins nfKeyBytes × Coins rBytes) × AuxU) : Finset (Coins rBytes) :=
  predU A b t (comU A a.1.1 a.1.2) (List.ofFn n) (List.ofFn a.1.1) a.2 false

/-- **The predictor for Client `true`.** -/
noncomputable def predU₁ (b : Bool) (n : Coins nfKeyBytes) (t : Bytes)
    (a : (Coins nfKeyBytes × Coins rBytes) × AuxU) : Finset (Coins rBytes) :=
  predU A b (comU A a.1.1 a.1.2) t (List.ofFn a.1.1) (List.ofFn n) a.2 true

theorem pr_winU_false (b : Bool) :
    pr (SecU × AuxU) (winU A b false) = puAdv (comU A) (predU₀ A b) := by
  let e : (Coins nfKeyBytes × Coins rBytes) × ((Coins nfKeyBytes × Coins rBytes) × AuxU) ≃
      SecU × AuxU :=
    { toFun := fun z => ((z.1, z.2.1), z.2.2)
      invFun := fun x => (x.1.1, (x.1.2, x.2))
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [← pr_equiv e]
  rfl

theorem pr_winU_true (b : Bool) :
    pr (SecU × AuxU) (winU A b true) = puAdv (comU A) (predU₁ A b) := by
  let e : (Coins nfKeyBytes × Coins rBytes) × ((Coins nfKeyBytes × Coins rBytes) × AuxU) ≃
      SecU × AuxU :=
    { toFun := fun z => ((z.2.1, z.1), z.2.2)
      invFun := fun x => (x.1.2, (x.1.1, x.2))
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [← pr_equiv e]
  rfl

theorem pr_hidEvU₃_le {q5 : ℕ} (h₃ : ∀ q₀ q₁ y v, (A.R₃ q₀ q₁ y v).card ≤ q5) (b : Bool) :
    pr (SecU × AuxU) (hidEvU₃ A b) ≤ (q5 + 1) / 2 ^ 128 := by
  have key := pr_d3_le (S := SecU) (K₁ := SimCoins pIu × Vis pIu) (K₂ := SimCoins pIu × Vis pIu)
    (Sh := Shared) (C := Bytes (16 * pRu.correctionBytes)) (X := Bytes (pRu.nMask * pRu.nMultBytes))
    (Y := Bytes 64) (Z := Bytes (16 * (pRu.qsDegree - 1))) (V := Vis pRu)
    (K₄ := SimCoins pRu × Vis pRu) mainP_pRu.hw
    (fun ω => hidRU A b 0 ω.1 ω.2.1.1 ω.2.2.1.1)
    (fun ω => hidGU A b 0 ω.1 ω.2.1.1 ω.2.2.1.1
      (A.R₃ (reqU (tUM A ω.1 false) ω.2.1.1) (reqU (tUM A ω.1 true) ω.2.2.1.1) none
        (ω.2.1.2, ω.2.2.1.2, ω.2.2.2.1.2, ω.2.2.2.2.2)) ω.2.2.2.1.1.1 ω.2.2.2.1.1.2.1)
    (q := q5)
    (fun ω => (card_hidGU_le A b 0 _ _ _ _ _ _).trans (Nat.succ_le_succ (h₃ _ _ _ _)))
  exact le_trans (le_of_eq (pr_inst_irrel _ _ _)) key

theorem pr_hidEvU₄_le {q5 : ℕ} (h₄ : ∀ q₀ q₁ y v, (A.R₄ q₀ q₁ y v).card ≤ q5) (b : Bool) :
    pr (SecU × AuxU) (hidEvU₄ A b) ≤ (q5 + 1) / 2 ^ 128 := by
  have key := pr_d4_le (S := SecU) (K₁ := SimCoins pIu × Vis pIu) (K₂ := SimCoins pIu × Vis pIu)
    (K₃ := SimCoins pRu × Vis pRu)
    (Sh := Shared) (C := Bytes (16 * pRu.correctionBytes)) (X := Bytes (pRu.nMask * pRu.nMultBytes))
    (Y := Bytes 64) (Z := Bytes (16 * (pRu.qsDegree - 1))) (V := Vis pRu) mainP_pRu.hw
    (fun ω => hidRU A b 1 ω.1 ω.2.1.1 ω.2.2.1.1)
    (fun ω => hidGU A b 1 ω.1 ω.2.1.1 ω.2.2.1.1
      (A.R₄ (reqU (tUM A ω.1 false) ω.2.1.1) (reqU (tUM A ω.1 true) ω.2.2.1.1) none
        (ω.2.1.2, ω.2.2.1.2, ω.2.2.2.1.2, ω.2.2.2.2.2)) ω.2.2.2.2.1.1 ω.2.2.2.2.1.2.1)
    (q := q5)
    (fun ω => (card_hidGU_le A b 1 _ _ _ _ _ _).trans (Nat.succ_le_succ (h₄ _ _ _ _)))
  exact le_trans (le_of_eq (pr_inst_irrel _ _ _)) key

/-- `puTermU` on the tape `SecU × AuxU`. -/
theorem puTermU_eq (b : Bool) :
    puTermU A b = pr (SecU × AuxU) (ev (gameU A b) (simP pIu) (simP pIu) (simP pRu) (simP pRu)
      (predAll Hashes.shake CrtGen.tables mainP_pIu mainP_pIu mainP_pRu mainP_pRu
        (rU₁ A b) (rU₂ A b) (rU₃ A b) (rU₄ A b))) := by
  unfold puTermU
  exact pr_inst_irrel _ _ _

/-- **The (PU) term is at most the advantage of the two explicit predictors**, plus
`2·(q₅ + 1)·2⁻¹²⁸` for the redemption proofs that are not shown. -/
theorem puTermU_le {q5 : ℕ} (h₃ : ∀ q₀ q₁ y v, (A.R₃ q₀ q₁ y v).card ≤ q5)
    (h₄ : ∀ q₀ q₁ y v, (A.R₄ q₀ q₁ y v).card ≤ q5) (b : Bool) :
    puTermU A b ≤ puAdv (comU A) (predU₀ A b) + puAdv (comU A) (predU₁ A b) +
      2 * ((q5 + 1) / 2 ^ 128) := by
  rw [puTermU_eq]
  have h := (pr_mono (puEvU_imp A b)).trans ((pr_or_le _ _).trans (add_le_add (pr_or_le _ _)
    (pr_or_le _ _)))
  rw [pr_winU_false, pr_winU_true] at h
  have a₃ := pr_hidEvU₃_le A h₃ b
  have a₄ := pr_hidEvU₄_le A h₄ b
  exact h.trans (by linarith)

/-! ## Theorem U5(a) on `main`, with (PU) as a game -/

-- (The defeq checks on the nested tape exceed the default recursion depth.)
set_option maxRecDepth 8192 in
/-- **Theorem U5(a) on `main` (no label rows), two redemption queries, with the (PU) advantage of
explicit predictors.** `anonymityU_main` with `puTermU` replaced by `puTermU_le`: for the colluding
adversary whose guess reads each `H₃` and cipher table at `q3`, `qE` keys and each `H₅` table at a
consistent read set of at most `q5` keys,

    |Pr[world 0] − Pr[world 1]| ≤ 8·εRF(q3, qE)
      + 15·(Σ_{b, c} puAdv UCom (predU_c b) + 4·(q5 + 1)·2⁻¹²⁸) + 2·εprf.

Each predictor outputs at most `3·(q5 + 1)` candidates (`card_predU_le`); in the ideal-permutation
model its advantage is bounded by `puAdvPerm_unbound_le`. The four `puAdv` terms and `εprf` are the
only terms that are not explicit numbers: (PU) for `UCom` and the PRF assumption on `Derive`, both
assumptions on Keccak-p[800,12]. -/
theorem anonymityU_main_pu {q3 q5 qE : ℕ} (hA : A.Budget q3 qE) (hC : A.Cons)
    (h₃ : ∀ q₀ q₁ y v, (A.R₃ q₀ q₁ y v).card ≤ q5) (h₄ : ∀ q₀ q₁ y v, (A.R₄ q₀ q₁ y v).card ≤ q5)
    {εprf : ℝ} (hprf : ∀ v b cc, prfAdv (A.atV v).ci (reduction (A.atV v) simIU simRU b cc) ≤ εprf) :
    |realU A false - realU A true| ≤
      8 * εRF q3 qE + 15 * (puAdv (comU A) (predU₀ A false) +
        puAdv (comU A) (predU₁ A false) + puAdv (comU A) (predU₀ A true) +
        puAdv (comU A) (predU₁ A true) + 4 * ((q5 + 1) / 2 ^ 128)) + 2 * εprf := by
  have h := anonymityU_main A hA hC hprf
  have p0 := puTermU_le A h₃ h₄ false
  have p1 := puTermU_le A h₃ h₄ true
  linarith

end VoleMole.Privacy.MoussakaUnbound
