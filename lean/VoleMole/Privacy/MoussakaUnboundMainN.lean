import VoleMole.ZK.MainSharedLin
import VoleMole.Privacy.MoussakaUnboundMainAll
import VoleMole.Privacy.MoussakaUnboundNCMainN
import VoleMole.Privacy.MoussakaUnboundAd
import VoleMole.Privacy.RatatouilleMainSharedPU

/-!
# Unbound Moussaka U5(a) on `main` with `n` adaptive redemption queries, all tables shared

`anonymityU_main_sharedAll` (`Privacy/MoussakaUnboundMainAll.lean`) is Theorem U5(a) on `main`
with **two** redemption queries chosen at once, all tables shared, and the prefix-collision term
`collUH b` of `main_sharedAll_le`, which is not bounded when one Client answers both queries. Here
the colluding adversary makes **`n` adaptive queries** (`MoussakaUnbound.AdversaryAd`'s game,
`Privacy/MoussakaUnboundAd.lean`), and the joint hop is the `ρ`-aware hop of `ZK/MainSharedN.lean`
in its linear form (`main_sharedAll_leLin`, `ZK/MainSharedLin.lean`), which has no
prefix-collision term.

## The game (`gameAN`, `realAN`)

The adversary (`AdversaryUAH`) chooses `ctx_iss`, the two issuing keys, the responses to the two
issuance requests, and each query from the requests and the history so far (`next`; it does not
read the tables); its guess sees the requests, the history (`none` if a token did not finalize),
the shared `H₅` table and cipher, the one `H₂³` table and `H₃`. `n + 2` slots of a
`ZK.Sim.NGame`: slots `0` and `1` are the two issuance proofs (`main`'s issuance layout, `pIu`),
slot `j + 2` is query `j` (`pRu`), proved iff both tokens finalized and the query is valid
(`validR`: both tokens redeemable in its set, and the context rule). The history after `j` queries
(`histA`) is read off the earlier slots' outputs.

## The steps

1. The joint hop (`real_sim_AN`): `main_sharedAll_leLin` for `n + 2` slots.
2. **With all proofs simulated** the guess's input is a function of the commitments, the nullifier
   table `c, ctx ↦ Derive(k_c, ctx)`, the simulators' coins and the tables (`simAN_iff`): the history
   is `MoussakaUnbound.runT` (`histA_sim`, `hist_runT`), and the `H₂³` table is the raw table
   programmed for the public statements of the history (`simAN_M`).
3. The PRF hop (`prf_hop_AN`, the PRF advantage with the commitments leaked, `prfAdv`) and the
   swap of `pr_run_swap` (`idealAN_eq`), whose guess may read the simulators' coins.
4. **The (PU) term**: with all proofs simulated, `bstarN` is a failed simulation (`noHitProb` per
   slot), a collision of two simulated proofs' sibling inputs (`313·2⁻¹²⁸` per pair), or a
   prediction of a slot's witness prefix, which is the opening of the Client that owns the slot,
   from the public candidates. The predictors `predAN_c b` of the game `PU.puAdv` for `UCom`
   **rerun the interaction**: from the commitment `t_c` and the public part `nf_key_c`, the other
   Client's coins and the rest of the tape, they recompute the requests, the run `runT` (on the
   nullifier table of the two keys), the statements, the `H₂³` table, the guess's read set and the
   proofs' active gate inputs, and output the candidates of all `n + 2` proofs
   (`card_candAN_le`: at most `(n + 2)·(q₅ + 312(n + 2) + 1)`).

## The bound (`anonymityU_main_sharedAllN`)

    |Pr[W₀] − Pr[W₁]| ≤ 4(n + 2)·(εS(2q₃ + n + 2, 2q_E + 2(n + 2)·4607) + Δ23N(9, n + 2))
        + Σ_{b,c} puAdv UCom (predAN_c b)
        + 2·((n + 2)·noHitProb + (n + 2)²·313·2⁻¹²⁸) + 2·εprf

for any queries, in particular several redemptions by one Client with one statement.
-/

open Finset

-- (The coin types are large products: their `Fintype` instances exceed the default size.)
set_option synthInstance.maxSize 1024

set_option linter.unusedSectionVars false
set_option linter.constructorNameAsVariable false

namespace VoleMole.Privacy.MoussakaUnbound

open VoleMole.Spec VoleMole.Spec.MoussakaUnbound VoleMole.ZK.Sim VoleMole.Privacy.MainChain
open VoleMole.Verifier VoleMole.Verifier.Bridge VoleMole.Privacy.PU
open VoleMole.Spec.Moussaka (NIZK AnchorSet Error ctxBytes proveSeedBytes rBytes nfBytes maxAnchors)
open VoleMole.Privacy.Moussaka (pf pgP)
open VoleMole.Privacy.Ratatouille (qo actLo candCo actO_qo candO_qo qOf_of card_imgo_le
  card_candCo_le)

-- `UCom` and `Derive` evaluate Keccak-p[800]; nothing below needs to unfold them.
attribute [local irreducible] ucom derive UOVKey.eval
attribute [local irreducible] simulate realRO progRO

/-! ## Adaptive histories -/

section HistR

variable {Q Y : Type*} (next : List (Q × Y) → Q) (valid : List (Q × Y) → Q → Bool) (refuse : Y)
  {n : ℕ}

lemma histR_succ (f : Fin n → Q → Y) {k : ℕ} (h : k < n) :
    histR next valid refuse f (k + 1) = histR next valid refuse f k ++
      [(next (histR next valid refuse f k),
        if valid (histR next valid refuse f k) (next (histR next valid refuse f k)) then
          f ⟨k, h⟩ (next (histR next valid refuse f k)) else refuse)] := by
  simp only [histR, h, ↓reduceDIte]

/-- **Two runs agree** if the oracles agree on every valid query they are asked. -/
theorem histR_congr_run (f f' : Fin n → Q → Y)
    (h : ∀ (k : ℕ) (hk : k < n),
      valid (histR next valid refuse f k) (next (histR next valid refuse f k)) = true →
      f ⟨k, hk⟩ (next (histR next valid refuse f k)) =
        f' ⟨k, hk⟩ (next (histR next valid refuse f k))) :
    ∀ k, histR next valid refuse f k = histR next valid refuse f' k
  | 0 => rfl
  | k + 1 => by
    have ih := histR_congr_run f f' h k
    by_cases hk : k < n
    · rw [histR_succ next valid refuse f hk, histR_succ next valid refuse f' hk, ← ih]
      by_cases hv : valid (histR next valid refuse f k) (next (histR next valid refuse f k)) = true
      · simp only [hv, ↓reduceIte, h k hk hv]
      · simp only [hv, Bool.false_eq_true, ↓reduceIte]
    · simp only [histR, hk, ↓reduceDIte]
      exact ih

/-- The history after `k` steps reads only the first `k` oracles. -/
theorem histR_congr_lt (f f' : Fin n → Q → Y) :
    ∀ k, (∀ i : Fin n, i.val < k → f i = f' i) →
      histR next valid refuse f k = histR next valid refuse f' k
  | 0, _ => rfl
  | k + 1, h => by
    have ih := histR_congr_lt f f' k fun i hi => h i (by omega)
    by_cases hk : k < n
    · rw [histR_succ next valid refuse f hk, histR_succ next valid refuse f' hk, ← ih,
        h ⟨k, hk⟩ (by simp)]
    · simp only [histR, hk, ↓reduceDIte]
      exact ih

/-- **Entry `k` of a later history** is query `k` and its answer. -/
theorem histR_get (f : Fin n → Q → Y) (k : ℕ) (hk : k < n) :
    ∀ m, k + 1 ≤ m → (histR next valid refuse f m)[k]? = some (next (histR next valid refuse f k),
      if valid (histR next valid refuse f k) (next (histR next valid refuse f k)) then
        f ⟨k, hk⟩ (next (histR next valid refuse f k)) else refuse)
  | 0, h => absurd h (by omega)
  | m + 1, h => by
    rcases Nat.eq_or_lt_of_le h with h' | h'
    · have hm : m = k := by omega
      subst hm
      have hl : (histR next valid refuse f m).length = m := by
        rw [histR_length]; omega
      rw [histR_succ next valid refuse f hk, List.getElem?_append_right (by omega), hl,
        Nat.sub_self]
      rfl
    · have ih := histR_get f k hk m (by omega)
      by_cases hm : m < n
      · rw [histR_succ next valid refuse f hm,
          List.getElem?_append_left (by rw [histR_length]; omega)]
        exact ih
      · simp only [histR, hm, ↓reduceDIte]
        exact ih

/-- A history entry is query `k` with its answer or nothing. -/
theorem histR_get_none (f : Fin n → Q → Y) (k : ℕ) (hk : ¬ k < n) (m : ℕ) :
    (histR next valid refuse f m)[k]? = none := by
  rw [List.getElem?_eq_none_iff, histR_length]
  omega

end HistR

/-! ## The adversary and the game -/

/-- **The colluding adversary on `main` with `n` adaptive queries and all tables shared**:
`AdversaryAd`'s interaction (not reading the tables) and a guess that also sees the shared `H₅`
table and cipher, the one `H₂³` table and `H₃`, with its `H₅` read set. -/
structure AdversaryUAH where
  ctxIss : Coins ctxBytes
  pk : Bool → UOVKey
  respond : Bytes → Bytes → Bool → Coins uovN
  next : Bytes → Bytes → Hist → Query
  guess : Bytes → Bytes → Option Hist → USh → Tab2G pIu → H3T → Prop
  R5 : Bytes → Bytes → Option Hist → USh → Tab2G pIu → H3T → Finset (ZK.Sim.Bytes 37)

namespace AdversaryUAH

variable (A : AdversaryUAH)

/-- Its interaction as an `AdversaryAd` (the guess is not used). -/
def ad : AdversaryAd := ⟨A.ctxIss, A.pk, A.respond, A.next, fun _ _ _ => True⟩

/-- The same as an `AdversaryUM` (for `main`'s statements `issStmtU`, `redStmtU`, `redOutU`). -/
def um : AdversaryUM :=
  ⟨A.ctxIss, A.pk, A.respond, fun q₀ q₁ _ => A.next q₀ q₁ [], fun _ _ _ _ => True,
    fun _ _ _ _ => ∅, fun _ _ _ _ => ∅, fun _ _ _ _ => ∅, fun _ _ _ _ => ∅⟩

/-- **Consistent reads**: with the requests and the history fixed, the guess and its `H₅` read set
read `H₃` at `q3` points, the cipher at `qE` keys and `H₅` at `R5`. -/
structure ConsH (q3 qE : ℕ) : Prop where
  g : ∀ q₀ q₁ y, RdUH (A.guess q₀ q₁ y) (A.R5 q₀ q₁ y) q3 qE
  r : ∀ q₀ q₁ y, RdUH (A.R5 q₀ q₁ y) (A.R5 q₀ q₁ y) q3 qE

end AdversaryUAH

/-- **The witness lengths of the `n + 2` slots**: the two issuance proofs (`232`), then the `n`
redemption proofs (`559`). -/
def nsA (n : ℕ) : Fin (n + 2) → ℕ :=
  Fin.cases (motive := fun _ => ℕ) 232 (Fin.cases (motive := fun _ => ℕ) 232 fun _ => 559)

/-- Slot `0`, Client `false`'s issuance. -/
def s0 (n : ℕ) : Fin (n + 2) := ⟨0, by omega⟩

/-- Slot `1`, Client `true`'s issuance. -/
def s1 (n : ℕ) : Fin (n + 2) := ⟨1, by omega⟩

lemma mainP_nsA (n : ℕ) (i : Fin (n + 2)) : MainP (pw pIu (nsA n i)) := by
  refine Fin.cases ?_ (fun j => Fin.cases ?_ (fun k => ?_) j) i
  · exact mainP_pIu
  · exact mainP_pIu
  · exact mainP_pRu

lemma small_nsA (n : ℕ) (i : Fin (n + 2)) : SmallParams (pw pIu (nsA n i)) := by
  refine Fin.cases ?_ (fun j => Fin.cases ?_ (fun k => ?_) j) i
  · exact small_pIu
  · exact small_pIu
  · exact small_pRu

/-- The view of the shared game. -/
abbrev NVA (n : ℕ) := NView SecU (n + 2) pIu

/-- The tape of the shared game. -/
abbrev NTA (n : ℕ) := NTape pIu (nsA n) SecU

section GameAN

variable (A : AdversaryUAH) (n : ℕ)

/-- Client `c`'s issuance output, from the issuance slot's output. -/
def iA (s : SecU) (os : Fin (n + 2) → Option Out) (c : Bool) : PendingToken × Bytes :=
  issU A.um s c (os (bif c then s1 n else s0 n))

/-- **The challenger's rule** after the issuance: both tokens finalized, both redeemable in the
query's set, and the context rule. -/
def validA (s : SecU) (os : Fin (n + 2) → Option Out) (H : Hist) (q : Query) : Bool :=
  finBoth A.ad (iA A n s os false) (iA A n s os true) &&
    validR A.ad (iA A n s os false) (iA A n s os true) H q

/-- **The history after `k` queries**, each answered from its slot's output. -/
def histA (b : Bool) (s : SecU) (os : Fin (n + 2) → Option Out) (k : ℕ) : Hist :=
  histR (A.next (iA A n s os false).2 (iA A n s os true).2) (validA A n s os) refused
    (fun j q => redOutU A.um (ptQ A.ad b (iA A n s os false) (iA A n s os true) q)
      (os j.succ.succ)) k

/-- The statement and witness of query `j`. -/
def stA (b : Bool) (j : Fin n) (s : SecU) (os : Fin (n + 2) → Option Out) : Option SW :=
  bif validA A n s os (histA A n b s os j)
      (A.next (iA A n s os false).2 (iA A n s os true).2 (histA A n b s os j)) then
    redStmtU A.um (ptQ A.ad b (iA A n s os false) (iA A n s os true)
      (A.next (iA A n s os false).2 (iA A n s os true).2 (histA A n b s os j)))
  else none

/-- **The game of world `b`**: the two issuance proofs, then the `n` adaptive queries. -/
def gameAN (b : Bool) : NGame SecU (n + 2) :=
  ⟨Fin.cases (motive := fun _ => SecU → (Fin (n + 2) → Option Out) → Option SW)
    (fun s _ => some (issStmtU A.um s false))
    (Fin.cases (motive := fun _ => SecU → (Fin (n + 2) → Option Out) → Option SW)
      (fun s _ => some (issStmtU A.um s true)) fun j => stA A n b j)⟩

/-- What the guess gets besides the requests and the tables: the history, or `none`. -/
def keyA (b : Bool) (v : NVA n) : Option Hist :=
  bif finBoth A.ad (iA A n v.s v.os false) (iA A n v.s v.os true) then
    some (histA A n b v.s v.os n) else none

/-- **The final event of world `b`.** -/
def evAN (b : Bool) (v : NVA n) : Prop :=
  A.guess (iA A n v.s v.os false).2 (iA A n v.s v.os true).2 (keyA A n b v) v.u v.M v.T

/-- Its `H₅` read set. -/
def r5AN (b : Bool) (v : NVA n) : Finset (ZK.Sim.Bytes 37) :=
  A.R5 (iA A n v.s v.os false).2 (iA A n v.s v.os true).2 (keyA A n b v) v.u v.M v.T

/-- **The real game on `main` with all tables shared** in world `b`, `n` adaptive queries. -/
noncomputable def realAN (b : Bool) : ℝ :=
  hybN Hashes.shake pIu (nsA n) (gameAN A n b) 0 (evAN A n b)

/-- The game with all `n + 2` proofs simulated. -/
noncomputable def simAN (b : Bool) : ℝ :=
  hybN Hashes.shake pIu (nsA n) (gameAN A n b) (n + 2) (evAN A n b)

/-- The bad event of the joint hop, with all proofs simulated. -/
noncomputable def bstarAN (b : Bool) : ℝ :=
  hybN Hashes.shake pIu (nsA n) (gameAN A n b) (n + 2)
    (bstarN Hashes.shake (gameAN A n b) (fun i => pw pIu (nsA n i)) (r5AN A n b))

lemma ptQ_valid (b : Bool) (s : SecU) (os : Fin (n + 2) → Option Out) (q : Query) :
    ∀ y ∈ redStmtU A.um (ptQ A.ad b (iA A n s os false) (iA A n s os true) q),
      ValidZK CrtGen.tables pRu y :=
  redStmtU_valid A.um _ (tokD_wf A.ad.base (issU_wf A.um s false _) (issU_wf A.um s true _) _)
    (by simp [ptQ, ctxBytes])

lemma nvalidAN (b : Bool) : NValid (gameAN A n b) pIu (nsA n) where
  v i s os y hy := by
    revert y
    refine Fin.cases ?_ (fun j => Fin.cases ?_ (fun k => ?_) j) i
    · intro y hy
      cases hy
      exact issStmtU_valid A.um s false
    · intro y hy
      cases hy
      exact issStmtU_valid A.um s true
    · intro y hy
      have hy' : y ∈ stA A n b k s os := hy
      unfold stA at hy'
      cases h : validA A n s os (histA A n b s os k)
          (A.next (iA A n s os false).2 (iA A n s os true).2 (histA A n b s os k))
      · rw [h] at hy'; cases hy'
      · rw [h] at hy'; exact ptQ_valid A n b s os _ y hy'
  m := mainP_nsA n
  sm := small_nsA n

/-- A reader of the guess's input with consistent reads is a reader of the view. -/
lemma rdN_ofAN {X : Sort*} {f : Bytes → Bytes → Option Hist → USh → Tab2G pIu → H3T → X}
    {R : Bytes → Bytes → Option Hist → USh → Tab2G pIu → H3T → Finset (ZK.Sim.Bytes 37)}
    {q3 qE : ℕ} (h : ∀ q₀ q₁ y, RdUH (f q₀ q₁ y) (R q₀ q₁ y) q3 qE) (b : Bool) :
    RdN (fun v : NVA n => f (iA A n v.s v.os false).2 (iA A n v.s v.os true).2 (keyA A n b v)
        v.u v.M v.T)
      (fun v => R (iA A n v.s v.os false).2 (iA A n v.s v.os true).2 (keyA A n b v) v.u v.M v.T)
      q3 qE := by
  choose QE hQEc hQE using fun q₀ q₁ y => (h q₀ q₁ y).hE
  choose QT hQTc hQT using fun q₀ q₁ y => (h q₀ q₁ y).hT
  exact ⟨fun v G5 hk => (h _ _ _).h5 v.u v.M v.T G5 hk,
    ⟨fun v => QE (iA A n v.s v.os false).2 (iA A n v.s v.os true).2 (keyA A n b v) v.u v.M v.T,
      fun _ => hQEc _ _ _ _ _ _, fun v E hk => hQE _ _ _ v.u v.M v.T E hk⟩,
    ⟨fun v => QT (iA A n v.s v.os false).2 (iA A n v.s v.os true).2 (keyA A n b v) v.u v.M v.T,
      fun _ => hQTc _ _ _ _ _ _, fun v T' hk => hQT _ _ _ v.u v.M v.T T' hk⟩⟩

/-- **The joint hop in each world**, all `n + 2` proofs at once, linear in `n`, no
prefix-collision term. -/
theorem real_sim_AN {q3 qE : ℕ} (hC : A.ConsH q3 qE) (b : Bool) :
    |realAN A n b - simAN A n b| ≤
      2 * ((n + 2 : ℕ) : ℝ) * (εS (2 * q3 + (n + 2)) (2 * qE + 2 * (n + 2) * 4607) +
        Δ23N 9 (n + 2)) + bstarAN A n b :=
  main_sharedAll_leLin hashesWF_shake (nvalidAN A n b) (evAN A n b) (r5AN A n b)
    (rdN_ofAN A n (f := fun q₀ q₁ y u G2 T => A.guess q₀ q₁ y u G2 T)
      (R := fun q₀ q₁ y u G2 T => A.R5 q₀ q₁ y u G2 T) hC.g b)
    (rdN_ofAN A n (f := fun q₀ q₁ y u G2 T => A.R5 q₀ q₁ y u G2 T)
      (R := fun q₀ q₁ y u G2 T => A.R5 q₀ q₁ y u G2 T) hC.r b)

end GameAN


/-! ## With all proofs simulated: the history -/

section SimAN

variable {A : AdversaryUAH} {n : ℕ}

/-- The simulated view of world `b` on tape `x`. -/
noncomputable abbrev simVAN (b : Bool) (x : NTA n) : NVA n :=
  hybVN Hashes.shake pIu (nsA n) (gameAN A n b) (n + 2) x

lemma stA_congr (b : Bool) (j : Fin n) (s : SecU) (os os' : Fin (n + 2) → Option Out)
    (h : ∀ i : Fin (n + 2), i.val < j.val + 2 → os i = os' i) :
    stA A n b j s os = stA A n b j s os' := by
  have h0 : os (s0 n) = os' (s0 n) := h _ (by simp [s0])
  have h1 : os (s1 n) = os' (s1 n) := h _ (by simp [s1])
  have hi : ∀ c, iA A n s os c = iA A n s os' c := fun c => by
    cases c
    · exact congrArg _ h0
    · exact congrArg _ h1
  have hv : validA A n s os = validA A n s os' := by
    unfold validA; rw [hi false, hi true]
  have hH : histA A n b s os j = histA A n b s os' j := by
    unfold histA
    rw [hi false, hi true, hv]
    exact histR_congr_lt _ _ _ _ _ j fun i hi' => by
      funext q
      rw [h i.succ.succ (by simp; omega)]
  unfold stA
  rw [hH, hv, hi false, hi true]

/-- Slot `0` and slot `1` of the simulated view output simulated issuance proofs. -/
lemma os_simA_iss (b : Bool) (x : NTA n) :
    (simVAN (A := A) b x).os (s0 n) = some (simulate pIu (x.2.1 (s0 n)).2) ∧
      (simVAN (A := A) b x).os (s1 n) = some (simulate pIu (x.2.1 (s1 n)).2) :=
  ⟨os_simN Hashes.shake pIu (nsA n) (gameAN A n b) x (s0 n),
    os_simN Hashes.shake pIu (nsA n) (gameAN A n b) x (s1 n)⟩

/-- The redemption slots of the simulated view. -/
lemma os_simA_red (b : Bool) (x : NTA n) (j : Fin n) :
    (simVAN (A := A) b x).os j.succ.succ =
      (stA A n b j x.1 (simVAN (A := A) b x).os).map fun _ => simulate pRu (x.2.1 j.succ.succ).2 := by
  rw [os_simN Hashes.shake pIu (nsA n) (gameAN A n b) x j.succ.succ]
  congr 1
  show stA A n b j x.1 (maskO j.succ.succ (simVAN (A := A) b x).os) = _
  refine stA_congr b j x.1 _ _ fun i hi => ?_
  have hi' : i.val < j.val + 1 + 1 := by omega
  simp only [maskO, maskK, Fin.val_succ, hi', ↓reduceIte]

/-- Client `c`'s issuance output in the simulated view. -/
lemma iA_sim (b : Bool) (x : NTA n) (c : Bool) :
    iA A n x.1 (simVAN (A := A) b x).os c =
      issU A.um x.1 c (some (simulate pIu (bif c then (x.2.1 (s1 n)).2 else (x.2.1 (s0 n)).2))) := by
  obtain ⟨h0, h1⟩ := os_simA_iss (A := A) b x
  cases c
  · exact congrArg _ h0
  · exact congrArg _ h1

/-- A redemption output with a simulated proof is `redSim`. -/
lemma redOutU_simA (B : AdversaryUAH) (P : RedeemPt) (c : SimCoins pRu) :
    redOutU B.um P ((redStmtU B.um P).map fun _ => simulate pRu c) = redSim B.ad.base simRU c P := by
  unfold redOutU redStmtU redSim
  rw [show B.ad.base.ci = B.um.int.ci from rfl]
  cases findIssuer P.anchors (ucom P.tok.k B.um.int.ci P.tok.r) P.tok.s <;> rfl

/-- **The simulated history**: the answers are simulated redemptions. -/
lemma histA_sim (b : Bool) (x : NTA n) :
    ∀ k, histA A n b x.1 (simVAN (A := A) b x).os k =
      histR (A.next (iA A n x.1 (simVAN (A := A) b x).os false).2
          (iA A n x.1 (simVAN (A := A) b x).os true).2)
        (validA A n x.1 (simVAN (A := A) b x).os) refused
        (fun j q => redSim A.ad.base simRU (x.2.1 j.succ.succ).2
          (ptQ A.ad b (iA A n x.1 (simVAN (A := A) b x).os false)
            (iA A n x.1 (simVAN (A := A) b x).os true) q)) k := by
  refine histR_congr_run _ _ _ _ _ fun k hk hv => ?_
  set v := simVAN (A := A) b x
  show redOutU A.um _ (v.os (Fin.succ (Fin.succ ⟨k, hk⟩))) = _
  rw [os_simA_red b x ⟨k, hk⟩]
  unfold stA
  have hv' : validA A n x.1 v.os (histA A n b x.1 v.os k)
      (A.next (iA A n x.1 v.os false).2 (iA A n x.1 v.os true).2 (histA A n b x.1 v.os k)) =
      true := hv
  rw [hv']
  exact redOutU_simA A _ _

end SimAN


/-! ## The public view: a function of the commitments, the nullifier table and the rest -/

section Pub

variable (A : AdversaryUAH) (n : ℕ)

/-- The rest of the tape: the slots' coins, `H₃`, the shared `H₅` table and cipher, the raw `H₂³`
table. -/
abbrev RestAN := CoinsN pIu (nsA n) × H3T × USh × Tab2G pIu

/-- The redemption simulators' coins. -/
def csRA (z : RestAN n) (j : Fin n) : SimCoins pRu := (z.1 j.succ.succ).2

/-- The requests, from the commitments and the issuance simulators' coins. -/
noncomputable def qAN (t₀ t₁ : Bytes) (z : RestAN n) (c : Bool) : Bytes :=
  bif c then reqU t₁ (z.1 (s1 n)).2 else reqU t₀ (z.1 (s0 n)).2

/-- Both tokens finalize, from public values. -/
noncomputable def finAN (t₀ t₁ : Bytes) (z : RestAN n) : Bool :=
  finT A.ad.base (qAN n t₀ t₁ z false) (qAN n t₀ t₁ z true) t₀ t₁ false &&
    finT A.ad.base (qAN n t₀ t₁ z false) (qAN n t₀ t₁ z true) t₀ t₁ true

/-- **The simulated run** (`MoussakaUnbound.runT`) on the nullifier table `O`. -/
noncomputable def runAN (b : Bool) (t₀ t₁ : Bytes) (O : Bool → Coins ctxBytes → Bytes)
    (z : RestAN n) : Hist :=
  runT A.ad simRU b (qAN n t₀ t₁ z false) (qAN n t₀ t₁ z true) t₀ t₁ O (csRA n z)

/-- **The statement of a history entry**: an answer `Derive ‖ π` was proved for the query's set,
context and digest, with the answer's first 32 bytes as the nullifier. -/
def stOfAnsN (q : Query) (a : Except Error Bytes) : Option Statement :=
  match a with
  | .ok bs => some (stR ⟨q.anchors.keys, bs.take nfBytes, A.um.int.ci, List.ofFn q.ctxRed, q.cd⟩)
  | .error _ => none

/-- The statement of entry `j` of a history. -/
def stAtN (H : Hist) (j : ℕ) : Option Statement :=
  match H[j]? with
  | some e => stOfAnsN A e.1 e.2
  | none => none

/-- **The public statements of the `n + 2` slots**: the issuance statements from the
commitments, the redemption statements from the history. -/
def stPubA (t₀ t₁ : Bytes) (H : Hist) : Fin (n + 2) → Option Statement :=
  Fin.cases (motive := fun _ => Option Statement) (some (stI ⟨t₀, A.um.int.ci⟩))
    (Fin.cases (motive := fun _ => Option Statement) (some (stI ⟨t₁, A.um.int.ci⟩))
      fun j => stAtN A H j)

/-- **The programmings of the first `k` slots**, the first outermost. -/
noncomputable def compAN (st : Fin (n + 2) → Option Statement)
    (cs : (i : Fin (n + 2)) → SimCoins (pw pIu (nsA n i))) (u : USh) :
    ℕ → Tab2G pIu → Tab2G pIu
  | 0 => id
  | k + 1 => if h : k < n + 2 then
      compAN st cs u k ∘ pgP (pw pIu (nsA n ⟨k, h⟩)) (cs ⟨k, h⟩) (st ⟨k, h⟩) u
    else compAN st cs u k

/-- The history the statements are read from (none proved unless both tokens finalized). -/
noncomputable def hsAN (b : Bool) (t₀ t₁ : Bytes) (O : Bool → Coins ctxBytes → Bytes)
    (z : RestAN n) : Hist :=
  bif finAN A n t₀ t₁ z then runAN A n b t₀ t₁ O z else []

/-- **The `H₂³` table the guess sees**, from public values. -/
noncomputable def tabAN (b : Bool) (t₀ t₁ : Bytes) (O : Bool → Coins ctxBytes → Bytes)
    (z : RestAN n) : Tab2G pIu :=
  compAN n (stPubA A n t₀ t₁ (hsAN A n b t₀ t₁ O z)) (fun i => (z.1 i).2) z.2.2.1 (n + 2) z.2.2.2

/-- The guess's history input, from public values. -/
noncomputable def keyAN (b : Bool) (t₀ t₁ : Bytes) (O : Bool → Coins ctxBytes → Bytes)
    (z : RestAN n) : Option Hist :=
  bif finAN A n t₀ t₁ z then some (runAN A n b t₀ t₁ O z) else none

/-- **The simulated game's event** from the commitments, the nullifier table and the rest. -/
noncomputable def hvAN (b : Bool) (t₀ t₁ : Bytes) (O : Bool → Coins ctxBytes → Bytes)
    (z : RestAN n) : Prop :=
  A.guess (qAN n t₀ t₁ z false) (qAN n t₀ t₁ z true) (keyAN A n b t₀ t₁ O z) z.2.2.1
    (tabAN A n b t₀ t₁ O z) z.2.1

/-- Its `H₅` read set. -/
noncomputable def r5PubAN (b : Bool) (t₀ t₁ : Bytes) (O : Bool → Coins ctxBytes → Bytes)
    (z : RestAN n) : Finset (ZK.Sim.Bytes 37) :=
  A.R5 (qAN n t₀ t₁ z false) (qAN n t₀ t₁ z true) (keyAN A n b t₀ t₁ O z) z.2.2.1
    (tabAN A n b t₀ t₁ O z) z.2.1

end Pub

/-! ## With all proofs simulated: the view is the public view -/

section SimPub

variable {A : AdversaryUAH} {n : ℕ}

/-- With all redemption proofs simulated and both tokens finalized, the adaptive run with the
honest pending tokens is `runT` on the nullifier table of the keys (`viewAd_redSim`). -/
lemma interact_redSim (B : AdversaryAd) (b : Bool) (i₀ i₁ : PendingToken × Bytes)
    (cs : Fin n → SimCoins pRu)
    (h₀ : i₀.1.t = ucom i₀.1.k B.base.ci i₀.1.r) (h₁ : i₁.1.t = ucom i₁.1.k B.base.ci i₁.1.r)
    (hf : ∀ c, finT B.base i₀.2 i₁.2 i₀.1.t i₁.1.t c = true) :
    interact (B.next i₀.2 i₁.2) (validR B i₀ i₁) refused
        (List.ofFn fun j q => redSim B.base simRU (cs j) (ptQ B b i₀ i₁ q)) [] =
      runT B simRU b i₀.2 i₁.2 i₀.1.t i₁.1.t
        (fun c ctx => bif c then derive i₁.1.k (List.ofFn ctx) else derive i₀.1.k (List.ofFn ctx))
        cs := by
  have hcom (c : Bool) : ucom (bif c then i₁ else i₀).1.k B.base.ci (bif c then i₁ else i₀).1.r =
      bif c then i₁.1.t else i₀.1.t := by
    cases c
    · exact h₀.symm
    · exact h₁.symm
  have hv : validR B i₀ i₁ = validT B i₀.2 i₁.2 i₀.1.t i₁.1.t := by
    funext H q
    unfold validR validT redeemable okT
    rw [tokD_of_finT B i₀ i₁ false (hf false), tokD_of_finT B i₀ i₁ true (hf true)]
    simp only [hcom]
  unfold runT
  rw [hv]
  refine interact_congr_of _ _ _
    (fun q => okT B.base i₀.2 i₁.2 i₀.1.t i₁.1.t (who b q) q.anchors = true) _ _
    (fun j q hq => redSim_ptQ B simRU b i₀ i₁ h₀ h₁ hf q hq (cs j)) _ fun H' _ _ hval => ?_
  unfold validT at hval
  simp only [Bool.and_eq_true] at hval
  cases who b (B.next i₀.2 i₁.2 H')
  · exact hval.1.1
  · exact hval.1.2

/-- A refusing rule refuses every query. -/
lemma histR_refused {Q Y : Type*} (next : List (Q × Y) → Q) (valid : List (Q × Y) → Q → Bool)
    (refuse : Y) (f : Fin n → Q → Y) (hv : ∀ H q, valid H q = false) :
    ∀ m, ∀ e ∈ histR next valid refuse f m, e.2 = refuse
  | 0 => by simp [histR]
  | m + 1 => by
    intro e he
    by_cases hm : m < n
    · rw [histR_succ next valid refuse f hm] at he
      rcases List.mem_append.1 he with he | he
      · exact histR_refused next valid refuse f hv m e he
      · rw [List.mem_singleton] at he
        subst he
        simp [hv]
    · simp only [histR, hm, ↓reduceDIte] at he
      exact histR_refused next valid refuse f hv m e he

/-- The statement of an answered query is the statement of its proof. -/
lemma stOfAnsN_redOutU (B : AdversaryUAH) (b : Bool) (i₀ i₁ : PendingToken × Bytes) (q : Query)
    (o : Option Out) :
    stOfAnsN B q (redOutU B.um (ptQ B.ad b i₀ i₁ q) o) =
      (redStmtU B.um (ptQ B.ad b i₀ i₁ q)).map Prod.fst := by
  unfold redOutU redStmtU
  cases findIssuer (ptQ B.ad b i₀ i₁ q).anchors
    (ucom (ptQ B.ad b i₀ i₁ q).tok.k B.um.int.ci (ptQ B.ad b i₀ i₁ q).tok.r)
    (ptQ B.ad b i₀ i₁ q).tok.s with
  | none => rfl
  | some i =>
    show some _ = some _
    unfold xRU
    rw [List.take_left' (length_derive _ _)]
    rfl

/-- **The statement of query `j`** is the statement of entry `j` of the final history. -/
lemma stA_fst (b : Bool) (j : Fin n) (s : SecU) (os : Fin (n + 2) → Option Out) :
    (stA A n b j s os).map Prod.fst = stAtN A (histA A n b s os n) j := by
  have hg : (histA A n b s os n)[j.val]? = some
      (A.next (iA A n s os false).2 (iA A n s os true).2 (histA A n b s os j),
        if validA A n s os (histA A n b s os j)
            (A.next (iA A n s os false).2 (iA A n s os true).2 (histA A n b s os j)) then
          redOutU A.um (ptQ A.ad b (iA A n s os false) (iA A n s os true)
            (A.next (iA A n s os false).2 (iA A n s os true).2 (histA A n b s os j)))
            (os j.succ.succ)
        else refused) :=
    histR_get _ _ _ _ j.val j.2 n (by omega)
  unfold stAtN
  rw [hg]
  unfold stA
  cases hv : validA A n s os (histA A n b s os j)
      (A.next (iA A n s os false).2 (iA A n s os true).2 (histA A n b s os j))
  · rfl
  · simp only [Bool.cond_true, ↓reduceIte]
    exact (stOfAnsN_redOutU A b _ _ _ _).symm

/-- With a token not finalized, no entry has a statement. -/
lemma stAtN_none (b : Bool) (s : SecU) (os : Fin (n + 2) → Option Out)
    (hf : finBoth A.ad (iA A n s os false) (iA A n s os true) = false) (j : ℕ) :
    stAtN A (histA A n b s os n) j = none := by
  unfold stAtN
  rcases he : (histA A n b s os n)[j]? with _ | e
  · rfl
  · have hm := List.mem_of_getElem? he
    have h2 := histR_refused _ _ _ _ (fun H q => by unfold validA; rw [hf]; rfl) n e hm
    show stOfAnsN A e.1 e.2 = none
    rw [h2]
    rfl

lemma stAtN_nil (j : ℕ) : stAtN A [] j = none := rfl

end SimPub


/-! ## With all proofs simulated: the event is the public event -/

section SimMain

variable {A : AdversaryUAH} {n : ℕ}

/-- The commitments, the nullifier table and the rest of a tape. -/
abbrev tA (x : NTA n) (c : Bool) : Bytes := tUM A.um x.1 c

/-- The nullifier table of the tape's keys. -/
abbrev oA (x : NTA n) : Bool → Coins ctxBytes → Bytes := tabU (kOfU x.1 false) (kOfU x.1 true)

lemma yN_simA_red (b : Bool) (x : NTA n) (j : Fin n) :
    yN (gameAN A n b) j.succ.succ (simVAN (A := A) b x) =
      stA A n b j x.1 (simVAN (A := A) b x).os := by
  show stA A n b j x.1 (maskO j.succ.succ (simVAN (A := A) b x).os) = _
  refine stA_congr b j x.1 _ _ fun i hi => ?_
  have hi' : i.val < j.val + 1 + 1 := by omega
  simp only [maskO, maskK, Fin.val_succ, hi', ↓reduceIte]

lemma qAN_sim (b : Bool) (x : NTA n) (c : Bool) :
    (iA A n x.1 (simVAN (A := A) b x).os c).2 = qAN n (tA (A := A) x false) (tA (A := A) x true) x.2 c := by
  rw [iA_sim b x c]
  cases c <;> rfl

lemma finAN_sim (b : Bool) (x : NTA n) :
    finBoth A.ad (iA A n x.1 (simVAN (A := A) b x).os false)
        (iA A n x.1 (simVAN (A := A) b x).os true) =
      finAN A n (tA (A := A) x false) (tA (A := A) x true) x.2 := by
  rw [finBoth_eq, iA_sim b x false, iA_sim b x true]
  rfl

/-- **With both tokens finalized, the simulated history is the run `runAN`** on the nullifier table
of the keys. -/
lemma histA_sim_fin (b : Bool) (x : NTA n)
    (hf : finAN A n (tA (A := A) x false) (tA (A := A) x true) x.2 = true) :
    histA A n b x.1 (simVAN (A := A) b x).os n =
      runAN A n b (tA (A := A) x false) (tA (A := A) x true) (oA x) x.2 := by
  rw [← finAN_sim b x] at hf
  rw [histA_sim b x n]
  have hvA : validA A n x.1 (simVAN (A := A) b x).os =
      validR A.ad (iA A n x.1 (simVAN (A := A) b x).os false)
        (iA A n x.1 (simVAN (A := A) b x).os true) := by
    funext H q
    unfold validA
    rw [hf]
    rfl
  rw [hvA, ← interact_eq_histR]
  rw [finBoth_eq] at hf
  simp only [Bool.and_eq_true] at hf
  have hf' : ∀ c, finT A.ad.base (iA A n x.1 (simVAN (A := A) b x).os false).2
      (iA A n x.1 (simVAN (A := A) b x).os true).2
      (iA A n x.1 (simVAN (A := A) b x).os false).1.t
      (iA A n x.1 (simVAN (A := A) b x).os true).1.t c = true := fun c => by
    cases c
    · exact hf.1
    · exact hf.2
  refine (interact_redSim A.ad b _ _ (fun j => (x.2.1 j.succ.succ).2)
    (by rw [iA_sim b x false]; rfl) (by rw [iA_sim b x true]; rfl) hf').trans ?_
  rw [iA_sim b x false, iA_sim b x true]
  rfl

/-- A simulator's programming depends on the statement only. -/
lemma simF_pg_A (i : Fin (n + 2)) (c : SimCoins (pw pIu (nsA n i))) (u : USh) (y : Option SW) :
    (simF Hashes.shake pIu (nsA n) i c u y).pg = pgP (pw pIu (nsA n i)) c (y.map Prod.fst) u := by
  rcases y with _ | y <;> rfl

set_option maxRecDepth 8192 in
/-- The simulated view's `H₂³` table: the raw table programmed for the slots' statements. -/
lemma simVAN_M (b : Bool) (x : NTA n) :
    (simVAN (A := A) b x).M = compAN n
      (fun i => (yN (gameAN A n b) i (simVAN (A := A) b x)).map Prod.fst) (fun i => (x.2.1 i).2)
      x.2.2.2.1 (n + 2) x.2.2.2.2 := by
  show (runN _ x.1 _ x.2.2.2.2 (n + 2)).2 x.2.2.2.2 = _
  suffices h : ∀ k, k ≤ n + 2 → (runN (gameAN A n b) x.1
      (modeF Hashes.shake pIu (nsA n) (n + 2) x.2.1 x.2.2.1 x.2.2.2.1) x.2.2.2.2 k).2 =
      compAN n (fun i => (yN (gameAN A n b) i (simVAN (A := A) b x)).map Prod.fst)
        (fun i => (x.2.1 i).2) x.2.2.2.1 k by
    rw [h _ le_rfl]
  intro k hk
  induction k with
  | zero => rfl
  | succ k ih =>
    have hkn : k < n + 2 := by omega
    rw [runN_succ _ _ _ _ hkn, ih (by omega)]
    simp only [compAN, hkn, ↓reduceDIte]
    congr 1
    unfold sfN
    have hki : (⟨k, hkn⟩ : Fin (n + 2)).val < n + 2 := hkn
    simp only [modeF, hki, ↓reduceIte]
    rw [simF_pg_A]
    congr 2
    exact (yN_viewN _ _ _ _ _ _ _).symm

/-- **The slots' statements are the public statements.** -/
lemma stF_pub (b : Bool) (x : NTA n) :
    (fun i => (yN (gameAN A n b) i (simVAN (A := A) b x)).map Prod.fst) =
      stPubA A n (tA (A := A) x false) (tA (A := A) x true)
        (hsAN A n b (tA (A := A) x false) (tA (A := A) x true) (oA x) x.2) := by
  funext i
  refine Fin.cases ?_ (fun j => Fin.cases ?_ (fun k => ?_) j) i
  · rfl
  · rfl
  · rw [yN_simA_red b x k, stA_fst]
    show stAtN A _ k = stAtN A (hsAN A n b (tA (A := A) x false) (tA (A := A) x true) (oA x) x.2) k
    unfold hsAN
    cases hf : finAN A n (tA (A := A) x false) (tA (A := A) x true) x.2
    · rw [stAtN_none b x.1 _ ((finAN_sim b x).trans hf)]
      rfl
    · rw [histA_sim_fin b x hf]
      rfl

lemma keyA_sim (b : Bool) (x : NTA n) :
    keyA A n b (simVAN (A := A) b x) =
      keyAN A n b (tA (A := A) x false) (tA (A := A) x true) (oA x) x.2 := by
  unfold keyA keyAN
  rw [show (simVAN (A := A) b x).s = x.1 from rfl, finAN_sim b x]
  cases hf : finAN A n (tA (A := A) x false) (tA (A := A) x true) x.2
  · rfl
  · rw [histA_sim_fin b x hf]

lemma M_sim (b : Bool) (x : NTA n) :
    (simVAN (A := A) b x).M = tabAN A n b (tA (A := A) x false) (tA (A := A) x true) (oA x) x.2 := by
  rw [simVAN_M, stF_pub]
  rfl

/-- **With all proofs simulated, the final event is the public event `hvAN`**: a function of the
commitments, the nullifier table of the keys and the rest of the tape. -/
theorem simAN_iff (b : Bool) (x : NTA n) :
    evAN A n b (simVAN (A := A) b x) ↔
      hvAN A n b (tA (A := A) x false) (tA (A := A) x true) (oA x) x.2 := by
  unfold evAN hvAN
  rw [show (simVAN (A := A) b x).s = x.1 from rfl, qAN_sim b x false, qAN_sim b x true,
    keyA_sim b x, M_sim b x]
  rfl

/-- The same for the read set. -/
theorem r5_sim (b : Bool) (x : NTA n) :
    r5AN A n b (simVAN (A := A) b x) =
      r5PubAN A n b (tA (A := A) x false) (tA (A := A) x true) (oA x) x.2 := by
  unfold r5AN r5PubAN
  rw [show (simVAN (A := A) b x).s = x.1 from rfl, qAN_sim b x false, qAN_sim b x true,
    keyA_sim b x, M_sim b x]
  rfl

end SimMain


/-! ## The PRF hop and the swap -/

section HopsAN

variable (A : AdversaryUAH) (n : ℕ)

/-- **The reduction to the PRF** at the rest of the tape: the guess on the run with the
commitments and the nullifier table it is given (read adaptively, at the queried contexts). -/
noncomputable def redAN (b : Bool) (z : RestAN n)
    (y : Bytes × Bytes × (Bool → Coins ctxBytes → Bytes)) : Prop :=
  hvAN A n b y.1 y.2.1 y.2.2 z

/-- The game after the PRF hop. -/
noncomputable def idealAN (b : Bool) : ℝ :=
  pr ((PTape × Table) × RestAN n) (fun y => redAN A n b y.2 (prfIdeal A.ad.base.ci y.1))

lemma simAN_eq (b : Bool) :
    simAN A n b = pr (PTape × RestAN n) (fun y => redAN A n b y.2 (prfReal A.ad.base.ci y.1)) :=
  pr_congr fun x => simAN_iff b x

/-- **The PRF hop** (the PRF advantage with the commitments leaked). -/
theorem prf_hop_AN (b : Bool) {εprf : ℝ}
    (hprf : ∀ z, prfAdv A.ad.base.ci (redAN A n b z) ≤ εprf) :
    |simAN A n b - idealAN A n b| ≤ εprf := by
  rw [simAN_eq]
  exact abs_pr_prod_sub_le' _ _ fun z => hprf z

/-- **After the PRF hop the worlds coincide** (the swap of `pr_run_swap`: the guess may read the
simulators' coins and the tables). -/
theorem idealAN_eq : idealAN A n false = idealAN A n true := by
  let t : PTape → Bool → Bytes := fun p c =>
    ucom (List.ofFn (bif c then p.2 else p.1).1) A.ad.base.ci (List.ofFn (bif c then p.2 else p.1).2)
  let q : PTape × RestAN n → Bool → Bytes := fun z c => qAN n (t z.1 false) (t z.1 true) z.2 c
  have hv (z : PTape × RestAN n) (H : Hist) (qq : Query)
      (h : validT A.ad (q z false) (q z true) (t z.1 false) (t z.1 true) H qq = true) :
      ctxOk H qq = true := by
    unfold validT at h
    simp only [Bool.and_eq_true] at h
    exact h.2
  have key := pr_run_swap simRU A.ad.base (fun z => A.next (q z false) (q z true))
    (fun z => validT A.ad (q z false) (q z true) (t z.1 false) (t z.1 true)) hv
    (fun z => csRA n z.2)
    (fun z Hs => A.guess (q z false) (q z true)
      (bif finAN A n (t z.1 false) (t z.1 true) z.2 then some Hs else none) z.2.2.2.1
      (compAN n (stPubA A n (t z.1 false) (t z.1 true)
          (bif finAN A n (t z.1 false) (t z.1 true) z.2 then Hs else []))
        (fun i => (z.2.1 i).2) z.2.2.2.1 (n + 2) z.2.2.2.2) z.2.2.1)
  let e : Table × (PTape × RestAN n) ≃ (PTape × Table) × RestAN n :=
    { toFun := fun y => ((y.2.1, y.1), y.2.2)
      invFun := fun x => (x.1.2, (x.1.1, x.2))
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  unfold idealAN
  rw [← pr_equiv e, ← pr_equiv e]
  exact key

end HopsAN

end VoleMole.Privacy.MoussakaUnbound
