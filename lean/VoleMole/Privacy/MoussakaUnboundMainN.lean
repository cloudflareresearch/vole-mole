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

end VoleMole.Privacy.MoussakaUnbound
