import VoleMole.ZK.MainSharedNSim
import VoleMole.Privacy.MoussakaUnboundNCMainAll

/-!
# Unbound Moussaka U5(b) on `main` with `n` adaptive redemption queries, all tables shared

`anonymityNC_main_U_sharedAll` (`Privacy/MoussakaUnboundNCMainAll.lean`) is Theorem U5(b) on
`main` with **two** adaptive queries, all tables shared, and an explicit prefix-collision term
`collNH b` that is unbounded when one Client answers both queries. Here the same game has **`n`
adaptive queries**, and the joint hop is `ZK.Sim.main_sharedAll_leN` (`ZK/MainSharedN.lean`),
which has no prefix-collision term: a later real proof with the same prefix reads the replaced
proof's `H₃` column only at its own `ρ`.

## The game (`gameNN`, `realNN`)

The Moderator of `AdversaryUNCH` (`ctx_iss`, the keys, the adaptive queries `next`, a guess that
sees the history or `none`, the shared `H₅` table and cipher, the one `H₂³` table and `H₃`). Slot
`k` is query `k`: the history after the first `k` queries (`histK`, answered from the outputs) gives
the query `next H`, proved iff both tokens finalized and the query is valid (`stK`). The game is a
`ZK.Sim.NGame` with the `n` slots of `main`'s redemption layout (`pRu`, as `pw pIu 559`).

## The steps

1. The joint hop (`real_sim_NN`): `(2ⁿ − 1)·(εS(q₃ + n, q_E + 2n·4607) + Δ23N(9, n))` and
   `(2ⁿ − 1)·Pr_sim[bstarN]`.
2. With all proofs simulated the guess's input is a function of the refusal bit, the history
   `histTN` (a function of the keys and the simulators' coins: `histK_sim_true`) and the tables
   (`tabHN`: the raw `H₂³` table programmed for the history's statements).
3. The abort hop (`sim_hyb_NN`), the PRF hop (`prf_hop_NN`) and the swap (`idealNN_eq`) of
   `Privacy/MoussakaUnboundNC.lean`.
4. **The (PU) term is statistical** (`pr_candNN_le`): with both tokens finalized each simulated
   proof's witness prefix is the answering Client's opening, uniform and independent of the
   candidates, which the keys, the coins and the tables determine.

## The bound (`anonymityNC_main_U_sharedAllN`)

    |Pr[W₀] − Pr[W₁]| ≤ 2·(2ⁿ − 1)·(εS(q₃ + n, q_E + 2n·4607) + Δ23N(9, n))
        + 2·(2ⁿ − 1)·(n·noHitProb + 2n·(q₅ + 312n + 1)·2⁻¹²⁸ + n²·313·2⁻¹²⁸)
        + 2·(ψ false + ψ true) + 2·εprf

for any queries, in particular two redemptions by one Client with one statement.
-/

open Finset

-- (The coin types are large products: their `Fintype` instances exceed the default size.)
set_option synthInstance.maxSize 1024

set_option linter.unusedSectionVars false
set_option linter.constructorNameAsVariable false

namespace VoleMole.Privacy.MoussakaUnbound

open VoleMole.Spec VoleMole.Spec.MoussakaUnbound VoleMole.ZK.Sim VoleMole.Privacy.MainChain
open VoleMole.Verifier VoleMole.Verifier.Bridge
open VoleMole.Spec.Moussaka (NIZK AnchorSet Error ctxBytes proveSeedBytes rBytes nfBytes maxAnchors)
open VoleMole.Privacy.Moussaka (pf pgP)

-- `UCom` and `Derive` evaluate Keccak-p[800]; nothing below needs to unfold them.
attribute [local irreducible] ucom derive UOVKey.eval
attribute [local irreducible] simulate realRO progRO

/-! ## Adaptive histories as recursions -/

section Hist

variable {Q Y : Type*} (next : List (Q × Y) → Q) (valid : List (Q × Y) → Q → Bool) (refuse : Y)
  {n : ℕ}

/-- **The history after `k` steps of an adaptive interaction** with `n` oracles. -/
def histR (f : Fin n → Q → Y) : ℕ → List (Q × Y)
  | 0 => []
  | k + 1 => if h : k < n then histR f k ++ [(next (histR f k),
      if valid (histR f k) (next (histR f k)) then f ⟨k, h⟩ (next (histR f k)) else refuse)]
    else histR f k

theorem interact_append : ∀ (l₁ l₂ : List (Q → Y)) (H : List (Q × Y)),
    interact next valid refuse (l₁ ++ l₂) H =
      interact next valid refuse l₂ (interact next valid refuse l₁ H)
  | [], _, _ => rfl
  | _ :: l₁, l₂, _ => interact_append l₁ l₂ _

/-- **`interact` is the recursion `histR`.** -/
theorem interact_eq_histR (f : Fin n → Q → Y) :
    interact next valid refuse (List.ofFn f) [] = histR next valid refuse f n := by
  suffices h : ∀ k (hk : k ≤ n), interact next valid refuse
      (List.ofFn fun j : Fin k => f ⟨j, by omega⟩) [] = histR next valid refuse f k by
    have := h n le_rfl
    simpa using this
  intro k hk
  induction k with
  | zero => rfl
  | succ k ih =>
    have hkn : k < n := by omega
    rw [List.ofFn_succ', List.concat_eq_append, interact_append]
    simp only [Fin.val_castSucc]
    rw [ih (by omega)]
    simp only [histR, hkn, ↓reduceDIte, interact, Fin.val_last]

lemma histR_length (f : Fin n → Q → Y) : ∀ k, (histR next valid refuse f k).length = min k n
  | 0 => by simp [histR]
  | k + 1 => by
    unfold histR
    split
    · rw [List.length_append, histR_length f k]; simp; omega
    · rw [histR_length f k]; omega

end Hist

/-! ## The game -/

section GameN

variable (A : AdversaryUNCH) (PI : NIZK IssueInstance) (sk : Bool → Signer) (n : ℕ)

/-- **The history after the first `k` queries**, each answered from the slot's output. -/
def histK (b : Bool) (s : SecN) (os : Fin n → Option Out) : ℕ → Hist
  | 0 => []
  | k + 1 => if h : k < n then histK b s os k ++ [(A.next (histK b s os k),
      ansN A.unc PI sk b s (histK b s os k) (A.next (histK b s os k)) (os ⟨k, h⟩))]
    else histK b s os k

/-- **The statement and witness of the query after history `H`**: proved iff both tokens
finalized and the query is valid. -/
def stK (b : Bool) (s : SecN) (H : Hist) : Option SW :=
  bif gN A.unc PI sk s && validNC A.unc.nc PI sk s.1 s.2 H (A.next H) then
    redStmtU A.unc.um (ptNC A.unc.nc PI sk b s.1 s.2 (A.next H)) else none

/-- **The game of world `b`** with `n` adaptive queries. -/
def gameNN (b : Bool) : NGame SecN n := ⟨fun j s os => stK A PI sk b s (histK A PI sk n b s os j)⟩

/-- The redemption slots' witness lengths. -/
abbrev nsU : Fin n → ℕ := fun _ => 559

/-- The view of the shared game. -/
abbrev NVU := NView SecN n pIu

/-- The tape of the shared game. -/
abbrev NTU := NTape pIu (nsU n) SecN

/-- What the guess gets besides the tables: the history, or `none`. -/
def keyNN (b : Bool) (v : NVU n) : Option Hist :=
  bif gN A.unc PI sk v.s then some (histK A PI sk n b v.s v.os n) else none

/-- **The final event of world `b`.** -/
def evNN (b : Bool) (v : NVU n) : Prop := A.guess (keyNN A PI sk n b v) v.u v.M v.T

/-- Its `H₅` read set. -/
def r5NN (b : Bool) (v : NVU n) : Finset (ZK.Sim.Bytes 37) :=
  A.R5 (keyNN A PI sk n b v) v.u v.M v.T

/-- **The real game on `main` with all tables shared** in world `b`, `n` adaptive queries. -/
noncomputable def realNN (b : Bool) : ℝ :=
  hybN Hashes.shake pIu (nsU n) (gameNN A PI sk n b) 0 (evNN A PI sk n b)

/-- The game with all `n` redemption proofs simulated. -/
noncomputable def simNN (b : Bool) : ℝ :=
  hybN Hashes.shake pIu (nsU n) (gameNN A PI sk n b) n (evNN A PI sk n b)

/-- The bad event of the joint hop, with all proofs simulated. -/
noncomputable def bstarNN (b : Bool) : ℝ :=
  hybN Hashes.shake pIu (nsU n) (gameNN A PI sk n b) n
    (bstarN Hashes.shake (gameNN A PI sk n b) (fun i => pw pIu (nsU n i)) (r5NN A PI sk n b))

lemma nvalidNN (hsk : ∀ c, (sk c).Correct (A.pk c)) (b : Bool) :
    NValid (gameNN A PI sk n b) pIu (nsU n) where
  v i s os y hy := by
    have hy' : y ∈ stK A PI sk b s (histK A PI sk n b s os i) := hy
    unfold stK at hy'
    cases h : (gN A.unc PI sk s && validNC A.unc.nc PI sk s.1 s.2 (histK A PI sk n b s os i)
      (A.next (histK A PI sk n b s os i)))
    · rw [h] at hy'; cases hy'
    · rw [h] at hy'; exact redStmtNU_valid A.unc PI sk hsk b s _ y hy'
  m _ := mainP_pRu
  sm _ := small_pRu

/-- A reader of the guess's input with consistent reads is a reader of the view. -/
lemma rdN_ofNN {X : Sort*} {f : Option Hist → USh → Tab2G pIu → H3T → X}
    {R : Option Hist → USh → Tab2G pIu → H3T → Finset (ZK.Sim.Bytes 37)} {q3 qE : ℕ}
    (h : ∀ y, RdUH (f y) (R y) q3 qE) (b : Bool) :
    RdN (fun v : NVU n => f (keyNN A PI sk n b v) v.u v.M v.T)
      (fun v => R (keyNN A PI sk n b v) v.u v.M v.T) q3 qE := by
  choose QE hQEc hQE using fun y => (h y).hE
  choose QT hQTc hQT using fun y => (h y).hT
  exact ⟨fun v G5 hk => (h _).h5 v.u v.M v.T G5 hk,
    ⟨fun v => QE (keyNN A PI sk n b v) v.u v.M v.T, fun _ => hQEc _ _ _ _,
      fun v E hk => hQE _ v.u v.M v.T E hk⟩,
    ⟨fun v => QT (keyNN A PI sk n b v) v.u v.M v.T, fun _ => hQTc _ _ _ _,
      fun v T' hk => hQT _ v.u v.M v.T T' hk⟩⟩

/-- **The joint hop in each world**, all `n` redemptions at once, all tables shared, no
prefix-collision term. -/
theorem real_sim_NN (hsk : ∀ c, (sk c).Correct (A.pk c)) {q3 qE : ℕ} (hC : A.ConsH q3 qE)
    (b : Bool) :
    |realNN A PI sk n b - simNN A PI sk n b| ≤
      (2 ^ n - 1) * (εS (q3 + n) (qE + 2 * n * 4607) + Δ23N 9 n) +
        (2 ^ n - 1) * bstarNN A PI sk n b :=
  main_sharedAll_leN hashesWF_shake (nvalidNN A PI sk n hsk b) (evNN A PI sk n b)
    (r5NN A PI sk n b)
    (rdN_ofNN A PI sk n (f := fun y u G2 T => A.guess y u G2 T)
      (R := fun y u G2 T => A.R5 y u G2 T) hC.g b)
    (rdN_ofNN A PI sk n (f := fun y u G2 T => A.R5 y u G2 T)
      (R := fun y u G2 T => A.R5 y u G2 T) hC.r b)

end GameN

/-! ## The histories of a run -/

section HistK

variable {A : AdversaryUNCH} {PI : NIZK IssueInstance} {sk : Bool → Signer} {n : ℕ}

lemma histK_succ (b : Bool) (s : SecN) (os : Fin n → Option Out) {k : ℕ} (h : k < n) :
    histK A PI sk n b s os (k + 1) = histK A PI sk n b s os k ++ [(A.next (histK A PI sk n b s os k),
      ansN A.unc PI sk b s (histK A PI sk n b s os k) (A.next (histK A PI sk n b s os k))
        (os ⟨k, h⟩))] := by
  simp only [histK, h, ↓reduceDIte]

/-- The history after `k` queries reads only the first `k` outputs. -/
lemma histK_congr (b : Bool) (s : SecN) (os os' : Fin n → Option Out) :
    ∀ k, (∀ i : Fin n, i.val < k → os i = os' i) →
      histK A PI sk n b s os k = histK A PI sk n b s os' k
  | 0, _ => rfl
  | k + 1, h => by
    by_cases hk : k < n
    · rw [histK_succ b s os hk, histK_succ b s os' hk,
        histK_congr b s os os' k fun i hi => h i (by omega), h ⟨k, hk⟩ (by simp)]
    · simp only [histK, hk, ↓reduceDIte]
      exact histK_congr b s os os' k fun i hi => h i (by omega)

lemma histK_length (b : Bool) (s : SecN) (os : Fin n → Option Out) :
    ∀ k, (histK A PI sk n b s os k).length = min k n
  | 0 => by simp [histK]
  | k + 1 => by
    unfold histK
    split
    · rw [List.length_append, histK_length b s os k]; simp; omega
    · rw [histK_length b s os k]; omega

/-- **Entry `k` of a later history** is query `k` and its answer. -/
lemma histK_get (b : Bool) (s : SecN) (os : Fin n → Option Out) (k : ℕ) (hk : k < n) :
    ∀ m, k + 1 ≤ m → (histK A PI sk n b s os m)[k]? = some (A.next (histK A PI sk n b s os k),
      ansN A.unc PI sk b s (histK A PI sk n b s os k) (A.next (histK A PI sk n b s os k))
        (os ⟨k, hk⟩))
  | 0, h => absurd h (by omega)
  | m + 1, h => by
    rcases Nat.eq_or_lt_of_le h with h' | h'
    · have hm : m = k := by omega
      subst hm
      have hl : (histK A PI sk n b s os m).length = m := by rw [histK_length]; omega
      rw [histK_succ b s os hk, List.getElem?_append_right (by omega), hl, Nat.sub_self]
      rfl
    · have ih := histK_get b s os k hk m (by omega)
      by_cases hm : m < n
      · rw [histK_succ b s os hm, List.getElem?_append_left (by rw [histK_length]; omega)]
        exact ih
      · simp only [histK, hm, ↓reduceDIte]
        exact ih

end HistK

/-! ## With all proofs simulated -/

section SimN

variable {A : AdversaryUNCH} {PI : NIZK IssueInstance} {sk : Bool → Signer} {n : ℕ}

/-- The simulators' coins of a tape. -/
def csN (x : NTU n) : Fin n → SimCoins pRu := fun j => (x.2.1 j).2

/-- The simulated view of world `b` on tape `x`. -/
noncomputable abbrev simVN (b : Bool) (x : NTU n) : NVU n :=
  hybVN Hashes.shake pIu (nsU n) (gameNN A PI sk n b) n x

lemma yN_simNN (b : Bool) (x : NTU n) (i : Fin n) :
    yN (gameNN A PI sk n b) i (simVN (A := A) (PI := PI) (sk := sk) b x) =
      stK A PI sk b x.1 (histK A PI sk n b x.1 (simVN (A := A) (PI := PI) (sk := sk) b x).os i) := by
  show stK A PI sk b x.1 (histK A PI sk n b x.1
    (maskO i (simVN (A := A) (PI := PI) (sk := sk) b x).os) i) = _
  rw [histK_congr b x.1 (maskO i (simVN (A := A) (PI := PI) (sk := sk) b x).os)
    (simVN (A := A) (PI := PI) (sk := sk) b x).os i fun j hj => by simp [maskO, maskK, hj]]

lemma os_simNN (b : Bool) (x : NTU n) (i : Fin n) :
    (simVN (A := A) (PI := PI) (sk := sk) b x).os i =
      (stK A PI sk b x.1 (histK A PI sk n b x.1 (simVN (A := A) (PI := PI) (sk := sk) b x).os i)).map
        fun _ => simulate pRu (csN x i) := by
  rw [os_simN, yN_simNN]
  rfl

/-- The simulators' programming is `pgP`. -/
lemma simF_pg_eq (i : Fin n) (c : SimCoins pRu) (u : USh) (y : Option SW) :
    (simF Hashes.shake pIu (nsU n) i c u y).pg = pgP pRu c (y.map Prod.fst) u := by
  rcases y with _ | y <;> rfl

/-- **The `H₂³` table the guess sees after a history**: the raw table programmed by the `n`
simulations for the statements of the history's entries, the first outermost. -/
noncomputable def compN (H : Hist) (cs : Fin n → SimCoins pRu) (u : USh) :
    ℕ → Tab2G pIu → Tab2G pIu
  | 0 => id
  | k + 1 => if h : k < n then compN H cs u k ∘ pgP pRu (cs ⟨k, h⟩) (stAt A H k) u
    else compN H cs u k

/-- The table after the whole history. -/
noncomputable def tabHN (H : Hist) (cs : Fin n → SimCoins pRu) (u : USh) (G2 : Tab2G pIu) :
    Tab2G pIu :=
  compN (A := A) H cs u n G2

lemma stK_none (b : Bool) (s : SecN) (hg : gN A.unc PI sk s = false) (H : Hist) :
    stK A PI sk b s H = none := by
  unfold stK; rw [hg]; rfl

set_option maxRecDepth 8192 in
/-- **With a token refused**, nothing is proved: the guess sees `none` and the raw table. -/
lemma simVN_false (b : Bool) (x : NTU n) (hg : gN A.unc PI sk x.1 = false) :
    keyNN A PI sk n b (simVN (A := A) (PI := PI) (sk := sk) b x) = none ∧
      (simVN (A := A) (PI := PI) (sk := sk) b x).M = x.2.2.2.2 := by
  constructor
  · unfold keyNN
    rw [show (simVN (A := A) (PI := PI) (sk := sk) b x).s = x.1 from rfl, hg]
    rfl
  show (runN _ x.1 _ x.2.2.2.2 n).2 x.2.2.2.2 = x.2.2.2.2
  suffices h : ∀ k, (runN (gameNN A PI sk n b) x.1
      (modeF Hashes.shake pIu (nsU n) n x.2.1 x.2.2.1 x.2.2.2.1) x.2.2.2.2 k).2 = id by
    rw [h]; rfl
  intro k
  induction k with
  | zero => rfl
  | succ k ih =>
    by_cases hk : k < n
    · rw [runN_succ _ _ _ _ hk, ih]
      unfold sfN stN
      have hki : (⟨k, hk⟩ : Fin n).val < n := hk
      simp only [modeF, hki, ↓reduceIte]
      show id ∘ (simF Hashes.shake pIu (nsU n) ⟨k, hk⟩ _ x.2.2.2.1
        (stK A PI sk b x.1 _)).pg = id
      rw [stK_none b x.1 hg]
      rfl
    · simp only [runN, hk, ↓reduceDIte]
      exact ih

end SimN

section SimTrue

variable {A : AdversaryUNCH} {PI : NIZK IssueInstance} {sk : Bool → Signer} {n : ℕ}

variable (A n) in
/-- **The history with both tokens finalized and all proofs simulated**, from the keys and the
simulators' coins (the run of `hNC`). -/
noncomputable def histTR (b : Bool) (k : KTape) (cs : Fin n → SimCoins pRu) : ℕ → Hist :=
  histR A.next (fun H q => ctxOk H q) refused
    (fun j q => ySim A.unc.nc.base simRU b (keyTable k) q (cs j))

variable (A n) in
/-- The adaptive run of the `n` simulated queries in world `b` on a nullifier table `O`. -/
noncomputable def runHN (b : Bool) (O : Bool → Coins ctxBytes → Bytes)
    (cs : Fin n → SimCoins pRu) : Hist :=
  interact A.next (fun H q => ctxOk H q) refused
    (List.ofFn fun j q => ySim A.unc.nc.base simRU b O q (cs j)) []

lemma runHN_eq (b : Bool) (k : KTape) (cs : Fin n → SimCoins pRu) :
    runHN A n b (keyTable k) cs = histTR A n b k cs n :=
  interact_eq_histR _ _ _ _

set_option maxRecDepth 8192 in
/-- **With both tokens finalized, the simulated history is `histTR`.** -/
lemma histK_sim_true (hsk : ∀ c, (sk c).Correct (A.pk c)) (hK : Contains A.unc.nc) (b : Bool)
    (x : NTU n) (hg : gN A.unc PI sk x.1 = true) :
    ∀ k, k ≤ n → histK A PI sk n b x.1 (simVN (A := A) (PI := PI) (sk := sk) b x).os k =
      histTR A n b (x.1.1.1, x.1.2.1) (csN x) k
  | 0, _ => rfl
  | k + 1, hk => by
    have hkn : k < n := by omega
    have ih := histK_sim_true hsk hK b x hg k (by omega)
    rw [histK_succ b x.1 _ hkn, os_simNN b x ⟨k, hkn⟩]
    simp only [ih]
    set H := histTR A n b (x.1.1.1, x.1.2.1) (csN x) k
    have e1 : ansN A.unc PI sk b x.1 H (A.next H)
        ((stK A PI sk b x.1 H).map fun _ => simulate pRu (csN x ⟨k, hkn⟩)) =
        if validNC A.unc.nc PI sk x.1.1 x.1.2 H (A.next H) then
          redSim A.unc.nc.base simRU (csN x ⟨k, hkn⟩) (ptNC A.unc.nc PI sk b x.1.1 x.1.2 (A.next H))
        else refused :=
      ansN_sim A.unc PI sk b x.1 H (A.next H) _ hg
    have e2 : validNC A.unc.nc PI sk x.1.1 x.1.2 H (A.next H) = ctxOk H (A.next H) :=
      validNC_good hsk hK hg H
    have e3 : redSim A.unc.nc.base simRU (csN x ⟨k, hkn⟩)
        (ptNC A.unc.nc PI sk b x.1.1 x.1.2 (A.next H)) =
        ySim A.unc.nc.base simRU b (keyTable (x.1.1.1, x.1.2.1)) (A.next H) (csN x ⟨k, hkn⟩) :=
      redSim_good hsk hK hg b H _
    rw [e1, e2, e3]
    simp only [histTR, histR, hkn, ↓reduceDIte]
    rfl

set_option maxRecDepth 8192 in
/-- **With both tokens finalized, the simulated view's `H₂³` table is `tabHN` of the history.** -/
lemma simVN_M_true (b : Bool) (x : NTU n) (hg : gN A.unc PI sk x.1 = true) :
    (simVN (A := A) (PI := PI) (sk := sk) b x).M =
      tabHN (A := A) (histK A PI sk n b x.1 (simVN (A := A) (PI := PI) (sk := sk) b x).os n)
        (csN x) x.2.2.2.1 x.2.2.2.2 := by
  set v := simVN (A := A) (PI := PI) (sk := sk) b x with hv
  show (runN _ x.1 _ x.2.2.2.2 n).2 x.2.2.2.2 = compN (A := A) _ (csN x) x.2.2.2.1 n x.2.2.2.2
  suffices h : ∀ k, k ≤ n → (runN (gameNN A PI sk n b) x.1
      (modeF Hashes.shake pIu (nsU n) n x.2.1 x.2.2.1 x.2.2.2.1) x.2.2.2.2 k).2 =
      compN (A := A) (histK A PI sk n b x.1 v.os n) (csN x) x.2.2.2.1 k by
    rw [h n le_rfl]
  intro k hk
  induction k with
  | zero => rfl
  | succ k ih =>
    have hkn : k < n := by omega
    rw [runN_succ _ _ _ _ hkn, ih (by omega)]
    simp only [compN, hkn, ↓reduceDIte]
    congr 1
    unfold sfN
    have hki : (⟨k, hkn⟩ : Fin n).val < n := hkn
    simp only [modeF, hki, ↓reduceIte]
    refine (simF_pg_eq (n := n) _ _ _ _).trans ?_
    congr 1
    have hy : stN (gameNN A PI sk n b) x.1
        (modeF Hashes.shake pIu (nsU n) n x.2.1 x.2.2.1 x.2.2.2.1) x.2.2.2.2 ⟨k, hkn⟩ =
        stK A PI sk b x.1 (histK A PI sk n b x.1 v.os k) := by
      rw [← yN_viewN]
      exact yN_simNN b x ⟨k, hkn⟩
    rw [hy]
    unfold stAt
    rw [histK_get b x.1 v.os k hkn n (by omega)]
    exact σ_map_fst b x.1 hg _ _ _

/-- **The simulated game's event** from the refusal bit `g`, the history, the simulators' coins,
the raw tables and `H₃`. -/
noncomputable def hvNN (g : Bool) (H : Hist) (cs : Fin n → SimCoins pRu) (u : USh)
    (G2 : Tab2G pIu) (T : H3T) : Prop :=
  A.guess (bif g then some H else none) u (bif g then tabHN (A := A) H cs u G2 else G2) T

/-- **With all proofs simulated, the final event is `hvNN`** at the refusal bit, the history
`histTR` (a function of the keys and the simulators' coins), the coins and the raw tables. -/
theorem simNN_iff (hsk : ∀ c, (sk c).Correct (A.pk c)) (hK : Contains A.unc.nc) (b : Bool)
    (x : NTU n) :
    evNN A PI sk n b (simVN (A := A) (PI := PI) (sk := sk) b x) ↔
      hvNN (A := A) (gN A.unc PI sk x.1) (histTR A n b (x.1.1.1, x.1.2.1) (csN x) n) (csN x)
        x.2.2.2.1 x.2.2.2.2 x.2.2.1 := by
  unfold evNN hvNN
  cases hg : gN A.unc PI sk x.1
  · obtain ⟨h1, h2⟩ := simVN_false (A := A) (PI := PI) (sk := sk) b x hg
    rw [h1, h2]; rfl
  · have h1 : keyNN A PI sk n b (simVN (A := A) (PI := PI) (sk := sk) b x) =
        some (histTR A n b (x.1.1.1, x.1.2.1) (csN x) n) := by
      unfold keyNN
      rw [show (simVN (A := A) (PI := PI) (sk := sk) b x).s = x.1 from rfl, hg,
        histK_sim_true hsk hK b x hg n le_rfl]
      rfl
    rw [h1, simVN_M_true b x hg, histK_sim_true hsk hK b x hg n le_rfl]
    rfl

end SimTrue

/-! ## The abort hop, the PRF hop and the swap -/

section HopsN

variable (A : AdversaryUNCH) (PI : NIZK IssueInstance) (sk : Bool → Signer) (n : ℕ)

lemma simNN_eq (hsk : ∀ c, (sk c).Correct (A.pk c)) (hK : Contains A.unc.nc) (b : Bool) :
    simNN A PI sk n b = pr (NTU n) (fun x =>
      hvNN (A := A) (gN A.unc PI sk x.1) (histTR A n b (x.1.1.1, x.1.2.1) (csN x) n) (csN x)
        x.2.2.2.1 x.2.2.2.2 x.2.2.1) :=
  pr_congr fun x => simNN_iff hsk hK b x

/-- The hybrid: both issuances counted as successful. -/
noncomputable def hybNN (b : Bool) : ℝ :=
  pr (NTU n) (fun x => hvNN (A := A) true (histTR A n b (x.1.1.1, x.1.2.1) (csN x) n) (csN x)
    x.2.2.2.1 x.2.2.2.2 x.2.2.1)

/-- **The abort hop**: replacing the refusal bit by `true` costs `ψ false + ψ true`. -/
theorem sim_hyb_NN (hsk : ∀ c, (sk c).Correct (A.pk c)) (hK : Contains A.unc.nc) (b : Bool) :
    |simNN A PI sk n b - hybNN A n b| ≤ psi A.unc.nc PI sk false + psi A.unc.nc PI sk true := by
  rw [simNN_eq A PI sk n hsk hK b]
  have hb := abs_pr_sub_le_of_agree
    (fun x : NTU n => hvNN (A := A) (gN A.unc PI sk x.1)
      (histTR A n b (x.1.1.1, x.1.2.1) (csN x) n) (csN x) x.2.2.2.1 x.2.2.2.2 x.2.2.1)
    (fun x => hvNN (A := A) true (histTR A n b (x.1.1.1, x.1.2.1) (csN x) n) (csN x)
      x.2.2.2.1 x.2.2.2.2 x.2.2.1)
    (fun x => failNC A.unc.nc PI sk false x.1.1 = true ∨ failNC A.unc.nc PI sk true x.1.2 = true)
    fun x hx => by
      simp only [not_or, Bool.not_eq_true] at hx
      have hg : gN A.unc PI sk x.1 = true := by
        unfold gN
        rw [tokNC_isSome A.unc.nc PI sk hsk, tokNC_isSome A.unc.nc PI sk hsk, hx.1, hx.2]
        rfl
      rw [hg]
  refine hb.trans ((pr_or_le _ _).trans (le_of_eq ?_))
  have m0 : pr (NTU n) (fun x => failNC A.unc.nc PI sk false x.1.1 = true) =
      psi A.unc.nc PI sk false := by
    rw [pr_prod_fst (fun s : SecN => failNC A.unc.nc PI sk false s.1 = true),
      pr_prod_fst (fun x : IssT => failNC A.unc.nc PI sk false x = true)]
    rfl
  have m1 : pr (NTU n) (fun x => failNC A.unc.nc PI sk true x.1.2 = true) =
      psi A.unc.nc PI sk true := by
    rw [pr_prod_fst (fun s : SecN => failNC A.unc.nc PI sk true s.2 = true),
      pr_prod_snd (fun x : IssT => failNC A.unc.nc PI sk true x = true)]
    rfl
  rw [m0, m1]

/-- The rest of the tape: the openings and issuance seeds, the coins, `H₃`, the shared tables. -/
abbrev RestN := ((Coins rBytes × Coins proveSeedBytes) × (Coins rBytes × Coins proveSeedBytes)) ×
  (CoinsN pIu (nsU n) × H3T × USh × Tab2G pIu)

/-- Split the tape into the keys and the rest. -/
def splitN : NTU n ≃ KTape × RestN n where
  toFun x := ((x.1.1.1, x.1.2.1), (((x.1.1.2.1, x.1.1.2.2), (x.1.2.2.1, x.1.2.2.2)), x.2))
  invFun y := (((y.1.1, y.2.1.1.1, y.2.1.1.2), (y.1.2, y.2.1.2.1, y.2.1.2.2)), y.2.2)
  left_inv _ := rfl
  right_inv _ := rfl

/-- The simulators' coins of the rest of the tape. -/
def csRN (z : RestN n) : Fin n → SimCoins pRu := fun j => (z.2.1 j).2

/-- **The reduction to the PRF** at the rest of the tape: the guess on the run with the table it is
given. -/
noncomputable def redNN (b : Bool) (z : RestN n) (O : Bool → Coins ctxBytes → Bytes) : Prop :=
  hvNN (A := A) true (runHN A n b O (csRN n z)) (csRN n z) z.2.2.2.1 z.2.2.2.2 z.2.2.1

/-- The game after the PRF hop. -/
noncomputable def idealNN (b : Bool) : ℝ :=
  pr (Table × RestN n) (fun y => redNN A n b y.2 (tbl y.1))

/-- **The PRF hop.** -/
theorem prf_hop_NN (b : Bool) {εprf : ℝ} (hprf : ∀ z, prfAdvNC (redNN A n b z) ≤ εprf) :
    |hybNN A n b - idealNN A n b| ≤ εprf := by
  have e : hybNN A n b = pr (KTape × RestN n) (fun y => redNN A n b y.2 (keyTable y.1)) := by
    unfold hybNN
    rw [← pr_equiv (splitN n).symm]
    refine pr_congr fun y => ?_
    show hvNN (A := A) true (histTR A n b y.1 (csRN n y.2) n) _ _ _ _ ↔
      hvNN (A := A) true (runHN A n b (keyTable y.1) (csRN n y.2)) _ _ _ _
    rw [runHN_eq]
    exact Iff.rfl
  rw [e]
  exact abs_pr_prod_sub_le' _ _ fun z => hprf z

/-- **After the PRF hop the worlds coincide** (the swap of `pr_run_swap`). -/
theorem idealNN_eq : idealNN A n false = idealNN A n true :=
  pr_run_swap simRU A.unc.nc.base (fun _ => A.next) (fun _ H q => ctxOk H q) (fun _ _ _ h => h)
    (fun z : RestN n => csRN n z)
    (fun z H => hvNN (A := A) true H (csRN n z) z.2.2.2.1 z.2.2.2.2 z.2.2.1)

end HopsN

end VoleMole.Privacy.MoussakaUnbound
