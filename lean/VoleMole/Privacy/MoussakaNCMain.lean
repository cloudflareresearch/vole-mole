import VoleMole.Privacy.MoussakaMainSharedAll
import VoleMole.Privacy.MoussakaNC

/-!
# Moussaka issuer hiding against a non-colluding Moderator on `main` (Theorem 4(b'))

`anonymityNC` (`Privacy/MoussakaNC.lean`) is Theorem 4(b') with the per-proof zero-knowledge
hypothesis, which on `main` no efficient simulator satisfies (`lean/docs/zk.md` Prop. 4.1). Here
the same game is run on `main`: the redemption proofs are the executable prover with `main`'s
layout (no label rows), all tables shared as in `Privacy/MoussakaMainSharedAll.lean` (one `H₃`,
one `H₂³` table, one `H₅` table, one cipher), and the joint hop `ZK.Sim.main_sharedAll_le`
replaces both redemption proofs at once. Its (PU) term is **statistical**: the Moderator sees no
issuance, so the view depends on the Clients' openings only through the refusal bit.

## The honest Anchor of `main` (`respN`, `tokN`, `goodN`)

`Privacy/MoussakaNC.lean`'s Anchor checks the label-row request length (`issueResponseLR`). Here
it is `Spec.Moussaka.issueResponse`, `main`'s Anchor (`issueRequestBytes = 45 + 7272`), with the
same lemmas: an honest issuance gives the Client's token iff the Anchor accepts and
`derive_preimage` succeeds (`tokN_issReal`); unless `derive_preimage` fails, success is
"accepted, and the issuer's key is found in both sets" (`goodN_eq_of_derive`). The issuance proof
system `PI` stays abstract: the issuance proofs are never shown, and they are neither simulated
nor run on the game's tables (as in `anonymityNC`).

## The game (`realNCM`)

Four slots of a `MainChain.Game` on the shared tables: the first two prove nothing, the third and
fourth are the left and right redemptions of world `b` (Client `b ^^ side`'s token), proved iff
the refusal bit `gNC` (both tokens finalized and each redeemable at its index in both sets) holds.
The secret is the two Clients' issuance tapes `(nf, r, ρ_iss)`. The Moderator's guess sees the two
redemption requests (or the refusal), the shared tables and the one `H₃`.

## The steps

1. The joint hop (`real_sim_NCM`, `main_sharedAll_le`), with the prefix-collision term `2⁻¹²⁸`
   (`pr_collNCM_le`: the two redemption witnesses start with the two openings).
2. **With both redemptions simulated, the view depends on the openings only through the refusal
   bit** (`simNCM_key`, `simNCM_vis`): it is a function of `gNC`, the two nullifiers, the
   simulators' coins and the raw tables.
3. **The (PU) term is statistical** (`bstarNCM_le`): `bstar` on the simulated proofs is a failed
   simulation, a collision of the two proofs' sibling inputs (`313·2⁻¹²⁸`, the right proof's
   uniform `d`, `pr_sib_hit_le`), or the prediction of a redemption's witness prefix (the
   Client's opening `r`) from candidates computed **with the refusal bit set**: these do not
   depend on the openings, so each prediction is at most `(q₅ + 625)·2⁻¹²⁸`
   (`pr_mem_uniform_le`). When the redemptions are refused no proof is computed, so there is
   nothing to predict.
4. The abort hop and the swap of the Clients' tapes (`simNCM_close`): as in `anonymityNC`,
   `2·(φ false + φ true)`.

## The bound (`anonymityNC_main`)

    |Pr[W₀] − Pr[W₁]| ≤ 30·(εS(q₃, q_E + 8·4607) + Δ23)
        + 15·(8·noHitProb + (4·(q₅ + 625) + 626)·2⁻¹²⁸) + 2·2⁻¹²⁸ + 2·(φ false + φ true)

for a guess reading `H₃` at `q₃` points, the cipher at `q_E` keys and `H₅` at a consistent read set
of at most `q₅` keys. Every term is a number except the abort term (`φ`, bounded in the vinegar
random-oracle model by `Privacy/MoussakaPqov.lean`). No assumption on `Com`.
-/

open Finset

-- (The coin types are large products: their `Fintype` instances exceed the default size.)
set_option synthInstance.maxSize 1024

set_option linter.unusedSectionVars false
set_option linter.constructorNameAsVariable false

namespace VoleMole.Privacy.Moussaka

open VoleMole.Spec VoleMole.Spec.Moussaka VoleMole.ZK.Sim VoleMole.Privacy.MainChain
open VoleMole.Verifier VoleMole.Verifier.Bridge VoleMole.Privacy.PU

-- `Com` evaluates Keccak-p[800]; nothing below needs to unfold it.
attribute [local irreducible] com UOVKey.eval
attribute [local irreducible] simulate realRO progRO

/-! ## The honest Anchor of `main` -/

section HonestN

variable (A : AdversaryNC) (idx : AnchorSet → UOVKey → ℕ) (PI : NIZK IssueInstance)
  (sk : Bool → Signer)

/-- The honest Anchor `c`'s answer to a request on `main` (`issue_response`, `main`'s request
length; `none` when it refuses or throws). -/
def respN (c : Bool) (q : Bytes) : Option Bytes :=
  match issueResponse PI (sk c) q A.base.ci with
  | .ok (some s) => some s
  | _ => none

/-- Client `c`'s token after `finalize_issue` on its Anchor's answer. -/
def tokN (c : Bool) (i : PendingToken × Bytes) : Option Token :=
  (respN A PI sk c i.2).bind (finalizeIssue (A.pk c) i.1)

/-- The token, or a well-formed dummy when issuance failed (then nothing is redeemed). -/
def tokDN (c : Bool) (i : PendingToken × Bytes) : Token :=
  (tokN A PI sk c i).getD ⟨List.replicate nfBytes 0, List.replicate rBytes 0, List.replicate uovN 0⟩

/-- Client `c` can redeem at its own index in the set of side `side`. -/
def okN (c side : Bool) (i : PendingToken × Bytes) : Bool :=
  redeemOk A.base.ci A.base.cr (tokDN A PI sk c i) (A.choose side).1
    (idx (A.choose side).1 (A.pk c))

/-- Client `c`'s issuance succeeded and its token is redeemable at its index in both sets. -/
def goodN (c : Bool) (i : PendingToken × Bytes) : Bool :=
  (tokN A PI sk c i).isSome && okN A idx PI sk c false i && okN A idx PI sk c true i

/-- The Anchor accepts the request: `main`'s length and a verifying issuance proof. -/
def accN (q : Bytes) : Bool :=
  decide (q.length = issueRequestBytes) && PI.verify (q.drop uovM) ⟨q.take uovM, A.base.ci⟩

lemma respN_eq (c : Bool) (q : Bytes) :
    respN A PI sk c q = if accN A PI q then (sk c).derivePreimage (q.take uovM) else none := by
  unfold respN issueResponse accN
  by_cases hl : q.length = issueRequestBytes
  · simp only [hl, length_ci, ne_eq, not_true_eq_false, or_self, ↓reduceIte, decide_true,
      Bool.true_and]
    cases PI.verify (q.drop uovM) ⟨q.take uovM, A.base.ci⟩
    · simp
    · simp only [↓reduceIte]
      cases (sk c).derivePreimage (q.take uovM) <;> rfl
  · simp [hl]

/-- **An honest issuance on `main`**: the token is `(nf, r, s)` for the Anchor's preimage `s`, if
the Anchor accepted and `derive_preimage` succeeded, and nothing otherwise. -/
lemma tokN_issReal (hsk : ∀ c, (sk c).Correct (A.pk c)) (c : Bool) (x : IssT) :
    tokN A PI sk c (issReal A.base PI x) =
      if accN A PI (issReal A.base PI x).2 then
        ((sk c).derivePreimage (tNC A x)).map fun s => ⟨List.ofFn x.1, List.ofFn x.2.1, s⟩
      else none := by
  unfold tokN
  rw [respN_eq, issReal_take]
  split_ifs
  · cases hd : (sk c).derivePreimage (tNC A x) with
    | none => rfl
    | some s =>
      have hc := (hsk c (tNC A x) s (length_com _ _ _ _) hd).2
      simp only [Option.bind_some, Option.map_some, finalizeIssue, issReal_t, hc, ↓reduceIte]
      rfl
  · rfl

lemma tokDN_wf (hsk : ∀ c, (sk c).Correct (A.pk c)) (c : Bool) (x : IssT) :
    (tokDN A PI sk c (issReal A.base PI x)).r.length = rBytes ∧
      (tokDN A PI sk c (issReal A.base PI x)).s.length = uovN ∧
      (tokDN A PI sk c (issReal A.base PI x)).nf.length = nfBytes := by
  unfold tokDN
  rw [tokN_issReal A PI sk hsk]
  split_ifs
  · cases hd : (sk c).derivePreimage (tNC A x) with
    | none => simp
    | some s =>
      have hs := (hsk c (tNC A x) s (length_com _ _ _ _) hd).1
      simp [hs]
  · simp

/-- **A finalized honest token carries the Client's `nf` and `r`.** -/
lemma tokDN_of_some (hsk : ∀ c, (sk c).Correct (A.pk c)) (c : Bool) (x : IssT)
    (h : (tokN A PI sk c (issReal A.base PI x)).isSome = true) :
    (tokDN A PI sk c (issReal A.base PI x)).nf = List.ofFn x.1 ∧
      (tokDN A PI sk c (issReal A.base PI x)).r = List.ofFn x.2.1 := by
  rw [tokN_issReal A PI sk hsk] at h
  unfold tokDN
  rw [tokN_issReal A PI sk hsk]
  split_ifs at h ⊢
  · cases hd : (sk c).derivePreimage (tNC A x) with
    | none => rw [hd] at h; cases h
    | some s => exact ⟨rfl, rfl⟩
  · cases h

/-- The symmetric success predicate of the hybrid on `main`. -/
def gSymN (x : IssT) : Bool :=
  accN A PI (issReal A.base PI x).2 &&
    ((foundNC A idx false false && foundNC A idx false true) &&
      (foundNC A idx true false && foundNC A idx true true))

/-- **Unless `derive_preimage` fails**, Client `c`'s success is "accepted, and its key is found in
both sets" (sound index rule). -/
lemma goodN_eq_of_derive (hsk : ∀ c, (sk c).Correct (A.pk c)) (hidx : IdxSound idx) (c : Bool)
    (x : IssT) (hd : (sk c).derivePreimage (tNC A x) ≠ none) :
    goodN A idx PI sk c (issReal A.base PI x) =
      (accN A PI (issReal A.base PI x).2 && (foundNC A idx c false && foundNC A idx c true)) := by
  obtain ⟨s, hs⟩ := Option.ne_none_iff_exists'.1 hd
  have hc := (hsk c (tNC A x) s (length_com _ _ _ _) hs).2
  have htok := tokN_issReal A PI sk hsk c x
  rw [hs] at htok
  unfold goodN okN tokDN
  cases ha : accN A PI (issReal A.base PI x).2
  · rw [ha] at htok
    simp [htok]
  · rw [ha] at htok
    simp only [Option.map_some, ite_true] at htok
    simp only [htok, Option.isSome_some, Option.getD_some, Bool.true_and]
    have hok (side : Bool) : redeemOk A.base.ci A.base.cr ⟨List.ofFn x.1, List.ofFn x.2.1, s⟩
        (A.choose side).1 (idx (A.choose side).1 (A.pk c)) = foundNC A idx c side := by
      unfold redeemOk foundNC
      cases hk : (A.choose side).1.keys[idx (A.choose side).1 (A.pk c)]? with
      | none => rfl
      | some k =>
        simp only [Option.isSome_some, decide_eq_true_eq]
        rw [hidx _ _ _ hk]
        exact hc
    rw [hok, hok]

end HonestN

/-! ## The non-colluding Moderator on `main` and the game -/

/-- **The non-colluding Moderator on `main` with all tables shared**: contexts, the two issuing
keys, per side an Anchor Set and a digest; its guess sees the two redemption requests (or the
refusal), the shared tables and the one `H₃`, with its `H₅` read set. -/
structure AdversaryNCM where
  ctxIss : Coins ctxBytes
  ctxRed : Coins ctxBytes
  pk : Bool → UOVKey
  choose : Bool → AnchorSet × Bytes
  guess : Option (Except Error Bytes × Except Error Bytes) → VisS → H3T → Prop
  R5 : Option (Except Error Bytes × Except Error Bytes) → VisS → H3T → Finset (ZK.Sim.Bytes 37)

namespace AdversaryNCM

variable (A : AdversaryNCM)

/-- Its contexts, keys and choices as an `AdversaryNC`. -/
def nc : AdversaryNC := ⟨A.ctxIss, A.ctxRed, A.pk, A.choose, fun _ => True⟩

/-- The same as an `AdversaryM` (for `main`'s redemption statements, `redStmt`, `redOut`). -/
def m : AdversaryM :=
  ⟨A.ctxIss, A.ctxRed, A.pk, fun _ _ _ _ => 0, fun _ _ side => A.choose side,
    fun _ _ _ _ => True, fun _ _ _ _ => ∅, fun _ _ _ _ => ∅, fun _ _ _ _ => ∅, fun _ _ _ _ => ∅⟩

lemma m_int : A.m.int = A.nc.base := rfl

/-- **Consistent reads**: with its input fixed, the guess and its `H₅` read set read `H₃` at `q3`
points, the cipher at `qE` keys and `H₅` at `R5`. -/
structure ConsH (q3 qE : ℕ) : Prop where
  g : ∀ y, RdTH (A.guess y) (A.R5 y) q3 qE
  r : ∀ y, RdTH (A.R5 y) (A.R5 y) q3 qE

end AdversaryNCM

/-- The secret: the two Clients' issuance tapes `(nf, r, ρ_iss)`. -/
abbrev SecNC := IssT × IssT

/-- Client `c`'s tape. -/
def xOf (s : SecNC) (c : Bool) : IssT := bif c then s.2 else s.1

section GameM

variable (A : AdversaryNCM) (idx : AnchorSet → UOVKey → ℕ) (PI : NIZK IssueInstance)
  (sk : Bool → Signer)

/-- Client `c`'s issuance output. -/
def iOf (s : SecNC) (c : Bool) : PendingToken × Bytes := issReal A.nc.base PI (xOf s c)

/-- **The refusal bit**: both Clients' tokens finalized and each is redeemable at its index in
both sets. -/
def gNC (s : SecNC) : Bool :=
  goodN A.nc idx PI sk false (iOf A PI s false) && goodN A.nc idx PI sk true (iOf A PI s true)

/-- The redemption of side `side` in world `b`: Client `b ^^ side`'s token. -/
def ptNM (b : Bool) (s : SecNC) (side : Bool) : RedeemPt :=
  ⟨tokDN A.nc PI sk (b ^^ side) (iOf A PI s (b ^^ side)), (A.choose side).1,
    idx (A.choose side).1 (A.pk (b ^^ side)), (A.choose side).2⟩

/-- **The game of world `b`** on `main`: no issuance slot, the two redemptions if not refused. -/
def gameNCM (b : Bool) : Game SecNC Out SW SW SW SW where
  σ₁ _ := none
  σ₂ _ _ := none
  σ₃ s _ _ := bif gNC A idx PI sk s then redStmt A.m (ptNM A idx PI sk b s false) else none
  σ₄ s _ _ _ := bif gNC A idx PI sk s then redStmt A.m (ptNM A idx PI sk b s true) else none

/-- What the guess gets besides the tables: the two redemption requests, or the refusal. -/
def keyNCM (b : Bool) (v : GView SecNC pIm pIm pRm pRm) :
    Option (Except Error Bytes × Except Error Bytes) :=
  bif gNC A idx PI sk v.s then
    some (redOut A.m (ptNM A idx PI sk b v.s false) v.o₃,
      redOut A.m (ptNM A idx PI sk b v.s true) v.o₄)
  else none

/-- **The final event of world `b`**. -/
def evNCM (b : Bool) (v : GView SecNC pIm pIm pRm pRm) (T : H3T) : Prop :=
  A.guess (keyNCM A idx PI sk b v) (clrS v.vis) T

/-- Its `H₅` read set. -/
def r5NCM (b : Bool) (v : GView SecNC pIm pIm pRm pRm) (T : H3T) : Finset (ZK.Sim.Bytes 37) :=
  A.R5 (keyNCM A idx PI sk b v) (clrS v.vis) T

/-- **The real game on `main`** in world `b`: the executable prover for the two redemptions, all
tables shared. -/
noncomputable def realNCM (b : Bool) : ℝ :=
  realAll (p₀ := pIm) (n₁ := 256) (n₂ := 256) (n₃ := 343) (n₄ := 343) Hashes.shake
    (gameNCM A idx PI sk b) (evNCM A idx PI sk b)

/-- The game with both redemptions simulated. -/
noncomputable def simNCM (b : Bool) : ℝ :=
  simAll (p₀ := pIm) (n₁ := 256) (n₂ := 256) (n₃ := 343) (n₄ := 343) Hashes.shake
    (gameNCM A idx PI sk b) (evNCM A idx PI sk b)

/-! ### The redemptions when they happen -/

variable {A idx PI sk}

lemma good_of_gNC {s : SecNC} (hg : gNC A idx PI sk s = true) (c : Bool) :
    goodN A.nc idx PI sk c (iOf A PI s c) = true := by
  unfold gNC at hg
  rw [Bool.and_eq_true] at hg
  cases c
  · exact hg.1
  · exact hg.2

lemma redStmt_of_ok (B : AdversaryM) (P : RedeemPt)
    (h : redeemOk B.int.ci B.int.cr P.tok P.anchors P.i = true) :
    redStmt B P = some (stR (xRM B P),
      toBA (encodeRedeemWitness P.tok.nf B.int.ci B.int.cr P.tok.r P.tok.s P.i)) := by
  unfold redeemOk at h
  unfold redStmt
  split
  · rename_i hk; rw [hk] at h; cases h
  · rename_i pk hk
    rw [hk] at h
    simp only [decide_eq_true_eq] at h
    simp only [h, ↓reduceIte]

lemma redOut_of_ok (B : AdversaryM) (P : RedeemPt) (o : Option Out)
    (h : redeemOk B.int.ci B.int.cr P.tok P.anchors P.i = true) :
    redOut B P o = .ok (P.tok.nf ++ pf o) := by
  unfold redeemOk at h
  unfold redOut
  split
  · rename_i hk; rw [hk] at h; cases h
  · rename_i pk hk
    rw [hk] at h
    simp only [decide_eq_true_eq] at h
    simp only [h, ↓reduceIte]

lemma ok_of_gNC {s : SecNC} (hg : gNC A idx PI sk s = true) (b side : Bool) :
    redeemOk A.m.int.ci A.m.int.cr (ptNM A idx PI sk b s side).tok
      (ptNM A idx PI sk b s side).anchors (ptNM A idx PI sk b s side).i = true := by
  have h := good_of_gNC hg (b ^^ side)
  unfold goodN okN at h
  simp only [Bool.and_eq_true] at h
  cases side
  · exact h.1.2
  · exact h.2

/-- **A redemption statement of the game** (not refused): the instance is that of Client
`b ^^ side`'s nullifier, the witness has `343` bytes and starts with the Client's opening. -/
lemma redStmt_gNC (hsk : ∀ c, (sk c).Correct (A.pk c)) {s : SecNC}
    (hg : gNC A idx PI sk s = true) (b side : Bool) :
    ∃ w : ByteArray, redStmt A.m (ptNM A idx PI sk b s side) =
      some (stR ⟨(A.choose side).1.keys, List.ofFn (xOf s (b ^^ side)).1, A.m.int.ci, A.m.int.cr,
        (A.choose side).2⟩, w) ∧ w.size = 343 ∧ wPre w = (xOf s (b ^^ side)).2.1 := by
  have hs := (good_of_gNC hg (b ^^ side))
  unfold goodN at hs
  simp only [Bool.and_eq_true] at hs
  have ht : (tokDN A.nc PI sk (b ^^ side) (iOf A PI s (b ^^ side))).nf =
      List.ofFn (xOf s (b ^^ side)).1 ∧
      (tokDN A.nc PI sk (b ^^ side) (iOf A PI s (b ^^ side))).r = List.ofFn (xOf s (b ^^ side)).2.1 :=
    tokDN_of_some A.nc PI sk hsk (b ^^ side) (xOf s (b ^^ side)) hs.1.1
  have hw := tokDN_wf A.nc PI sk hsk (b ^^ side) (xOf s (b ^^ side))
  refine ⟨toBA (encodeRedeemWitness (ptNM A idx PI sk b s side).tok.nf A.m.int.ci A.m.int.cr
    (ptNM A idx PI sk b s side).tok.r (ptNM A idx PI sk b s side).tok.s
    (ptNM A idx PI sk b s side).i), (redStmt_of_ok A.m _ (ok_of_gNC hg b side)).trans ?_, ?_, ?_⟩
  · show some (stR ⟨_, (tokDN A.nc PI sk (b ^^ side) (iOf A PI s (b ^^ side))).nf, _, _, _⟩, _) = _
    rw [ht.1]
    rfl
  · show (toBA _).size = _
    rw [size_toBA]
    exact length_encodeRedeemWitness hw.1 hw.2.1 _
  · show wPre (toBA (encodeRedeemWitness _ _ _
      (tokDN A.nc PI sk (b ^^ side) (iOf A PI s (b ^^ side))).r _ _)) = _
    rw [ht.2]
    exact wPre_redeemWitness _ _ _ _ _ _

/-- The redemption requests when not refused: Client `b ^^ side`'s nullifier and the proof. -/
lemma redOut_gNC (hsk : ∀ c, (sk c).Correct (A.pk c)) {s : SecNC}
    (hg : gNC A idx PI sk s = true) (b side : Bool) (o : Option Out) :
    redOut A.m (ptNM A idx PI sk b s side) o = .ok (List.ofFn (xOf s (b ^^ side)).1 ++ pf o) := by
  have hs := (good_of_gNC hg (b ^^ side))
  unfold goodN at hs
  simp only [Bool.and_eq_true] at hs
  have ht : (tokDN A.nc PI sk (b ^^ side) (iOf A PI s (b ^^ side))).nf =
      List.ofFn (xOf s (b ^^ side)).1 ∧
      (tokDN A.nc PI sk (b ^^ side) (iOf A PI s (b ^^ side))).r = List.ofFn (xOf s (b ^^ side)).2.1 :=
    tokDN_of_some A.nc PI sk hsk (b ^^ side) (xOf s (b ^^ side)) hs.1.1
  rw [redOut_of_ok A.m _ o (ok_of_gNC hg b side)]
  show Except.ok ((tokDN A.nc PI sk (b ^^ side) (iOf A PI s (b ^^ side))).nf ++ pf o) = _
  rw [ht.1]

/-! ### The hypotheses of the joint hop -/

variable (A idx PI sk)

lemma gvalidNCM (hsk : ∀ c, (sk c).Correct (A.pk c)) (b : Bool) :
    GValid (gameNCM A idx PI sk b) pIm pIm pRm pRm where
  v₁ _ y hy := by cases hy
  v₂ _ _ y hy := by cases hy
  v₃ s o₁ o₂ y hy := by
    have hy' : y ∈ (bif gNC A idx PI sk s then redStmt A.m (ptNM A idx PI sk b s false)
      else none) := hy
    cases h : gNC A idx PI sk s
    · rw [h] at hy'; cases hy'
    · rw [h] at hy'
      have hw := tokDN_wf A.nc PI sk hsk (b ^^ false) (xOf s (b ^^ false))
      exact redStmt_valid A.m _ hw.1 hw.2.1 hw.2.2 y hy'
  v₄ s o₁ o₂ _ y hy := by
    have hy' : y ∈ (bif gNC A idx PI sk s then redStmt A.m (ptNM A idx PI sk b s true)
      else none) := hy
    cases h : gNC A idx PI sk s
    · rw [h] at hy'; cases hy'
    · rw [h] at hy'
      have hw := tokDN_wf A.nc PI sk hsk (b ^^ true) (xOf s (b ^^ true))
      exact redStmt_valid A.m _ hw.1 hw.2.1 hw.2.2 y hy'

lemma rdH_ofNC {X : Sort*}
    {f : Option (Except Error Bytes × Except Error Bytes) → VisS → H3T → X}
    {R : Option (Except Error Bytes × Except Error Bytes) → VisS → H3T → Finset (ZK.Sim.Bytes 37)}
    {q3 qE : ℕ} (h : ∀ y, RdTH (f y) (R y) q3 qE) (b : Bool) :
    RdH (fun (v : GView SecNC pIm pIm pRm pRm) T => f (keyNCM A idx PI sk b v) (clrS v.vis) T)
      (fun v T => R (keyNCM A idx PI sk b v) (clrS v.vis) T) q3 qE := by
  choose QE hQEc hQE using fun y => (h y).hE
  choose QT hQTc hQT using fun y => (h y).hT
  refine ⟨fun v T G5 hk => (h _).h5 (clrS v.vis) T G5 hk,
    ⟨fun v T => QE (keyNCM A idx PI sk b v) (clrS v.vis) T, fun _ _ => hQEc _ _ _,
      fun v T E hk => hQE _ (clrS v.vis) T E hk⟩,
    ⟨fun v T => QT (keyNCM A idx PI sk b v) (clrS v.vis) T, fun _ _ => hQTc _ _ _,
      fun v T T' hk => hQT _ (clrS v.vis) T T' hk⟩,
    fun _ _ _ => rfl, fun _ _ _ => rfl, fun _ _ _ => rfl, fun _ _ _ => rfl⟩

/-- **The joint hop in each world**, both redemptions at once, all tables shared. -/
theorem real_sim_NCM (hsk : ∀ c, (sk c).Correct (A.pk c)) {q3 qE : ℕ} (hC : A.ConsH q3 qE)
    (b : Bool) :
    |realNCM A idx PI sk b - simNCM A idx PI sk b| ≤
      15 * (εS q3 (qE + 8 * 4607) + Δ23 9) +
        15 * simAll (p₀ := pIm) (n₁ := 256) (n₂ := 256) (n₃ := 343) (n₄ := 343) Hashes.shake
          (gameNCM A idx PI sk b) (fun v T => bstar Hashes.shake (gameNCM A idx PI sk b)
            (fun v => r5NCM A idx PI sk b v T) v) +
        pr (GTape SecNC pIm pIm pRm pRm) (fun x => ¬ DistV Hashes.shake (gameNCM A idx PI sk b)
          (hybV23 (p₀ := pIm) (n₁ := 256) (n₂ := 256) (n₃ := 343) (n₄ := 343) Hashes.shake
            (gameNCM A idx PI sk b) false false false false x)) :=
  main_sharedAll_le (p₀ := pIm) (n₁ := 256) (n₂ := 256) (n₃ := 343) (n₄ := 343) Hashes.shake
    (gameNCM A idx PI sk b) mainP_pIm mainP_pIm mainP_pRm mainP_pRm small_pIm small_pIm small_pRm
    small_pRm hashesWF_shake (gvalidNCM A idx PI sk hsk b) (evNCM A idx PI sk b)
    (r5NCM A idx PI sk b)
    (rdH_ofNC A idx PI sk (f := fun y t T => A.guess y t T) (R := fun y t T => A.R5 y t T) hC.g b)
    (rdH_ofNC A idx PI sk (f := fun y t T => A.R5 y t T) (R := fun y t T => A.R5 y t T) hC.r b)

end GameM

/-! ## Two redemptions with one prefix -/

section CollM

variable {A : AdversaryNCM} {idx : AnchorSet → UOVKey → ℕ} {PI : NIZK IssueInstance}
  {sk : Bool → Signer}

lemma σNC_wit (hsk : ∀ c, (sk c).Correct (A.pk c)) (b : Bool) (s : SecNC) (side : Bool) (y : SW)
    (hy : y ∈ (bif gNC A idx PI sk s then redStmt A.m (ptNM A idx PI sk b s side) else none)) :
    y.2.size = pRm.witnessBytes ∧ wPre y.2 = (xOf s (b ^^ side)).2.1 := by
  cases hg : gNC A idx PI sk s
  · rw [hg] at hy; cases hy
  · rw [hg] at hy
    obtain ⟨w, hw, h1, h2⟩ := redStmt_gNC hsk hg b side
    have hy' : redStmt A.m (ptNM A idx PI sk b s side) = some y := hy
    rw [hw] at hy'
    cases hy'
    exact ⟨h1, h2⟩

/-- **Two redemptions of a world with one prefix**: then the two Clients' openings agree (each
redemption witness starts with its Client's opening; the issuance slots prove nothing). -/
theorem coll_impNC (hsk : ∀ c, (sk c).Correct (A.pk c)) (b : Bool)
    (v : GView SecNC pIm pIm pRm pRm) (h : ¬ DistV Hashes.shake (gameNCM A idx PI sk b) v) :
    (xOf v.s false).2.1 = (xOf v.s true).2.1 := by
  by_contra hne
  have r₃ : ∀ y ∈ yv₃ (gameNCM A idx PI sk b) v, y.2.size = pRm.witnessBytes ∧
      wPre y.2 = (xOf v.s (b ^^ false)).2.1 := fun y hy => σNC_wit hsk b v.s false y hy
  have r₄ : ∀ y ∈ yv₄ (gameNCM A idx PI sk b) v, y.2.size = pRm.witnessBytes ∧
      wPre y.2 = (xOf v.s (b ^^ true)).2.1 := fun y hy => σNC_wit hsk b v.s true y hy
  have n₁ : ∀ y ∈ yv₁ (gameNCM A idx PI sk b) v, y.2.size = pIm.witnessBytes :=
    fun y hy => by cases hy
  have n₂ : ∀ y ∈ yv₂ (gameNCM A idx PI sk b) v, y.2.size = pIm.witnessBytes :=
    fun y hy => by cases hy
  have h16 : 16 ≤ pIm.witnessBytes := by decide
  have h16' : 16 ≤ pRm.witnessBytes := by decide
  have mI : pIm.witnessBytes + 32 < preMax := by decide
  have mR : pRm.witnessBytes + 32 < preMax := by decide
  apply h
  have e₁ : ∀ y, y ∉ yv₁ (gameNCM A idx PI sk b) v := fun y hy => Option.not_mem_none y hy
  have e₂ : ∀ y, y ∉ yv₂ (gameNCM A idx PI sk b) v := fun y hy => Option.not_mem_none y hy
  refine ⟨distO_of hashesWF_shake n₁ n₂ h16 mI mI fun y hy => (e₁ y hy).elim,
    distO_of hashesWF_shake n₁ (fun y hy => (r₃ y hy).1) h16 mI mR fun y hy => (e₁ y hy).elim,
    distO_of hashesWF_shake n₁ (fun y hy => (r₄ y hy).1) h16 mI mR fun y hy => (e₁ y hy).elim,
    distO_of hashesWF_shake n₂ (fun y hy => (r₃ y hy).1) h16 mI mR fun y hy => (e₂ y hy).elim,
    distO_of hashesWF_shake n₂ (fun y hy => (r₄ y hy).1) h16 mI mR fun y hy => (e₂ y hy).elim,
    distO_of hashesWF_shake (fun y hy => (r₃ y hy).1) (fun y hy => (r₄ y hy).1) h16' mR mR
      fun y hy y' hy' _ => by
        rw [(r₃ y hy).2, (r₄ y' hy').2]
        cases b
        · exact hne
        · exact Ne.symm hne⟩

variable (A idx PI sk) in
/-- **The prefix-collision term is at most `2⁻¹²⁸`**: the two Clients' uniform openings agree. -/
theorem pr_collNCM_le (hsk : ∀ c, (sk c).Correct (A.pk c)) (b : Bool) :
    pr (GTape SecNC pIm pIm pRm pRm) (fun x => ¬ DistV Hashes.shake (gameNCM A idx PI sk b)
      (hybV23 (p₀ := pIm) (n₁ := 256) (n₂ := 256) (n₃ := 343) (n₄ := 343) Hashes.shake
        (gameNCM A idx PI sk b) false false false false x)) ≤ 1 / 2 ^ 128 := by
  refine (pr_mono fun x hx => coll_impNC hsk b _ hx).trans ?_
  have e1 := pr_prod_fst (β := USh × KS pIm × KS pIm × KS pRm × KS pRm)
    (fun s : SecNC => (xOf s false).2.1 = (xOf s true).2.1)
  refine (le_of_eq e1).trans ?_
  let e : Coins rBytes × ((Coins nfBytes × Coins proveSeedBytes) × IssT) ≃ SecNC :=
    { toFun := fun z => ((z.2.1.1, z.1, z.2.1.2), z.2.2)
      invFun := fun s => (s.1.2.1, ((s.1.1, s.1.2.2), s.2))
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [← pr_equiv e]
  have := pr_mem_uniform_le (X := (Coins nfBytes × Coins proveSeedBytes) × IssT)
    (fun z => {z.2.2.1}) (q := 0) (fun _ => by simp)
  simpa [e, xOf] using this

end CollM

/-! ## With both redemptions simulated: the view depends on the openings only through the
refusal bit -/

section SimM

variable (A : AdversaryNCM)

/-- The redemption statement of side `side` for the nullifier `n`. -/
def stNCM (side : Bool) (n : Bytes) : Statement :=
  stR ⟨(A.choose side).1.keys, n, A.m.int.ci, A.m.int.cr, (A.choose side).2⟩

/-- The statement of side `side` if the redemptions happen. -/
def stOptNCM (g side : Bool) (n : Bytes) : Option Statement :=
  bif g then some (stNCM A side n) else none

/-- Client `c`'s nullifier. -/
def nNC (s : SecNC) (c : Bool) : Bytes := List.ofFn (xOf s c).1

/-- **The `H₂³` table with both redemptions simulated**, from the refusal bit, the nullifiers in
Client order and the simulators' coins and raw tables. -/
noncomputable def tabNCM (b g : Bool) (n₀ n₁ : Bytes) (a : AuxS) : Tab2G pIm :=
  pgP pRm a.2.2.2.1.1.2 (stOptNCM A g false (bif b then n₁ else n₀)) a.1
    (pgP pRm a.2.2.2.2.1.2 (stOptNCM A g true (bif b then n₀ else n₁)) a.1 a.2.1.2.2)

/-- The tables the guess sees with both redemptions simulated. -/
noncomputable def visNCM (b g : Bool) (n₀ n₁ : Bytes) (a : AuxS) : VisS :=
  (a.1, ((fun _ => 0, tabNCM A b g n₀ n₁ a), (fun _ => 0, tabNCM A b g n₀ n₁ a),
    (fun _ => 0, tabNCM A b g n₀ n₁ a), (fun _ => 0, tabNCM A b g n₀ n₁ a)))

/-- The redemption requests with both redemptions simulated (or the refusal). -/
noncomputable def keyNM (b g : Bool) (n₀ n₁ : Bytes) (a : AuxS) :
    Option (Except Error Bytes × Except Error Bytes) :=
  bif g then
    some (.ok ((bif b then n₁ else n₀) ++ pf (some (simulate pRm a.2.2.2.1.1.2))),
      .ok ((bif b then n₀ else n₁) ++ pf (some (simulate pRm a.2.2.2.2.1.2))))
  else none

variable {A} {idx : AnchorSet → UOVKey → ℕ} {PI : NIZK IssueInstance} {sk : Bool → Signer}

lemma σ₃NC_map (hsk : ∀ c, (sk c).Correct (A.pk c)) (b : Bool) (s : SecNC) (side : Bool) :
    (bif gNC A idx PI sk s then redStmt A.m (ptNM A idx PI sk b s side) else none).map
      Prod.fst = stOptNCM A (gNC A idx PI sk s) side (nNC s (b ^^ side)) := by
  cases hg : gNC A idx PI sk s
  · rfl
  · obtain ⟨w, hw, -, -⟩ := redStmt_gNC hsk hg b side
    show (redStmt A.m (ptNM A idx PI sk b s side)).map Prod.fst = _
    rw [hw]
    rfl

lemma nNC_xor (s : SecNC) (b : Bool) :
    nNC s (b ^^ false) = (bif b then nNC s true else nNC s false) ∧
      nNC s (b ^^ true) = (bif b then nNC s false else nNC s true) := by
  cases b <;> exact ⟨rfl, rfl⟩

variable (idx PI sk) in
/-- **The guess's input with both redemptions simulated** is a function of the refusal bit, the
nullifiers and the simulators' coins. -/
theorem simNCM_key (hsk : ∀ c, (sk c).Correct (A.pk c)) (b : Bool)
    (x : GTape SecNC pIm pIm pRm pRm) :
    keyNCM A idx PI sk b (hybV23 (p₀ := pIm) (n₁ := 256) (n₂ := 256) (n₃ := 343) (n₄ := 343)
        Hashes.shake (gameNCM A idx PI sk b) true true true true x) =
      keyNM b (gNC A idx PI sk x.1) (nNC x.1 false) (nNC x.1 true) x.2 := by
  have hs : (hybV23 (p₀ := pIm) (n₁ := 256) (n₂ := 256) (n₃ := 343) (n₄ := 343)
      Hashes.shake (gameNCM A idx PI sk b) true true true true x).s = x.1 := rfl
  unfold keyNCM keyNM
  rw [hs]
  cases hg : gNC A idx PI sk x.1
  · rfl
  · obtain ⟨w₃, hw₃, -, -⟩ := redStmt_gNC hsk hg b false
    obtain ⟨w₄, hw₄, -, -⟩ := redStmt_gNC hsk hg b true
    have o₃ : (hybV23 (p₀ := pIm) (n₁ := 256) (n₂ := 256) (n₃ := 343) (n₄ := 343)
        Hashes.shake (gameNCM A idx PI sk b) true true true true x).o₃ =
        some (simulate pRm x.2.2.2.2.1.1.2) := by
      show (bif gNC A idx PI sk x.1 then redStmt A.m (ptNM A idx PI sk b x.1 false)
        else none).map _ = _
      rw [hg]
      show (redStmt A.m (ptNM A idx PI sk b x.1 false)).map _ = _
      rw [hw₃]
      rfl
    have o₄ : (hybV23 (p₀ := pIm) (n₁ := 256) (n₂ := 256) (n₃ := 343) (n₄ := 343)
        Hashes.shake (gameNCM A idx PI sk b) true true true true x).o₄ =
        some (simulate pRm x.2.2.2.2.2.1.2) := by
      show (bif gNC A idx PI sk x.1 then redStmt A.m (ptNM A idx PI sk b x.1 true)
        else none).map _ = _
      rw [hg]
      show (redStmt A.m (ptNM A idx PI sk b x.1 true)).map _ = _
      rw [hw₄]
      rfl
    simp only [Bool.cond_true]
    rw [redOut_gNC hsk hg, redOut_gNC hsk hg, o₃, o₄]
    have := nNC_xor x.1 b
    simp only [nNC] at this
    rw [this.1, this.2]
    rfl

variable (idx PI sk) in
/-- **The tables the guess sees with both redemptions simulated** are a function of the refusal
bit, the nullifiers and the simulators' coins and raw tables. -/
theorem simNCM_vis (hsk : ∀ c, (sk c).Correct (A.pk c)) (b : Bool)
    (x : GTape SecNC pIm pIm pRm pRm) :
    clrS (hybV23 (p₀ := pIm) (n₁ := 256) (n₂ := 256) (n₃ := 343) (n₄ := 343)
        Hashes.shake (gameNCM A idx PI sk b) true true true true x).vis =
      visNCM A b (gNC A idx PI sk x.1) (nNC x.1 false) (nNC x.1 true) x.2 := by
  have e := σ₃NC_map (idx := idx) (PI := PI) hsk b x.1
  have hn := nNC_xor x.1 b
  have hM : (simSB Hashes.shake pIm x.2.2.1.1.2 x.2.2.1.2.1).pg none x.2.1
      ((simSB Hashes.shake pIm x.2.2.2.1.1.2 x.2.2.2.1.2.1).pg none x.2.1
        ((simSB Hashes.shake pRm x.2.2.2.2.1.1.2 x.2.2.2.2.1.2.1).pg
          (bif gNC A idx PI sk x.1 then redStmt A.m (ptNM A idx PI sk b x.1 false) else none) x.2.1
          ((simSB Hashes.shake pRm x.2.2.2.2.2.1.2 x.2.2.2.2.2.2.1).pg
            (bif gNC A idx PI sk x.1 then redStmt A.m (ptNM A idx PI sk b x.1 true) else none)
              x.2.1 x.2.2.1.2.2))) =
      tabNCM A b (gNC A idx PI sk x.1) (nNC x.1 false) (nNC x.1 true) x.2 := by
    simp only [simSB_pg_eq]
    rw [e false, e true, hn.1, hn.2]
    rfl
  unfold clrS visNCM
  refine Prod.ext rfl (Prod.ext (Prod.ext rfl ?_) (Prod.ext (Prod.ext rfl ?_)
    (Prod.ext (Prod.ext rfl ?_) (Prod.ext rfl ?_)))) <;> exact hM

end SimM
/-! ## The abort hop and the swap of the Clients -/

section SwapM

variable (A : AdversaryNCM) (idx : AnchorSet → UOVKey → ℕ) (PI : NIZK IssueInstance)
  (sk : Bool → Signer)

/-- **The simulated game's event** from the refusal bit, the nullifiers in Client order, the
simulators' coins and raw tables, and `H₃`. -/
noncomputable def hvNCM (b g : Bool) (n₀ n₁ : Bytes) (a : AuxS) (T : H3T) : Prop :=
  A.guess (keyNM b g n₀ n₁ a) (visNCM A b g n₀ n₁ a) T

lemma simNCM_eq (hsk : ∀ c, (sk c).Correct (A.pk c)) (b : Bool) :
    simNCM A idx PI sk b = pr (GTape SecNC pIm pIm pRm pRm × H3T) (fun z =>
      hvNCM A b (gNC A idx PI sk z.1.1) (nNC z.1.1 false) (nNC z.1.1 true) z.1.2 z.2) :=
  pr_congr fun z => by
    exact Iff.of_eq (congrArg₂ (fun a t => A.guess a t z.2) (simNCM_key idx PI sk hsk b z.1)
      (simNCM_vis idx PI sk hsk b z.1))

/-- The hybrid with the symmetric refusal bit. -/
noncomputable def hybNCM (b : Bool) : ℝ :=
  pr (GTape SecNC pIm pIm pRm pRm × H3T) (fun z =>
    hvNCM A b (gSymN A.nc idx PI z.1.1.1 && gSymN A.nc idx PI z.1.1.2) (nNC z.1.1 false)
      (nNC z.1.1 true) z.1.2 z.2)

/-- **The abort hop**: with both redemptions simulated, replacing the refusal bit by the
symmetric one costs at most `φ false + φ true` (identical until a `derive_preimage` fails). -/
theorem sim_hyb_NCM (hsk : ∀ c, (sk c).Correct (A.pk c)) (hidx : IdxSound idx) (b : Bool) :
    |simNCM A idx PI sk b - hybNCM A idx PI b| ≤ phi A.nc sk false + phi A.nc sk true := by
  have hsk' : ∀ c, (sk c).Correct (A.nc.pk c) := hsk
  rw [simNCM_eq A idx PI sk hsk b]
  have hb := abs_pr_sub_le_of_agree
    (fun z : GTape SecNC pIm pIm pRm pRm × H3T =>
      hvNCM A b (gNC A idx PI sk z.1.1) (nNC z.1.1 false) (nNC z.1.1 true) z.1.2 z.2)
    (fun z => hvNCM A b (gSymN A.nc idx PI z.1.1.1 && gSymN A.nc idx PI z.1.1.2) (nNC z.1.1 false)
      (nNC z.1.1 true) z.1.2 z.2)
    (fun z => (sk false).derivePreimage (tNC A.nc z.1.1.1) = none ∨
      (sk true).derivePreimage (tNC A.nc z.1.1.2) = none) fun z hz => by
    simp only [not_or] at hz
    have g0 := goodN_eq_of_derive A.nc idx PI sk hsk' hidx false z.1.1.1 hz.1
    have g1 := goodN_eq_of_derive A.nc idx PI sk hsk' hidx true z.1.1.2 hz.2
    have hg : gNC A idx PI sk z.1.1 = (gSymN A.nc idx PI z.1.1.1 && gSymN A.nc idx PI z.1.1.2) := by
      unfold gNC iOf xOf gSymN
      simp only [Bool.cond_false, Bool.cond_true]
      rw [g0, g1]
      have e : ∀ a₀ a₁ f₀ f₁ f₂ f₃ : Bool, ((a₀ && (f₀ && f₁)) && (a₁ && (f₂ && f₃))) =
          ((a₀ && ((f₀ && f₁) && (f₂ && f₃))) && (a₁ && ((f₀ && f₁) && (f₂ && f₃)))) := by decide
      exact e _ _ _ _ _ _
    rw [hg]
  refine hb.trans ((pr_or_le _ _).trans (le_of_eq ?_))
  have m0 : pr (GTape SecNC pIm pIm pRm pRm × H3T) (fun z =>
      (sk false).derivePreimage (tNC A.nc z.1.1.1) = none) = phi A.nc sk false := by
    rw [pr_prod_fst (fun x : GTape SecNC pIm pIm pRm pRm =>
        (sk false).derivePreimage (tNC A.nc x.1.1) = none),
      pr_prod_fst (fun s : SecNC => (sk false).derivePreimage (tNC A.nc s.1) = none),
      pr_prod_fst (fun x : IssT => (sk false).derivePreimage (tNC A.nc x) = none)]
    exact pr_derive_none A.nc sk false
  have m1 : pr (GTape SecNC pIm pIm pRm pRm × H3T) (fun z =>
      (sk true).derivePreimage (tNC A.nc z.1.1.2) = none) = phi A.nc sk true := by
    rw [pr_prod_fst (fun x : GTape SecNC pIm pIm pRm pRm =>
        (sk true).derivePreimage (tNC A.nc x.1.2) = none),
      pr_prod_fst (fun s : SecNC => (sk true).derivePreimage (tNC A.nc s.2) = none),
      pr_prod_snd (fun x : IssT => (sk true).derivePreimage (tNC A.nc x) = none)]
    exact pr_derive_none A.nc sk true
  rw [m0, m1]

/-- Exchange the two Clients' tapes. -/
def swapNCM : GTape SecNC pIm pIm pRm pRm × H3T ≃ GTape SecNC pIm pIm pRm pRm × H3T where
  toFun z := (((z.1.1.2, z.1.1.1), z.1.2), z.2)
  invFun z := (((z.1.1.2, z.1.1.1), z.1.2), z.2)
  left_inv _ := rfl
  right_inv _ := rfl

/-- The simulated game with the refusal bit `G x₀ && G x₁` for a predicate `G` of a Client's tape. -/
noncomputable def hybG (G : IssT → Bool) (b : Bool) : ℝ :=
  pr (GTape SecNC pIm pIm pRm pRm × H3T) (fun z =>
    hvNCM A b (G z.1.1.1 && G z.1.1.2) (nNC z.1.1 false) (nNC z.1.1 true) z.1.2 z.2)

/-- **A symmetric refusal bit makes the worlds coincide**: swapping the Clients' tapes exchanges
them. -/
theorem hybG_eq (G : IssT → Bool) : hybG A G false = hybG A G true := by
  unfold hybG
  rw [← pr_equiv swapNCM]
  refine pr_congr fun z => ?_
  simp only [swapNCM, Equiv.coe_fn_mk, Bool.and_comm (G z.1.1.2)]
  rfl

theorem hybNCM_eq : hybNCM A idx PI false = hybNCM A idx PI true :=
  hybG_eq A (gSymN A.nc idx PI)

end SwapM
/-! ## The (PU) term: statistical -/

section BstarM

variable (A : AdversaryNCM) (idx : AnchorSet → UOVKey → ℕ) (PI : NIZK IssueInstance)
  (sk : Bool → Signer)

/-- **The public key set with the redemptions happening**: the guess's read set (computed with the
refusal bit set) and the two simulated proofs' active gate inputs. -/
noncomputable def spNCM (b : Bool) (n₀ n₁ : Bytes) (a : AuxS) (T : H3T) :
    Finset (ZK.Sim.Bytes 37) :=
  A.R5 (keyNM b true n₀ n₁ a) (visNCM A b true n₀ n₁ a) T ∪
    ((actL Hashes.shake pRm (stNCM A false (bif b then n₁ else n₀)) a.1.2
        a.2.2.2.1.1.2).toFinset.image (blk 37) ∪
      (actL Hashes.shake pRm (stNCM A true (bif b then n₀ else n₁)) a.1.2
        a.2.2.2.2.1.2).toFinset.image (blk 37))

/-- **The candidates for the opening in the redemption of side `side`**, computed with the
refusal bit set: from the nullifiers, the simulators' coins, the raw tables and `H₃`, not from
the openings. -/
noncomputable def candNCM (b side : Bool) (n₀ n₁ : Bytes) (a : AuxS) (T : H3T) :
    Finset (ZK.Sim.Bytes 16) :=
  candC Hashes.shake (stNCM A side (bif b ^^ side then n₁ else n₀)) a.1.2
    (bif side then a.2.2.2.2.1.2 else a.2.2.2.1.1.2) (spNCM A b n₀ n₁ a T)

lemma card_candNCM_le {q5 : ℕ} (h5 : ∀ y t T, (A.R5 y t T).card ≤ q5) (b side : Bool)
    (n₀ n₁ : Bytes) (a : AuxS) (T : H3T) : (candNCM A b side n₀ n₁ a T).card ≤ q5 + 624 + 1 := by
  refine (card_candC_le Hashes.shake mainP_pRm _ _ _ _).trans (Nat.succ_le_succ ?_)
  unfold spNCM
  refine (card_union_le _ _).trans (add_le_add (h5 _ _ _) ((card_union_le _ _).trans ?_))
  have l₁ := (card_image_le (f := blk 37)).trans ((List.toFinset_card_le _).trans
    (actL_length_le Hashes.shake (p := pRm) (stNCM A false (bif b then n₁ else n₀)) a.1.2
      a.2.2.2.1.1.2))
  have l₂ := (card_image_le (f := blk 37)).trans ((List.toFinset_card_le _).trans
    (actL_length_le Hashes.shake (p := pRm) (stNCM A true (bif b then n₀ else n₁)) a.1.2
      a.2.2.2.2.1.2))
  omega

variable {A idx PI sk}

set_option maxRecDepth 8000 in
lemma candO_some {q : Option (Statement × ZK.Sim.Bytes 16)} {st : Statement} {r : ZK.Sim.Bytes 16}
    {E : Cipher} {c : SimCoins pRm} {S : Finset (ZK.Sim.Bytes 37)} (hq : q = some (st, r))
    (h : candO Hashes.shake q E c S) : r ∈ candC Hashes.shake st E c S := by
  subst hq; exact h

set_option maxRecDepth 8192 in
/-- **`bstar` with both redemptions simulated**: a failed simulation, a prediction of a
redemption's opening from candidates computed with the refusal bit set, or a sibling gate input of
the left proof that is one of the right proof's. -/
theorem bstarNCM_imp (hsk : ∀ c, (sk c).Correct (A.pk c)) (b : Bool)
    (x : GTape SecNC pIm pIm pRm pRm) (T : H3T)
    (h : bstar Hashes.shake (gameNCM A idx PI sk b) (fun v => r5NCM A idx PI sk b v T)
      (hybV23 (p₀ := pIm) (n₁ := 256) (n₂ := 256) (n₃ := 343) (n₄ := 343) Hashes.shake
        (gameNCM A idx PI sk b) true true true true x)) :
    (errC pIm x.2.2.1.1.2 ∨ errC pIm x.2.2.2.1.1.2 ∨ errC pRm x.2.2.2.2.1.1.2 ∨
      errC pRm x.2.2.2.2.2.1.2) ∨
    (gNC A idx PI sk x.1 = true ∧
      (xOf x.1 (b ^^ false)).2.1 ∈ candNCM A b false (nNC x.1 false) (nNC x.1 true) x.2 T) ∨
    (gNC A idx PI sk x.1 = true ∧
      (xOf x.1 (b ^^ true)).2.1 ∈ candNCM A b true (nNC x.1 false) (nNC x.1 true) x.2 T) ∨
    (∃ w ∈ sibO Hashes.shake pRm (qOf ((gameNCM A idx PI sk b).σ₃ x.1 none none)) x.2.1.2
        x.2.2.2.2.1.1.2,
      w ∈ sibO Hashes.shake pRm (qOf ((gameNCM A idx PI sk b).σ₄ x.1 none none none)) x.2.1.2
        x.2.2.2.2.2.1.2) := by
  classical
  set G := gameNCM A idx PI sk b
  set R := r5NCM A idx PI sk b (hybV23 (p₀ := pIm) (n₁ := 256) (n₂ := 256) (n₃ := 343)
    (n₄ := 343) Hashes.shake G true true true true x) T with hR
  have hb := bstar_sim (p₁ := pIm) (p₂ := pIm) (p₃ := pRm) (p₄ := pRm) Hashes.shake G hashesWF_shake
    x.1 x.2.1.2 x.2.2.1.1.2 x.2.2.2.1.1.2 x.2.2.2.2.1.1.2 x.2.2.2.2.2.1.2 R
    none none ((G.σ₃ x.1 none none).map fun _ => simulate pRm x.2.2.2.2.1.1.2)
    ((G.σ₄ x.1 none none none).map fun _ => simulate pRm x.2.2.2.2.2.1.2)
    none none (qOf (G.σ₃ x.1 none none)) (qOf (G.σ₄ x.1 none none none))
    rfl rfl rfl rfl rfl rfl rfl rfl _ rfl h
  -- the read set with the redemptions happening
  have hRg : gNC A idx PI sk x.1 = true → R = A.R5 (keyNM b true (nNC x.1 false) (nNC x.1 true)
      x.2) (visNCM A b true (nNC x.1 false) (nNC x.1 true) x.2) T := fun hg => by
    rw [hR]
    have k := simNCM_key idx PI sk hsk b x
    have v := simNCM_vis idx PI sk hsk b x
    rw [hg] at k v
    exact congrArg₂ (fun a t => A.R5 a t T) k v
  have hq : ∀ side, gNC A idx PI sk x.1 = true →
      qOf (bif gNC A idx PI sk x.1 then redStmt A.m (ptNM A idx PI sk b x.1 side) else none) =
        some (stNCM A side (bif b ^^ side then nNC x.1 true else nNC x.1 false),
          (xOf x.1 (b ^^ side)).2.1) := fun side hg => by
    obtain ⟨w, hw, -, hw'⟩ := redStmt_gNC hsk hg b side
    rw [hg]
    show (redStmt A.m (ptNM A idx PI sk b x.1 side)).map _ = _
    rw [hw]
    show some (_, wPre w) = _
    rw [hw']
    have e : List.ofFn (xOf x.1 (b ^^ side)).1 =
        (bif b ^^ side then nNC x.1 true else nNC x.1 false) := by
      cases b ^^ side <;> rfl
    rw [e]
    rfl
  have hn : ∀ side, (bif b ^^ side then nNC x.1 true else nNC x.1 false) =
      (bif side then (bif b then nNC x.1 false else nNC x.1 true)
        else (bif b then nNC x.1 true else nNC x.1 false)) := fun side => by
    cases b <;> cases side <;> rfl
  have hsub : gNC A idx PI sk x.1 = true →
      R ∪ ((actO Hashes.shake pIm none x.2.1.2 x.2.2.1.1.2).toFinset.image (blk 37) ∪
        (actO Hashes.shake pIm none x.2.1.2 x.2.2.2.1.1.2).toFinset.image (blk 37) ∪
        (actO Hashes.shake pRm (qOf (G.σ₃ x.1 none none)) x.2.1.2
          x.2.2.2.2.1.1.2).toFinset.image (blk 37) ∪
        (actO Hashes.shake pRm (qOf (G.σ₄ x.1 none none none)) x.2.1.2
          x.2.2.2.2.2.1.2).toFinset.image (blk 37)) ⊆
      spNCM A b (nNC x.1 false) (nNC x.1 true) x.2 T := fun hg => by
    have q₃ : qOf (G.σ₃ x.1 none none) = _ := hq false hg
    have q₄ : qOf (G.σ₄ x.1 none none none) = _ := hq true hg
    rw [q₃, q₄, hRg hg, hn false, hn true]
    intro k hk
    simp only [actO, List.toFinset_nil, image_empty, empty_union, mem_union] at hk
    unfold spNCM
    simp only [mem_union]
    tauto
  rcases hb with he | hc | hs
  · exact Or.inl he
  · rcases hc with h1 | h2 | h3 | h4
    · exact h1.elim
    · exact h2.elim
    · right; left
      cases hg : gNC A idx PI sk x.1
      · have : qOf (G.σ₃ x.1 none none) = none := by
          show qOf (bif gNC A idx PI sk x.1 then _ else none) = none
          rw [hg]; rfl
        rw [this] at h3; exact h3.elim
      · refine ⟨rfl, ?_⟩
        have q₃ : qOf (G.σ₃ x.1 none none) = _ := hq false hg
        exact candC_mono Hashes.shake (hsub hg) (candO_some q₃ h3)
    · right; right; left
      cases hg : gNC A idx PI sk x.1
      · have : qOf (G.σ₄ x.1 none none none) = none := by
          show qOf (bif gNC A idx PI sk x.1 then _ else none) = none
          rw [hg]; rfl
        rw [this] at h4; exact h4.elim
      · refine ⟨rfl, ?_⟩
        have q₄ : qOf (G.σ₄ x.1 none none none) = _ := hq true hg
        exact candC_mono Hashes.shake (hsub hg) (candO_some q₄ h4)
  · right; right; right
    rcases hs with ⟨w, hw, -⟩ | ⟨w, hw, -⟩ | ⟨w, hw, hw'⟩
    · exact (List.not_mem_nil hw).elim
    · exact (List.not_mem_nil hw).elim
    · exact ⟨w, by simpa [sibO] using hw, hw'⟩

end BstarM
/-! ## The (PU) term: the numbers -/

section PrM

variable (A : AdversaryNCM) (idx : AnchorSet → UOVKey → ℕ) (PI : NIZK IssueInstance)
  (sk : Bool → Signer)

theorem pr_errNC₁_le : pr (GTape SecNC pIm pIm pRm pRm) (fun x => errC pIm x.2.2.1.1.2) ≤
    noHitProb :=
  pr_le_of_fst fun _ => pr_le_of_fst fun _ => pr_le_of_snd fun _ => pr_errC_le

theorem pr_errNC₂_le : pr (GTape SecNC pIm pIm pRm pRm) (fun x => errC pIm x.2.2.2.1.1.2) ≤
    noHitProb :=
  pr_le_of_fst fun _ => pr_le_of_fst fun _ => pr_le_of_fst fun _ => pr_le_of_snd fun _ =>
    pr_errC_le

theorem pr_errNC₃_le : pr (GTape SecNC pIm pIm pRm pRm) (fun x => errC pRm x.2.2.2.2.1.1.2) ≤
    noHitProb :=
  pr_le_of_fst fun _ => pr_le_of_fst fun _ => pr_le_of_fst fun _ => pr_le_of_fst fun _ =>
    pr_le_of_snd fun _ => pr_errC_le

theorem pr_errNC₄_le : pr (GTape SecNC pIm pIm pRm pRm) (fun x => errC pRm x.2.2.2.2.2.1.2) ≤
    noHitProb :=
  pr_le_of_fst fun _ => pr_le_of_fst fun _ => pr_le_of_fst fun _ => pr_le_of_fst fun _ =>
    pr_le_of_fst fun _ => pr_errC_le

set_option maxRecDepth 8192 in
/-- **A Client's opening against candidates from the nullifiers, coins, tables and `H₃`**: at most
`(q + 1)·2⁻¹²⁸`, the opening being uniform and independent of them. -/
theorem pr_open_le (c : Bool) (C : Bytes → Bytes → AuxS → H3T → Finset (ZK.Sim.Bytes 16)) {q : ℕ}
    (hC : ∀ n₀ n₁ a T, (C n₀ n₁ a T).card ≤ q + 1) :
    pr (GTape SecNC pIm pIm pRm pRm × H3T) (fun z =>
      (xOf z.1.1 c).2.1 ∈ C (nNC z.1.1 false) (nNC z.1.1 true) z.1.2 z.2) ≤ (q + 1) / 2 ^ 128 := by
  cases c
  · let e : Coins rBytes × (((Coins nfBytes × Coins proveSeedBytes) × IssT) × (AuxS × H3T)) ≃
        GTape SecNC pIm pIm pRm pRm × H3T :=
      { toFun := fun z => ((((z.2.1.1.1, z.1, z.2.1.1.2), z.2.1.2), z.2.2.1), z.2.2.2)
        invFun := fun z => (z.1.1.1.2.1, (((z.1.1.1.1, z.1.1.1.2.2), z.1.1.2), (z.1.2, z.2)))
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
    rw [← pr_equiv e]
    exact pr_mem_uniform_le (X := ((Coins nfBytes × Coins proveSeedBytes) × IssT) × (AuxS × H3T))
      (fun y => C (List.ofFn y.1.1.1) (List.ofFn y.1.2.1) y.2.1 y.2.2) fun _ => hC _ _ _ _
  · let e : Coins rBytes × ((IssT × (Coins nfBytes × Coins proveSeedBytes)) × (AuxS × H3T)) ≃
        GTape SecNC pIm pIm pRm pRm × H3T :=
      { toFun := fun z => (((z.2.1.1, (z.2.1.2.1, z.1, z.2.1.2.2)), z.2.2.1), z.2.2.2)
        invFun := fun z => (z.1.1.2.2.1, ((z.1.1.1, (z.1.1.2.1, z.1.1.2.2.2)), (z.1.2, z.2)))
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
    rw [← pr_equiv e]
    exact pr_mem_uniform_le (X := (IssT × (Coins nfBytes × Coins proveSeedBytes)) × (AuxS × H3T))
      (fun y => C (List.ofFn y.1.1.1) (List.ofFn y.1.2.1) y.2.1 y.2.2) fun _ => hC _ _ _ _

set_option maxRecDepth 8192 in
/-- **The two simulated redemptions collide with probability `≤ 313·2⁻¹²⁸`**: the right proof's
`d` is uniform and independent of the left proof. -/
theorem pr_sibNCM_le (hsk : ∀ c, (sk c).Correct (A.pk c)) (b : Bool) :
    pr (GTape SecNC pIm pIm pRm pRm) (fun x =>
      ∃ w ∈ sibO Hashes.shake pRm (qOf ((gameNCM A idx PI sk b).σ₃ x.1 none none)) x.2.1.2
          x.2.2.2.2.1.1.2,
        w ∈ sibO Hashes.shake pRm (qOf ((gameNCM A idx PI sk b).σ₄ x.1 none none none)) x.2.1.2
          x.2.2.2.2.2.1.2) ≤ ((312 : ℕ) + 1) / 2 ^ 128 := by
  refine pr_le_of_fst fun s => pr_le_of_fst fun u => pr_le_of_fst fun k₁ => pr_le_of_fst fun k₂ =>
    pr_le_of_fst fun k₃ => pr_KS_d_le _ fun ρ sh c1 c2 c3 c5 V => ?_
  have hlen := sibO_length_le Hashes.shake (p := pRm)
    (qOf ((gameNCM A idx PI sk b).σ₃ s none none)) u.2 k₃.1.2
  cases hg : gNC A idx PI sk s
  · refine le_trans (le_of_eq ?_) (by positivity)
    rw [pr_congr (Q := fun _ => False) fun d => by
      have : qOf ((gameNCM A idx PI sk b).σ₄ s none none none) = none := by
        show qOf (bif gNC A idx PI sk s then _ else none) = none
        rw [hg]; rfl
      rw [this]
      simp [sibO]]
    exact pr_false
  · obtain ⟨w, hw, -, hw'⟩ := redStmt_gNC hsk hg b true
    have hq : qOf ((gameNCM A idx PI sk b).σ₄ s none none none) =
        some (stR ⟨(A.choose true).1.keys, List.ofFn (xOf s (b ^^ true)).1, A.m.int.ci,
          A.m.int.cr, (A.choose true).2⟩, (xOf s (b ^^ true)).2.1) := by
      show qOf (bif gNC A idx PI sk s then _ else none) = _
      rw [hg]
      show (redStmt A.m (ptNM A idx PI sk b s true)).map _ = _
      rw [hw]
      show some (_, wPre w) = _
      rw [hw']
    refine le_trans (pr_mono fun d hd => ?_) (pr_sib_hit_le Hashes.shake mainP_pRm
      (stR ⟨(A.choose true).1.keys, List.ofFn (xOf s (b ^^ true)).1, A.m.int.ci,
        A.m.int.cr, (A.choose true).2⟩) u.2 sh c1 c2 c3 c5 (xOf s (b ^^ true)).2.1 _ hlen)
    rw [hq] at hd
    exact hd

set_option maxRecDepth 8192 in
/-- **The (PU) term of the non-colluding game on `main` is statistical**: with both redemptions
simulated, `bstar` has probability at most `4·noHitProb + 2·(q₅ + 625)·2⁻¹²⁸ + 313·2⁻¹²⁸`, for a
guess whose `H₅` read sets have at most `q₅` keys. -/
theorem pr_bstarNCM_le (hsk : ∀ c, (sk c).Correct (A.pk c)) {q5 : ℕ}
    (h5 : ∀ y t T, (A.R5 y t T).card ≤ q5) (b : Bool) :
    simAll (p₀ := pIm) (n₁ := 256) (n₂ := 256) (n₃ := 343) (n₄ := 343) Hashes.shake
        (gameNCM A idx PI sk b) (fun v T => bstar Hashes.shake (gameNCM A idx PI sk b)
          (fun v => r5NCM A idx PI sk b v T) v) ≤
      4 * noHitProb + 2 * ((q5 + 625) / 2 ^ 128) + 313 / 2 ^ 128 := by
  unfold simAll
  have h := (pr_mono fun (z : GTape SecNC pIm pIm pRm pRm × H3T) hz =>
    bstarNCM_imp (idx := idx) (PI := PI) hsk b z.1 z.2 hz).trans ((pr_or_le _ _).trans
    (add_le_add ((pr_or_le _ _).trans (add_le_add le_rfl ((pr_or_le _ _).trans (add_le_add le_rfl
      (pr_or_le _ _))))) ((pr_or_le _ _).trans (add_le_add le_rfl ((pr_or_le _ _).trans
        (add_le_add le_rfl le_rfl))))))
  have e₁ := (le_of_eq (pr_prod_fst (β := H3T) (fun x : GTape SecNC pIm pIm pRm pRm =>
    errC pIm x.2.2.1.1.2))).trans (pr_errNC₁_le)
  have e₂ := (le_of_eq (pr_prod_fst (β := H3T) (fun x : GTape SecNC pIm pIm pRm pRm =>
    errC pIm x.2.2.2.1.1.2))).trans (pr_errNC₂_le)
  have e₃ := (le_of_eq (pr_prod_fst (β := H3T) (fun x : GTape SecNC pIm pIm pRm pRm =>
    errC pRm x.2.2.2.2.1.1.2))).trans (pr_errNC₃_le)
  have e₄ := (le_of_eq (pr_prod_fst (β := H3T) (fun x : GTape SecNC pIm pIm pRm pRm =>
    errC pRm x.2.2.2.2.2.1.2))).trans (pr_errNC₄_le)
  have c₃ := (pr_mono fun (z : GTape SecNC pIm pIm pRm pRm × H3T)
      (hz : gNC A idx PI sk z.1.1 = true ∧ (xOf z.1.1 (b ^^ false)).2.1 ∈
        candNCM A b false (nNC z.1.1 false) (nNC z.1.1 true) z.1.2 z.2) => hz.2).trans
    (pr_open_le (b ^^ false) (fun n₀ n₁ a T => candNCM A b false n₀ n₁ a T)
      (q := q5 + 624) fun n₀ n₁ a T => card_candNCM_le A h5 b false n₀ n₁ a T)
  have c₄ := (pr_mono fun (z : GTape SecNC pIm pIm pRm pRm × H3T)
      (hz : gNC A idx PI sk z.1.1 = true ∧ (xOf z.1.1 (b ^^ true)).2.1 ∈
        candNCM A b true (nNC z.1.1 false) (nNC z.1.1 true) z.1.2 z.2) => hz.2).trans
    (pr_open_le (b ^^ true) (fun n₀ n₁ a T => candNCM A b true n₀ n₁ a T)
      (q := q5 + 624) fun n₀ n₁ a T => card_candNCM_le A h5 b true n₀ n₁ a T)
  have s₃₄ := (le_of_eq (pr_prod_fst (β := H3T) (fun x : GTape SecNC pIm pIm pRm pRm =>
      ∃ w ∈ sibO Hashes.shake pRm (qOf ((gameNCM A idx PI sk b).σ₃ x.1 none none)) x.2.1.2
          x.2.2.2.2.1.1.2,
        w ∈ sibO Hashes.shake pRm (qOf ((gameNCM A idx PI sk b).σ₄ x.1 none none none)) x.2.1.2
          x.2.2.2.2.2.1.2))).trans (pr_sibNCM_le A idx PI sk hsk b)
  have hq : ((q5 + 624 : ℕ) + 1 : ℝ) = (q5 : ℝ) + 625 := by push_cast; ring
  rw [hq] at c₃ c₄
  have hn : (((312 : ℕ) + 1 : ℝ) / 2 ^ 128) = 313 / 2 ^ 128 := by norm_num
  rw [hn] at s₃₄
  refine h.trans ?_
  linarith

end PrM
/-! ## Theorem 4(b') on `main` -/

section MainM

variable (A : AdversaryNCM) (idx : AnchorSet → UOVKey → ℕ) (PI : NIZK IssueInstance)
  (sk : Bool → Signer)

/-- **Theorem 4(b') on `main` (no label rows), all tables shared.** For every non-colluding
Moderator (contexts, keys, Anchor Sets and digests of its choice; it sees no issuance), honest
Anchors with signers correct for their keys answering with `main`'s `issue_response`, a sound index
rule, any issuance proof system, and the executable prover for the two redemptions with one `H₃`,
one `H₂³` table, one `H₅` table and one cipher: if the guess reads `H₃` at `q3` points, the cipher
at `qE` keys and `H₅` at a consistent read set of at most `q5` keys,

    |Pr[W₀] − Pr[W₁]| ≤ 30·(εS(q3, qE + 8·4607) + Δ23)
        + 15·(8·noHitProb + (4·(q5 + 625) + 626)·2⁻¹²⁸) + 2·2⁻¹²⁸ + 2·(φ false + φ true).

The (PU) term is statistical: no assumption on `Com`. `φ c` is the abort probability of
Anchor `c` (`phi`; `≤ δ_c^255` for pqov in the vinegar random-oracle model). -/
theorem anonymityNC_main (hsk : ∀ c, (sk c).Correct (A.pk c)) (hidx : IdxSound idx) {q3 qE q5 : ℕ}
    (hC : A.ConsH q3 qE) (h5 : ∀ y t T, (A.R5 y t T).card ≤ q5) :
    |realNCM A idx PI sk false - realNCM A idx PI sk true| ≤
      30 * (εS q3 (qE + 8 * 4607) + Δ23 9) +
        15 * (8 * noHitProb + (4 * (q5 + 625) + 626) / 2 ^ 128) + 2 / 2 ^ 128 +
        2 * (phi A.nc sk false + phi A.nc sk true) := by
  have r0 := real_sim_NCM A idx PI sk hsk hC false
  have r1 := real_sim_NCM A idx PI sk hsk hC true
  have b0 := pr_bstarNCM_le A idx PI sk hsk h5 false
  have b1 := pr_bstarNCM_le A idx PI sk hsk h5 true
  have c0 := pr_collNCM_le A idx PI sk hsk false
  have c1 := pr_collNCM_le A idx PI sk hsk true
  have g0 := sim_hyb_NCM A idx PI sk hsk hidx false
  have g1 := sim_hyb_NCM A idx PI sk hsk hidx true
  have he := hybNCM_eq A idx PI
  have hn : (4 * ((q5 : ℝ) + 625) + 626) / 2 ^ 128 =
      2 * ((q5 + 625) / 2 ^ 128) + 313 / 2 ^ 128 + (2 * ((q5 + 625) / 2 ^ 128) + 313 / 2 ^ 128) := by
    ring
  have := abs_sub_le_iff.1 r0; have := abs_sub_le_iff.1 r1; have := abs_sub_le_iff.1 g0
  have := abs_sub_le_iff.1 g1
  rw [abs_sub_le_iff, hn]
  constructor <;> linarith

/-- **Unlinkability against a non-colluding Moderator on `main`**: with one Anchor (equal keys
and signers) and any index rule, the same bound without the abort term. -/
theorem unlinkabilityNC_main (hsk : ∀ c, (sk c).Correct (A.pk c)) (hpk : A.pk false = A.pk true)
    (hs : sk false = sk true) {q3 qE q5 : ℕ} (hC : A.ConsH q3 qE)
    (h5 : ∀ y t T, (A.R5 y t T).card ≤ q5) :
    |realNCM A idx PI sk false - realNCM A idx PI sk true| ≤
      30 * (εS q3 (qE + 8 * 4607) + Δ23 9) +
        15 * (8 * noHitProb + (4 * (q5 + 625) + 626) / 2 ^ 128) + 2 / 2 ^ 128 := by
  have hg : goodN A.nc idx PI sk false = goodN A.nc idx PI sk true := by
    funext i
    have hpk' : A.nc.pk false = A.nc.pk true := hpk
    simp only [goodN, okN, tokDN, tokN, respN, hpk', hs]
  have hsim (b : Bool) : simNCM A idx PI sk b =
      hybG A (fun x => goodN A.nc idx PI sk true (issReal A.nc.base PI x)) b := by
    rw [simNCM_eq A idx PI sk hsk b]
    refine pr_congr fun z => ?_
    have e : gNC A idx PI sk z.1.1 = (goodN A.nc idx PI sk true (issReal A.nc.base PI z.1.1.1) &&
        goodN A.nc idx PI sk true (issReal A.nc.base PI z.1.1.2)) := by
      unfold gNC iOf xOf
      rw [hg]
      rfl
    rw [e]
  have r0 := real_sim_NCM A idx PI sk hsk hC false
  have r1 := real_sim_NCM A idx PI sk hsk hC true
  have b0 := pr_bstarNCM_le A idx PI sk hsk h5 false
  have b1 := pr_bstarNCM_le A idx PI sk hsk h5 true
  have c0 := pr_collNCM_le A idx PI sk hsk false
  have c1 := pr_collNCM_le A idx PI sk hsk true
  have he := hybG_eq A (fun x => goodN A.nc idx PI sk true (issReal A.nc.base PI x))
  rw [← hsim, ← hsim] at he
  have hn : (4 * ((q5 : ℝ) + 625) + 626) / 2 ^ 128 =
      2 * ((q5 + 625) / 2 ^ 128) + 313 / 2 ^ 128 + (2 * ((q5 + 625) / 2 ^ 128) + 313 / 2 ^ 128) := by
    ring
  have := abs_sub_le_iff.1 r0; have := abs_sub_le_iff.1 r1
  rw [abs_sub_le_iff, hn]
  constructor <;> linarith

end MainM

end VoleMole.Privacy.Moussaka
