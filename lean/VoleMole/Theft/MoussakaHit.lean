import VoleMole.Theft.HitTheft

/-!
# Moussaka: redemption non-malleability with `ε_hit` bounded

`noRedirect_leanX_plain` (`Theft/Tables.lean`) leaves the programmed-point term `ε_hit`
(`ProgEv … HitOpX`). `Theft/HitLevel.lean` bounds it for two proof systems whose forgeries have
table-point chain inputs and `H₂⁰` inputs other than the simulated statements' (`progEv_chain`).
For Moussaka this needs more than the game's freshness `FreshOp`, for two reasons.

* **Lengths.** The spec's instances are byte lists. The issuance encoding `t ‖ ctx_iss` and the
  redemption encoding `64 ‖ n ‖ digests ‖ nf ‖ ctx_iss ‖ ctx_red ‖ cd` are injective only for
  fields of fixed lengths (`issueEncode_inj`, `redeemEncode_inj`), and a chain input is a table
  point only if it is short. The C++ API fixes the lengths by its types (`Context`,
  `ChallengeDigest`, `Nullifier`, the requests: `std::array`; the key digest is 32 bytes of
  SHAKE). `WfI`, `WfR`: the instance has these lengths (and at most 64 Anchors).
* **The Anchor keys are not hashed, their digests are.** The redemption statement's `H₂⁰` input
  has the digests of the Anchor Set, not the public maps. In the spec a key is a digest and a map
  (`UOVKey`), unrelated; in C++ the digest is SHAKE256 of the key. Two redemption statements with
  the same digests and other maps have the same chain (as Ratatouille's spend statements with
  different keys, `Hit.Rata.FreshOk`).

So `ε_hit` is bounded for **`FreshOk`**: the forgery's statement is well-formed, and each simulated
statement of its relation is well-formed and differs from it in a hashed field (`hashedR`: the
digests, `nf`, both contexts, the challenge digest). `FreshOk` implies `FreshOp`
(`FreshOk.freshOp`).

* `muIn_stI_inj`, `muIn_stR_inj`, `muIn_stI_ne_stR`: the `H₂⁰` input of a well-formed statement
  determines it (the redemption's: its hashed fields); issuance and redemption inputs differ (the
  domain separators).
* `fd_fOk`: a fresh forgery's chain inputs have at most `Lmin = 6293` bytes (`H₂¹` inputs of the
  redemption relation).
* **`progEv_hit`**: `ε_hit ≤ 2·((q_μ+3)·2⁻²⁵⁶ + (q₂₁+3)·2⁻¹⁰⁸⁸ + (q₂₂+3)·2⁻⁴⁴⁸)` for `FreshOk`.
* **In the game** (`HitWf`): an adversary whose Anchor Sets have 32-byte digests, whose challenge
  digests have 32 bytes, whose redemptions have 16-byte contexts, and whose redemption's Anchor
  Set is the Client's if it has the same digests. Then an accepted operation that is fresh for the
  game (`FreshOp`) is `FreshOk` (`freshOk_of_game`: the issuance lengths are the ones
  `finalize`/`issue_response` check, `AccOp`; the Client's statements are well-formed), so weak
  simulation-extractability for `FreshOk` suffices (`sim_se_le_ok`, `noRedirect_ok`).
* **`noRedirect_leanX_hit`**: `noRedirect_leanX_plain` with `ε_hit` replaced by its bound,

      Pr[Bad] ≤ εz(pI; q) + εz(pR; q) + δ_R + ε_plain
        + 2·((q_μ+3)·2⁻²⁵⁶ + (q₂₁+3)·2⁻¹⁰⁸⁸ + (q₂₂+3)·2⁻⁴⁴⁸) + Adv^ow(inverter),

  for `HitWf` adversaries whose last stage reads the chain tables `H₂⁰`, `H₂¹`, `H₂²` (inputs of at
  most `L ≥ 6293` bytes) with `q_μ`, `q₂₁`, `q₂₂` queries (`AdmHit`).
-/

-- (The coin types are large products: their `Fintype` instances exceed the default size.)
set_option synthInstance.maxSize 1024

namespace VoleMole.Theft.Hit.Mous

open VoleMole.Privacy
open VoleMole.Verifier VoleMole.Verifier.Bridge VoleMole.ZK.Sim VoleMole.ZK
open VoleMole.Privacy.Moussaka VoleMole.Spec VoleMole.Spec.Moussaka VoleMole.Theft.Moussaka
open VoleMole.Theft.Chain
open VoleMole.ROM.IC (muIn)
open VoleMole.EndToEnd.SpecRel (toL_toBA toBA_inj)

-- `Com` evaluates Keccak-p[800]; nothing below needs to unfold it.
attribute [local irreducible] com UOVKey.eval

/-! ## Well-formed instances and the freshness of the bound -/

/-- **A well-formed issuance instance**: `t` of `uov::M` bytes, a 16-byte context. -/
def WfI (x : IssueInstance) : Prop := x.t.length = uovM ∧ x.ctxIss.length = ctxBytes

/-- **A well-formed redemption instance**: at most 64 Anchors with 32-byte digests, a 24-byte
nullifier, 16-byte contexts, a 32-byte challenge digest. -/
def WfR (x : RedeemInstance) : Prop :=
  (∀ pk ∈ x.anchors, pk.digest.length = digestBytes) ∧ x.anchors.length ≤ maxAnchors ∧
    x.nf.length = nfBytes ∧ x.ctxIss.length = ctxBytes ∧ x.ctxRed.length = ctxBytes ∧
    x.challengeDigest.length = cdBytes

/-- **What a redemption statement hashes**: the Anchors' digests (not their maps), the nullifier,
the contexts, the challenge digest. -/
def hashedR (x : RedeemInstance) : List Bytes × Bytes × Bytes × Bytes × Bytes :=
  (x.anchors.map (·.digest), x.nf, x.ctxIss, x.ctxRed, x.challengeDigest)

/-- **The freshness of the bound on `ε_hit`**: the operation's statement is well-formed, and each
simulated statement of its relation is well-formed and differs from it in a hashed field. -/
def FreshOk (p₁ : Option (IssueInstance × Bytes)) (p₂ : Option (RedeemInstance × Bytes)) :
    MOp → Prop
  | .issue req ci => WfI (stOfI req ci) ∧ ∀ y, p₁ = some y → WfI y.1 ∧ stOfI req ci ≠ y.1
  | .redeem S' req ci cr cd => WfR (stOfR S' req ci cr cd) ∧
      ∀ y, p₂ = some y → WfR y.1 ∧ hashedR (stOfR S' req ci cr cd) ≠ hashedR y.1

lemma FreshOk.freshOp {p₁ : Option (IssueInstance × Bytes)} {p₂ : Option (RedeemInstance × Bytes)}
    {op : MOp} (h : FreshOk p₁ p₂ op) : FreshOp p₁ p₂ op := by
  cases op with
  | issue req ci => exact fun y hy => (h.2 y hy).2
  | redeem S' req ci cr cd => exact fun y hy he => (h.2 y hy).2 (by rw [he])

/-! ## The statements' `H₂⁰` inputs -/

lemma muIn_stI (x : IssueInstance) : muIn (Privacy.Moussaka.stI x) =
    (toBA x.encode ++ toBA (makeDst "mous" 0 'i' '0')).push 8 := by
  simp [muIn, Privacy.Moussaka.stI, moussakaIssue, toL_toBA]

lemma muIn_stR (x : RedeemInstance) : muIn (Privacy.Moussaka.stR x) =
    (toBA x.encode ++ toBA (makeDst "mous" 0 'r' '0')).push 8 :=
  rfl

/-- **A well-formed issuance statement is determined by its `H₂⁰` input.** -/
lemma muIn_stI_inj {x y : IssueInstance} (hx : WfI x) (hy : WfI y)
    (h : muIn (Privacy.Moussaka.stI x) = muIn (Privacy.Moussaka.stI y)) : x = y := by
  rw [muIn_stI, muIn_stI] at h
  have h1 := toBA_inj ((ByteArray.append_left_inj _).1 (push_injective 8 h))
  obtain ⟨ht, hc⟩ := issueEncode_inj (hx.1.trans hy.1.symm) h1
  cases x
  cases y
  simp only at ht hc
  rw [ht, hc]

/-- **The hashed fields of a well-formed redemption statement are determined by its `H₂⁰`
input.** -/
lemma muIn_stR_inj {x y : RedeemInstance} (hx : WfR x) (hy : WfR y)
    (h : muIn (Privacy.Moussaka.stR x) = muIn (Privacy.Moussaka.stR y)) : hashedR x = hashedR y := by
  rw [muIn_stR, muIn_stR] at h
  have h1 := toBA_inj ((ByteArray.append_left_inj _).1 (push_injective 8 h))
  obtain ⟨h1, h2, h3, h4, h5⟩ := redeemEncode_inj hx.1 hy.1
    (lt_of_le_of_lt hx.2.1 (by decide)) (lt_of_le_of_lt hy.2.1 (by decide))
    (hx.2.2.1.trans hy.2.2.1.symm) (hx.2.2.2.1.trans hy.2.2.2.1.symm)
    (hx.2.2.2.2.1.trans hy.2.2.2.2.1.symm) h1
  simp only [hashedR, h1, h2, h3, h4, h5]

/-- **Issuance and redemption `H₂⁰` inputs differ** (the domain separators). -/
lemma muIn_stI_ne_stR (x : IssueInstance) (y : RedeemInstance) :
    muIn (Privacy.Moussaka.stI x) ≠ muIn (Privacy.Moussaka.stR y) := by
  rw [muIn_stI, muIn_stR]
  intro h
  have h1 := push_injective 8 h
  have hs := congrArg ByteArray.size h1
  have h7 : (toBA (makeDst "mous" 0 'i' '0')).size = 7 := by decide
  have h7' : (toBA (makeDst "mous" 0 'r' '0')).size = 7 := by decide
  simp only [ByteArray.size_append, h7, h7'] at hs
  have hd := toBA_inj (append_split h1 (by omega)).2
  revert hd
  decide

lemma size_muIn_stI {x : IssueInstance} (hx : WfI x) : (muIn (Privacy.Moussaka.stI x)).size = 69 := by
  have h7 : (toBA (makeDst "mous" 0 'i' '0')).size = 7 := by decide
  rw [muIn_stI]
  simp only [ByteArray.size_push, ByteArray.size_append, size_toBA, IssueInstance.encode,
    List.length_append, hx.1, hx.2, h7, uovM, ctxBytes]

lemma size_muIn_stR_le {x : RedeemInstance} (hx : WfR x) :
    (muIn (Privacy.Moussaka.stR x)).size ≤ 2152 := by
  have h7 : (toBA (makeDst "mous" 0 'r' '0')).size = 7 := by decide
  have hd : ∀ d ∈ x.anchors.map (·.digest), d.length = digestBytes := by
    simp only [List.mem_map]
    rintro d ⟨pk, hpk, rfl⟩
    exact hx.1 pk hpk
  have hn := hx.2.1
  rw [muIn_stR]
  simp only [ByteArray.size_push, ByteArray.size_append, size_toBA, RedeemInstance.encode,
    List.length_append, length_flatten_of_forall hd, List.length_map, hx.2.2.1, hx.2.2.2.1,
    hx.2.2.2.2.1, hx.2.2.2.2.2, h7, u32le, List.length_cons, List.length_nil]
  simp only [maxAnchors, digestBytes, nfBytes, ctxBytes, cdBytes] at hn ⊢
  omega

/-! ## The forgery -/

/-- **The forgery of an operation**: its statement and proof bytes. -/
def fd : MOp → FD
  | .issue req ci => (Privacy.Moussaka.stI (stOfI req ci), toBA (req.drop uovM))
  | .redeem S' req ci cr cd =>
      (Privacy.Moussaka.stR (stOfR S' req ci cr cd), toBA (req.drop nfBytes))

/-- The shortest table length that holds every chain input of the fresh forgeries:
`H₂¹` inputs of the redemption relation (`6293` bytes). -/
def Lmin : ℕ := 6293

variable {L M : ℕ}

lemma fd_fOk (hL : Lmin ≤ L) {p₁ : Option (IssueInstance × Bytes)}
    {p₂ : Option (RedeemInstance × Bytes)} {op : MOp} (h : FreshOk p₁ p₂ op) : FOk L (fd op).1 := by
  cases op with
  | issue req ci =>
    refine ⟨rfl, rfl, rfl, le_trans ?_ hL, le_trans ?_ hL, le_trans ?_ hL⟩
    · show 64 + 16 * pI.correctionBytes + pI.nMask * pI.nMultBytes + 16 + 0 + 1 ≤ Lmin
      decide
    · show 264 + 0 + pI.witnessBytes + 1 ≤ Lmin
      decide
    · simp only [fd, size_muIn_stI h.1, Lmin]
      omega
  | redeem S' req ci cr cd =>
    refine ⟨rfl, rfl, rfl, le_trans ?_ hL, le_trans ?_ hL, le_trans ?_ hL⟩
    · show 64 + 16 * pR.correctionBytes + pR.nMask * pR.nMultBytes + 16 + 0 + 1 ≤ Lmin
      decide
    · show 264 + 0 + pR.witnessBytes + 1 ≤ Lmin
      decide
    · have := size_muIn_stR_le h.1
      simp only [fd, Lmin]
      omega

/-! ## The programmings, the hit, freshness -/

variable {R : Type} [CipherRow R]

/-- The issuance simulator's programming. -/
lemma simProgI : SimProg (R := R) (L := L) (M := M) (leanProgIX hbX)
    (fun i c => (Privacy.Moussaka.stI i, simulate pI c)) :=
  simProg_progRO Privacy.Moussaka.stI fun _ => rfl

/-- The redemption simulator's programming. -/
lemma simProgR : SimProg (R := R) (p := pI) (L := L) (M := M) (leanProgRX hbX)
    (fun i c => (Privacy.Moussaka.stR i, simulate pR c)) :=
  simProg_progRO (p := pR) Privacy.Moussaka.stR fun _ => rfl

/-- **A programmed point of the verifier is a hit of the forgery.** -/
lemma hitG_of_hitOpX (op : MOp) (t' t : ShT R pI L M) (h : HitOpX (Hb := hbX) op t' t) :
    HitG (fd op) t' t := by
  cases op with
  | issue req ci => exact hitG_of_hitPt _ _ t' t h
  | redeem S' req ci cr cd => exact hitG_of_hitPt (p := pR) _ _ t' t h

/-- **A fresh forgery's `H₂⁰` input is not the simulated issuance's.** -/
lemma fresh_ne₁ (x₁ : Option IssueInstance) (c₁ : SimCoins pI)
    (p₂ : Option (RedeemInstance × Bytes)) (op : MOp) (i : IssueInstance)
    (hfr : FreshOk (pairO x₁ (simO (simI' (leanSim pI)) x₁ c₁)) p₂ op) (hi : x₁ = some i) :
    muIn (fd op).1 ≠ muIn (Privacy.Moussaka.stI i) := by
  subst hi
  intro hm
  cases op with
  | issue req ci =>
    obtain ⟨hw, hne⟩ := hfr.2 (i, leanSim pI i c₁) rfl
    exact hne (muIn_stI_inj hfr.1 hw hm)
  | redeem S' req ci cr cd => exact muIn_stI_ne_stR _ _ hm.symm

/-- **A fresh forgery's `H₂⁰` input is not the simulated redemption's.** -/
lemma fresh_ne₂ (p₁ : Option (IssueInstance × Bytes)) (x₂ : Option RedeemInstance)
    (c₂ : SimCoins pR) (op : MOp) (i : RedeemInstance)
    (hfr : FreshOk p₁ (pairO x₂ (simO (simR' (leanSim pR)) x₂ c₂)) op) (hi : x₂ = some i) :
    muIn (fd op).1 ≠ muIn (Privacy.Moussaka.stR i) := by
  subst hi
  intro hm
  cases op with
  | issue req ci => exact muIn_stI_ne_stR _ _ hm
  | redeem S' req ci cr cd =>
    obtain ⟨hw, hne⟩ := hfr.2 (i, leanSim pR i c₂) rfl
    exact hne (muIn_stR_inj hfr.1 hw hm)

/-- **`ε_hit` for the Lean verifiers and simulators of Moussaka, with the chain hashes random
tables.** With `H₂⁰`, `H₂¹`, `H₂²` uniform tables on the inputs of at most `L ≥ 6293` bytes
(`hbX`), against adversaries that read them with `q_μ`, `q₂₁`, `q₂₂` queries (`AdmHit`), a fresh
forgery (`FreshOk`) hits a programmed `H₂³` point with probability

    ≤ 2·((q_μ+3)·2⁻²⁵⁶ + (q₂₁+3)·2⁻¹⁰⁸⁸ + (q₂₂+3)·2⁻⁴⁴⁸)

(`progEv_chain`). -/
theorem progEv_hit [Fintype R] [Nonempty R] (hL : Lmin ≤ L) (qMu q21 q22 : ℕ) :
    ProgEv (simI' (leanSim pI)) (leanProgIX (R := R) hbX) (simR' (leanSim pR)) (leanProgRX hbX)
      FreshOk (HitOpX (R := R) (Hb := hbX))
      (AdmHit (R := R) (p := pI) (L := L) (M := M) (G := Tab3) qMu q21 q22)
      (epsHit qMu q21 q22) :=
  progEv_chain (R := R) (G := Tab3) (sim₁ := simI' (leanSim pI)) (sim₂ := simR' (leanSim pR))
    simProgI simProgR fd (Fresh := FreshOk) (fun _ _ _ h => fd_fOk hL h) hitG_of_hitOpX
    (fun x₁ c₁ p₂ op i hfr hi _ => by
      dsimp only
      exact fresh_ne₁ x₁ c₁ p₂ op i hfr hi)
    (fun p₁ x₂ c₂ op i hfr hi _ => by
      dsimp only
      exact fresh_ne₂ p₁ x₂ c₂ op i hfr hi) qMu q21 q22

/-! ## In the game -/

section Game

variable {G S : Type} (A : Thief G S)

/-- **The adversaries of the bound.** The lengths the C++ types fix and the spec's byte lists do
not: the Anchor Sets the adversary chooses have 32-byte digests, its challenge digests have 32
bytes, and its redemptions have 16-byte contexts. And the digest names the key: a redemption
whose Anchor Set has the digests of the Client's is under the Client's set (in C++ the digest is
SHAKE256 of the key; in the spec a key is any digest with any map). -/
def HitWf : Prop :=
  (∀ req, (∀ pk ∈ (A.choose req).1.keys, pk.digest.length = digestBytes) ∧
    (A.choose req).2.length = cdBytes) ∧
  ∀ o₁ o₂ g₁ g₂ s S' req ci cr cd, A.out o₁ o₂ g₁ g₂ s = .redeem S' req ci cr cd →
    (∀ pk ∈ S'.keys, pk.digest.length = digestBytes) ∧ ci.length = ctxBytes ∧
      cr.length = ctxBytes ∧ cd.length = cdBytes ∧
      (S'.keys.map (·.digest) = (A.choose o₁).1.keys.map (·.digest) →
        S'.keys = (A.choose o₁).1.keys)

lemma xR_some {nf t req : Bytes} {x : RedeemInstance} (h : xR A nf t req = some x) :
    x = ⟨(A.choose req).1.keys, nf, A.ci, A.cr, (A.choose req).2⟩ := by
  unfold xR at h
  split_ifs at h
  cases hf : findIssuer (A.choose req).1 t (sig A req) with
  | none => rw [hf] at h; cases h
  | some i =>
    rw [hf] at h
    cases h
    rfl

/-- **In the game, an accepted operation that is fresh is `FreshOk`.** The Client's statements
are well-formed (its `t`, `nf` and the adversary's contexts have the right lengths; the Anchor Set
and digest are the adversary's, `HitWf`); an accepted issuance has the lengths the API checks;
a redemption that differs from the Client's differs in a hashed field (`HitWf`). -/
lemma freshOk_of_game (hw : HitWf A) {verI : IssueInstance → Bytes → S → Bool}
    {verR : RedeemInstance → Bytes → S → Bool} {t nf : Bytes} (ht : t.length = uovM)
    (hn : nf.length = nfBytes) (o₁ : Bytes) (o₂ : Except Error Bytes) (g₁ g₂ : G) (s : S)
    (π₁ π₂ : Option Bytes) (hacc : AccOp verI verR (A.out o₁ o₂ g₁ g₂ s) s)
    (hfr : FreshOp (pairO (some ⟨t, A.ci⟩) π₁) (pairO (xR A nf t o₁) π₂) (A.out o₁ o₂ g₁ g₂ s)) :
    FreshOk (pairO (some ⟨t, A.ci⟩) π₁) (pairO (xR A nf t o₁) π₂) (A.out o₁ o₂ g₁ g₂ s) := by
  have hci : A.ci.length = ctxBytes := List.length_ofFn
  have hcr : A.cr.length = ctxBytes := List.length_ofFn
  cases hop : A.out o₁ o₂ g₁ g₂ s with
  | issue req ci =>
    rw [hop] at hacc hfr
    obtain ⟨hl, hc, -⟩ := (accOp_issue verI verR req ci s).1 hacc
    refine ⟨⟨by simp [stOfI, hl, issueRequestBytes], hc⟩, fun y hy => ⟨?_, hfr y hy⟩⟩
    rcases π₁ with _ | π
    · cases hy
    · cases hy
      exact ⟨ht, hci⟩
  | redeem S' req ci cr cd =>
    rw [hop] at hacc hfr
    obtain ⟨hl, -⟩ := (accOp_redeem verI verR S' req ci cr cd s).1 hacc
    obtain ⟨hd, hc1, hc2, hc3, hk⟩ := hw.2 o₁ o₂ g₁ g₂ s S' req ci cr cd hop
    refine ⟨⟨hd, S'.valid.2.1, by simp [stOfR, hl, redeemRequestBytes], hc1, hc2, hc3⟩,
      fun y hy => ?_⟩
    rcases hx : xR A nf t o₁ with _ | x
    · rw [hx] at hy
      cases hy
    rcases π₂ with _ | π
    · rw [hx] at hy
      cases hy
    rw [hx] at hy
    cases hy
    have ex := xR_some A hx
    subst ex
    refine ⟨⟨(hw.1 o₁).1, (A.choose o₁).1.valid.2.1, hn, hci, hcr, (hw.1 o₁).2⟩, fun he => ?_⟩
    simp only [hashedR, stOfR, Prod.mk.injEq] at he
    obtain ⟨e1, e2, e3, e4, e5⟩ := he
    refine hfr _ (by rw [hx]; rfl) ?_
    simp only [stOfR, hk e1, e2, e3, e4, e5]

variable (verI : IssueInstance → Bytes → S → Bool) (verR : RedeemInstance → Bytes → S → Bool)
  (ext : Ext G S) {CI CR : Type} (simI : IssueInstance → CI → Bytes)
  (progI : IssueInstance → CI → S → S) (simR : RedeemInstance → CR → Bytes)
  (progR : RedeemInstance → CR → S → S) [Fintype CI] [Fintype CR] [Fintype G] [Fintype S]

/-- **`sim_se_le` for `FreshOk`**, for `HitWf` adversaries. -/
theorem sim_se_le_ok (hw : HitWf A) {AdmE : (G → G → S → MOp) → Prop} {εSE : ℝ}
    (hse : WeakSE2 (simI' simI) progI (simR' simR) progR (AccOp verI verR) FreshOk RelOp ext AdmE
      εSE) (hAE : ∀ o₁ o₂, AdmE (A.out o₁ o₂)) :
    pr ((Sec × (CI × G)) × ((CR × G) × S))
        (simG (fun ω => simIssP A simI (tOf A ω)) (fun ω => pgIP A progI (tOf A ω))
          (fun ω => simRedP A simR (List.ofFn ω.1) (tOf A ω))
          (fun ω => pgRP A progR (List.ofFn ω.1) (tOf A ω)) (seEv A verI verR ext)) ≤ εSE := by
  have h := hse Sec (fun ω => some ⟨tOf A ω, A.ci⟩)
    (fun ω π₁ => xR A (List.ofFn ω.1) (tOf A ω) (reqI (tOf A ω) π₁))
    (fun ω π₁ π₂ => A.out (reqI (tOf A ω) π₁)
      (reqR A (List.ofFn ω.1) (tOf A ω) (reqI (tOf A ω) π₁) π₂))
    fun _ _ _ => hAE _ _
  refine (Privacy.pr_mono fun z hz => ?_).trans h
  have h1 := stI_simIss A simI (tOf A z.1.1) (length_com _ _ _ _) z.1.2.1
  have h2 := stR_simRed A simR (List.ofFn z.1.1.1) (tOf A z.1.1) (simIssP A simI (tOf A z.1.1) z.1.2.1)
    List.length_ofFn z.2.1.1
  simp only [simG, seEv, accE, freshE, relE, h1, h2] at hz
  exact ⟨hz.1, freshOk_of_game A hw (length_com _ _ _ _) List.length_ofFn _ _ _ _ _ _ _ hz.1 hz.2.1,
    hz.2.2⟩

variable (PI : Bytes → IssueInstance → Bytes → G → S → Bytes)
  (PR : Bytes → RedeemInstance → Bytes → G → S → Bytes)

/-- **Redemption non-malleability with weak simulation-extractability for `FreshOk`**
(`noRedirect`, whose `WeakSE2` is for `FreshOp`), for `HitWf` adversaries. -/
theorem noRedirect_ok [Nonempty CI] [Nonempty CR] [Nonempty G] [Nonempty S] (hw : HitWf A)
    {AdmI : (Bytes → G → S → Prop) → Prop} {AdmR : (Bytes → G → S → Prop) → Prop}
    {AdmE : (G → G → S → MOp) → Prop} {εI εR εSE : ℝ}
    (hzkI : ZeroKnowledgeRO IssueRelW (fun x w (ρ : Coins proveSeedBytes) g s => PI w x (List.ofFn ρ) g s)
      simI progI AdmI εI) (hεI : 0 ≤ εI)
    (hzkR : ZeroKnowledgeRO RedeemRelW (fun x w (ρ : Coins proveSeedBytes) g s => PR w x (List.ofFn ρ) g s)
      simR progR AdmR εR) (hεR : 0 ≤ εR)
    (hAI : ∀ ω r₂ g₂, AdmI (distI A PR verI verR ext ω r₂ g₂))
    (hAR : ∀ ω c₁ g₁, AdmR (distR A verI verR ext simI progI ω c₁ g₁))
    (hse : WeakSE2 (simI' simI) progI (simR' simR) progR (AccOp verI verR) FreshOk RelOp ext AdmE
      εSE) (hAE : ∀ o₁ o₂, AdmE (A.out o₁ o₂)) :
    pr _ (nmReal A PI PR verI verR ext) ≤
      εI + εR + pr _ (deltaR A PR simI progI) + εSE +
        owAdv A.ci A.cr (inverter A ext simI progI simR progR) :=
  noRedirect_of_se A PI PR verI verR ext simI progI simR progR hzkI hεI hzkR hεR hAI hAR
    (sim_se_le_ok A verI verR ext simI progI simR progR hw hse hAE)

end Game

end VoleMole.Theft.Hit.Mous

namespace VoleMole.Theft.Moussaka

open VoleMole.Privacy VoleMole.ZK.Sim VoleMole.Verifier VoleMole.Verifier.Bridge
open VoleMole.Privacy.Moussaka VoleMole.Spec VoleMole.Spec.Moussaka

variable {R : Type} [CipherRow R] {L M : ℕ}

/-- **Redemption non-malleability with the other hashes random tables and `ε_hit` bounded.** As
`noRedirect_leanX_plain` with the concrete extra table `XTab L M` (`hbX`, `L ≥ 6293`), the
programming term bounded by `Hit.Mous.progEv_hit`: for a `HitWf` adversary whose last stage reads
`(a₃, a₅, a_E)` and the chain tables with `(q_μ, q₂₁, q₂₂)` queries (`AdmHit`, implied by its
class `Adm`), and an extractor `extOf e` that reads `(x₃, x₅, x_E)`,

    Pr[Bad] ≤ εz(pI; q) + εz(pR; q) + δ_R + ε_plain
      + 2·((q_μ+3)·2⁻²⁵⁶ + (q₂₁+3)·2⁻¹⁰⁸⁸ + (q₂₂+3)·2⁻⁴⁴⁸) + Adv^ow(inverter),

`q = (a₃ + x₃, a₅ + x₅ + 936, a_E + x_E + 9214)`. Plain extraction (`hplain`) stays a hypothesis,
against a class `Adm₀` that contains the last stage composed with both programmings (`hadm`). -/
theorem noRedirect_leanX_hit [Fintype R] [Nonempty R] [ZKRow R]
    (A : Thief Tab3 (ShX R pI (XTab L M))) (hw : Hit.Mous.HitWf A) (hL : Hit.Mous.Lmin ≤ L)
    {e : Option (IssueInstance × Bytes) → Option (RedeemInstance × Bytes) → MOp → Tab3 → Tab3 →
      (Tab5F × (Blk → R)) × XTab L M → Bytes}
    {Adm Adm₀ : (Tab3 → Tab3 → ShX R pI (XTab L M) → MOp) → Prop} {ε₀ : ℝ}
    {a3 a5 aE x3 x5 xE qMu q21 q22 : ℕ}
    (hA : ∀ o₁ o₂, StageBudgetX (A.out o₁ o₂) a3 a5 aE)
    (hX : ∀ o₁ o₂, StageBudgetX (extOf e (stI A o₁) (stR A o₁ o₂) (A.out o₁ o₂)) x3 x5 xE)
    (hplain : PlainSE (AccOp (verILX hbX) (verRLX hbX)) FreshOp RelOp e Adm₀ ε₀)
    (hAdm : ∀ o₁ o₂, Adm (A.out o₁ o₂)) (hAH : ∀ F, Adm F → Hit.AdmHit qMu q21 q22 F)
    (hadm : ∀ F x₁ c₁ x₂ c₂, Adm F → Adm₀ (fun g₁ g₂ t =>
      F g₁ g₂ (progT (leanProgIX hbX) (leanProgRX hbX) x₁ c₁ x₂ c₂ t))) :
    pr _ (nmReal A (leanPIX hbX) (leanPRX hbX) (verILX hbX) (verRLX hbX) (extOf e)) ≤
      ZKRow.εz R pI (a3 + x3) (a5 + x5 + 936) (aE + xE + 9214) +
        ZKRow.εz R pR (a3 + x3) (a5 + x5 + 936) (aE + xE + 9214) +
        pr _ (deltaR A (leanPRX hbX) (leanSim pI) (leanProgIX hbX)) +
        (ε₀ + Hit.epsHit qMu q21 q22) +
        owAdv A.ci A.cr (inverter A (extOf e) (leanSim pI) (leanProgIX hbX) (leanSim pR)
          (leanProgRX hbX)) :=
  Hit.Mous.noRedirect_ok (CI := SimCoins pI) (CR := SimCoins pR) A (verILX hbX) (verRLX hbX)
    (extOf e) (leanSim pI) (leanProgIX hbX) (leanSim pR) (leanProgRX hbX) (leanPIX hbX)
    (leanPRX hbX) hw (leanPIX_zkRO hbX_wf _ _ _) (ZKRow.εz_nonneg _ _ _ _)
    (leanPRX_zkRO hbX_wf _ _ _) (ZKRow.εz_nonneg _ _ _ _)
    (distI_budgetX A (fun x => extOf fun p₁ p₂ o g₁ g₂ b => e p₁ p₂ o g₁ g₂ (b, x)) hbX_wf hA
      (fun x o₁ o₂ => hX o₁ o₂ x))
    (distR_budgetX hbX A (fun x => extOf fun p₁ p₂ o g₁ g₂ b => e p₁ p₂ o g₁ g₂ (b, x)) hA
      (fun x o₁ o₂ => hX o₁ o₂ x))
    (weakSE2_of_plain (hplain.fresh_mono fun _ _ _ h => h.freshOp)
      (progMoves_of_ev (fun _ _ _ => rfl) (fun _ _ _ => rfl) (accOp_movesX (R := R) hbX)
        ((Hit.Mous.progEv_hit hL qMu q21 q22).mono hAH))
      (fun _ _ _ => rfl) (fun _ _ _ => rfl) hadm) hAdm

end VoleMole.Theft.Moussaka
