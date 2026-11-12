import VoleMole.ROM.OneMore
import VoleMole.ROM.SpecSound
import VoleMole.Arith.GF256Field

open OracleComp OracleSpec
open scoped ENNReal

namespace VoleMole.ROM.OneMore.Pomfrit

open VoleMole.Prob VoleMole.Arith VoleMole.Verifier VoleMole.ROM VoleMole.ROM.IC
open VoleMole.EndToEnd VoleMole.EndToEnd.SpecRel

/-! ## Targets, the statement with a given target, the relation -/

/-- A target `h ∈ GF(256)^45`. -/
abbrev TG := Fin 45 → GF256

noncomputable instance : SampleableType TG := SampleableType.ofFintype _

/-- A target as 45 bytes. -/
def encT (a : TG) : ByteArray := toBA (List.ofFn fun i => (a i).val)

/-- **PomFRIT redemption with the target function `h`** (`pomfritRedeem` with `h` in place of
`hash_to_target` at the verifier's `chal1`, and the binders given). -/
def pomfritRedeemT (pk : UovPk) (h : ByteArray → ByteArray) (b1 b2 : ByteArray)
    (labelRows : Bool) : Statement :=
  { params := pomfritParams labelRows
    dst := toBA (Spec.makeDst "pomf" 0 'p' '0')
    delayed := true
    binder1 := b1
    binder2 := b2
    instEnc := fun c1 => pk.digest ++ h c1
    comb := some (45, toBA (Spec.makeDst "pomf" 0 'l' '0'))
    values := fun c1 lb w =>
      UovEval.pomfritRedeemValues 119 45 pk.map (fun k => ⟨fnOf (h c1) k.val⟩)
        (combinationOf 45 lb) w }

@[simp] lemma pomfritRedeemT_params (pk : UovPk) (h : ByteArray → ByteArray) (b1 b2 : ByteArray)
    (lr : Bool) : (pomfritRedeemT pk h b1 b2 lr).params = pomfritParams lr := rfl

/-- `pomfritRedeem` is `pomfritRedeemT` at `hash_to_target`. -/
theorem pomfritRedeem_eq_T (pk : UovPk) (sig msg : ByteArray) (lr : Bool) :
    pomfritRedeem pk sig msg lr = pomfritRedeemT pk
      (fun c1 => pomfritTarget (pomfritParams lr) pk.digest c1 sig msg)
      (sig.extract (pomfritParams lr).proofBytes ((pomfritParams lr).proofBytes + 32))
      (sig.extract ((pomfritParams lr).proofBytes + 32) ((pomfritParams lr).proofBytes + 64))
      lr := rfl

/-- The Issuer's answer: a preimage, or `none` (pqov's signer failed). -/
abbrev SIss := Option Spec.Bytes

/-- **Def. 3.1's relation**: `s` is a 119-byte preimage of `t` under the public map. -/
def relP (pk : UovPk) (s : SIss) (t : TG) : Prop :=
  ∃ σ, s = some σ ∧ σ.length = 119 ∧ pk.toSpec.eval σ = toL (encT t)

/-! ## The forger and its oracles -/

/-- The forger's oracles: the hashes and the cipher (`specIC`), `hash_to_target` (`H_T`, inputs
the byte strings, answers a target), and the Issuer (targets to preimages). -/
abbrev AnsU : DomIC ⊕ (ByteArray ⊕ TG) → Type := Sum.elim AnsIC (Sum.elim (fun _ => TG) fun _ => SIss)

abbrev specU : OracleSpec (DomIC ⊕ (ByteArray ⊕ TG)) := OracleSpec.ofFn AnsU

/-- The composed adversary's oracles (`OneMore.specA` at PomFRIT's types), with hints `Hn`. -/
abbrev specC (Hn : Type) := specA Ans ByteArray Hn TG SIss

variable {Hn : Type}

/-- A hash query of the composed adversary. -/
def liftW : QueryImpl spec (OracleComp (specC Hn)) := fun d =>
  (liftM ((specC Hn).query (.inl d)) : OracleComp (specC Hn) (Ans d))

/-- A computation against the hashes, as one of the composed adversary. -/
def toC {α : Type} (oa : OracleComp spec α) : OracleComp (specC Hn) α := simulateQ liftW oa

/-- **The wrapper**: the forger's hash queries go to the world oracle, its cipher queries are
answered by the table `E`, both logged (in order); its `H_T` query `x` goes to the target oracle
with the hint `hint L x` computed from the log `L` so far; its Issuer queries are forwarded. -/
def wrapImpl (E : CTable) (hint : QueryLog specIC → ByteArray → Hn) :
    QueryImpl specU (StateT (QueryLog specIC) (OracleComp (specC Hn)))
  | .inl (.inl d) => StateT.mk fun L => (fun u => (u, L ++ [⟨.inl d, u⟩])) <$>
      (liftM ((specC Hn).query (.inl d)) : OracleComp (specC Hn) (Ans d))
  | .inl (.inr x) => StateT.mk fun L => pure (E x, L ++ [⟨.inr x, E x⟩])
  | .inr (.inl x) => StateT.mk fun L => (fun a => (a.1, L)) <$>
      (liftM ((specC Hn).query (.inr (.inl (x, hint L x)))) : OracleComp (specC Hn) (TG × Hn))
  | .inr (.inr t) => StateT.mk fun L => (fun s => (s, L)) <$>
      (liftM ((specC Hn).query (.inr (.inr t))) : OracleComp (specC Hn) SIss)

/-! ## The verification of one forgery -/

/-- The verifier's steps up to `chal1` (as in `verifyQ`). -/
def chal1Pre (st : Statement) (proof : ByteArray) : OracleComp spec (Option ByteArray) := do
  let pf : Proof := { params := st.params, bytes := proof }
  if !pf.checkFormat then return none
  let mu1 ← mu1Q st
  let iv ← hashQ .h4 ((pf.ivPre ++ mu1).push 4)
  match BAVC.reconstruct iv pf.opening pf.delta with
  | none => return none
  | some leaves =>
    let lh ← (BAVC.leafHashInputs leaves.coms).mapM (hashQ .h1)
    let com ← hashQ .h1 (BAVC.comInput lh)
    let c1 ← hashQ .h21 (chal1Input pf mu1 com st.binder1)
    return some c1

/-- **`hash_to_target`'s input** for the signature `sig` on `msg` at the verifier's `chal1`
(`pomfritTarget` hashes it with SHAKE128). -/
def tgtIn (pk : UovPk) (lr : Bool) (sig msg c1 : ByteArray) : ByteArray :=
  let pf : Proof := { params := pomfritParams lr, bytes := sig.extract 0 (pomfritParams lr).proofBytes }
  toBA (Spec.PomFRIT.targetInput (toL pk.digest) (toL c1) (toL pf.voleCheck)
    (toL (pf.correction.extract 0 45)) (toL msg))

lemma pomfritTarget_eq_tgtIn (pk : UovPk) (lr : Bool) (sig msg c1 : ByteArray) :
    pomfritTarget (pomfritParams lr) pk.digest c1 sig msg =
      toBA (Spec.shake128B (toL (tgtIn pk lr sig msg c1)) 45) := by
  simp only [pomfritTarget, tgtIn, toL_toBA]

/-- The decoded preimages `s` (witness bytes `[45, 164)`) of the known trees' candidates, in tree
order. -/
noncomputable def candidates (E : CTable) (st : Statement) (r : Out (Unit × QueryLog specIC)) :
    List Spec.Bytes :=
  letI : HasPrg := VoleMole.ZK.Sim.icPrg E.cipher
  ((List.finRange BAVC.tau).filter (· ∈ r.2.1.known)).map fun i =>
    bytesOf (bitsOf (candidate (F := GF128) ((outChain r).u st) ((outChain r).dc st) i)) 45 119

/-- The first candidate that is a preimage of one of the targets `ts`. -/
def pick (pk : UovPk) (ts : List TG) (cs : List Spec.Bytes) : SIss :=
  cs.find? fun σ => decide (σ.length = 119 ∧ ∃ t ∈ ts, pk.toSpec.eval σ = toL (encT t))

variable (T : CrtTables) (lr : Bool) (E : CTable) (hint : QueryLog specIC → ByteArray → Hn)
  (tgts : TG × Hn → List TG) (pk : UovPk)

/-- **The verification of one forgery `(msg, sig)`** (`pomfritVerify` with `hash_to_target` the
target oracle), followed by the straight-line extractor on the forger's log `L`. Returns the
claim (the `H_T` input `x` and a candidate preimage of one of `tgts (H_T(x), hint)`) and the
verifier's decision. -/
noncomputable def verOne (L : QueryLog specIC) (msg sig : ByteArray) :
    OracleComp (specC Hn) ((ByteArray × SIss) × Bool) := do
  let n := (pomfritParams lr).proofBytes
  let proof := sig.extract 0 n
  let b1 := sig.extract n (n + 32)
  let b2 := sig.extract (n + 32) (n + 64)
  if toBA (Spec.PomFRIT.commitRefresher (toL b2)) != b1 then return ((ByteArray.empty, none), false)
  let oc1 ← toC (chal1Pre (pomfritRedeemT pk (fun _ => ByteArray.empty) b1 b2 lr) proof)
  match oc1 with
  | none => return ((ByteArray.empty, none), false)
  | some c1 =>
    let x := tgtIn pk lr sig msg c1
    let ah ← (liftM ((specC Hn).query (.inr (.inl (x, hint L x)))) : OracleComp (specC Hn) (TG × Hn))
    let st := pomfritRedeemT pk (fun _ => encT ah.1) b1 b2 lr
    let ex ← toC (extractIC st E ((proof, ()), L))
    let t ← toC (@verifyQ (VoleMole.ZK.Sim.icPrg E.cipher) T st proof)
    pure ((x, pick pk (tgts ah) (candidates E st (ex.1, ex.2, t))), t.accept)

/-- Every forgery, in order. -/
noncomputable def verAll (L : QueryLog specIC) :
    List (ByteArray × ByteArray) → OracleComp (specC Hn) (List ((ByteArray × SIss) × Bool))
  | [] => pure []
  | (m, sg) :: rest => do
    let v ← verOne T lr E hint tgts pk L m sg
    let vs ← verAll L rest
    pure (v :: vs)

/-- The forger: from the Issuer's public key, `ℓ + 1` message–signature pairs. -/
abbrev Forger := UovPk → OracleComp specU (List (ByteArray × ByteArray))

/-- **The composed adversary**: the forger (wrapped), then the verification and extraction of its
forgeries. The flag: every forgery verifies, the messages are pairwise distinct, and there are
`ℓ + 1` of them. -/
noncomputable def Acomp (ℓ : ℕ) (A : Forger) :
    OracleComp (specC Hn) (List (ByteArray × SIss) × Bool) := do
  let r ← (simulateQ (wrapImpl E hint) (A pk)).run []
  let vs ← verAll T lr E hint tgts pk r.2 r.1
  pure (vs.map Prod.fst,
    decide ((∀ v ∈ vs, v.2 = true) ∧ (r.1.map Prod.fst).Nodup ∧ r.1.length = ℓ + 1))

/-! ## The games and the two reductions -/

section Games

variable {K : Type} (KG : ProbComp (UovPk × K)) (pre : K → TG → SIss) (n ℓ : ℕ) (T : CrtTables)
  (lr : Bool) (A : Forger)

/-- The composed adversary with its cipher table drawn uniformly, for the hint rule `hint E`. -/
noncomputable def advC (hint : CTable → QueryLog specIC → ByteArray → Hn)
    (tgts : TG × Hn → List TG) (pk : UovPk) :
    ProbComp (OracleComp (specC Hn) (List (ByteArray × SIss) × Bool)) := do
  let E ← $ᵗ CTable
  pure (Acomp T lr E (hint E) tgts pk ℓ A)

/-- **The one-more forgery game for PomFRIT** with the Issuer `pre sk` (any key generation `KG`
and signer `pre`; the honest Issuer is pqov's `derive_preimage`): the forger runs against the
hashes and the ideal cipher (random oracles, a uniform cipher table), `hash_to_target` (a random
oracle fed by `n` uniform targets, see `OneMore.omuf`) and the Issuer; its forgeries are then
verified. The hint rule `hint` (E₁ for U1, the shift lists for U2) and the target rule `tgts` only
feed the analysis: the forger never sees a hint, and the targets only choose which extracted
candidate is reported. -/
noncomputable def game (φ : Hn → TG ≃ TG) (hint : CTable → QueryLog specIC → ByteArray → Hn)
    (tgts : TG × Hn → List TG) :=
  omuf KG pre n φ (advC ℓ T lr A hint tgts)

/-- **The forger wins**: every one of its `ℓ + 1` forgeries verifies, on pairwise distinct
messages, after at most `ℓ` Issuer queries. -/
def PomWin (r : UovPk × (List (ByteArray × SIss) × Bool) × (ByteArray → Option (TG × Hn)) ×
    Ch Ans ByteArray Hn TG) : Prop :=
  r.2.1.2 = true ∧ r.2.2.2.iq ≤ ℓ

end Games

/-! ## Support facts: accepted forgeries on distinct messages have distinct `H_T` inputs -/

section Support

theorem support_toC {α : Type} (oa : OracleComp spec α) :
    support (toC (Hn := Hn) oa) ⊆ support oa := by
  induction oa using OracleComp.inductionOn with
  | pure x => simp [toC]
  | query_bind t k ih =>
    intro x hx
    simp only [toC, simulateQ_bind, simulateQ_spec_query] at hx
    rw [mem_support_bind_iff] at hx ⊢
    obtain ⟨u, -, hu⟩ := hx
    exact ⟨u, mem_support_query t u, ih u hu⟩

lemma size_of_checkFormat {pf : Proof} (h : pf.checkFormat = true) :
    pf.bytes.size = pf.params.proofBytes := by
  unfold Proof.checkFormat at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  exact h.1

lemma size_of_mem_hashQ {k : Kind} {x c : ByteArray} (h : c ∈ support (hashQ k x)) :
    c.size = k.outLen := by
  simp only [hashQ, support_map, Set.mem_image] at h
  obtain ⟨u, -, rfl⟩ := h
  show (Array.ofFn u).size = _
  rw [Array.size_ofFn]

lemma chal1Pre_some {st : Statement} {proof c1 : ByteArray}
    (h : some c1 ∈ support (chal1Pre st proof)) :
    c1.size = 136 ∧ ({ params := st.params, bytes := proof } : Proof).checkFormat = true := by
  unfold chal1Pre at h
  by_cases hf : ({ params := st.params, bytes := proof } : Proof).checkFormat = true
  · refine ⟨?_, hf⟩
    simp only [hf, Bool.not_true, Bool.false_eq_true, ite_false] at h
    rw [mem_support_bind_iff] at h
    obtain ⟨mu1, -, h⟩ := h
    rw [mem_support_bind_iff] at h
    obtain ⟨iv, -, h⟩ := h
    split at h
    · simp at h
    · rw [mem_support_bind_iff] at h
      obtain ⟨lh, -, h⟩ := h
      rw [mem_support_bind_iff] at h
      obtain ⟨com, -, h⟩ := h
      rw [mem_support_bind_iff] at h
      obtain ⟨c, hc, h⟩ := h
      simp only [support_pure, Set.mem_singleton_iff, Option.some.injEq] at h
      subst h
      exact size_of_mem_hashQ hc
  · simp [hf] at h

variable (T : CrtTables) (lr : Bool) (E : CTable) (hint : QueryLog specIC → ByteArray → Hn)
  (tgts : TG × Hn → List TG) (pk : UovPk)

set_option linter.constructorNameAsVariable false in
/-- An accepted forgery's claim is labelled by `hash_to_target`'s input at a 136-byte `chal1`, for a
proof of the right length. -/
lemma verOne_accept {L : QueryLog specIC} {m sg : ByteArray} {v : (ByteArray × SIss) × Bool}
    (hv : v ∈ support (verOne T lr E hint tgts pk L m sg)) (hacc : v.2 = true) :
    ∃ c1 : ByteArray, c1.size = 136 ∧
      (sg.extract 0 (pomfritParams lr).proofBytes).size = (pomfritParams lr).proofBytes ∧
      v.1.1 = tgtIn pk lr sg m c1 := by
  unfold verOne at hv
  dsimp only at hv
  split at hv
  · simp only [support_pure, Set.mem_singleton_iff] at hv
    subst hv
    simp at hacc
  · rw [mem_support_bind_iff] at hv
    obtain ⟨oc1, hoc1, hv⟩ := hv
    cases oc1 with
    | none =>
      simp only [support_pure, Set.mem_singleton_iff] at hv
      subst hv
      simp at hacc
    | some c1 =>
      generalize hC : chal1Pre _ _ = C at hoc1
      have h1 := support_toC (Hn := Hn) C hoc1
      subst hC
      obtain ⟨hc1, hfmt⟩ := chal1Pre_some h1
      rw [pomfritRedeemT_params] at hfmt
      refine ⟨c1, hc1, ?_, ?_⟩
      · have h3 := size_of_checkFormat hfmt
        exact h3
      simp only [mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hv
      obtain ⟨_, -, _, -, _, -, rfl⟩ := hv
      rfl

lemma field_vole (lr : Bool) :
    (pomfritParams lr).field? "vole_check" = some (if lr then 3075 else 2819, 64) := by
  cases lr <;> decide

lemma field_corr (lr : Bool) :
    (pomfritParams lr).field? "correction" = some (if lr then 3139 else 2883, 164) := by
  cases lr <;> decide

lemma proofBytes_pomfrit (lr : Bool) :
    (pomfritParams lr).proofBytes = if lr then 5579 else 5323 := by
  cases lr <;> decide

lemma size_voleCheck {lr : Bool} {b : ByteArray} (hb : b.size = (pomfritParams lr).proofBytes) :
    ({ params := pomfritParams lr, bytes := b } : Proof).voleCheck.size = 64 := by
  simp only [Proof.voleCheck, Proof.field, field_vole, ByteArray.size_extract, hb,
    proofBytes_pomfrit]
  cases lr <;> simp

lemma size_correction {lr : Bool} {b : ByteArray} (hb : b.size = (pomfritParams lr).proofBytes) :
    (({ params := pomfritParams lr, bytes := b } : Proof).correction.extract 0 45).size = 45 := by
  simp only [Proof.correction, Proof.field, field_corr, ByteArray.size_extract, hb,
    proofBytes_pomfrit]
  cases lr <;> simp

lemma toL_injective : Function.Injective toL := by
  intro a b h
  rw [VoleMole.Privacy.toL_eq, VoleMole.Privacy.toL_eq] at h
  exact ByteArray.ext (Array.toList_inj.1 h)

/-- **Distinct messages give distinct `hash_to_target` inputs**, for 136-byte `chal1`s and proofs
of the right length. -/
lemma tgtIn_inj {pk : UovPk} {lr : Bool} {sg sg' m m' c1 c1' : ByteArray}
    (hc : c1.size = 136) (hc' : c1'.size = 136)
    (hs : (sg.extract 0 (pomfritParams lr).proofBytes).size = (pomfritParams lr).proofBytes)
    (hs' : (sg'.extract 0 (pomfritParams lr).proofBytes).size = (pomfritParams lr).proofBytes)
    (h : tgtIn pk lr sg m c1 = tgtIn pk lr sg' m' c1') : m = m' := by
  have h' := congrArg toL h
  simp only [tgtIn, toL_toBA, Spec.PomFRIT.targetInput] at h'
  refine toL_injective (List.append_inj h' ?_).2
  simp only [List.length_append, VoleMole.Privacy.length_toL, hc, hc', size_voleCheck hs,
    size_voleCheck hs', size_correction hs, size_correction hs']

/-- The relation between a forgery and its verification result. -/
def AccLabel (pk : UovPk) (lr : Bool) (p : ByteArray × ByteArray) (v : (ByteArray × SIss) × Bool) :
    Prop :=
  v.2 = true → ∃ c1 : ByteArray, c1.size = 136 ∧
    (p.2.extract 0 (pomfritParams lr).proofBytes).size = (pomfritParams lr).proofBytes ∧
    v.1.1 = tgtIn pk lr p.2 p.1 c1

lemma verAll_support (L : QueryLog specIC) :
    ∀ (outs : List (ByteArray × ByteArray)) (vs : List ((ByteArray × SIss) × Bool)),
      vs ∈ support (verAll T lr E hint tgts pk L outs) → List.Forall₂ (AccLabel pk lr) outs vs
  | [], vs, h => by
    simp only [verAll, support_pure, Set.mem_singleton_iff] at h
    subst h
    exact List.Forall₂.nil
  | (m, sg) :: rest, vs, h => by
    simp only [verAll, mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at h
    obtain ⟨v, hv, vs', hvs', rfl⟩ := h
    exact List.Forall₂.cons (fun hacc => verOne_accept T lr E hint tgts pk hv hacc)
      (verAll_support L rest vs' hvs')

lemma forall₂_mem {α β : Type} {R : α → β → Prop} :
    ∀ {l₁ : List α} {l₂ : List β}, List.Forall₂ R l₁ l₂ → ∀ w ∈ l₂, ∃ q ∈ l₁, R q w
  | _, _, List.Forall₂.nil => fun _ hw => by simp at hw
  | _, _, List.Forall₂.cons (a := a) hab h => fun w hw => by
    rcases List.mem_cons.1 hw with rfl | hw
    · exact ⟨a, List.mem_cons_self .., hab⟩
    · obtain ⟨q, hq, hr⟩ := forall₂_mem h w hw
      exact ⟨q, List.mem_cons_of_mem _ hq, hr⟩

lemma labels_nodup {pk : UovPk} {lr : Bool} :
    ∀ {outs : List (ByteArray × ByteArray)} {vs : List ((ByteArray × SIss) × Bool)},
      List.Forall₂ (AccLabel pk lr) outs vs → (∀ v ∈ vs, v.2 = true) →
        (outs.map Prod.fst).Nodup → ((vs.map Prod.fst).map Prod.fst).Nodup
  | _, _, List.Forall₂.nil, _, _ => List.nodup_nil
  | _, _, List.Forall₂.cons (a := p) (b := v) hpv h, hacc, hnd => by
    simp only [List.map_cons, List.nodup_cons, List.mem_map] at hnd ⊢
    refine ⟨?_, labels_nodup h (fun w hw => hacc w (List.mem_cons_of_mem _ hw)) hnd.2⟩
    rintro ⟨⟨x, σ⟩, ⟨w, hw, hwx⟩, hx⟩
    obtain ⟨q, hq, hqw⟩ := forall₂_mem h w hw
    obtain ⟨c1, hc1, hs, hv1⟩ := hpv (hacc v List.mem_cons_self)
    obtain ⟨c1', hc1', hs', hw1⟩ := hqw (hacc w (List.mem_cons_of_mem _ hw))
    have := tgtIn_inj hc1' hc1 hs' hs (hw1.symm.trans ((congrArg Prod.fst hwx).trans (hx.trans hv1)))
    exact hnd.1 ⟨q, hq, this⟩

/-- **An accepted run of the composed adversary claims `ℓ + 1` distinct labels.** -/
lemma acomp_support (ℓ : ℕ) (A : Forger) {z : List (ByteArray × SIss) × Bool}
    (hz : z ∈ support (Acomp T lr E hint tgts pk ℓ A)) (hacc : z.2 = true) :
    z.1.length = ℓ + 1 ∧ (z.1.map Prod.fst).Nodup := by
  simp only [Acomp, mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hz
  obtain ⟨r, -, vs, hvs, rfl⟩ := hz
  simp only [decide_eq_true_eq] at hacc
  obtain ⟨hall, hnd, hlen⟩ := hacc
  have h2 := verAll_support T lr E hint tgts pk r.2 r.1 vs hvs
  exact ⟨by rw [List.length_map, ← h2.length_eq, hlen], labels_nodup h2 hall hnd⟩

end Support

/-! ## Theorems U1 and U2 -/

section Theorems

variable {K : Type} (KG : ProbComp (UovPk × K)) (pre : K → TG → SIss) (n ℓ : ℕ) (T : CrtTables)
  (lr : Bool) (A : Forger)

set_option linter.constructorNameAsVariable false in
lemma pomWin_forges {Hn : Type} (φ : Hn → TG ≃ TG) (hint : CTable → QueryLog specIC → ByteArray → Hn)
    (tgts : TG × Hn → List TG)
    {r : UovPk × (List (ByteArray × SIss) × Bool) × (ByteArray → Option (TG × Hn)) ×
      Ch Ans ByteArray Hn TG} (hr : r ∈ support (game KG pre n ℓ T lr A φ hint tgts))
    (hw : PomWin ℓ r) : Forges ℓ r.2.1 r.2.2.2 := by
  simp only [game, omuf, mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hr
  obtain ⟨kp, -, a, ha, L, -, r', hr', rfl⟩ := hr
  simp only [advC, mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at ha
  obtain ⟨E, -, rfl⟩ := ha
  have h1 : r'.1 ∈ support (Acomp T lr E (hint E) tgts kp.1 ℓ A) := by
    refine support_simulateQ_run'_subset (realImpl φ (pre kp.2))
      (Acomp T lr E (hint E) tgts kp.1 ℓ A) (fun _ => none, ch0 L) ?_
    rw [StateT.run'_eq, support_map]
    exact ⟨r', hr', rfl⟩
  obtain ⟨hlen, hnd⟩ := acomp_support T lr E (hint E) tgts kp.1 ℓ A h1 hw.1
  exact ⟨hw.1, hlen, hnd, hw.2⟩

/-- E₁'s targets: the target is the answer plus the hint. -/
def tgts1 : TG × TG → List TG := fun ah => [ah.1 + ah.2]

/-- **Theorem U1 (PomFRIT one-more unforgeability from Def. 3.1)**, for any first-phase rule
`e1` (Lemma P's `E₁`): the forger's win probability is at most the advantage of the reduction
`red addHint …` in Def. 3.1's experiment (`n` targets, at most `ℓ` preimage queries, `ℓ + 1`
preimages of distinct targets) plus, per forgery, the probability that it verifies but the claim
is not a preimage of its programmed target `H_T(x) + E₁(x)` (Lemma P's failure). -/
theorem pomfrit_U1 (e1 : CTable → QueryLog specIC → ByteArray → TG) :
    Pr{let r ← game KG pre n ℓ T lr A addHint e1 tgts1}[PomWin ℓ r] ≤
      Pr{let r ← omExp KG pre n (red addHint (advC ℓ T lr A e1 tgts1))}[
        Wins ℓ (goodPre relP) r.1 r.2.1 r.2.2] +
      ∑ i : Fin (ℓ + 1), Pr{let r ← game KG pre n ℓ T lr A addHint e1 tgts1}[
        BadAt (goodPre relP) i.val r] :=
  (prEvent_mono_of_support _ _ _ fun _ hr hw => pomWin_forges KG pre n ℓ T lr A _ _ _ hr hw).trans
    (omuf_le KG pre n ℓ addHint _ (goodPre relP))

/-- U2's targets: the answer plus each shift. -/
def tgts2 : TG × List TG → List TG := fun ah => ah.2.map (ah.1 + ·)

/-- U2's hint: the first `τ` shifts of the rule `sh`. -/
def hint2 (τ : ℕ) (sh : CTable → QueryLog specIC → ByteArray → List TG) :
    CTable → QueryLog specIC → ByteArray → List TG := fun E L x => (sh E L x).take τ

/-- **Theorem U2 (from the τ-shift assumption A-OMPR⊕τ)**, for any shift rule `sh` (Lemma P's
alive-tree prefixes; at most `τ` are submitted): as U1, with the reduction submitting the shift list
with each target request and winning with preimages of a shifted target. -/
theorem pomfrit_U2 (τ : ℕ) (sh : CTable → QueryLog specIC → ByteArray → List TG) :
    Pr{let r ← game KG pre n ℓ T lr A noHint (hint2 τ sh) tgts2}[PomWin ℓ r] ≤
      Pr{let r ← omExp KG pre n
          (red noHint (advC ℓ T lr A (hint2 τ sh) tgts2))}[
        Wins ℓ (goodShift τ relP) r.1 r.2.1 r.2.2] +
      ∑ i : Fin (ℓ + 1),
        Pr{let r ← game KG pre n ℓ T lr A noHint (hint2 τ sh) tgts2}[
          BadAt (goodShift τ relP) i.val r] :=
  (prEvent_mono_of_support _ _ _ fun _ hr hw => pomWin_forges KG pre n ℓ T lr A _ _ _ hr hw).trans
    (omuf_le KG pre n ℓ noHint _ (goodShift τ relP))

end Theorems

end VoleMole.ROM.OneMore.Pomfrit

