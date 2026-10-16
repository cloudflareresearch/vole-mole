import VoleMole.ROM.Verifier
import VoleMole.ROM.Comb

/-!
# Extraction failures of the executable verifier against the random oracle (plan M5)

`ROM/Chains.lean` and `ROM/Comb.lean` bound an abstract event, assuming `htrace`: for every
complete answer table, the event implies a bad `H₂¹`, `H₂²` or `H₂³` query. Here the event is
concrete: **the executable verifier, with the oracle's hashes, accepts the prover's proof, and
extraction from it fails**, in the game `game T st oa` of `ROM/Verifier.lean` (the prover, then
`verifyQ` on its proof). `htrace` is proved; what remains assumed is listed below.

## The event

The prover `oa` outputs a proof and the extractor's data (`ExtData β`: the committed leaf keys it
recovered, the trees it treats as known, and an auxiliary output, e.g. a log for the failure events
to read). The keys are not computed here: read `oa` as the prover together with the straight-line
extractor; the theorems hold for any key recovery, and its quality enters only through the
assumptions. The theorems hold for every CTR PRG (`[HasPrg]`); `ROM/CipherGame.lean` runs them with
the ideal cipher, the extractor computing the keys from the prover's cipher log, and replaces
`ε_bind` by an explicit term (plan §2d). The game's output is `(proof, ext, transcript)`.
* `Extracted st Wit r`: some known tree's corrected small-VOLE value `u^{(i)} + d`, computed from
  the extractor's keys, the proof's corrections and `d` and the verifier's `iv`, encodes a witness
  (`Wit chal1`; PomFRIT's relation depends on `chal1`). This is the candidate of `*_extract_chain`.
* The event is `accept ∧ ¬Extracted`.

## What remains assumed

* **Binding** (L1, `ε_bind`): `bindFail st r` = accepted, and the opening's leaves (at the verifier's
  `iv`) differ from the extractor's keys at a non-hidden leaf. A concrete event of the output; its
  probability is a hypothesis (`hbind`).
* **The "same chain" step** (`hsame`, `ε_chain`): outside an event `chainFail` of the output, the
  data committed at the verifier's own `H₂¹`, `H₂²`, `H₂³` queries (`runX`, `runY`, `runZ`) are
  those of the accepted proof's chain (`runChain`, with the extractor's keys): `SameChain`. This is
  the identification of the earlier queries by their answers (`chal1` in the `H₂²` input,
  `chal2` in the `H₂³` input) and of the keys committed in the `H₂¹` input; `hclaim1` is part of it
  (`SameChain.acc`: the chal3 accepted at `z` are those on the chain).
* **L2** (`hL2`, `ε_dead`): outside `chainFail` and an event `deadFail`, the trees outside `known`
  have a fixed block on the chain's challenges.

Everything else of `htrace` is proved (`chainBad_of_accept`, `combBad_of_accept`): the verifier's
queries are in the log (`inLog_verifyQ`), an accepted proof is on its chain at its `Δ`
(`onChain_of_accept`, from binding), and the per-chain step of `*_good_of_not_bad`.

## Results

* `prEvent_accept_le_chain_terms` (issue relations), `prEvent_accept_le_comb_terms` (combined):
  `Pr[accept ∧ ¬Extracted] ≤ (q₁+1)·ε_KOS + (q₂+1)·ε₂ + (Q+1)·N·2⁻¹²⁸ + ε_bind + ε_dead + ε_chain`
  for a prover with `q₁`, `q₂`, `Q` queries to `H₂¹`, `H₂²`, `H₂³` (the `+1` are the verifier's), and
  for the combined relations `ε₂ = ε_QS(n') + ε_c + (n+337)·2⁻⁴⁴⁸` with `n` the prover's total.
* Numerically, per relation: `moussakaIssue_accept_le`, `ratatouilleIssue_accept_le`,
  `moussakaRedeem_accept_le`, `ratatouilleSpend_accept_le`, `pomfritRedeem_accept_le`.
* Against one SHAKE oracle instead of the per-domain oracles: `ROM/SingleOracle.lean`
  (`prEvent_game₁_eq`).
-/

open Finset ENNReal

namespace VoleMole.ROM

-- The statements hold for any CTR PRG (`HasPrg`, `Verifier/Prg.lean`), AES included.
variable [VoleMole.Verifier.HasPrg]

open VoleMole.Prob VoleMole.Arith VoleMole.Verifier VoleMole.Verifier.Bridge
open VoleMole.EndToEnd VoleMole.SeedExtraction OracleComp OracleSpec

/-- The `iv` and `chal1` of an accepted transcript are the verifier's. -/
theorem verify_iv_chal1 (Hs : Hashes) (T : CrtTables) (st : Statement) (proof : ByteArray)
    (h : (verify Hs T st proof).accept = true) {leaves : BAVC.Leaves}
    (hr : BAVC.reconstruct (ivOf Hs ⟨st.params, proof⟩ (st.mu1 Hs)) (Proof.opening ⟨st.params, proof⟩)
      (Proof.delta ⟨st.params, proof⟩) = some leaves) :
    (verify Hs T st proof).iv = ivOf Hs ⟨st.params, proof⟩ (st.mu1 Hs) ∧
      (verify Hs T st proof).chal1 = chal1 Hs ⟨st.params, proof⟩ (st.mu1 Hs)
        (BAVC.check (Hs.hash .h1) leaves.coms) st.binder1 := by
  revert h
  simp only [verify, Id.run]
  split
  · simp_all
  · simp only [hr]
    split_ifs <;> simp_all [pure]

/-! ## The event and the assumptions -/

variable {β : Type}

/-- The game's output: the proof, the extractor's data, the verifier's transcript. -/
abbrev Out (β : Type) := ByteArray × ExtData β × Transcript

/-- The proof's chain as the extractor reads it from the output: the proof, its keys and the
verifier's `iv` (all `Chain.u` and `Chain.dc` read). -/
def outChain (r : Out β) : Chain :=
  { proof := r.1, keys := r.2.1.keys, iv := r.2.2.iv, h5 := fun _ => ByteArray.empty,
    chal1 := r.2.2.chal1, hV := #[], z := 0, chal2 := r.2.2.chal2, vals := fun _ => [] }

/-- **Extraction succeeds**: a known tree's candidate (from the extractor's keys) is a witness of
`Wit chal1`. -/
def Extracted (st : Statement) (Wit : ByteArray → (ℕ → GF128) → Prop) (r : Out β) : Prop :=
  ∃ i ∈ r.2.1.known, Wit r.2.2.chal1
    (candidate (F := GF128) ((outChain r).u st) ((outChain r).dc st) i)

/-- The opening of the proof (at the verifier's `iv`) reconstructs the extractor's keys at every
non-hidden leaf (L1). -/
def Binds (st : Statement) (r : Out β) : Prop :=
  ∀ leaves, BAVC.reconstruct r.2.2.iv (Proof.opening ⟨st.params, r.1⟩)
      (Proof.delta ⟨st.params, r.1⟩) = some leaves →
    ∀ i < BAVC.tau, ∀ j < 2 ^ BAVC.kOf i, j ≠ BAVC.deltaIndex (Proof.delta ⟨st.params, r.1⟩) i →
      leafKey leaves i j = r.2.1.keys i j

/-- **The binding failure** (`ε_bind`): an accepted proof whose opening does not bind to the
extractor's keys. -/
def bindFail (st : Statement) (r : Out β) : Prop := r.2.2.accept = true ∧ ¬Binds st r

/-- **The "same chain" step at a table** `g`: the data committed at the `H₂¹` input `x`, the `H₂²`
input `y` and the `H₂³` input `z` are those of the chain `ch`, and the `chal3` accepted at `z` are
those on the chain. -/
structure SameChain (st : Statement) (T : CrtTables) (preOf midOf : ByteArray → Table → Chain)
    (accOf : ByteArray → Table → Bytes 16 → Prop) (g : Table) (ch : Chain) (x y z : ByteArray) :
    Prop where
  pre : Chain.SamePrefix st (preOf x g) ch
  mid : Chain.SameMid st (midOf y g) ch
  acc : ∀ b, accOf z g b ↔ deltaBlocks b ∈ onSet st T ch chal3Blocks

/-! ## The deterministic step -/

/-- The candidates of the output are those of the run's chain. -/
lemma outChain_u_dc (Hs : Hashes) (T : CrtTables) (st : Statement) (r : Out β)
    (leaves : BAVC.Leaves) (hiv : r.2.2.iv = ivOf Hs ⟨st.params, r.1⟩ (st.mu1 Hs)) :
    (outChain r).u st = (runChain Hs T st r.1 leaves r.2.1.keys).u st ∧
      (outChain r).dc st = (runChain Hs T st r.1 leaves r.2.1.keys).dc st := by
  refine ⟨?_, rfl⟩
  funext i j
  simp only [Chain.u, outChain, runChain, hiv]
  rfl

-- As for `chainBad_h23_of_accept`: elaborating against `chainBad`'s match needs a deeper recursion.
set_option maxRecDepth 4000 in
/-- **An accepted proof at a table `g` whose binding, "same chain" and L2 hold, and from which
extraction fails, makes one of the verifier's `H₂¹`, `H₂²`, `H₂³` queries bad** (issue relations,
`chainBad`). `hdet` is the per-chain deterministic theorem (`*_extract_chain`, through
`chain_good_of_not_bad`), quantified over the chain. -/
theorem chainBad_of_accept {T : CrtTables} (hT : liftInvOk T = true) {st : Statement}
    (C : ChainData st) (N : ℕ) (Wit : ByteArray → (ℕ → GF128) → Prop)
    (hvals : ∀ y g c1 lb w, st.values c1 lb w = (C.csOf y g).values w)
    (hdet : ∀ (y : ByteArray) (g : Table) (ch : Chain) (known : Finset (Fin BAVC.tau))
      (acc : Bytes 16 → Prop), (∀ w, ch.vals w = (C.csOf y g).values w) →
      ∀ A : Finset Blocks, (∀ Δ ∈ A, ch.OnChain st T Δ) → (A : Set Blocks) ⊆ chal3Blocks →
      Seed.KOSGood ch.kosCh (chal3Blocks : Set Blocks) (lift T) (ch.kosQ st T) (ch.kosD st T) →
      (2 ≤ A.card → ∀ uStar,
        (∀ j, ∃ v, ∀ Δ ∈ A, ch.Qw st T j Δ = v + uStar j * lift T Δ) →
        ¬(C.csOf y g).Holds (wStar uStar (ch.dc st)) →
        Seed.zkHash _ (gfOfBytes ch.chal2 0) (gfOfBytes ch.chal2 16) (gfOfBytes ch.chal2 32)
          ⟨W128.word ch.chal2 48, 0⟩ (valVec (C.csOf y g) (wStar uStar (ch.dc st))) ≠ 0) →
      ChainHyps A known acc →
      (∃ i ∈ known, Wit ch.chal1 (candidate (F := GF128) (ch.u st) (ch.dc st) i)) ∨
        (open Classical in #{x ∈ admissible | acc x} ≤ N))
    {g : Table} {proof : ByteArray} {e : ExtData β}
    (hacc : (verify (Hashes.ofTable g) T st proof).accept = true) {leaves : BAVC.Leaves}
    (hr : BAVC.reconstruct (ivOf (Hashes.ofTable g) ⟨st.params, proof⟩
      (st.mu1 (Hashes.ofTable g))) (Proof.opening ⟨st.params, proof⟩)
      (Proof.delta ⟨st.params, proof⟩) = some leaves)
    (hbind : ∀ i < BAVC.tau, ∀ j < 2 ^ BAVC.kOf i,
      j ≠ BAVC.deltaIndex (Proof.delta ⟨st.params, proof⟩) i → leafKey leaves i j = e.keys i j)
    (hsame : SameChain st T C.preOf C.midOf C.accOf g
      (runChain (Hashes.ofTable g) T st proof leaves e.keys)
      (runX (Hashes.ofTable g) st proof leaves)
      (runY (Hashes.ofTable g) st (runChain (Hashes.ofTable g) T st proof leaves e.keys))
      (runZ st (runChain (Hashes.ofTable g) T st proof leaves e.keys)))
    (hL2 : ∀ i ∉ e.known, IsFixed ((onSet st T (runChain (Hashes.ofTable g) T st proof leaves
      e.keys) chal3Blocks : Finset Blocks) : Set Blocks) i)
    (hnot : ¬∃ i ∈ e.known, Wit (runChain (Hashes.ofTable g) T st proof leaves e.keys).chal1
      (candidate (F := GF128) ((runChain (Hashes.ofTable g) T st proof leaves e.keys).u st)
        ((runChain (Hashes.ofTable g) T st proof leaves e.keys).dc st) i)) :
    let ch := runChain (Hashes.ofTable g) T st proof leaves e.keys
    chainBad C T chal3Blocks N (.h21, runX (Hashes.ofTable g) st proof leaves) g ∨
      chainBad C T chal3Blocks N (.h22, runY (Hashes.ofTable g) st ch) g ∨
      chainBad C T chal3Blocks N (.h23, runZ st ch) g := by
  classical
  intro ch
  set Hs := Hashes.ofTable g
  set x := runX Hs st proof leaves
  set y := runY Hs st ch
  set z := runZ st ch
  -- The accepted proof is on its chain, at its `Δ` (`onChain_of_accept`, from binding).
  have hon := onChain_of_accept Hs T st ch rfl rfl rfl rfl proof hacc
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ fun leaves' hr' => by
      have : leaves' = leaves := Option.some_injective _ (hr'.symm.trans hr)
      subst this
      exact ⟨hbind, rfl, rfl, rfl⟩
  obtain ⟨hf, -⟩ := (accept_iff Hs T st proof).1 hacc
  by_contra hno
  simp only [not_or] at hno
  obtain ⟨h1, h2, h3⟩ := hno
  have hpre : Chain.SamePrefix st (C.preOf x g) (C.midOf y g) :=
    hsame.pre.trans hsame.mid.1.symm
  have hc1 : (C.midOf y g).chal1 = (g (.h21, x) : Bytes 136).ba := hsame.mid.2.1.symm
  have hgood := chain_good_of_not_bad hT C chal3Blocks N hpre hc1 hsame.mid rfl
    (fun A => ChainHyps A e.known (C.accOf z g)) _
    (fun A hA hAS hkos hQS hP => hdet y g ch e.known (C.accOf z g)
      (fun w => hvals y g _ _ w) A hA hAS hkos hQS hP) h1 h2
    ⟨hL2, fun b _ hb => (hsame.acc b).1 hb⟩
  have hd : (g (.h23, z)).ba = Proof.delta ⟨st.params, proof⟩ := hon.2
  have hadm : g (.h23, z) ∈ admissible := by
    have h15 : (Proof.delta ⟨st.params, proof⟩).get! 15 = 0 := by
      simp only [Proof.checkFormat, Bool.and_eq_true, beq_iff_eq] at hf
      exact hf.2
    rw [← hd, Bytes.get!_ba _ (by simp [Kind.outLen])] at h15
    exact Finset.mem_filter.2 ⟨Finset.mem_univ _, h15⟩
  rcases hgood with hex | hfew
  · exact hnot hex
  · refine h3 (chainBad_h23_of_accept C T chal3Blocks N hfew hadm ((hsame.acc _).2 ?_))
    refine mem_onSet.2 ⟨Finset.mem_image_of_mem _ hadm, ?_⟩
    rw [deltaBlocks, show (g.chal3 z).ba = _ from hd]
    exact hon.1

omit [VoleMole.Verifier.HasPrg] in
/-- `InLog` as a log entry. -/
lemma exists_of_inLog {α : Type} {oa : OracleComp spec α} {g : Table} {t : Dom}
    (h : InLog oa g t) : ∃ e ∈ tableQueryLog oa g, e.1 = t := by
  simpa [InLog, List.mem_map] using h

/-! ## The issue relations -/

/-- **The issue relations against the random oracle: the executable verifier accepts and
extraction fails** with probability `≤ (q₁+1)·ε_KOS + (q₂+1)·ε_QS(n) + (Q+1)·N·2⁻¹²⁸ + ε_bind +
ε_dead + ε_chain`, for a prover `oa` making at most `q k` queries to each domain, chain data `C`
committed as in `ChainData.Committed`, and a deterministic per-chain theorem `hdet`. Assumed:
binding (`hbind`, a bound on the concrete `bindFail`), "same chain" (`hsame` outside `chainFail`),
L2 (`hL2` outside `chainFail` and `deadFail`). -/
theorem prEvent_accept_le_chain_terms {T : CrtTables} (hT : liftInvOk T = true) {st : Statement}
    (C : ChainData st) (hC : C.Committed) {n : ℕ} (hn : ∀ y g, (C.csOf y g).length = n) (N : ℕ)
    (Wit : ByteArray → (ℕ → GF128) → Prop)
    (hvals : ∀ y g c1 lb w, st.values c1 lb w = (C.csOf y g).values w)
    (hdet : ∀ (y : ByteArray) (g : Table) (ch : Chain) (known : Finset (Fin BAVC.tau))
      (acc : Bytes 16 → Prop), (∀ w, ch.vals w = (C.csOf y g).values w) →
      ∀ A : Finset Blocks, (∀ Δ ∈ A, ch.OnChain st T Δ) → (A : Set Blocks) ⊆ chal3Blocks →
      Seed.KOSGood ch.kosCh (chal3Blocks : Set Blocks) (lift T) (ch.kosQ st T) (ch.kosD st T) →
      (2 ≤ A.card → ∀ uStar,
        (∀ j, ∃ v, ∀ Δ ∈ A, ch.Qw st T j Δ = v + uStar j * lift T Δ) →
        ¬(C.csOf y g).Holds (wStar uStar (ch.dc st)) →
        Seed.zkHash _ (gfOfBytes ch.chal2 0) (gfOfBytes ch.chal2 16) (gfOfBytes ch.chal2 32)
          ⟨W128.word ch.chal2 48, 0⟩ (valVec (C.csOf y g) (wStar uStar (ch.dc st))) ≠ 0) →
      ChainHyps A known acc →
      (∃ i ∈ known, Wit ch.chal1 (candidate (F := GF128) (ch.u st) (ch.dc st) i)) ∨
        (open Classical in #{x ∈ admissible | acc x} ≤ N))
    (oa : OracleComp spec (ByteArray × ExtData β)) (q : Kind → ℕ) (hq : IsKindQueryBound oa q)
    (chainFail deadFail : Out β → Prop) {εb εd εs : ℝ≥0∞}
    (hbind : Pr{let r ← (simulateQ randomOracle (game T st oa)).run' ∅}[bindFail st r] ≤ εb)
    (hdead : Pr{let r ← (simulateQ randomOracle (game T st oa)).run' ∅}[deadFail r] ≤ εd)
    (hchain : Pr{let r ← (simulateQ randomOracle (game T st oa)).run' ∅}[chainFail r] ≤ εs)
    (hsame : ∀ g : Table, let r := evalWithAnswerFn (QueryImpl.ofFn g) (game T st oa);
      r.2.2.accept = true → ¬chainFail r → ∀ leaves, BAVC.reconstruct r.2.2.iv
        (Proof.opening ⟨st.params, r.1⟩) (Proof.delta ⟨st.params, r.1⟩) = some leaves →
      SameChain st T C.preOf C.midOf C.accOf g
        (runChain (Hashes.ofTable g) T st r.1 leaves r.2.1.keys)
        (runX (Hashes.ofTable g) st r.1 leaves)
        (runY (Hashes.ofTable g) st (runChain (Hashes.ofTable g) T st r.1 leaves r.2.1.keys))
        (runZ st (runChain (Hashes.ofTable g) T st r.1 leaves r.2.1.keys)))
    (hL2 : ∀ g : Table, let r := evalWithAnswerFn (QueryImpl.ofFn g) (game T st oa);
      r.2.2.accept = true → ¬chainFail r → ¬deadFail r → ∀ leaves, BAVC.reconstruct r.2.2.iv
        (Proof.opening ⟨st.params, r.1⟩) (Proof.delta ⟨st.params, r.1⟩) = some leaves →
      ∀ i ∉ r.2.1.known, IsFixed ((onSet st T (runChain (Hashes.ofTable g) T st r.1 leaves
        r.2.1.keys) chal3Blocks : Finset Blocks) : Set Blocks) i) :
    Pr{let r ← (simulateQ randomOracle (game T st oa)).run' ∅}[
        r.2.2.accept = true ∧ ¬Extracted st Wit r] ≤
      (q .h21 + 1) * epsKOS #chal3Blocks (Chain.kosL st) +
        (q .h22 + 1) * ENNReal.ofReal (Seed.epsQS (2 ^ 128) (2 ^ 64) n) +
        (q .h23 + 1) * ((N : ℝ≥0∞) / 2 ^ 128) + εb + εd + εs := by
  let mx := (simulateQ randomOracle (game T st oa)).run' ∅
  have hmain := prEvent_le_chain_terms hT C hC chal3Blocks hn N (game T st oa)
    (q + verifierQueries) (isKindQueryBound_game T st hq)
    (fun r => (r.2.2.accept = true ∧ ¬Extracted st Wit r) ∧ ¬chainFail r) (bindFail st) deadFail
    hbind hdead ?_
  · calc Pr{let r ← mx}[r.2.2.accept = true ∧ ¬Extracted st Wit r]
        ≤ Pr{let r ← mx}[((r.2.2.accept = true ∧ ¬Extracted st Wit r) ∧ ¬chainFail r) ∨
            chainFail r] := prEvent_mono mx _ _ fun r h => by tauto
      _ ≤ Pr{let r ← mx}[(r.2.2.accept = true ∧ ¬Extracted st Wit r) ∧ ¬chainFail r] +
            Pr{let r ← mx}[chainFail r] := prEvent_or_le mx _ _
      _ ≤ _ := by
          refine add_le_add (hmain.trans_eq ?_) hchain
          simp [verifierQueries]
  intro g
  have hs := hsame g
  have hl := hL2 g
  simp only [evalWithAnswerFn_game] at hs hl ⊢
  set π := (evalWithAnswerFn (QueryImpl.ofFn g) oa).1
  set e := (evalWithAnswerFn (QueryImpl.ofFn g) oa).2
  rintro ⟨⟨hacc, hnex⟩, hnc⟩ hnb hnd
  obtain ⟨-, leaves, hr, -⟩ := (accept_iff _ T st π).1 hacc
  obtain ⟨hiv, hc1⟩ := verify_iv_chal1 _ T st π hacc hr
  have hr' : BAVC.reconstruct (verify (Hashes.ofTable g) T st π).iv (Proof.opening ⟨st.params, π⟩)
      (Proof.delta ⟨st.params, π⟩) = some leaves := by rw [hiv]; exact hr
  have hbinds : Binds st (π, e, verify (Hashes.ofTable g) T st π) := by
    by_contra hb; exact hnb ⟨hacc, hb⟩
  have huc := outChain_u_dc (Hashes.ofTable g) T st (π, e, verify (Hashes.ofTable g) T st π) leaves
    hiv
  have hbad := chainBad_of_accept hT C N Wit hvals hdet hacc hr
    (fun i hi j hj hji => hbinds leaves hr' i hi j hj hji) (hs hacc hnc leaves hr')
    (hl hacc hnc hnd leaves hr')
    (by
      rintro ⟨i, hi, hw⟩
      refine hnex ⟨i, hi, ?_⟩
      simp only [huc.1, huc.2, hc1]
      exact hw)
  have hlog := inLog_verifyQ g T st π hacc hr e.keys
  rcases hbad with hb | hb | hb
  · obtain ⟨x, hx, hx1⟩ := exists_of_inLog (inLog_game hlog.1)
    exact ⟨x, hx, hx1 ▸ hb⟩
  · obtain ⟨x, hx, hx1⟩ := exists_of_inLog (inLog_game hlog.2.1)
    exact ⟨x, hx, hx1 ▸ hb⟩
  · obtain ⟨x, hx, hx1⟩ := exists_of_inLog (inLog_game hlog.2.2)
    exact ⟨x, hx, hx1 ▸ hb⟩

/-- **Moussaka issuance against the random oracle**: the executable verifier accepts and the
extractor's candidate is not an issuance witness with probability
`≤ (q₁+1)·2⁻¹⁵⁰ + (q₂+1)·ε_QS(4008) + (Q+1)·9·2⁻¹²⁸ + ε_bind + ε_dead + ε_chain`. -/
theorem moussakaIssue_accept_le (t ctxIss : ByteArray) (labelRows : Bool)
    (preOf midOf : ByteArray → Table → Chain) (accOf : ByteArray → Table → Bytes 16 → Prop)
    (hC : (ChainData.ofSys (st := moussakaIssue t ctxIss labelRows) preOf midOf
      (moussakaIssueSys t ctxIss) accOf).Committed)
    (oa : OracleComp spec (ByteArray × ExtData β)) (q : Kind → ℕ) (hq : IsKindQueryBound oa q)
    (chainFail deadFail : Out β → Prop) {εb εd εs : ℝ≥0∞}
    (hbind : Pr{let r ← (simulateQ randomOracle
      (game CrtGen.tables (moussakaIssue t ctxIss labelRows) oa)).run' ∅}[
        bindFail (moussakaIssue t ctxIss labelRows) r] ≤ εb)
    (hdead : Pr{let r ← (simulateQ randomOracle
      (game CrtGen.tables (moussakaIssue t ctxIss labelRows) oa)).run' ∅}[deadFail r] ≤ εd)
    (hchain : Pr{let r ← (simulateQ randomOracle
      (game CrtGen.tables (moussakaIssue t ctxIss labelRows) oa)).run' ∅}[chainFail r] ≤ εs)
    (hsame : ∀ g : Table, let st := moussakaIssue t ctxIss labelRows
      let r := evalWithAnswerFn (QueryImpl.ofFn g) (game CrtGen.tables st oa)
      r.2.2.accept = true → ¬chainFail r → ∀ leaves, BAVC.reconstruct r.2.2.iv
        (Proof.opening ⟨st.params, r.1⟩) (Proof.delta ⟨st.params, r.1⟩) = some leaves →
      let ch := runChain (Hashes.ofTable g) CrtGen.tables st r.1 leaves r.2.1.keys
      SameChain st CrtGen.tables preOf midOf accOf g ch (runX (Hashes.ofTable g) st r.1 leaves)
        (runY (Hashes.ofTable g) st ch) (runZ st ch))
    (hL2 : ∀ g : Table, let st := moussakaIssue t ctxIss labelRows
      let r := evalWithAnswerFn (QueryImpl.ofFn g) (game CrtGen.tables st oa)
      r.2.2.accept = true → ¬chainFail r → ¬deadFail r → ∀ leaves, BAVC.reconstruct r.2.2.iv
        (Proof.opening ⟨st.params, r.1⟩) (Proof.delta ⟨st.params, r.1⟩) = some leaves →
      ∀ i ∉ r.2.1.known, IsFixed ((onSet st CrtGen.tables (runChain (Hashes.ofTable g)
        CrtGen.tables st r.1 leaves r.2.1.keys) chal3Blocks : Finset Blocks) : Set Blocks) i) :
    Pr{let r ← (simulateQ randomOracle
      (game CrtGen.tables (moussakaIssue t ctxIss labelRows) oa)).run' ∅}[
        r.2.2.accept = true ∧ ¬Extracted (moussakaIssue t ctxIss labelRows)
          (fun _ => moussakaIssueWit (fun k => fnOf t k.val) (fnOf ctxIss)) r] ≤
      (q .h21 + 1) * (2 ^ 150 : ℝ≥0∞)⁻¹ +
        (q .h22 + 1) * ENNReal.ofReal (Seed.epsQS (2 ^ 128) (2 ^ 64) 4008) +
        (q .h23 + 1) * ((9 : ℝ≥0∞) / 2 ^ 128) + εb + εd + εs := by
  classical
  refine (prEvent_accept_le_chain_terms liftInvOk_tables _ hC
    (fun _ _ => Moussaka.issueSystem_length _ _) 9 _
    (fun _ _ c1 lb w => moussakaIssue_values t ctxIss labelRows c1 lb w)
    (fun y g ch known acc hv A hA hAS hkos hQS hP =>
      moussakaIssue_extract_chain t ctxIss labelRows ch hv hA hAS hkos hP.1 hQS admissible
        deltaBlocks deltaBlocks_injOn acc hP.2)
    oa q hq chainFail deadFail hbind hdead hchain hsame hL2).trans ?_
  gcongr
  · exact epsKOS_chal3Blocks_le _ (by norm_num [moussakaIssue]) (by norm_num [moussakaIssue])
  · norm_num

/-- **Ratatouille issuance against the random oracle**:
`≤ (q₁+1)·2⁻¹⁵⁰ + (q₂+1)·ε_QS(3776) + (Q+1)·9·2⁻¹²⁸ + ε_bind + ε_dead + ε_chain`
(as `moussakaIssue_accept_le`). -/
theorem ratatouilleIssue_accept_le (c : ByteArray) (tInit : ℕ) (ctxIss : ByteArray)
    (labelRows : Bool) (preOf midOf : ByteArray → Table → Chain)
    (accOf : ByteArray → Table → Bytes 16 → Prop)
    (hC : (ChainData.ofSys (st := ratatouilleIssue c tInit ctxIss labelRows) preOf midOf
      (ratatouilleIssueSys c tInit ctxIss) accOf).Committed)
    (oa : OracleComp spec (ByteArray × ExtData β)) (q : Kind → ℕ) (hq : IsKindQueryBound oa q)
    (chainFail deadFail : Out β → Prop) {εb εd εs : ℝ≥0∞}
    (hbind : Pr{let r ← (simulateQ randomOracle
      (game CrtGen.tables (ratatouilleIssue c tInit ctxIss labelRows) oa)).run' ∅}[
        bindFail (ratatouilleIssue c tInit ctxIss labelRows) r] ≤ εb)
    (hdead : Pr{let r ← (simulateQ randomOracle
      (game CrtGen.tables (ratatouilleIssue c tInit ctxIss labelRows) oa)).run' ∅}[deadFail r] ≤
        εd)
    (hchain : Pr{let r ← (simulateQ randomOracle
      (game CrtGen.tables (ratatouilleIssue c tInit ctxIss labelRows) oa)).run' ∅}[chainFail r] ≤
        εs)
    (hsame : ∀ g : Table, let st := ratatouilleIssue c tInit ctxIss labelRows
      let r := evalWithAnswerFn (QueryImpl.ofFn g) (game CrtGen.tables st oa)
      r.2.2.accept = true → ¬chainFail r → ∀ leaves, BAVC.reconstruct r.2.2.iv
        (Proof.opening ⟨st.params, r.1⟩) (Proof.delta ⟨st.params, r.1⟩) = some leaves →
      let ch := runChain (Hashes.ofTable g) CrtGen.tables st r.1 leaves r.2.1.keys
      SameChain st CrtGen.tables preOf midOf accOf g ch (runX (Hashes.ofTable g) st r.1 leaves)
        (runY (Hashes.ofTable g) st ch) (runZ st ch))
    (hL2 : ∀ g : Table, let st := ratatouilleIssue c tInit ctxIss labelRows
      let r := evalWithAnswerFn (QueryImpl.ofFn g) (game CrtGen.tables st oa)
      r.2.2.accept = true → ¬chainFail r → ¬deadFail r → ∀ leaves, BAVC.reconstruct r.2.2.iv
        (Proof.opening ⟨st.params, r.1⟩) (Proof.delta ⟨st.params, r.1⟩) = some leaves →
      ∀ i ∉ r.2.1.known, IsFixed ((onSet st CrtGen.tables (runChain (Hashes.ofTable g)
        CrtGen.tables st r.1 leaves r.2.1.keys) chal3Blocks : Finset Blocks) : Set Blocks) i) :
    Pr{let r ← (simulateQ randomOracle
      (game CrtGen.tables (ratatouilleIssue c tInit ctxIss labelRows) oa)).run' ∅}[
        r.2.2.accept = true ∧ ¬Extracted (ratatouilleIssue c tInit ctxIss labelRows)
          (fun _ => ratatouilleIssueWit (fnOf c) tInit (fnOf ctxIss)) r] ≤
      (q .h21 + 1) * (2 ^ 150 : ℝ≥0∞)⁻¹ +
        (q .h22 + 1) * ENNReal.ofReal (Seed.epsQS (2 ^ 128) (2 ^ 64) 3776) +
        (q .h23 + 1) * ((9 : ℝ≥0∞) / 2 ^ 128) + εb + εd + εs := by
  classical
  refine (prEvent_accept_le_chain_terms liftInvOk_tables _ hC
    (fun _ _ => Ratatouille.issueSystem_length _ _ _) 9 _
    (fun _ _ c1 lb w => ratatouilleIssue_values c tInit ctxIss labelRows c1 lb w)
    (fun y g ch known acc hv A hA hAS hkos hQS hP =>
      ratatouilleIssue_extract_chain c tInit ctxIss labelRows ch hv hA hAS hkos hP.1 hQS
        admissible deltaBlocks deltaBlocks_injOn acc hP.2)
    oa q hq chainFail deadFail hbind hdead hchain hsame hL2).trans ?_
  gcongr
  · exact epsKOS_chal3Blocks_le _ (by norm_num [ratatouilleIssue])
      (by norm_num [ratatouilleIssue])
  · norm_num

/-! ## The combined relations -/

omit [VoleMole.Verifier.HasPrg] in
/-- The verifier's combination bytes are the table's combination cell at `chal2 ‖ dst`. -/
lemma combBytes_ofTable {st : Statement} {M : ℕ} {dst : ByteArray} (hcomb : st.comb = some (M, dst))
    (g : Table) (u : Bytes 56) :
    st.combBytes (Hashes.ofTable g) u.ba = (g (combKey M dst u) : Bytes (16 * M)).ba := by
  simp [Statement.combBytes, hcomb, combKey]

set_option maxRecDepth 4000 in
/-- **`chainBad_of_accept` for the combined relations** (`combBad`, with `l` read from the table
at `chal2 ‖ dst`): the statement's combination is `(M, C.dst)` (`hcomb`) and its evaluator at the
combination bytes `v` is the system at `combDec v` (`hvals`). `hdet` may use that the chain's
`chal1` is the one committed at `y` (PomFRIT's system reads it). -/
theorem combBad_of_accept {T : CrtTables} (hT : liftInvOk T = true) {st : Statement} {M : ℕ}
    (C : CombData st M) (N : ℕ) (Wit : ByteArray → (ℕ → GF128) → Prop)
    (hcomb : st.comb = some (M, C.dst))
    (hvals : ∀ y g (v : Bytes (16 * M)) w,
      st.values (C.midOf y g).chal1 v.ba w = (C.sysOf y g (combDec v)).values w)
    (hdet : ∀ (y : ByteArray) (g : Table) (ch : Chain) (known : Finset (Fin BAVC.tau))
      (acc : Bytes 16 → Prop) (l : Fin M → GF128), ch.chal1 = (C.midOf y g).chal1 →
      (∀ w, ch.vals w = (C.sysOf y g l).values w) →
      ∀ A : Finset Blocks, (∀ Δ ∈ A, ch.OnChain st T Δ) → (A : Set Blocks) ⊆ chal3Blocks →
      Seed.KOSGood ch.kosCh (chal3Blocks : Set Blocks) (lift T) (ch.kosQ st T) (ch.kosD st T) →
      (2 ≤ A.card → ∀ uStar,
        (∀ j, ∃ v, ∀ Δ ∈ A, ch.Qw st T j Δ = v + uStar j * lift T Δ) →
        ¬(C.sysOf y g l).Holds (wStar uStar (ch.dc st)) →
        Seed.zkHash _ (gfOfBytes ch.chal2 0) (gfOfBytes ch.chal2 16) (gfOfBytes ch.chal2 32)
          ⟨W128.word ch.chal2 48, 0⟩ (valVec (C.sysOf y g l) (wStar uStar (ch.dc st))) ≠ 0) →
      (2 ≤ A.card → ∀ uStar,
        (∀ j, ∃ v, ∀ Δ ∈ A, ch.Qw st T j Δ = v + uStar j * lift T Δ) →
        (C.sysOf y g l).Holds (wStar uStar (ch.dc st)) → C.witOf y g (wStar uStar (ch.dc st))) →
      ChainHyps A known acc →
      (∃ i ∈ known, Wit ch.chal1 (candidate (F := GF128) (ch.u st) (ch.dc st) i)) ∨
        (open Classical in #{x ∈ admissible | acc x} ≤ N))
    {g : Table} {proof : ByteArray} {e : ExtData β}
    (hacc : (verify (Hashes.ofTable g) T st proof).accept = true) {leaves : BAVC.Leaves}
    (hr : BAVC.reconstruct (ivOf (Hashes.ofTable g) ⟨st.params, proof⟩
      (st.mu1 (Hashes.ofTable g))) (Proof.opening ⟨st.params, proof⟩)
      (Proof.delta ⟨st.params, proof⟩) = some leaves)
    (hbind : ∀ i < BAVC.tau, ∀ j < 2 ^ BAVC.kOf i,
      j ≠ BAVC.deltaIndex (Proof.delta ⟨st.params, proof⟩) i → leafKey leaves i j = e.keys i j)
    (hsame : SameChain st T C.preOf C.midOf C.accOf g
      (runChain (Hashes.ofTable g) T st proof leaves e.keys)
      (runX (Hashes.ofTable g) st proof leaves)
      (runY (Hashes.ofTable g) st (runChain (Hashes.ofTable g) T st proof leaves e.keys))
      (runZ st (runChain (Hashes.ofTable g) T st proof leaves e.keys)))
    (hL2 : ∀ i ∉ e.known, IsFixed ((onSet st T (runChain (Hashes.ofTable g) T st proof leaves
      e.keys) chal3Blocks : Finset Blocks) : Set Blocks) i)
    (hnot : ¬∃ i ∈ e.known, Wit (runChain (Hashes.ofTable g) T st proof leaves e.keys).chal1
      (candidate (F := GF128) ((runChain (Hashes.ofTable g) T st proof leaves e.keys).u st)
        ((runChain (Hashes.ofTable g) T st proof leaves e.keys).dc st) i)) :
    let ch := runChain (Hashes.ofTable g) T st proof leaves e.keys
    combBad C T chal3Blocks N (.h21, runX (Hashes.ofTable g) st proof leaves) g ∨
      combBad C T chal3Blocks N (.h22, runY (Hashes.ofTable g) st ch) g ∨
      combBad C T chal3Blocks N (.h23, runZ st ch) g := by
  classical
  intro ch
  set Hs := Hashes.ofTable g
  set x := runX Hs st proof leaves
  set y := runY Hs st ch
  set z := runZ st ch
  have hon := onChain_of_accept Hs T st ch rfl rfl rfl rfl proof hacc
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ fun leaves' hr' => by
      have : leaves' = leaves := Option.some_injective _ (hr'.symm.trans hr)
      subst this
      exact ⟨hbind, rfl, rfl, rfl⟩
  obtain ⟨hf, -⟩ := (accept_iff Hs T st proof).1 hacc
  by_contra hno
  simp only [not_or] at hno
  obtain ⟨h1, h2, h3⟩ := hno
  have hpre : Chain.SamePrefix st (C.preOf x g) (C.midOf y g) :=
    hsame.pre.trans hsame.mid.1.symm
  have hc1 : (C.midOf y g).chal1 = (g (.h21, x) : Bytes 136).ba := hsame.mid.2.1.symm
  have hch1 : ch.chal1 = (C.midOf y g).chal1 := hsame.mid.2.1
  have hc2 : ch.chal2 = (g (.h22, y) : Bytes 56).ba := rfl
  have hv : ∀ w, ch.vals w =
      (C.sysOf y g (combDec (g (combKey M C.dst (g (.h22, y)))))).values w := fun w => by
    change st.values ch.chal1 (st.combBytes Hs ch.chal2) w = _
    rw [show st.combBytes Hs ch.chal2 = _ from combBytes_ofTable hcomb g (g (.h22, y)), hch1]
    exact hvals y g _ w
  have hgood := comb_good_of_not_bad hT C chal3Blocks N hpre hc1 hsame.mid hc2
    (fun A => ChainHyps A e.known (C.accOf z g)) _
    (fun A hA hAS hkos hQS hcb hP => hdet y g ch e.known (C.accOf z g) _ hch1 hv A hA hAS hkos
      hQS hcb hP) h1 h2
    ⟨hL2, fun b _ hb => (hsame.acc b).1 hb⟩
  have hd : (g (.h23, z)).ba = Proof.delta ⟨st.params, proof⟩ := hon.2
  have hadm : g (.h23, z) ∈ admissible := by
    have h15 : (Proof.delta ⟨st.params, proof⟩).get! 15 = 0 := by
      simp only [Proof.checkFormat, Bool.and_eq_true, beq_iff_eq] at hf
      exact hf.2
    rw [← hd, Bytes.get!_ba _ (by simp [Kind.outLen])] at h15
    exact Finset.mem_filter.2 ⟨Finset.mem_univ _, h15⟩
  rcases hgood with hex | hfew
  · exact hnot hex
  · refine h3 ?_
    simp only [combBad, reduceCtorEq, ite_false]
    refine chainBad_h23_of_accept C.toChainData T chal3Blocks N hfew hadm ((hsame.acc _).2 ?_)
    refine mem_onSet.2 ⟨Finset.mem_image_of_mem _ hadm, ?_⟩
    rw [deltaBlocks, show (g.chal3 z).ba = _ from hd]
    exact hon.1

set_option exponentiation.threshold 500 in
-- `Finset.univ : Finset (Bytes 56)` (the combination cells) needs a deeper recursion to elaborate.
set_option maxRecDepth 4000 in
/-- **The combined relations against the random oracle: the executable verifier accepts and
extraction fails** with probability
`≤ (q₁+1)·ε_KOS + (q₂+1)·(ε_QS(n') + ε_c + (n+337)·2⁻⁴⁴⁸) + (Q+1)·N·2⁻¹²⁸ + ε_bind + ε_dead + ε_chain`,
for a prover with at most `n` queries in total and `q k` to each domain (as
`prEvent_accept_le_chain_terms`, with `l` read from the table at `chal2 ‖ dst`). -/
theorem prEvent_accept_le_comb_terms {T : CrtTables} (hT : liftInvOk T = true) {st : Statement}
    {M : ℕ} (C : CombData st M) (hC : C.Committed) {n' : ℕ}
    (hn' : ∀ y g l, (C.sysOf y g l).length = n') {εc : ℝ≥0∞}
    (hεc : ∀ y g w, prU (Fin M → GF128) (fun l => (C.sysOf y g l).Holds w ∧ ¬C.witOf y g w) ≤ εc)
    (N : ℕ) (Wit : ByteArray → (ℕ → GF128) → Prop) (hcomb : st.comb = some (M, C.dst))
    (hvals : ∀ y g (v : Bytes (16 * M)) w,
      st.values (C.midOf y g).chal1 v.ba w = (C.sysOf y g (combDec v)).values w)
    (hdet : ∀ (y : ByteArray) (g : Table) (ch : Chain) (known : Finset (Fin BAVC.tau))
      (acc : Bytes 16 → Prop) (l : Fin M → GF128), ch.chal1 = (C.midOf y g).chal1 →
      (∀ w, ch.vals w = (C.sysOf y g l).values w) →
      ∀ A : Finset Blocks, (∀ Δ ∈ A, ch.OnChain st T Δ) → (A : Set Blocks) ⊆ chal3Blocks →
      Seed.KOSGood ch.kosCh (chal3Blocks : Set Blocks) (lift T) (ch.kosQ st T) (ch.kosD st T) →
      (2 ≤ A.card → ∀ uStar,
        (∀ j, ∃ v, ∀ Δ ∈ A, ch.Qw st T j Δ = v + uStar j * lift T Δ) →
        ¬(C.sysOf y g l).Holds (wStar uStar (ch.dc st)) →
        Seed.zkHash _ (gfOfBytes ch.chal2 0) (gfOfBytes ch.chal2 16) (gfOfBytes ch.chal2 32)
          ⟨W128.word ch.chal2 48, 0⟩ (valVec (C.sysOf y g l) (wStar uStar (ch.dc st))) ≠ 0) →
      (2 ≤ A.card → ∀ uStar,
        (∀ j, ∃ v, ∀ Δ ∈ A, ch.Qw st T j Δ = v + uStar j * lift T Δ) →
        (C.sysOf y g l).Holds (wStar uStar (ch.dc st)) → C.witOf y g (wStar uStar (ch.dc st))) →
      ChainHyps A known acc →
      (∃ i ∈ known, Wit ch.chal1 (candidate (F := GF128) (ch.u st) (ch.dc st) i)) ∨
        (open Classical in #{x ∈ admissible | acc x} ≤ N))
    (oa : OracleComp spec (ByteArray × ExtData β)) (n : ℕ) (hn : IsTotalQueryBound oa n)
    (q : Kind → ℕ) (hq : IsKindQueryBound oa q) (chainFail deadFail : Out β → Prop)
    {εb εd εs : ℝ≥0∞}
    (hbind : Pr{let r ← (simulateQ randomOracle (game T st oa)).run' ∅}[bindFail st r] ≤ εb)
    (hdead : Pr{let r ← (simulateQ randomOracle (game T st oa)).run' ∅}[deadFail r] ≤ εd)
    (hchain : Pr{let r ← (simulateQ randomOracle (game T st oa)).run' ∅}[chainFail r] ≤ εs)
    (hsame : ∀ g : Table, let r := evalWithAnswerFn (QueryImpl.ofFn g) (game T st oa);
      r.2.2.accept = true → ¬chainFail r → ∀ leaves, BAVC.reconstruct r.2.2.iv
        (Proof.opening ⟨st.params, r.1⟩) (Proof.delta ⟨st.params, r.1⟩) = some leaves →
      SameChain st T C.preOf C.midOf C.accOf g
        (runChain (Hashes.ofTable g) T st r.1 leaves r.2.1.keys)
        (runX (Hashes.ofTable g) st r.1 leaves)
        (runY (Hashes.ofTable g) st (runChain (Hashes.ofTable g) T st r.1 leaves r.2.1.keys))
        (runZ st (runChain (Hashes.ofTable g) T st r.1 leaves r.2.1.keys)))
    (hL2 : ∀ g : Table, let r := evalWithAnswerFn (QueryImpl.ofFn g) (game T st oa);
      r.2.2.accept = true → ¬chainFail r → ¬deadFail r → ∀ leaves, BAVC.reconstruct r.2.2.iv
        (Proof.opening ⟨st.params, r.1⟩) (Proof.delta ⟨st.params, r.1⟩) = some leaves →
      ∀ i ∉ r.2.1.known, IsFixed ((onSet st T (runChain (Hashes.ofTable g) T st r.1 leaves
        r.2.1.keys) chal3Blocks : Finset Blocks) : Set Blocks) i) :
    Pr{let r ← (simulateQ randomOracle (game T st oa)).run' ∅}[
        r.2.2.accept = true ∧ ¬Extracted st Wit r] ≤
      (q .h21 + 1) * epsKOS #chal3Blocks (Chain.kosL st) +
        (q .h22 + 1) * (ENNReal.ofReal (Seed.epsQS (2 ^ 128) (2 ^ 64) n') + εc +
          ((n + verifierTotal : ℕ) : ℝ≥0∞) / 2 ^ 448) +
        (q .h23 + 1) * ((N : ℝ≥0∞) / 2 ^ 128) + εb + εd + εs := by
  let mx := (simulateQ randomOracle (game T st oa)).run' ∅
  have hmain := prEvent_le_comb_terms hT C hC chal3Blocks hn' hεc N (game T st oa)
    (n + verifierTotal) (isTotalQueryBound_game T st hn) (q + verifierQueries)
    (isKindQueryBound_game T st hq)
    (fun r => (r.2.2.accept = true ∧ ¬Extracted st Wit r) ∧ ¬chainFail r) (bindFail st) deadFail
    hbind hdead ?_
  · calc Pr{let r ← mx}[r.2.2.accept = true ∧ ¬Extracted st Wit r]
        ≤ Pr{let r ← mx}[((r.2.2.accept = true ∧ ¬Extracted st Wit r) ∧ ¬chainFail r) ∨
            chainFail r] := prEvent_mono mx _ _ fun r h => by tauto
      _ ≤ Pr{let r ← mx}[(r.2.2.accept = true ∧ ¬Extracted st Wit r) ∧ ¬chainFail r] +
            Pr{let r ← mx}[chainFail r] := prEvent_or_le mx _ _
      _ ≤ _ := by
          refine add_le_add (hmain.trans_eq ?_) hchain
          simp [verifierQueries]
  intro g
  have hs := hsame g
  have hl := hL2 g
  simp only [evalWithAnswerFn_game] at hs hl ⊢
  set π := (evalWithAnswerFn (QueryImpl.ofFn g) oa).1
  set e := (evalWithAnswerFn (QueryImpl.ofFn g) oa).2
  rintro ⟨⟨hacc, hnex⟩, hnc⟩ hnb hnd
  obtain ⟨-, leaves, hr, -⟩ := (accept_iff _ T st π).1 hacc
  obtain ⟨hiv, hc1⟩ := verify_iv_chal1 _ T st π hacc hr
  have hr' : BAVC.reconstruct (verify (Hashes.ofTable g) T st π).iv (Proof.opening ⟨st.params, π⟩)
      (Proof.delta ⟨st.params, π⟩) = some leaves := by rw [hiv]; exact hr
  have hbinds : Binds st (π, e, verify (Hashes.ofTable g) T st π) := by
    by_contra hb; exact hnb ⟨hacc, hb⟩
  have huc := outChain_u_dc (Hashes.ofTable g) T st (π, e, verify (Hashes.ofTable g) T st π) leaves
    hiv
  have hbad := combBad_of_accept hT C N Wit hcomb hvals hdet hacc hr
    (fun i hi j hj hji => hbinds leaves hr' i hi j hj hji) (hs hacc hnc leaves hr')
    (hl hacc hnc hnd leaves hr')
    (by
      rintro ⟨i, hi, hw⟩
      refine hnex ⟨i, hi, ?_⟩
      simp only [huc.1, huc.2, hc1]
      exact hw)
  have hlog := inLog_verifyQ g T st π hacc hr e.keys
  rcases hbad with hb | hb | hb
  · obtain ⟨x, hx, hx1⟩ := exists_of_inLog (inLog_game hlog.1)
    exact ⟨x, hx, hx1 ▸ hb⟩
  · obtain ⟨x, hx, hx1⟩ := exists_of_inLog (inLog_game hlog.2.1)
    exact ⟨x, hx, hx1 ▸ hb⟩
  · obtain ⟨x, hx, hx1⟩ := exists_of_inLog (inLog_game hlog.2.2)
    exact ⟨x, hx, hx1 ▸ hb⟩

/-! ### Per relation, numerically -/

omit [VoleMole.Verifier.HasPrg] in
lemma ofArr_combinationOf_ba {M : ℕ} (v : Bytes (16 * M)) :
    ofArr (n := M) (combinationOf M v.ba) = combDec v := by
  funext k; exact ofArr_combinationOf _ k

set_option exponentiation.threshold 500 in
set_option maxRecDepth 4000 in
/-- **Moussaka redemption against the random oracle** (at most 64 anchors): the executable
verifier accepts and the extractor's candidate is not a redemption witness with probability
`≤ (q₁+1)·2⁻¹⁵⁰ + (q₂+1)·(ε_QS(4409) + 2⁻¹²⁸ + (n+337)·2⁻⁴⁴⁸) + (Q+1)·9·2⁻¹²⁸ + ε_bind + ε_dead +
ε_chain`. -/
theorem moussakaRedeem_accept_le (anchors : List UovPk) (hn64 : anchors.length ≤ 64)
    (nf ctxIss ctxRed challengeDigest : ByteArray) (labelRows : Bool)
    (preOf midOf : ByteArray → Table → Chain) (accOf : ByteArray → Table → Bytes 16 → Prop)
    (hC : (CombData.ofSys (st := moussakaRedeem anchors nf ctxIss ctxRed challengeDigest labelRows)
      preOf midOf (moussakaRedeemSysL anchors nf ctxIss ctxRed)
      (moussakaRedeemWit GF256.ofBits (anchors.map UovPk.map) (fnOf nf) (fnOf ctxIss)
        (fnOf ctxRed)) accOf (toBA (VoleMole.Spec.makeDst "mous" 0 'l' '0'))).Committed)
    (oa : OracleComp spec (ByteArray × ExtData β)) (n : ℕ) (hn : IsTotalQueryBound oa n)
    (q : Kind → ℕ) (hq : IsKindQueryBound oa q)
    (chainFail deadFail : Out β → Prop) {εb εd εs : ℝ≥0∞}
    (hbind : Pr{let r ← (simulateQ randomOracle (game CrtGen.tables (moussakaRedeem anchors nf ctxIss ctxRed challengeDigest labelRows) oa)).run' ∅}[
      bindFail (moussakaRedeem anchors nf ctxIss ctxRed challengeDigest labelRows) r] ≤ εb)
    (hdead : Pr{let r ← (simulateQ randomOracle (game CrtGen.tables (moussakaRedeem anchors nf ctxIss ctxRed challengeDigest labelRows) oa)).run' ∅}[
      deadFail r] ≤ εd)
    (hchain : Pr{let r ← (simulateQ randomOracle (game CrtGen.tables (moussakaRedeem anchors nf ctxIss ctxRed challengeDigest labelRows) oa)).run' ∅}[
      chainFail r] ≤ εs)
    (hsame : ∀ g : Table, let r := evalWithAnswerFn (QueryImpl.ofFn g) (game CrtGen.tables (moussakaRedeem anchors nf ctxIss ctxRed challengeDigest labelRows) oa)
      r.2.2.accept = true → ¬chainFail r → ∀ leaves, BAVC.reconstruct r.2.2.iv
        (Proof.opening ⟨(moussakaRedeem anchors nf ctxIss ctxRed challengeDigest labelRows).params, r.1⟩) (Proof.delta ⟨(moussakaRedeem anchors nf ctxIss ctxRed challengeDigest labelRows).params, r.1⟩) = some leaves →
      let ch := runChain (Hashes.ofTable g) CrtGen.tables (moussakaRedeem anchors nf ctxIss ctxRed challengeDigest labelRows) r.1 leaves r.2.1.keys
      SameChain (moussakaRedeem anchors nf ctxIss ctxRed challengeDigest labelRows) CrtGen.tables preOf midOf accOf g ch (runX (Hashes.ofTable g) (moussakaRedeem anchors nf ctxIss ctxRed challengeDigest labelRows) r.1 leaves)
        (runY (Hashes.ofTable g) (moussakaRedeem anchors nf ctxIss ctxRed challengeDigest labelRows) ch) (runZ (moussakaRedeem anchors nf ctxIss ctxRed challengeDigest labelRows) ch))
    (hL2 : ∀ g : Table, let r := evalWithAnswerFn (QueryImpl.ofFn g) (game CrtGen.tables (moussakaRedeem anchors nf ctxIss ctxRed challengeDigest labelRows) oa)
      r.2.2.accept = true → ¬chainFail r → ¬deadFail r → ∀ leaves, BAVC.reconstruct r.2.2.iv
        (Proof.opening ⟨(moussakaRedeem anchors nf ctxIss ctxRed challengeDigest labelRows).params, r.1⟩) (Proof.delta ⟨(moussakaRedeem anchors nf ctxIss ctxRed challengeDigest labelRows).params, r.1⟩) = some leaves →
      ∀ i ∉ r.2.1.known, IsFixed ((onSet (moussakaRedeem anchors nf ctxIss ctxRed challengeDigest labelRows) CrtGen.tables (runChain (Hashes.ofTable g)
        CrtGen.tables (moussakaRedeem anchors nf ctxIss ctxRed challengeDigest labelRows) r.1 leaves r.2.1.keys) chal3Blocks : Finset Blocks) : Set Blocks) i) :
    Pr{let r ← (simulateQ randomOracle (game CrtGen.tables
      (moussakaRedeem anchors nf ctxIss ctxRed challengeDigest labelRows) oa)).run' ∅}[
        r.2.2.accept = true ∧ ¬Extracted
          (moussakaRedeem anchors nf ctxIss ctxRed challengeDigest labelRows)
          (fun _ => moussakaRedeemWit GF256.ofBits (anchors.map UovPk.map) (fnOf nf)
            (fnOf ctxIss) (fnOf ctxRed)) r] ≤
      (q .h21 + 1) * (2 ^ 150 : ℝ≥0∞)⁻¹ +
        (q .h22 + 1) * (ENNReal.ofReal (Seed.epsQS (2 ^ 128) (2 ^ 64) 4409) +
          (2 ^ 128 : ℝ≥0∞)⁻¹ + ((n + verifierTotal : ℕ) : ℝ≥0∞) / 2 ^ 448) +
        (q .h23 + 1) * ((9 : ℝ≥0∞) / 2 ^ 128) + εb + εd + εs := by
  classical
  refine (prEvent_accept_le_comb_terms liftInvOk_tables _ hC
    (fun _ _ _ => Moussaka.redeemSystem_length _ _ _ _ _ _ _)
    (fun _ _ w => prU_comb_bad_le _ _ w fun hW =>
      moussaka_redeem_comb_bad_gf128 _ (by simpa using hn64) _ _ _ w hW) 9 _ rfl
    (fun _ _ v w => by
      rw [moussakaRedeem_values]; simp only [moussakaRedeemSys, ofArr_combinationOf_ba]; rfl)
    (fun y g ch known acc l _ hv A hA hAS hkos hQS hcb hP =>
      moussakaRedeem_extract_chain anchors nf ctxIss ctxRed challengeDigest labelRows ch l hv hA
        hAS hkos hP.1 hQS hcb admissible deltaBlocks deltaBlocks_injOn acc hP.2)
    oa n hn q hq chainFail deadFail hbind hdead hchain hsame hL2).trans ?_
  gcongr
  · exact epsKOS_chal3Blocks_le _ (by norm_num [moussakaRedeem]) (by norm_num [moussakaRedeem])
  · norm_num

set_option exponentiation.threshold 500 in
set_option maxRecDepth 8000 in
/-- **Ratatouille spend against the random oracle** (`d < 2⁶⁴`):
`≤ (q₁+1)·2⁻¹⁵⁰ + (q₂+1)·(ε_QS(12282) + 2⁻¹²⁸ + (n+337)·2⁻⁴⁴⁸) + (Q+1)·9·2⁻¹²⁸ + ε_bind + ε_dead +
ε_chain`. -/
theorem ratatouilleSpend_accept_le (pk : UovPk) (nf : ByteArray) (d : ℕ) (hd : d < 2 ^ 64)
    (cNext ctxIss : ByteArray) (labelRows : Bool)
    (preOf midOf : ByteArray → Table → Chain) (accOf : ByteArray → Table → Bytes 16 → Prop)
    (hC : (CombData.ofSys (st := ratatouilleSpend pk nf d cNext ctxIss labelRows)
      preOf midOf (ratatouilleSpendSysL pk nf d cNext ctxIss)
      (ratatouilleSpendWit GF256.ofBits pk.map (fnOf nf) d (fnOf cNext) (fnOf ctxIss)) accOf
      (toBA (VoleMole.Spec.makeDst "rata" 0 'l' '0'))).Committed)
    (oa : OracleComp spec (ByteArray × ExtData β)) (n : ℕ) (hn : IsTotalQueryBound oa n)
    (q : Kind → ℕ) (hq : IsKindQueryBound oa q)
    (chainFail deadFail : Out β → Prop) {εb εd εs : ℝ≥0∞}
    (hbind : Pr{let r ← (simulateQ randomOracle (game CrtGen.tables (ratatouilleSpend pk nf d cNext ctxIss labelRows) oa)).run' ∅}[
      bindFail (ratatouilleSpend pk nf d cNext ctxIss labelRows) r] ≤ εb)
    (hdead : Pr{let r ← (simulateQ randomOracle (game CrtGen.tables (ratatouilleSpend pk nf d cNext ctxIss labelRows) oa)).run' ∅}[
      deadFail r] ≤ εd)
    (hchain : Pr{let r ← (simulateQ randomOracle (game CrtGen.tables (ratatouilleSpend pk nf d cNext ctxIss labelRows) oa)).run' ∅}[
      chainFail r] ≤ εs)
    (hsame : ∀ g : Table, let r := evalWithAnswerFn (QueryImpl.ofFn g) (game CrtGen.tables (ratatouilleSpend pk nf d cNext ctxIss labelRows) oa)
      r.2.2.accept = true → ¬chainFail r → ∀ leaves, BAVC.reconstruct r.2.2.iv
        (Proof.opening ⟨(ratatouilleSpend pk nf d cNext ctxIss labelRows).params, r.1⟩) (Proof.delta ⟨(ratatouilleSpend pk nf d cNext ctxIss labelRows).params, r.1⟩) = some leaves →
      let ch := runChain (Hashes.ofTable g) CrtGen.tables (ratatouilleSpend pk nf d cNext ctxIss labelRows) r.1 leaves r.2.1.keys
      SameChain (ratatouilleSpend pk nf d cNext ctxIss labelRows) CrtGen.tables preOf midOf accOf g ch (runX (Hashes.ofTable g) (ratatouilleSpend pk nf d cNext ctxIss labelRows) r.1 leaves)
        (runY (Hashes.ofTable g) (ratatouilleSpend pk nf d cNext ctxIss labelRows) ch) (runZ (ratatouilleSpend pk nf d cNext ctxIss labelRows) ch))
    (hL2 : ∀ g : Table, let r := evalWithAnswerFn (QueryImpl.ofFn g) (game CrtGen.tables (ratatouilleSpend pk nf d cNext ctxIss labelRows) oa)
      r.2.2.accept = true → ¬chainFail r → ¬deadFail r → ∀ leaves, BAVC.reconstruct r.2.2.iv
        (Proof.opening ⟨(ratatouilleSpend pk nf d cNext ctxIss labelRows).params, r.1⟩) (Proof.delta ⟨(ratatouilleSpend pk nf d cNext ctxIss labelRows).params, r.1⟩) = some leaves →
      ∀ i ∉ r.2.1.known, IsFixed ((onSet (ratatouilleSpend pk nf d cNext ctxIss labelRows) CrtGen.tables (runChain (Hashes.ofTable g)
        CrtGen.tables (ratatouilleSpend pk nf d cNext ctxIss labelRows) r.1 leaves r.2.1.keys) chal3Blocks : Finset Blocks) : Set Blocks) i) :
    Pr{let r ← (simulateQ randomOracle (game CrtGen.tables
      (ratatouilleSpend pk nf d cNext ctxIss labelRows) oa)).run' ∅}[
        r.2.2.accept = true ∧ ¬Extracted (ratatouilleSpend pk nf d cNext ctxIss labelRows)
          (fun _ => ratatouilleSpendWit GF256.ofBits pk.map (fnOf nf) d (fnOf cNext)
            (fnOf ctxIss)) r] ≤
      (q .h21 + 1) * (2 ^ 150 : ℝ≥0∞)⁻¹ +
        (q .h22 + 1) * (ENNReal.ofReal (Seed.epsQS (2 ^ 128) (2 ^ 64) 12282) +
          (2 ^ 128 : ℝ≥0∞)⁻¹ + ((n + verifierTotal : ℕ) : ℝ≥0∞) / 2 ^ 448) +
        (q .h23 + 1) * ((9 : ℝ≥0∞) / 2 ^ 128) + εb + εd + εs := by
  classical
  refine (prEvent_accept_le_comb_terms liftInvOk_tables _ hC
    (fun _ _ _ => Ratatouille.spendSystem_length _ _ _ _ _ _ _ _)
    (fun _ _ w => prU_comb_bad_le _ _ w fun hW =>
      ratatouille_spend_comb_bad_gf128 _ _ hd _ _ w hW) 9 _ rfl
    (fun _ _ v w => by
      rw [ratatouilleSpend_values]; simp only [ratatouilleSpendSys, ofArr_combinationOf_ba]; rfl)
    (fun y g ch known acc l _ hv A hA hAS hkos hQS hcb hP =>
      ratatouilleSpend_extract_chain pk nf d cNext ctxIss labelRows ch l hv hA hAS hkos hP.1 hQS
        hcb admissible deltaBlocks deltaBlocks_injOn acc hP.2)
    oa n hn q hq chainFail deadFail hbind hdead hchain hsame hL2).trans ?_
  gcongr
  · exact epsKOS_chal3Blocks_le _ (by norm_num [ratatouilleSpend])
      (by norm_num [ratatouilleSpend])
  · norm_num

set_option exponentiation.threshold 500 in
set_option maxRecDepth 4000 in
/-- **PomFRIT redemption against the random oracle**: the executable verifier accepts and the
extractor's candidate is not a signature witness for the target at the verifier's `chal1` with
probability `≤ (q₁+1)·2⁻¹⁵⁰ + (q₂+1)·(ε_QS(1313) + 2⁻¹²⁸ + (n+337)·2⁻⁴⁴⁸) + (Q+1)·2·2⁻¹²⁸ + ε_bind +
ε_dead + ε_chain`. -/
theorem pomfritRedeem_accept_le (pk : UovPk) (sig msg : ByteArray) (labelRows : Bool)
    (preOf midOf : ByteArray → Table → Chain) (accOf : ByteArray → Table → Bytes 16 → Prop)
    (hC : (pomfritData pk sig msg labelRows preOf midOf accOf).Committed)
    (oa : OracleComp spec (ByteArray × ExtData β)) (n : ℕ) (hn : IsTotalQueryBound oa n)
    (q : Kind → ℕ) (hq : IsKindQueryBound oa q)
    (chainFail deadFail : Out β → Prop) {εb εd εs : ℝ≥0∞}
    (hbind : Pr{let r ← (simulateQ randomOracle (game CrtGen.tables (pomfritRedeem pk sig msg labelRows) oa)).run' ∅}[
      bindFail (pomfritRedeem pk sig msg labelRows) r] ≤ εb)
    (hdead : Pr{let r ← (simulateQ randomOracle (game CrtGen.tables (pomfritRedeem pk sig msg labelRows) oa)).run' ∅}[
      deadFail r] ≤ εd)
    (hchain : Pr{let r ← (simulateQ randomOracle (game CrtGen.tables (pomfritRedeem pk sig msg labelRows) oa)).run' ∅}[
      chainFail r] ≤ εs)
    (hsame : ∀ g : Table, let r := evalWithAnswerFn (QueryImpl.ofFn g) (game CrtGen.tables (pomfritRedeem pk sig msg labelRows) oa)
      r.2.2.accept = true → ¬chainFail r → ∀ leaves, BAVC.reconstruct r.2.2.iv
        (Proof.opening ⟨(pomfritRedeem pk sig msg labelRows).params, r.1⟩) (Proof.delta ⟨(pomfritRedeem pk sig msg labelRows).params, r.1⟩) = some leaves →
      let ch := runChain (Hashes.ofTable g) CrtGen.tables (pomfritRedeem pk sig msg labelRows) r.1 leaves r.2.1.keys
      SameChain (pomfritRedeem pk sig msg labelRows) CrtGen.tables preOf midOf accOf g ch (runX (Hashes.ofTable g) (pomfritRedeem pk sig msg labelRows) r.1 leaves)
        (runY (Hashes.ofTable g) (pomfritRedeem pk sig msg labelRows) ch) (runZ (pomfritRedeem pk sig msg labelRows) ch))
    (hL2 : ∀ g : Table, let r := evalWithAnswerFn (QueryImpl.ofFn g) (game CrtGen.tables (pomfritRedeem pk sig msg labelRows) oa)
      r.2.2.accept = true → ¬chainFail r → ¬deadFail r → ∀ leaves, BAVC.reconstruct r.2.2.iv
        (Proof.opening ⟨(pomfritRedeem pk sig msg labelRows).params, r.1⟩) (Proof.delta ⟨(pomfritRedeem pk sig msg labelRows).params, r.1⟩) = some leaves →
      ∀ i ∉ r.2.1.known, IsFixed ((onSet (pomfritRedeem pk sig msg labelRows) CrtGen.tables (runChain (Hashes.ofTable g)
        CrtGen.tables (pomfritRedeem pk sig msg labelRows) r.1 leaves r.2.1.keys) chal3Blocks : Finset Blocks) : Set Blocks) i) :
    Pr{let r ← (simulateQ randomOracle (game CrtGen.tables
      (pomfritRedeem pk sig msg labelRows) oa)).run' ∅}[
        r.2.2.accept = true ∧ ¬Extracted (pomfritRedeem pk sig msg labelRows)
          (fun c1 => pomfritWit GF256.ofBits 119 45 pk.map
            (fun k => ⟨fnOf (pomfritTarget (pomfritParams labelRows) pk.digest c1 sig msg) k.val⟩))
          r] ≤
      (q .h21 + 1) * (2 ^ 150 : ℝ≥0∞)⁻¹ +
        (q .h22 + 1) * (ENNReal.ofReal (Seed.epsQS (2 ^ 128) (2 ^ 64) 1313) +
          (2 ^ 128 : ℝ≥0∞)⁻¹ + ((n + verifierTotal : ℕ) : ℝ≥0∞) / 2 ^ 448) +
        (q .h23 + 1) * ((2 : ℝ≥0∞) / 2 ^ 128) + εb + εd + εs := by
  classical
  refine (prEvent_accept_le_comb_terms liftInvOk_tables _ hC
    (fun _ _ _ => PomFRIT.pomfritRedeemSystem_length _ _ _ _ _ _ _)
    (fun _ _ w => prU_comb_bad_le _ _ w fun hW => pomfrit_comb_bad_gf128 _ _ _ _ w hW) 2 _ rfl
    (fun _ _ v w => by
      rw [pomfritRedeem_values]; simp only [pomfritRedeemSys, ofArr_combinationOf_ba]; rfl)
    (fun y g ch known acc l hch1 hv A hA hAS hkos hQS hcb hP => by
      rw [hch1]
      exact pomfritRedeem_extract_chain pk sig msg labelRows ch _ l hv hA hAS hkos hP.1 hQS hcb
        admissible deltaBlocks deltaBlocks_injOn acc hP.2)
    oa n hn q hq chainFail deadFail hbind hdead hchain hsame hL2).trans ?_
  gcongr
  · exact epsKOS_chal3Blocks_le _ (by norm_num [pomfritRedeem, pomfritParams])
      (by norm_num [pomfritRedeem, pomfritParams])
  · norm_num

end VoleMole.ROM
