# Plan: mechanizing the classical probabilistic steps

Status: **phase A (M1–M3) implemented** in `VoleMole/Prob/` (Mathlib only, no new dependency), with
the deviations listed in §2a. **Phase B: M4 done, M5 done** in `VoleMole/ROM/` (VCVio), including
the run of the executable verifier against the oracle (§2c); what remains is listed at the end of
§2c. **M6: done for the soundness game with a fixed statement**: binding (`ε_bind`) in the
ideal-cipher model, PRF view (§2d), its residual `ε_open` (§2e), and now the "same chain" step
(`ε_chain`) and L2 (`ε_dead`) after correcting the L2 interface (§2f, finding F2): for all five
relations, `Pr[accept ∧ ¬Extracted]` is bounded by an explicit function of the prover's query counts
alone (`ROM/CipherFull.lean`, `*_accept_le_full`). Scope: the classical (ROM + ideal cipher) proof of knowledge
of `docs/extraction/README.md`. The ZK hybrids (`docs/zk.md` §10, "proved only on paper") and the
QROM documents (Q1–Q7) are out of scope here. Notes on ZK are at the end.

## 0. Where we stand

The deterministic cores are in Lean. Each per-relation theorem `*_extract_chain`
(`Verifier/Bridge/ChainRelations.lean`) still takes these hypotheses:

| Hypothesis | Lemma | Existing Lean count | Missing probability statement |
|---|---|---|---|
| `hkos : KOSGood ch.kosCh S (lift T) (ch.kosQ …) (ch.kosD …)` | L3 | `Seed.card_not_kosGood_le` (`#bad ≤ \|S\|³(\|F\|⁴\|T\| + (L−1)⁵\|F\|⁴)` over `Ch F T`) | uniform `chal1` (136 bytes) ⇒ `Pr[¬KOSGood] ≤ ε_KOS`; then a union over `q₁` H₂¹ queries (RO) |
| `hQS` | L4 | `EndToEnd.card_qs_bad_le`, `Seed.zkHash_prob_le` (over `chalSpace S`) | uniform `chal2` (56 bytes) ⇒ `Pr[bad] ≤ ε_QS(n)` for the **canonical** slope (§M2); union over `q₂` (RO) |
| `hcomb` (3 combined relations) | L4 | `*_comb_bad`, `*_comb_bad_gf128`, `SeedExtraction.combination_prob` | `l` uniform and independent of `chal2` ⇒ `Pr ≤ 1/\|F\|`; RO freshness of `chal2 ‖ dst` (`q_c·2⁻⁴⁴⁸`) |
| `hδ : Set.InjOn δ Z` | L1 (bookkeeping) | none | **deterministic**: `chal3` with zero grinding bits ↦ `blocksOf (deltaBit ·)` is injective |
| `hclaim1` | L1 | `onChain_of_accept` (given `hrun`) | binding of leaf commitments (ideal cipher, C1–C3) and the RO "same chain" step |
| `hL2 : ∀ i ∉ known, IsFixed A i` | L2 | `isFixed_hideSet` with `A = hideSet` | done (§2f): `A` the challenges on the chain hiding the committed dead leaves; L2(c) and L2(a) in `ROM/CipherSame.lean` |
| final step: "at most `max(d,1)` accepted ⇒ accepted with prob. ≤ `max(d,1)·2⁻¹²⁸`" | assembly step 4 | the `#{x ∈ Z \| acc x} ≤ max d 1` conclusion | uniform `chal3` ⇒ per query; union over `Q` H₂³ queries (RO) |

So three kinds of work remain:
- **(a) Single-sample statements.** A uniform challenge drawn independently of fixed data, turned
  from a count into a probability. These need no oracle model. They are almost free given the
  `*_card` lemmas, apart from byte decoding.
- **(b) Random-oracle bookkeeping.** "A fresh RO answer is uniform and independent of the view."
  A union bound over the `q₁`, `q₂`, `Q` queries. Freshness of `chal2 ‖ dst`. The "same chain" step:
  an accepted proof's H₂ inputs occur in the log, otherwise guessing costs `2⁻ᵏ`.
- **(c) Ideal-cipher arguments** (L1/L2: C1–C3, `ε_bind`, `ε_dead`). These are the biggest and the
  least reusable.

## 1. Framework

**Options.**
- **VCVio** (github.com/dtumad/VCV-io, Apache-2.0, very active). `OracleComp`, `ProbComp`,
  `SampleableType` / `$ᵗ`, `simulateQ`, a lazy random oracle `OracleSpec.randomOracle`
  (`QueryTracking/RandomOracle/{Basic,Eager,DeferredSampling,FreshQuery,Programming}.lean`), the
  query bounds `IsQueryBound` / `IsPerIndexQueryBound` / `IsTotalQueryBound`
  (`QueryTracking/QueryBound/Basic.lean`), birthday/collision bounds (`QueryTracking/Birthday.lean`,
  `Collision.lean`, `Unpredictability.lean`), a forking lemma, Fiat–Shamir for Σ-protocols, and a
  pRHL-style program logic. The core has no `sorry`; about 11 remain in the lattice/signature
  examples. Paper: ePrint 2024/1819, which describes the older PMF API.
  - **Caveat:** PR #710 (Sep 2026) made `evalDist` `Measure`-valued (`𝒟[mx]`, `Pr{let x ← mx}[p x]`
    = `prEvent`). `probOutput` and `Pr[= x | oa]` are gone. Expect API churn on each bump.
- **Mathlib only** (`PMF.uniformOfFintype`, `PMF.bind/map`, `PMF.toOuterMeasure`,
  `ProbabilityTheory.uniformOn`). No new dependency. Enough for (a). For (b) we would hand-roll
  oracle computations, lazy sampling and query logs, which means re-doing what VCVio already has.
- **EasyCrypt** is the most mature tool for pRHL/ROM game hopping, but it is a separate tool: the
  proofs could not reuse our Lean cores or the verifier model. **SSProve** (Rocq) and **CryptHOL**
  (Isabelle; VCVio's conceptual ancestor) are mentioned only for comparison. No competing Lean
  framework exists. ArkLib (Verified-zkEVM) builds on VCVio and is worth watching for IOP / FS
  round-by-round soundness.

**Version compatibility, concretely.**
- **Ours:** toolchain `v4.34.0-rc1`, Mathlib tag `v4.34.0-rc1` = `de5ce8a9` (2026-08-11). (Since
  M4: `v4.34.0`, Mathlib `5ed29652`, VCVio `afa6593f`; §2b.)
- **VCVio `main`** (`afa6593f`, 2026-10-11) and tag `v4.34.0` (2026-09-17): toolchain `v4.34.0`,
  Mathlib `v4.34.0` = `5ed29652` (2026-09-15). VCVio tracks only stable tags and has never built
  against `-rc1`.
- **So yes, adding it forces a bump:** `v4.34.0-rc1 → v4.34.0`. That is one step within the same
  series, about 5 weeks of Mathlib, with `rc2` in between. Keeping rc1 as the root pin would make
  VCVio fail to compile. Using VCVio `v4.33.1` would mean downgrading and an older (pre-#710) API.
- **New transitive dependencies:** PolyFun, cslib (only for the optional `VCVioCslib` lib), Cli. The
  VCVio core is about 400 files / 100k lines to build. Check `lake exe cache get` coverage for
  VCVio itself; it has no Mathlib-style cache, so its first build is local.
- **Expected breakage from the bump** is small to moderate. rc1 → stable changes are usually
  renames and simp-set changes. The risky spots are `decide +kernel` proofs and the
  heavy-computation files (`Arith/GFField.lean`, `CrtSearch`, `Keygen`). Do it as a separate
  commit, under the OOM rules (one worker, `MemoryMax`).
- These version facts were read from GitHub on 2026-10-14. No build was attempted.

**Recommendation: VCVio, introduced in two phases.**
- **Phase A (M1–M3), Mathlib only, no bump.** Phrase every single-sample statement over Mathlib
  `PMF.uniformOfFintype`, which is what VCVio's `SampleableType` is specified against
  (`𝒟[$ᵗ β] = uniformOn univ`). The phase-A lemmas then transfer unchanged.
- **Phase B (M4+).** Bump to Mathlib `v4.34.0` and `require VCVio` at tag `v4.34.0` (or a pinned
  `main` rev), in a new lib `VoleMole/ROM/` so that the rest of the library doesn't import it. Use
  VCVio's lazy RO, query bounds and logging oracles for the union bounds and freshness.
- **Why not hand-roll:** the query-bound and lazy-sampling infrastructure is exactly the error-prone
  part, and VCVio has it, proved.
- **Why not EasyCrypt:** the end goal is one Lean theorem over the executable verifier.

## 2. Milestones

Effort is in agent-days of focused work, assuming the current proof style.

### M1 — Probability layer and byte decoding (Phase A, ~2–3 days) — done

New file `VoleMole/Prob/Uniform.lean`:
```lean
/-- Probability of `P` under the uniform distribution on a finite type. -/
noncomputable def prU (α) [Fintype α] [Nonempty α] (P : α → Prop) : ℝ≥0∞ :=
  (PMF.uniformOfFintype α).toOuterMeasure {x | P x}
theorem prU_eq_card [DecidablePred P] : prU α P = #{x | P x} / Fintype.card α
theorem prU_le_of_card_le (h : #{x | P x} ≤ N) : prU α P ≤ N / Fintype.card α
theorem prU_or_le : prU α (fun x => P x ∨ R x) ≤ prU α P + prU α R
theorem prU_map_equiv (e : α ≃ β) : prU β P = prU α (P ∘ e)
theorem prU_prod_le (h : ∀ b, prU α (fun a => P (a, b)) ≤ ε) : prU (α × β) P ≤ ε
```
Byte models (`ByteArray` is not a `Fintype`): `Bytes n := Fin n → UInt8` with `toBA : Bytes n →
ByteArray`. Decoding equivalences:
- `gf128OfBytesEquiv : Bytes 16 ≃ GF128` (`gfOfBytes`, i.e. `W128.ofBytes … |>.toGF`);
- `chal1Equiv : Bytes 136 ≃ Seed.Ch GF128 shortKeys`, with `(chOf gfId mem_shortKeys (toBA b))`
  as its forward map (8 field elements plus the low 64 bits of word 128);
- `chal2Equiv : Bytes 56 ≃ GF128 × GF128 × GF128 × shortKeys`, matching the arguments that
  `*_extract_chain` passes to `zkCoeff` (`gfOfBytes (chal2) 0/16/32`, `⟨W128.word chal2 48, 0⟩`), as
  an element of `chalSpace shortKeys`;
- `card_shortKeys : #shortKeys = 2^64` (proved by injectivity, not by `decide`).

### M2 — First target: single-challenge bounds for L3 and L4 (Phase A, ~4–6 days) — done

These have the best value per effort. They turn the existing `*_card` lemmas into the exact
probability statements the hypotheses need, at the executable verifier's challenge encoding.

**L3 (`hkos`).** One prerequisite step: `kosQ`/`kosD` must not depend on `chal1`. `Chain.resp` is
built from `proof`, `keys` and `iv` only, but the statement must say so. Add
`Chain.withChal1 (ch) (c : ByteArray)` (replaces the field) and the `rfl` lemmas
`kosQ_withChal1 : (ch.withChal1 c).kosQ st T = ch.kosQ st T` (and the same for `kosD`).
```lean
theorem prU_not_kosGood (T' : Finset F) (S : Finset X) (he : Set.InjOn e S) (Q D) :
    prU (Seed.Ch F T') (fun c => ¬ KOSGood c S e Q D) ≤
      (#S^3 * (card F^4 * #T' + (L-1)^5 * card F^4) : ℝ≥0∞) / (card F^8 * #T')
-- at the executable encoding, all five relations:
theorem chain_kos_bad_le (st) (ch : Chain) (S : Finset Blocks) :
    prU (Bytes 136) (fun b => ¬ KOSGood (ch.withChal1 (toBA b)).kosCh S (lift CrtGen.tables)
        (ch.kosQ st CrtGen.tables) (ch.kosD st CrtGen.tables)) ≤ epsKOS #S (kosL st)
theorem epsKOS_num : #S ≤ 2^120 → kosL st ≤ 2^13 → epsKOS … ≤ 2^(-150)   -- the Lean |S|³ is 6× looser than C(|S|,3)
```

**L4 (`hQS`, `hcomb`): the canonical slope first.** The hypotheses quantify over every `A` with
`|A| ≥ 2` and every slope `uStar` on `A`, and `A` depends on `chal2` (`OnChain` includes the `z`
check). L4 §5 resolves this, and we mechanize it deterministically:
```lean
/-- A_V: the challenges in S on which the VOLE check passes with the chain's h_V (no chal2). -/
def Chain.AV (st ch T S) : Finset Blocks
noncomputable def Chain.uCanon : Fin st.params.witnessBits → GF128  -- slope on A_V if |A_V| ≥ 2, else 0
theorem slope_eq_uCanon (hkos : KOSGood …) (hA : ∀ Δ ∈ A, ch.OnChain st T Δ) (hAS : A ⊆ S)
    (h2 : 2 ≤ #A) (hs : ∀ j, ∃ v, ∀ Δ ∈ A, ch.Qw st T j Δ = v + uStar j * lift T Δ) :
    uStar = ch.uCanon st T S
```
(Uses `lift_injective`; on `A_V ⊇ A` the line is unique.) Then `hQS`/`hcomb` in `*_extract_chain`
follow from a single event about `w* = uCanon + d`, which is fixed before `chal2`.

**L4: the probability.** Make `chal2` an argument (`Chain.withChal2` / a `chal2` field with the
SHAKE equation as a hypothesis in `onChain_of_accept`; see Risks). Then:
```lean
-- issue relations (no l):
theorem chain_qs_bad_le (cs : System GF128) (w : ℕ → GF128) :
    prU (Bytes 56) (fun b => ¬cs.Holds w ∧ zkHash cs.length (chal2Equiv b).… (valVec cs w) = 0)
      ≤ ENNReal.ofReal (epsQS (2^128) (2^64) cs.length)
-- combined relations: over (chal2, l) independent, systems parametrised by l
theorem pomfrit_qs_comb_bad_le (w) :
    prU (Bytes 56 × (Fin 45 → GF128)) (fun (b, l) =>
      (¬(pomfritRedeemSystem … l).Holds w ∧ zkHash … = 0) ∨
      ((pomfritRedeemSystem … l).Holds w ∧ ¬pomfritWit … w))
      ≤ ENNReal.ofReal (epsQS (2^128) (2^64) n) + 2^(-128)
```
(Built from `card_qs_bad_le` per fixed `l` + `prU_prod_le`, and `*_comb_bad_gf128` + `prU_or_le`.)
The step "the `l` the verifier computes as `SHAKE(chal2 ‖ dst)` is uniform and independent of
`chal2`" is RO (M5). In M2 it is a hypothesis-free statement over the product space, which is what
the L4 paper proof also does.

**L1 bookkeeping (`hδ`), deterministic, ~1 day.** Take `Z := {x : Bytes 16 | grinding bits zero}`,
`δ x := blocksOf (BAVC.deltaBit (toBA x))`. Prove `Set.InjOn δ Z`, `#Z = 2^120`, so that the final
step is `prU (Bytes 16) acc ≤ max(d,1)/2^128` from `#{x ∈ Z | acc x} ≤ max d 1`.

### M3 — Per-chain conditional theorem (Phase A, ~3–4 days) — done

For a fixed chain *prefix* (everything before `chal1`, then everything between `chal1` and `chal2`
as a function of `chal1`), sample `chal1`, `chal2`, `l` uniformly and conclude, with `hL2` and
`hclaim1` still hypotheses (functions of the samples):
```lean
theorem pomfritRedeem_chain_prob (pre : ChainPrefix) (next : Bytes 136 → ChainMid) … :
    prU (Bytes 136 × Bytes 56 × (Fin 45 → GF128)) (fun ω =>
      hL2 ω ∧ hclaim1 ω ∧ ¬(extracts ω ∨ #{x ∈ Z | acc ω x} ≤ 2))
    ≤ epsKOS … + epsQS … + 2^(-128)
```
This is the classical "one chain, independent challenges" form of L3 + L4 + L6, which is exactly
the FAEST spec's per-round knowledge-soundness bound. It is a self-contained deliverable before
any RO model exists.

### 2a. Phase A as implemented, and deviations from the sketches above

Files: `Prob/Uniform.lean` (M1), `Prob/Bytes.lean` (M1, and `hδ` of M2), `Prob/Challenges.lean`
(M2), `Prob/ChainRelations.lean` (M3). `#print axioms` of the main results: `propext`,
`Classical.choice`, `Quot.sound`.

- **The chain refactor** (risk §3). `Chain` got two fields instead of `chal2` and `l`: `chal2`, and
  `vals : (ℕ → GF128) → List GF128`, the constraint evaluator of the QuickSilver check (used by
  `Chain.check`). For the executable verifier `vals = st.values chal1 chal2`, which reads
  `l = H(chal2 ‖ dst)` internally; `onChain_of_accept` takes `hc2 : chal2 = Verifier.chal2 …` and
  `hvals : vals = st.values chal1 chal2`. `chain_claim4` takes one system `cs` with
  `vals = cs.values`. `Bridge/Relations.lean` gained `moussakaRedeemSysL`, `ratatouilleSpendSysL`,
  `pomfritRedeemSysL` (the system at a free `l`; the old `*Sys … chal2` are these at
  `ofArr (combinationArr …)`, by definition), and the combined relations' `*_extract_chain` take
  `l` and `hvals : ∀ x, ch.vals x = (*SysL … l).values x`; PomFRIT's also takes the `c1` its
  target is computed from. The executable verifier and the KAT runners are untouched.
- **No `ChainPrefix`/`ChainMid` structures.** `proof` is one byte string holding data from all three
  rounds, so the per-chain theorem takes a chain family `ch : Bytes 136 × Bytes 56 × Λ → Chain`
  with hypotheses saying what it may depend on: `Chain.SamePrefix st pre (mid b₁)` (keys, `c_i`,
  `c_mult`, `iv_pre` fixed), `Chain.SameMid st (mid ω.1) (ch ω)` (`chal1`, `ũ`, `d`, `h_V` functions
  of `b₁`), `(mid b₁).chal1 = b₁`, `(ch ω).chal2 = b₂`, and `hvals` at `(b₁, l)`. `Chain.withChal1`
  and its `rfl` lemmas exist (`chain_kos_bad_le`) but M3 does not need them.
- **`chal2Equiv`** has codomain `Chal2 = GF128 × GF128 × GF128 × shortKeys` (a subtype); the count
  is transported to `chalSpace shortKeys` inside `prU_qs_bad_le`. All decodings are proved
  bijective by injectivity (`word_byte`: the words at offsets `0, 8, …` determine the bytes) and a
  cardinality count; nothing of size `≥ 2⁶⁴` is enumerated.
- **`epsKOS`** is an `ℝ≥0∞` ratio of naturals; `epsKOS_le` needs
  `set_option exponentiation.threshold 1100` (Lean refuses to evaluate `2^n` for `n > 256` by
  default). `ε_QS` stays real (`ENNReal.ofReal`), with `epsQS_le : ε_QS(n) ≤ 2⁻¹²⁷` for `n ≤ 2³²`.
- **The canonical slope.** `uCanon` is "a slope on `A_V` if one exists, else `0`" (no case on
  `|A_V| ≥ 2`: uniqueness is only needed on `A`). `slope_eq_uCanon` takes `A ⊆ A_V` (with
  `mem_AV_of_onChain`) instead of `OnChain`; `forall_slope_of_uCanon` turns a property of `uCanon`
  into `hQS`/`hcomb`'s quantified form.
- **L4 names.** `prU_qs_bad_le` (one system, uniform `chal2`), `prU_comb_bad_le` (uniform `l`,
  from a `*_comb_bad_gf128` count), `prU_qs_comb_bad_le` (both, independent, generic in the type of
  `l`) instead of one lemma per relation.
- **`hδ`.** `Z = admissible` (byte 15, the grinding bits, zero: what `check_format` accepts),
  `δ = deltaBlocks = blocksOf ∘ deltaBit`, and the KOS set is `S = deltaBlocks '' admissible`
  (`|S| ≤ 2¹²⁰`).
- **M3's statement.** `chain_prob` is generic: a deterministic theorem `hdet` of the shape of
  `*_extract_chain` is an argument, and each `*_chain_prob` instantiates it. The event is
  `ChainHyps A known acc ∧ ¬(extraction ∨ #{x ∈ admissible | acc x} ≤ max(d, 1))` with
  `A = onSet = {Δ ∈ S | OnChain}` and `ChainHyps` = L2 ∧ `hclaim1`. Bound:
  `2⁻¹⁵⁰ + ε_QS(n) + 2⁻¹²⁸`. The issue relations have no `l`: they are stated over
  `Bytes 136 × Bytes 56`, bound `2⁻¹⁵⁰ + ε_QS(n)`. The "same chain" binding is in `hclaim1`;
  hypotheses on statement data that the `*_comb_bad` counts need (`anchors.length ≤ 64`,
  `d < 2⁶⁴`) are hypotheses of the corresponding theorems.

What phase A does not give, and phase B has to: that the executable verifier's `chal1`, `chal2`
are fresh uniform RO answers on the chain and `l = H(chal2 ‖ dst)` is uniform and independent of
`chal2` (the M3 statement is over independent samples); the union over queries; L2; `hclaim1`.

### 2b. Phase B as implemented (M4, M5), and deviations

Files: `ROM/Basic.lean` (M4), `ROM/UnionBound.lean`, `ROM/Fresh.lean`, `ROM/Chains.lean`,
`ROM/Comb.lean` (M5); `Prob/Bytes.lean` gained `combEquiv`. Only `ROM/` imports VCVio.
`#print axioms` of the main results: `propext`, `Classical.choice`, `Quot.sound`.

- **The bump** (separate commit): `lean-toolchain`, `lakefile.toml`, `lake-manifest.json` to
  `v4.34.0` (Mathlib `5ed29652`, the rev VCVio pins), and three fixes: `Arith/GFField.lean`
  (`irreducible_modulus`: `simpa [hcard]` evaluated `2 ^ 64`, after which the kernel unfolded
  `X ^ 2 ^ 64` until deep recursion; now `rw`), `Protocols/UOVAssumptions.lean`
  (`Finset.prod_le_one` is now the ordered-monoid lemma; `prod_le_one₀`), `Seed/CipherSim.lean`
  (`gcongr` now closes a side goal). No `decide +kernel` proof or heavy computation broke.
- **VCVio** is pinned to `main` at `afa6593f` (2026-10-11, unchanged since the plan was written),
  not to the tag `v4.34.0`. New packages: VCVio, PolyFun, cslib. Building what `ROM/` imports takes
  about 120 modules and 2 minutes (2 threads, under 7 GB). The executables now link VCVio's empty
  native-backend stubs; all runners pass unchanged.
- **The oracle specification** is `OracleSpec.ofFn Ans` over `Dom = Kind × ByteArray`, with
  `Ans (k, x) = Bytes k.outLen`: every domain answers bytes, and `l` is decoded by
  `combEquiv M : Bytes (16·M) ≃ (Fin M → GF128)` (as `combinationOf` decodes it), so the range is
  not `Fin 45 → GF128`. `comb M` is indexed by the number of combined equations; `H₁`'s three
  shapes are one kind. The "domain separation ⇒ independent oracles" lemma was not done in M5; it
  is now (§2c).
- **The bridge** is `SampleableType.prEvent_uniformSample` (an event of `$ᵗ α` is a count) against
  `prU_eq_card`, not `evalDist_selectElem_eq_uniform` and `PMF.toMeasure`.
- **The union bound exists in VCVio**: `prEvent_randomOracle_le_of_bad_queries[_weighted]`
  (`QueryTracking/RandomOracle/FreshQuery.lean`). It is stronger than the sketch: the bad predicate
  `bad t g` may read the whole answer table (eager sampling), provided resampling the cell `t` alone
  bounds it for every background table, and the event is tied to bad queries by a deterministic
  implication over complete tables (`htrace`, with `evalWithAnswerFn`, `tableQueryLog`) instead of a
  logged run. We add per-domain counts (`IsKindQueryBound`, turned into VCVio's weighted budget)
  and state it as `prEvent_exists_bad_query_le`.
- **"Parse a prefix from `x`"** became chain data that are functions of the query input and the
  table, with the hypothesis that they do not read the query's own cell (`ChainData.Committed`; for
  `H₂²` of the combined relations, no combination cell either, `CombData.Committed`). This is the
  sketch's "committed keys are a function of the prior log", in the all-table form.
- **Freshness of `chal2 ‖ dst`** is not from the `Unpredictability`/birthday lemmas. For the combined
  relations the `H₂²` bad event reads the cell `chal2 ‖ dst`, chosen by the answer, so no single-cell
  bound holds. `ROM/Fresh.lean` re-proves VCVio's theorem with the bound averaged over the uncached
  cells of a cache of fewer than `n` keys (`prEvent_randomOracle_le_of_fresh_bad_queries`), and
  `prEvent_completeTable_le_two_cells` exposes `chal2` and then `l`. The freshness term is
  `n·2⁻⁴⁴⁸` per `H₂²` query, with `n` the total query count, instead of `q_c·2⁻⁴⁴⁸` (`n ≥ q_c`).
- **`ε_bind`, `ε_dead`** are named hypotheses on events of the game's output (`bindFail`,
  `deadFail`, `Pr ≤ ε`), split off by the union bound.
- **The theorems** (`prEvent_le_chain_terms`, `prEvent_le_comb_terms`, and numerically
  `moussakaIssue_prEvent_le`, `ratatouilleIssue_prEvent_le`, `moussakaRedeem_prEvent_le`,
  `ratatouilleSpend_prEvent_le`, `pomfritRedeem_prEvent_le`):
  `Pr[event] ≤ q₁·2⁻¹⁵⁰ + q₂·(ε_QS(n') [+ 2⁻¹²⁸ + n·2⁻⁴⁴⁸]) + Q·N·2⁻¹²⁸ + ε_bind + ε_dead`, with
  `N = max(d, 1)` as in M3 (9, or 2 for PomFRIT). The deterministic per-chain part of `htrace` is
  proved (`chain_good_of_not_bad`, `comb_good_of_not_bad`, instantiated for Moussaka and
  Ratatouille issuance and PomFRIT): a chain whose `H₂¹` and `H₂²` queries are not bad extracts or
  has at most `N` accepted `chal3`, and then an accepted `H₂³` answer is a bad query
  (`chainBad_h23_of_accept`).

Not done in M5 as first implemented, and done since (§2c): the hash-record refactor, the run of the
executable verifier against the oracle (the event concrete, `htrace` proved), `*_good_of_not_bad`
for Moussaka redemption and Ratatouille spend, and "domain separation ⇒ independent oracles".

### 2c. The executable verifier against the oracle (M5, continued), and deviations

Files: `Verifier/Hashes.lean` (the hash record), `ROM/Verifier.lean`, `ROM/Accept.lean`,
`ROM/DomainSep.lean`, `ROM/SingleOracle.lean`; the verifier, the KAT runners and the bridge files
changed as below. `#print axioms` of the main results: `propext`, `Classical.choice`,
`Quot.sound`.

- **The hash record** (`Verifier/Hashes.lean`). `Kind` and `Kind.outLen` moved here from
  `ROM/Basic.lean` (re-exported there). `Hashes` is one structure with one field
  `hash : Kind → ByteArray → ByteArray` (a function per L0 domain, indexed by `Kind` rather than
  one named field per domain, so that `Hashes.ofTable g := ⟨fun k x => (g (k, x)).ba⟩` is one
  line); the argument is the whole SHAKE input, domain byte included. `Hashes.shake` is SHAKE128
  in every domain. The steps take `Hs`: `mu Hs`, `ivOf Hs`, `chal1 Hs`, `chal2 Hs`, `chal3 Hs`,
  `crtReconstruct Hs`; the lower-level `BAVC.check h1`, `gateHashes h5`, `crtReconstructAt h5`
  take the one function they use (so a chain's response depends only on `H₅`). The inputs are
  separate definitions (`chal1Input`, `chal2Input`, `chal3Input`, `BAVC.leafHashInputs`,
  `BAVC.comInput`, `gateInputs`), and `crtReconstructWith` takes the gate hashes, so that the
  oracle version can query them. `verify Hs T st proof`; the runners use `Hashes.shake` and are
  unchanged (18 accepted / 51 rejected on both layouts, `spec_kats`, `arith_vectors`; the
  `@[csimp]` fast paths untouched).
- **The combination is hashed by the verifier.** `Statement` has a field `comb : Option (ℕ ×
  ByteArray)` (`M` and the combine DST) and `values chal1 lb` now takes the combination *bytes*
  `lb = H_comb(chal2 ‖ dst)` (`Statement.combBytes`) instead of `chal2`; `combinationArr` became
  `combinationOf n lb` (decoding only). Otherwise the verifier's queries would be hidden inside
  `values`. `Bridge/Relations.lean`'s `*Sys` take `lb` (`ofArr_combinationOf`).
- **Hashes outside L0 stay SHAKE**: the UOV key digests and expansion (computed by `UovPk` before
  verification), PomFRIT's `hash_to_target` (part of the statement, `instEnc`/`values`) and the
  refresher commitment (`pomfritVerify`). They are application-level hashes (L0 §2.5).
- **Chain**: `iv` and the gate hash `h5` are fields (were `Chain.iv`, computed with SHAKE), with
  `iv = ivOf Hs …`, `h5 = Hs.hash .h5` hypotheses of `onChain_of_accept` (generic in `Hs`);
  `Chain.SamePrefix` compares `iv`, `h5` instead of `iv_pre`. `Transcript` has an `iv` field.
- **The verifier as an oracle computation** (`ROM/Verifier.lean`): `verifyQ` makes the verifier's
  queries in order (`mu₁`, `iv`, 17 leaf hashes, `com`, `chal1`, 312 gate hashes, PomFRIT's `mu`,
  `chal2`, the combination, `chal3`); against a complete table it is `verify (Hashes.ofTable g)`
  (`evalWithAnswerFn_verifyQ`), its accepted `H₂¹`, `H₂²`, `H₂³` queries are in its log at the
  run's inputs (`inLog_verifyQ`, `runX`, `runY`, `runZ`, `runChain`), and it makes at most one
  query to each of them, 337 in total (`isKindQueryBound_verifyQ`, `isTotalQueryBound_verifyQ`).
  `game T st oa`: the prover, then `verifyQ` on its proof.
- **The extractor's data are part of the prover's output** (`ExtData β`: the committed leaf keys it
  recovered, the known trees, and an arbitrary `aux`, e.g. a log for the failure events to read).
  The ideal cipher is not modelled, so the keys cannot be computed from the oracle log: the
  statement holds for any key recovery, whose quality enters only through the assumptions below
  (read `oa` as the prover together with the straight-line extractor).
- **The event** is `accept ∧ ¬Extracted`, with `Extracted` the candidate of `*_extract_chain`
  computed from the extractor's keys, the proof and the verifier's `iv` (and `chal1` for PomFRIT's
  target). `htrace` is proved (`chainBad_of_accept`, `combBad_of_accept`): the accepted proof is on
  its run's chain at its `Δ` (`onChain_of_accept`, from binding), `*_good_of_not_bad` gives
  extraction or few accepted `chal3`, and then the verifier's own `H₂³` query is bad.
- **What remains assumed**, explicitly:
  - binding (L1, `ε_bind`): a bound on the concrete output event `bindFail` (accepted, and the
    opening's leaves at the verifier's `iv` differ from the extractor's keys at a non-hidden leaf);
  - the "same chain" step (`hsame`, outside an output event `chainFail` with `Pr ≤ ε_chain`, a new
    term): `SameChain`, i.e. the data `C` commits at the verifier's own `H₂¹`/`H₂²`/`H₂³` inputs are
    the accepted proof's chain (`pre`, `mid`), and the `chal3` accepted at the `H₂³` input are those
    on the chain (`acc`; this is where `hclaim1` went). With complete tables over an infinite domain
    the identification of the earlier queries by their answers can only be made through the log,
    so it is not derivable inside VCVio's all-table formulation;
  - L2 (`hL2`, outside `chainFail` and an output event `deadFail` with `Pr ≤ ε_dead`).
- **The bounds** (`prEvent_accept_le_chain_terms`, `prEvent_accept_le_comb_terms`;
  `moussakaIssue_accept_le`, `ratatouilleIssue_accept_le`, `moussakaRedeem_accept_le`,
  `ratatouilleSpend_accept_le`, `pomfritRedeem_accept_le`): as in §2b with the verifier's queries
  added, `(q₁+1)·2⁻¹⁵⁰ + (q₂+1)·(ε_QS(n') [+ 2⁻¹²⁸ + (n+337)·2⁻⁴⁴⁸]) + (Q+1)·N·2⁻¹²⁸ + ε_bind +
  ε_dead + ε_chain`, `q` and `n` the prover's counts.
- **Domain separation ⇒ independent oracles** (`ROM/DomainSep.lean`, not via the plan's
  "restriction of one lazy RO"): one random oracle on byte strings `spec₁ κ`, answering `x` with
  `(κ x).outLen` bytes for a domain rule `κ`; `route κ` asks `(k, x)` at `x`. If every query of
  `oa` satisfies `κ x = k`, both lazy oracles give every event the same probability
  (`prEvent_route_eq`: finite restriction, eager tables, and the bijection `(k, x) ↦ x` between
  the uniform tables). Every single-oracle adversary is such a computation (`unroute`,
  `prEvent_unroute_eq`, with its per-domain counts, `isKindQueryBound_unroute`). VCVio's
  `Routing.lean` has the non-dependent finite version only. `ROM/SingleOracle.lean`: L0's rule
  `l0Kind` (the final byte), the verifier's queries respect it (`allQueriesSatisfy_verifyQ`, for
  statements whose combination is 45 equations with a DST ending in `'0'`: all five), and the game
  against one SHAKE oracle `game₁` has the per-domain game's probabilities (`prEvent_game₁_eq`), so
  the bounds above hold for single-oracle provers. Remaining modelling: SHAKE128 as a random oracle
  with a fixed output length per input.
- **`*_good_of_not_bad`** for Moussaka redemption and Ratatouille spend (`ROM/Comb.lean`), as
  PomFRIT's.
- **Not done: the statement-binding term `(q²+q)·2⁻²⁵⁶`** (L4 (H-stmt)). VCVio's birthday lemmas
  (`prEvent_cacheCollision_le_birthday*`, `QueryTracking/Birthday.lean`) bound a collision anywhere
  in a `cachingOracle` cache with one range size (the smallest; here `H₅`'s 4 bytes), not a
  collision among `H₂⁰` answers, and the event ("μ's preimage was queried before `y`") is again an
  ordering fact about the log; it belongs with the "same chain" step.

Still open after §2c: the "same chain" step (`hsame`, `ε_chain`), L2 (`ε_dead`) and binding
(`ε_bind`) as named assumptions (M6: ideal cipher, query ordering), and the statement-binding
term. §2d replaces `ε_bind` by an explicit term and a smaller residual.

### 2d. M6, first part: binding in the ideal-cipher model, as implemented

Files: `ROM/FreshCache.lean`, `ROM/CipherBind.lean`, `ROM/CipherGame.lean`; and the ROM layer made
cipher-generic: `variable [HasPrg]` in `Verifier/Bridge/ChainRelations.lean`,
`Prob/Challenges.lean`, `Prob/ChainRelations.lean`, `ROM/Chains.lean`, `ROM/Comb.lean`,
`ROM/Verifier.lean`, `ROM/Accept.lean`, `ROM/SingleOracle.lean` (proofs unchanged; `omit` where a
lemma does not use the PRG). So every bound of §2b/§2c holds for every CTR PRG, in particular for
`icPrg E` (the CTR PRG of a cipher table `E`, `ZK/HopsH4.lean`), and at `aesPrg` it is the
statement as before. No executable definition changed. `#print axioms` of the main results:
`propext`, `Classical.choice`, `Quot.sound`.

- **The model: PRF view, forward queries.** The cipher is a random oracle on cells
  `(k, z) ↦ E_k(z)` (`cspec`, `CTable = Blk × Blk → Blk`), every row a uniform function, as on
  the ZK side (`ZK/IdealCipher.lean`, `icPrg E`). The prover queries cells; the verifier and the
  extractor *read* the table (the verifier through `icPrg E.cipher`), so their evaluations are not
  counted. A lazy random permutation per key with inverse queries (the plan's sketch) was not
  built: VCVio has none, and the cache-based argument below would have to be redone for a lazy
  permutation. **PRP/PRF:** the switching lemma costs `q_E²/2¹²⁹`, much more than the bound below,
  so it is not the route; in the permutation model the same argument runs with `2⁻¹²⁸` per fresh
  answer replaced by `p = 1/(2¹²⁸ − q_E)` (a fresh forward or inverse answer is uniform over at
  least `2¹²⁸ − q_E` values; L0-L2 §3.1), giving `2·q_E²·p²`. That version, and inverse queries
  generally, are on paper only.
- **The union bound with a cache-reading bad event** (`ROM/FreshCache.lean`). VCVio's
  `freshBadQuery` tests a fresh query with a predicate of the table only; a collision bound needs
  to know which cells were queried before. `freshBadC oa c g bad`: some log entry, at a cell not in
  the cache `c` nor earlier in the log, is bad for the cache of the earlier log
  (`cacheOfLog c pre`). `prEvent_freshBadC_le_of_cached` (VCVio's proof with the cache passed
  along): if a fresh query is bad with probability `≤ ε` over the uncached cells for every cache of
  fewer than `N` cells, an `n`-query computation meets one with probability `≤ n·ε`
  (`prEvent_le_of_freshBadC`, eager form, finite key type).
- **The collision event** (`ROM/CipherBind.lean`, C2 of L0-L2 §4 in a log-local form):
  `collBad (k, w) c E` — for a neighbour `w'` of `w` (`adj w = {w ⊞ e₀, w ⊟ e₀}`, `nxt`, `prv`;
  the two points of a leaf commitment are `x₀` and `x₁ = x₀ ⊞ e₀`, `nxt_lp`, `prv_lp`) with
  `(k, w')` not yet queried, a key `κ ≠ k` with a cached cell at `w` or `w'` has
  `E_κ(w) = E_k(w)` and `E_κ(w') = E_k(w')`. Charged at the first query of the *second* key, so
  both of `k`'s cells are fresh: `pr_two_cells_le` (two fresh cells hitting two values,
  `≤ 2⁻²⁵⁶`, by an injection of the tables) and at most `2·|cache|` pairs (`card_collPairs_le`)
  give `pr_collBad_le ≤ 2N·2⁻²⁵⁶`, and **`prEvent_coll_le`: `≤ 2·q_E²·2⁻²⁵⁶ = q_E²·2⁻²⁵⁵`** for a
  `q_E`-query prover. `freshBadC_of_two_keys`: two different keys, each queried at one of a leaf's
  two points, with equal blocks at both, make a fresh query bad. This is the doc's C2 with the
  pair's four cells all charged to the log; the doc's 10 `q_E²p²` also covers inverse queries and
  determinations the verifier makes. C1 (`E[N_coll] ≤ q_E²p`) is not needed here, and C3 (for L2)
  is not done.
- **Straight-line key extraction from the query log.** `extractKey log E iv i a`: the key of the
  first entry of the prover's cipher log at one of tree `i`'s two leaf points whose key has
  commitment `a = E_κ(x₀) ‖ E_κ(x₁)` (the second block read from the table: L0-L2 §6, the
  extractor evaluates the partner block, Definition B). `keysOf`: these keys for the commitments
  that the reconstruction from the opening computes (the opened ones at the hidden leaves);
  `knownOf`: the trees whose hidden leaf has such a key. These replace `ExtData`'s keys and known
  set (`proverIC`, below). `extractKey_eq_of_wit`: outside the collision event every logged
  witness of a commitment is the extracted key (L1.2; at a hidden leaf, L2(c) without "before
  `chal1`").
- **Binding** (`binds_or_coll_or_dead`, deterministic, any `iv`, opening and `Δ`): if the
  reconstruction's key at a non-hidden leaf differs from the extracted key, the log has a fresh
  `collBad` query or a **dead leaf is opened** (`DeadOpen`: the reconstruction's key at a
  non-hidden leaf was queried by the prover at neither of that leaf's points). Uses
  `comAt_reconstruct` (a non-hidden leaf's commitment is its key's `leafCom`) and `leafCom_ic`
  (under `icPrg E` that is the key's row at the two points). **`prEvent_not_binds_le`**:
  `Pr_E[¬BindsIC] ≤ q_E²·2⁻²⁵⁵ + Pr_E[DeadOpen]`, for any cipher-only prover.
- **The joint game and the bridge** (`ROM/CipherGame.lean`). The prover is
  `P : OracleComp specIC _`, one random oracle on `Dom ⊕ Cell` (hashes and cipher), with
  `IsQueryBoundP P Sum.isRight q_E` and per-domain hash counts `IsKindQueryBoundIC P q`.
  `proverIC st E P`: `P` with the cipher answered by `E` (`runE`, which also returns its cipher
  log), then the extractor (queries `mu₁` and `iv`, two more hash queries, and sets `keys`, `known`
  from the log, `E` and the proof; the log goes into `aux`). `gameIC T st P E`: `game` at the
  instance `icPrg E.cipher`. The experiment draws `E` uniformly, then runs `gameIC … E` against the
  lazy hash oracle. `runH h P` is `P` with the hashes answered by a fixed table (a cipher-only
  prover); `evalWithAnswerFn_runE` ties the two. **`prEvent_joint_le_add`**: if for every complete
  hash table an event has cipher probability `≤ c +` that of another, the same holds in the joint
  experiment (the lazy oracle becomes a uniform table on the finite set of all games' possible
  queries, `prEvent_randomOracle_eq_eager`, and the two draws are swapped). Hence
  **`prEvent_joint_bindFail_le`**: `Pr[bindFail] ≤ 2·q_E²·2⁻²⁵⁶ + Pr[DeadOpenOut]`
  (`DeadOpenOut`: an accepted proof with a dead opened leaf), and
  **`prEvent_joint_le_of_bindFail`**: any bound of §2c taken at each cipher table with
  `ε_bind := Pr[bindFail]` holds in the joint experiment with that term replaced.
- **Plugged in: `moussakaIssue_accept_le_ic`**: in the joint experiment,
  `Pr[accept ∧ ¬Extracted] ≤ (q₁+1)·2⁻¹⁵⁰ + (q₂+1)·ε_QS(4008) + (Q+1)·9·2⁻¹²⁸ +
  (2·q_E²·2⁻²⁵⁶ + ε_open) + ε_dead + ε_chain`, with `q_E` the prover's cipher queries, `ε_open` a
  bound on `DeadOpenOut`, and `hsame`, `hL2`, `hdead`, `hchain` as in `moussakaIssue_accept_le`
  for every cipher table (the committed chain data may depend on it). The other four relations go
  through `prEvent_joint_le_of_bindFail` the same way; not stated (the combined relations also
  need `P`'s total hash count transferred to `proverIC`, `+2`).

**What `ε_bind` became, and what is left.** L0-L2's `ε_bind` has four parts: `Coll₁`, `Hit₁` (the
`H₁` linking of L1.4), `Coll_E` (C2) and `Cross` (Definition B). `Coll_E` and `Cross` are covered
by `2·q_E²·2⁻²⁵⁶` (in the PRF view, forward queries; a second committed key whose blocks match as
cipher values is a second logged witness). What remains is `ε_open = Pr[DeadOpenOut]`: an
accepted proof opens a leaf whose key the prover never evaluated at either of the leaf's points.
Bounding it is L1.4 (the leaf commitments the verifier recomputes are the `H₁` preimages
committed before the chain's `H₂¹` query: `Coll₁`, `Hit₁`) together with L2(a) (C3, `Post`): an
ordering argument over the hash and cipher logs, the same kind as the "same chain" step. (Done in
§2e, without the ordering: `Pr[DeadOpenOut] ≤ openHashEps q + q₁·2⁻²⁵⁶`, because a key never
queried at all needs no "before".) Note also
that the extracted keys are logged keys, but "logged before `chal1`" (committed by the chain) is
not part of binding here: it is in `hsame` (`SameChain.pre` compares the keys committed at the
chain's `H₂¹` input with the extractor's).

**For `ε_chain` and `ε_dead`.** The joint game is the place for both: the committed data of a chain
can now be computed from the cipher table and the query log (`extractKey` on the commitments
committed at the `H₂¹` input), and L2's `Post` event is a `collBad`-style fresh-query event of the
cipher log charged against the half-targets of earlier chains (C3), for which
`prEvent_freshBadC_le_of_cached` is the union bound (with a bad event that reads the log of the
hash queries too; the combined oracle `specIC` puts both in one log).

### 2e. M6, second part: `ε_open`, the other relations, and what is left

Files: `ROM/Queried.lean`, `ROM/FreshGuess.lean`, `ROM/CipherOpen.lean`, `ROM/CipherRelations.lean`;
`ROM/CipherGame.lean` changed (below). No executable definition changed. `#print axioms` of the
main results: `propext`, `Classical.choice`, `Quot.sound`.

- **The joint log.** `runE E P` now returns `P`'s **joint log** (hash and cipher queries, in order,
  with answers), which is `tableQueryLog P (join h E)` (`evalWithAnswerFn_runE`); `proverIC` keeps it
  in `aux`. `cipherLog` (its cipher entries, `= tableQueryLog (runH h P) E`,
  `cipherLog_tableQueryLog`) feeds `keysOf`, `knownOf`, `DeadOpenOut` as before; `hashLog` (its hash
  cells) is `P`'s own hash queries. Generic log facts (`ROM/Queried.lean`): two tables agreeing on
  the queried cells give the same run (`tableQueryLog_congr`), and a queried cell stays queried when
  the table is changed there (`mem_tableQueryLog_congr`).
- **The hash ladder** (`ROM/Queried.lean`, generic in `HasPrg` and the prover): the verifier's chain
  `w_i → cw → x → y → z` (17 leaf hashes, `com`, `H₂¹`, `H₂²`, `H₂³`), each input containing the
  previous answer at a fixed position. If the prover (its reported queries `qs aux`, behaving as a
  log: `hfix`, `hmem`, `hcnt`) did not query some `w_i` but the verifier accepts, then walking up
  the chain, either the prover did not query `z` either, or the first queried input contains the
  answer of an unqueried cell: a bad answer (`ladderBad`, targets `ladderTargets`), i.e. `Hit₁` and
  its analogues for `H₂¹`, `H₂²` (`ladder_walk`). Union bound: **`prEvent_accept_leafUnqueried_z_le`**
  `≤ (q₁+18)·(17q'₁+q'₂₁)·2⁻²⁵⁶ + (q₂₁+1)·q'₂₂·2⁻¹⁰⁸⁸ + (q₂₂+1)·q'₂₃·2⁻⁴⁴⁸` when `z` was queried
  (`zOut`: `z` read off the transcript). The all-in-one union bound with the `H₂³` step charged to
  every `H₂³` query is `prEvent_accept_leafUnqueried_le` (`+ (q₂₃+1)·2⁻¹²⁸`).
- **A fresh answer guessed** (`ROM/FreshGuess.lean`). `card_finOf_mul_le`: abstract class counting
  (cells `t g`, classes `{update g (t g) w}` of `|W|` tables, at most `K` per class in the event,
  classes disjoint), stated over abstract finite types so that no cardinality of a concrete
  `2¹²⁸`-element type enters arithmetic (the kernel would evaluate it: `0 * Fintype.card …`
  through `zero_mul` already recurses). `prEvent_fresh_guess_le`: lazy oracle → uniform table on the
  possible queries → counting, `Pr ≤ K·2^{-8·outLen}`. Hence **`prEvent_accept_zUnqueried_le`**:
  accepted with the verifier's `H₂³` input not queried by the prover, `≤ 2⁻¹²⁸` (not `(q₂₃+1)·2⁻¹²⁸`:
  the verifier's chain reads no `H₂³` cell, `runChain_ofTable_update_h23`).
- **Two fresh cipher cells** (`ROM/CipherOpen.lean`). If the dead leaf's leaf-hash input `w_i` *was*
  queried by `P`, block `j` of it is the commitment `E_{s'}(x₀) ‖ E_{s'}(x₁)` of the dead leaf
  (`extract_leafHashInput`, `comAt_reconstruct`, `leafCom_ic`), at two cells `P` never queried. At a
  fixed hash table, updating the cipher table at those two cells changes neither `P`'s run (not in
  its log), nor the verifier's tree (the GGM derivation reads only points of tweak `< L − 1`,
  `recTree_ic_congr_cells`, `lp_ne_gp`), nor the dead leaf, nor `P`'s `H₁` inputs: the class
  counting with two cells, **`prEvent_two_cells_le`**, gives `≤ q₁·2⁻²⁵⁶`
  (`prEvent_deadQueried_le`).
- **`ε_open` discharged**: **`prEvent_joint_deadOpen_le`**,
  `Pr[DeadOpenOut] ≤ openHashEps q + q₁·2⁻²⁵⁶` with
  `openHashEps q = (q₁+18)·(17q₁+q₂₁)·2⁻²⁵⁶ + (q₂₁+1)·q₂₂·2⁻¹⁰⁸⁸ + (q₂₂+1)·q₂₃·2⁻⁴⁴⁸ + 2⁻¹²⁸`
  (`q` = `P`'s per-domain hash counts). For `q ≤ 2⁶⁴` this is `2⁻¹²⁸ + O(2⁻¹²⁰)`; the `2⁻¹²⁸`
  is the one fresh guess of `Δ`, as the paper's "the verifier's own query is fresh".
- **The five relations, `ε_bind` explicit**: `moussakaIssue_accept_le_ic'` (`ROM/CipherOpen.lean`),
  `ratatouilleIssue_accept_le_ic`, `moussakaRedeem_accept_le_ic`, `ratatouilleSpend_accept_le_ic`,
  `pomfritRedeem_accept_le_ic` (`ROM/CipherRelations.lean`): the `ROM/Accept.lean` bounds in the
  joint experiment with `ε_bind` replaced by `2·q_E²·2⁻²⁵⁶ + openHashEps q + q₁·2⁻²⁵⁶`; for the
  combined relations the total hash count `n` of `P` (`IsQueryBoundP P Sum.isLeft n`) becomes `n + 2`
  (the extractor's two queries, `isTotalQueryBound_proverIC`). Remaining hypotheses: `hsame`
  (`ε_chain`) and `hL2` (`ε_dead`), per cipher table.

**Finding F2: `hL2` cannot be discharged with a small `ε_dead`.** `hL2` asks, outside `deadFail` on
accepted runs, that every tree outside `known` has a fixed block on `onSet st T ch chal3Blocks`,
the `chal3` values on the chain *computed with the extractor's keys*. Take an honest prover that,
in one tree `i₀`, replaces the commitment of one leaf `j₀` by a random 32-byte string and uses the
key `0` there in its VOLE (ConvertToVOLE does not need the hidden leaf's key, so its proofs are
accepted whenever `Δ_{i₀} = j₀`; it grinds `chal3` for that). Then `i₀ ∉ known` (no logged key for
the hidden commitment), the extractor's key at `(i₀, j₀)` is `zeroBlock` (`keysOf`), i.e. exactly
the key the prover used, so the committed chain is consistent for *every* `Δ'` and `onSet` is all
of `chal3Blocks`: tree `i₀` is not fixed on it. So `deadFail` must contain essentially every
accepted run of this prover, and adding the trick to any cheating prover makes `ε_dead ≈ Pr[accept]`.
The bound is still true, but `ε_dead` is not uniformly small, so the theorem says nothing in
general. The paper's L2 is fine: L3 uses "a tree with a dead leaf has, *on the accepting set*,
`Δ_i` fixed", and the accepting set excludes every `Δ'` that would open a dead leaf. The formal
translation used `onSet` (consistency of the committed data, with garbage keys at dead leaves) in
place of the accepting set. **Correction** (implemented, §2f; it changed the hypotheses of
`ROM/Accept.lean`'s theorems): let the chain data at `z` carry the committed dead leaves
`dead i : Finset ℕ` (leaves with no key evaluated before the chain's `H₂¹` query, a function of the
log prefix, so `Committed`), take `A := {Δ' ∈ onSet | ∀ i, ∀ j ∈ dead i, Δ'_i = j}` in
`chainBad_of_accept` (`chain_good_of_not_bad` needs only `A ⊆ onSet`; its `hP` should take any
such `A`), `SameChain.acc : accOf z g b ↔ deltaBlocks b ∈ A`, and replace `hL2` by (i) L2(c):
`i ∉ known → (dead i).Nonempty` (then `IsFixed A i` holds by construction) and (ii) L2(a): the
accepted `Δ` hides every committed dead leaf (`Δ ∈ A`, from `onChain_of_accept`). Both are
small-probability statements (`Post`/C3 and the `DeadOpen` argument of this section).

**What was left for `ε_chain` and `ε_dead`** (all done in §2f). Both need the **committed data of a chain
from the log prefix**: for the verifier's `H₂¹` input `x`, the `com` field of `x` (bytes
`32 … 64`), its first `H₁` preimage of length 545 in the joint log before the first query of `x`,
the 17 leaf-hash preimages of its blocks, and for each leaf the first key in the cipher log
*before `x`* with that commitment (Definition B); `preOf x g` is this, with `c_i`, `c_mult`,
`iv_pre`, `mu₁` parsed from `x` (and `iv = H₄(iv_pre ‖ mu₁ ‖ 4)`, `h5` from the table). Such data are
`Committed` automatically (the log before the first query of a cell does not read it). The missing
lemmas:
1. *Ordering* (L1.4, `Hit₁` up the chain): on accepted runs, outside hits whose targets are fields
   of *earlier* queries, the first queries of `w_i`, `cw`, `x`, `y`, `z` are `P`'s and in this order.
   The union bound is the ladder's with targets taken from the log before the first occurrence
   (invariant when that cell is resampled); the event is about the log, so it needs the game's log
   in the output (a logged game, or `P`'s joint log as here, with answers).
2. *`Coll₁`* (`H₁` answers distinct among the logged inputs, `≤ (q₁+18)²·2⁻²⁵⁶`) and an `H₂¹`
   collision bound (`chal1` identifies `x` inside `y`), both cache-reading union bounds
   (`prEvent_freshBadC_le_of_cached`).
3. *`Post`* (C3(b), L2(c)): a key whose two matching cells are both first queried after `x` (so the
   extractor's key from the full log differs from the pre-`x` one), `≤ 8·L·q₂·q_E·p²`; a joint
   ordering event (hash log before the cipher query), at a fixed hash table a `freshBadC`-type
   bound over the cipher log with the half-targets of the earlier `H₂¹` queries.
4. *Parsing*: `chal1Input`, `chal2Input` (with `h_V` serialized), `chal3Input` inverted on their
   fields, and `keysOf` made zero outside `i < τ, j < 2^{k_i}` so that `SamePrefix.keys` (equality
   of functions `ℕ → ℕ → ByteArray`) does not ask for agreement on meaningless indices.
5. For `ε_dead`: the corrected interface of F2, then (i) and (ii) above from 1–3.

### 2f. M6, third part: the L2 interface, `ε_chain` and `ε_dead`, as implemented

Files: `ROM/LogPrefix.lean`, `ROM/ChainParse.lean`, `ROM/CipherChain.lean`, `ROM/CipherSame.lean`,
`ROM/CipherFull.lean`; changed: `ROM/Chains.lean`, `ROM/Comb.lean`, `ROM/Accept.lean`,
`ROM/CipherBind.lean`, `ROM/CipherGame.lean`, `ROM/CipherOpen.lean`, `ROM/CipherRelations.lean`. No
executable definition changed. `#print axioms` of the five `*_accept_le_full`: `propext`,
`Classical.choice`, `Quot.sound`.

**The result.** In the joint hash and ideal-cipher experiment (cipher table uniform, PRF view,
forward queries; hashes lazy random oracles; a fixed statement), for a prover with `q_E` cipher
queries and `q k` hash queries of kind `k` (total `n` for the combined relations):

    Pr[accept ∧ ¬Extracted] ≤ (q₂₁+1)·2⁻¹⁵⁰ + (q₂₂+1)·ε₂ + (q₂₃+1)·N·2⁻¹²⁸
      + 2·q_E²·2⁻²⁵⁶ + 2·(openHashEps q + q₁·2⁻²⁵⁶) + 1024·q_E·q₁·2⁻²⁵⁶ + chainHitEps q [+ comb]

with `ε₂ = ε_QS(n')` (issue) or `ε_QS(n') + 2⁻¹²⁸ + (n+339)·2⁻⁴⁴⁸` (combined), `N = 9` (`2` for
PomFRIT), `openHashEps q = (q₁+18)(17q₁+q₂₁)·2⁻²⁵⁶ + (q₂₁+1)q₂₂·2⁻¹⁰⁸⁸ + (q₂₂+1)q₂₃·2⁻⁴⁴⁸ + 2⁻¹²⁸`,
`chainHitEps q = (q₁+18)(18q₁+q₂₁+325)·2⁻²⁵⁶ + (q₂₁+1)(q₂₁+q₂₂+2)·2⁻¹⁰⁸⁸ + (q₂₂+1)(q₂₂+q₂₃+2)·2⁻⁴⁴⁸`,
and for the combined relations `+ (q₂₂+1)(q_comb+1)·2⁻⁴⁴⁸` (`chainHitEpsComb`):
`moussakaIssue_accept_le_full`, `ratatouilleIssue_accept_le_full`, `moussakaRedeem_accept_le_full`,
`ratatouilleSpend_accept_le_full`, `pomfritRedeem_accept_le_full`. No hypothesis remains besides
the query bounds. The `2·openHashEps` counts `ε_open` twice (once in `ε_bind`, once in `ε_dead`);
that is slack, not a gap. For `q ≤ 2⁶⁴` the new terms are `O(2⁻¹²⁰)` (`1024·q_E·q₁·2⁻²⁵⁶ ≤ 2⁻¹¹⁸`).

**The L2 interface (F2 fixed).** `SameChain` takes the committed dead leaves `dead : Fin τ → Finset ℕ`,
and `acc : accOf z g b ↔ deltaBlocks b ∈ hideSet st T ch dead`, the challenges on the chain that
hide every committed dead leaf (`ROM/Accept.lean`). A tree with a dead leaf has a fixed block on
`hideSet` (`isFixed_hideSet`; `chain_good_of_not_bad` and `comb_good_of_not_bad` now take any
`A ⊆ onSet`). `hL2` is replaced by L2(c) (inside `hsame`, now `SameChainHyp`: every tree outside
`known` has a committed dead leaf) and L2(a) (`hL2 : DeadHiddenHyp`: the accepted `Δ` hides every
committed dead leaf), both under `¬chainFail`, `¬deadFail` and "no hit".

**Hits** (new in the interface). `prEvent_accept_le_chain_terms`/`_comb_terms` and all per-relation
theorems take a family `hit : Dom → Table → Prop` with per-query bound `εh` (resampling the cell
alone, as `chainBad`), merged into the union bound (`prEvent_le_chain_terms_hit`,
`prEvent_le_comb_terms_hit`), and assume `hsame`, `hL2` only when no query of the game's log is a
hit (`NoHit`); the bound gains `hitSum (q + verifierQueries) εh`. The IC theorems take `ε_dead`,
`ε_chain` as bounds on joint probabilities (`prEvent_joint_le_of_fails`), since Post is small only
on average over the cipher table.

**The committed data** (`ROM/CipherChain.lean`) are read off the game's hash log and `P`'s joint log
*before the first query of the cell* (`logBefore`; `logBefore_tableQueryLog_update`: invariant under
a change of the table at that cell, so committed): at `x`, `com` from `x`, its first 545-byte `H₁`
preimage `cw`, the first preimages `w_i` of `cw`'s blocks, the leaf commitments, and per leaf the
first key in the cipher log before `x` with that commitment (`keyPre`; dead if none, `deadPre`);
`c_i`, `c_mult`, `iv_pre` parsed from `x`; at `y` the prefix at the first `H₂¹` preimage of `y`'s
`chal1` plus `ũ`, `h_V`, `d`; at `z` the chain at the first `H₂²` preimage of `z`'s `chal2` plus `ã`
and the check value. The parsers and their inverse lemmas are `ROM/ChainParse.lean` (item 4 of
§2e); `keysOf` is now zero outside `i < τ, j < 2^{k_i}`.

**The hits** (`chainHit`): an `H₁` answer equal to a block of an earlier 545-byte `H₁` input, to
the `com` field of an earlier `H₂¹` input, or to an earlier `H₁` answer; an `H₂¹` answer equal to
the `chal1` field of an earlier `H₂²` input or to an earlier `H₂¹` answer; an `H₂²` answer equal to
the `chal2` field of an earlier `H₂³` or combination input or to an earlier `H₂²` answer
(`prEvent_chainHit_le`). Without hits the verifier's cells `w_i → cw → x → y → z` were first
queried in this order (`before_of_noHit`, the ordering half of L1.4) and are the first preimages
found (`cell_eq_of_noHit`: `Coll₁` and the `H₂¹`, `H₂²` collisions); `chain_ident`.

**Post** (C3, `PostJ`): a cipher query of `P` that is the first at both points `w`, `w'` of a key
and whose two blocks (in either order) form a 32-byte block `jj < 256` of an earlier `H₁` input.
`prEvent_postAt_le` (fixed query index and neighbour: two fresh cells, `prEvent_two_cells_le`,
`≤ 512 q₁·2⁻²⁵⁶`, with `tableQueryLog_prefix_congr` for the invariance) and the union over `q_E`
indices and 2 neighbours: `Pr ≤ 1024·q_E·q₁·2⁻²⁵⁶` (`prEvent_joint_postOut_le`). (The paper's
`8·L·q₂·q_E·p²` charges `H₂¹` queries; here the targets are the `H₁` inputs.) Without Post, a key
found in the whole cipher log for a committed commitment was found before `x`
(`extractKey_pre_eq`).

**Assembly** (`ROM/CipherSame.lean`): `sameChain_core`/`sameChainHyp_ic` (SameChain and L2(c)),
`deadHiddenHyp_ic` (L2(a): a non-hidden committed dead leaf's reconstructed key was queried at a
leaf point, after `x`, a Post, or never, `DeadOpenOut`), with `chainFail := PostOut`,
`deadFail := DeadOpenOut`.

**Combined relations.** `CombData.Committed.midComb` required the chain data at `y` to read *no*
combination cell, which log-based data cannot satisfy (the prover may query combination cells before
`y`). `CombData` now has `pre : ByteArray → Table → List Dom` (default `[]`), `midComb`/`sysComb`/
`witComb` only for cells outside `pre y g`, with `preMid`, `preComb`; `combBad` at `H₂²` requires
the combination cell of the answer outside `pre y g`, and `prEvent_accept_le_comb_terms` assumes it
for the verifier's own query (`hcombFresh : CombFreshHyp`), discharged by the hit on earlier
combination inputs (`combFreshHyp_ic`, `preCells`, `midOf_comb`).

**Not covered.** The statement is fixed in these games, so statement binding (`(q²+q)·2⁻²⁵⁶`,
adaptively chosen statements) is not part of them. The cipher is a random function (PRF view) with
forward queries only; the permutation model with inverse queries (`p = 1/(2¹²⁸−q_E)`) is on paper.

### M4 — Mathlib bump and VCVio dependency (Phase B, ~1–3 days, mostly waiting on builds) — done

- Bump to `v4.34.0` (separate commit). Fix the breakage. Then `require VCVio` and add
  `VoleMole/ROM/Basic.lean`.
- Bridge phase-A `prU` to VCVio: `Pr{let x ← $ᵗ α}[P x] = prU α P` (via
  `evalDist_selectElem_eq_uniform` and `PMF.toMeasure`).
- Model the hashes as one `OracleSpec` indexed by domain (L0's disjointness justifies independent
  oracles): `H₂¹ : Bytes* → Bytes 136`, `H₂² → Bytes 56`, `H₂³ → Bytes 16`,
  `H_comb → Fin 45 → GF128`, `H₁`, `H₄`, `H₅`.

### M5 — ROM: union over queries and freshness (Phase B, ~1–2 weeks) — done, see §2b

Lazy RO = `OracleSpec.randomOracle` (`uniformSampleImpl.withCaching`), adversary
`P* : OracleComp spec α` with `IsPerIndexQueryBound P* qb`. Key generic lemma (check
`FreshQuery.lean` / `Unpredictability.lean` first; it may exist in some form):
```lean
/-- "Bad answer" union bound: if every possible answer to a query at index i is bad with
probability ≤ ε given its input, then some logged query is bad with probability ≤ qb i · ε. -/
theorem prEvent_exists_bad_query_le (bad : spec.Domain i → spec.Range i → Prop)
    (hε : ∀ x, Pr{let y ← $ᵗ _}[bad x y] ≤ ε) (hq : IsPerIndexQueryBound oa qb) :
    Pr{let z ← (simulateQ randomOracle (withLogging oa)).run ∅}[∃ (x, y) ∈ log z i, bad x y]
      ≤ qb i * ε
```
Instances:
- `bad₁ x c := ¬KOSGood …` for the prefix parsed from `x` (M2), giving `q₁·ε_KOS`;
- `bad₂ y c :=` M2's event for the canonical slope parsed from `y` (and `l` read through the RO
  cache), giving `q₂·(ε_QS + 2⁻¹²⁸)`;
- freshness of `chal2 ‖ dst` in `H_comb` (`q_c·2⁻⁴⁴⁸`, `Unpredictability` / birthday lemmas);
- `bad₃ := acc` on doomed chains, giving `Q·max(d,1)·2⁻¹²⁸`;
- statement binding before `chall₂`, `(q²+q)·2⁻²⁵⁶`: `prEvent_cacheCollision_le_birthday`.

Subtlety: the "parse a prefix from `x`" functions must be total functions of the query input (and
the RO cache *before* the query). This is where L1's "committed data" enters. In M5 take it as
given via a hypothesis that the committed keys are a function of the prior log.

### M6 — Ideal cipher, L1/L2, the "same chain" step (Phase B, ~3–6 weeks, optional) — done (PRF view, fixed statement), see §2d, §2e, §2f

- Model AES as an ideal cipher: a lazy random *permutation* per key, with forward and inverse
  queries. VCVio has no ready-made ideal cipher that I could find; build it as a stateful
  `QueryImpl` with a partial bijection per key.
- Prove C1 (`E[N_coll] ≤ q_E²p`), C2 and C3 (`L0-L2-commitments.md` §4), then `ε_bind` and
  `ε_dead`.
- Derive `hrun` of `onChain_of_accept` (binding) and `hL2`.
- The "same chain" step: an accepted proof whose H₂¹/H₂²/H₂³ inputs were never queried is accepted
  with probability `≤ 2⁻¹²⁸`-ish, because the verifier's own query is fresh.
- Final theorem: `Pr[accept ∧ ¬R(x, E(π, log))] ≤ ε_ext` for `E` the straight-line extractor run
  on the log.

This is where most of the risk and effort sits. A useful intermediate is M5's theorem with `ε_bind`
and `ε_dead` as named hypotheses about the cipher.

## 3. Risks

- **The executable verifier hard-codes SHAKE** (resolved: §2a for `chal2`/`l` as chain fields,
  §2c for the hash record). `Verifier.chal1`, `chal2`, `chal3`, `ivOf` and
  `Combination` called the concrete `H`, and `Chain.chal2` was a def, not a field.
  - For M2/M3: add `chal2` (and `l`) as chain fields, with `chal2 = Verifier.chal2 …` as an explicit
    hypothesis where `onChain_of_accept` needs it.
  - For M5+: parametrise the verifier by a hash record `Hs` (`verify (Hs := shakeHashes)` stays
    executable for the KATs).
  - That is a refactor touching `Verifier/*` and the Bridge files. Plan it early, as a
    behaviour-preserving change checked by `verifier_vectors`.
- **ByteArray vs `Fintype`.** All sampled values must be `Bytes n`/`Vector UInt8 n`, coerced.
  Lemmas about `ByteArray.extract`/`get!` on coerced values are tedious but routine.
- **Big finite sets.** `shortKeys` (2⁶⁴) and `Bytes 136` must never be decided or enumerated. Every
  cardinality goes through equivalences.
- **ℝ≥0∞ arithmetic.** Numeric bounds like `2^(−150)` are painful in `ℝ≥0∞`. Keep the `ℝ` forms
  (`epsQS` is already real) and convert once.
- **VCVio churn.** Measure-valued semantics just landed (#710). Pin a rev, isolate it in
  `VoleMole/ROM/`, and keep phase-A lemmas framework-free.
- **Bump fallout and memory.** The rc1 → v4.34.0 bump re-checks the heavy kernel computations.
  VCVio adds about 100k lines to build locally. Respect the one-worker / `MemoryMax` rule.
- **Modelling gap.** The ROM statement is about the *model* (independent oracles per L0 domain,
  ideal cipher). L0's disjointness (`Seed/Commitments.lean`, `Protocols/DomainSeparation.lean`)
  justifies splitting one SHAKE into independent oracles; this is now a lemma (§2c,
  `ROM/DomainSep.lean`, `ROM/SingleOracle.lean`). The ideal cipher remains.

## 4. ZK (for later)

`docs/zk.md` §10's paper-only steps are H1/H2 programming, H6 identical-until-bad, and the union
over adaptive H₅ queries. They need VCVio's `ProgrammingOracle`, the identical-until-bad /
TV-distance lemmas (`EvalDist/MeasureTVDist/`), and the same `prEvent_exists_bad_query_le` as M5.
The existing `*_fiberCard` / `*_indep` lemmas become `=ᵈ` statements through `prU_map_equiv`. Do
this after M5 has proved the RO setup.
