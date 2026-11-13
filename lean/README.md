# Security proofs for vole-mole: an LLM-assisted, partial formalization

> **Read this first.** Everything in this directory was produced with heavy assistance from a large
> language model (Claude), working under the direction of a human maintainer. It has **not been
> peer reviewed or audited**. The Lean files are checked by Lean's kernel, but a Lean theorem is
> only as meaningful as its statement and its model of the code, and those were written by the
> same process. The paper proofs (Markdown) are unreviewed drafts. Treat all of it as a detailed
> starting point for expert review, not as a security guarantee.

This directory holds the security analysis of the zero-knowledge proofs (FAEST v3 VOLE-in-the-head
with QuickSilver, `src/voleith.hpp`) and of the three token protocols built on them: PomFRIT,
Moussaka and Ratatouille. The analysis has three layers, and every result below says which layer it
lives in:

| Layer | What it means |
|---|---|
| **[Lean]** | Machine-checked in `VoleMole/`. No `sorry`, no `axiom`, no `native_decide`; `#print axioms` shows only `propext`, `Classical.choice` and `Quot.sound`. Covers the deterministic steps (linear algebra, counting, polynomial degrees, combinatorics, numeric bounds) and some probabilistic ones: the single-challenge and random-oracle bounds for extraction (§9), zero knowledge and the protocol privacy theorems in the classical random-oracle and ideal-cipher model (§3), and the protocol reductions for Moussaka unforgeability, Ratatouille balance and PomFRIT's one-more unforgeability, with their assumptions as explicit terms (§5). |
| **[paper]** | A written proof in `docs/`. Covers the other probabilistic steps: random-oracle and ideal-cipher arguments, quantum oracle arguments, union bounds, reductions. |
| **[test]** | A Lean model or a deterministic fact checked against the C++ by a test in `tests/` (exhaustively where the domain is small). This is how the Lean models are tied to the code. |

**Partial** means: no end-to-end statement about the C++ is machine-checked. Most Lean results
are the deterministic cores that the paper proofs call; the probabilistic Lean results are about
the Lean models (the executable verifier, prover and specs). The C++ is tested against the Lean
models, never proved equal to them, and constant-time behaviour and side channels are out of
scope.

## At a glance

**Proved in Lean** (classical; the probabilistic results in the random-oracle and ideal-cipher
model, AES's rows uniform functions and, for extraction, zero knowledge and privacy, also uniform
permutations with inverse queries):
- *Extraction* (§1, §6, §9). For all seven relations (the five base relations and unbound
  Moussaka's two), the executable Lean verifier "accepts and
  extraction fails" with probability bounded by an explicit function of the prover's query counts,
  with no hypothesis beyond the query bounds and well-formed instances; for fixed and for
  adaptively chosen statements (Moussaka and Ratatouille: families with injective encodings,
  `hinj`, proved for fixed-length families). The extracted witness decodes to a witness of the
  byte-level spec relation (`ROM/SpecSound.lean`). Underneath: the deterministic extraction core,
  end to end over the real constraint systems over GF(2¹²⁸) (`EndToEnd/`).
- *Completeness* (§8). The Lean verifier accepts the Lean prover's proofs except with probability
  `≤ 2⁻¹¹³`, for all five relations with label rows.
- *Zero knowledge, with the label-row fix* (§3). One proof of the executable Lean prover is
  `≈ 2⁻¹⁰⁷·⁰`-close to a simulator, plus the distinguisher's read terms.
- *Privacy, with the fix* (§3). PomFRIT blindness, Moussaka issuer hiding and unlinkability
  (Thm 4(a), colluding Anchors; Thm 4(b), corrected, non-colluding) and Ratatouille
  unlinkability, as games on the executable specs with the Lean prover, the adversary seeing the
  tables, every term explicit:
  - two challenge sessions: `≈ 2⁻¹⁰³·⁴` to `2⁻¹⁰¹·¹` plus budget terms, also with
    table-reading interactions and key stages, one shared `H₃` and the real Clients' seeds
    (Moussaka 4(b) also with the Moderator's choices read off the tables, except in its
    shared-`H₃` game);
  - PomFRIT, Moussaka 4(a) and Ratatouille with any number `n` of further honest sessions,
    concurrent, adaptively scheduled or interleaved in any order by a scheduler that reads the
    tables: linear in `n`, at most about `n·2⁻¹⁰¹` (`2⁻⁸¹` at `n = 2²⁰`, `2⁻⁶⁹` at `2³²`;
    Ratatouille's interleaved bound counts proofs) plus budget terms;
  - the same three with `N` challenge pairs: quadratic, an artifact of the proof (`2⁻⁶³` at
    `2²⁰` sessions; PomFRIT with `H₄` a table `N·2⁻¹⁰³ + 32·N²·2⁻¹²⁸`); for Moussaka and
    Ratatouille linear in `N` up to one bad event `β` that is bounded on paper only
    (`anonymityP_lin`, `unlinkabilityP_lin`; with the paper bound on `β`, `2⁻⁸¹·⁴` at `2²⁰`
    Clients);
  - Moussaka 4(a) and Ratatouille also carry `2·εhide`, the hiding of `Com`, a computational
    hypothesis; Moussaka 4(b) carries the Anchors' abort term, `≈ 2⁻²⁹³·⁸` with pqov's signer on
    average over pqov's keys (not for a fixed key);
  - Moussaka's random-oracle games model the Client of the API before `21be618`, which took its
    issuer's index from an index rule; `main`'s Client finds the index itself (`find_issuer`).
    Thm 4(a) and 4(b) for it are proved from per-proof zero knowledge (`Privacy/MoussakaFind.lean`,
    `MoussakaNCFind.lean`; 4(b) for Anchor Sets containing both issuers), not yet in the
    random-oracle model.
- *Unbound Moussaka* (late `ctx_red` binding, `docs/security/moussaka-unbound.md`). Extraction as
  above; issuer hiding and unlinkability on the executable spec with `n` adaptively chosen
  redemption queries, colluding (Thm U5(a), `anonymityAd`, `≤ 4εI + 2n·εR + 2εprf`) and
  non-colluding (Thm U5(b), corrected, `anonymityNC`, `anonymityNC_vinegarRO`), from per-proof
  zero knowledge and the PRF advantage of Keccak-p[800,12] as hypotheses.
- *Protocol reductions* (§5), in the random-oracle and ideal-cipher model on the executable
  specs, with the Lean verifier as the honest parties' check (`ROM/VerifyIC.lean`):
  - Moussaka one-more unforgeability (Thm 1, `omuf_le_num`): `Pr[Win] ≤ qI·ε_I + qR·ε_R +
    Adv^bind_Com(B₁) + Adv^ct-uf-open_K(B₂)`, `ε_I`, `ε_R` the adaptive spec soundness bounds at the
    game's budgets; the last term is a CT-UF^open advantage in a standalone game
    (`omuf_le_num_open`). **Down to one-more-UOV** (`omuf_le_num_ompr`): with `Com` idealized in
    that standalone game only (the named modelling hypothesis `hmodel`), it is at most
    `Σ_k (Adv^ompr_k(B_k; q_f + 2q_S + 1, q_S) + (q_f + 2q_S + 1)·failPr_k)` over the `K` Anchor
    keys (T4 with `Com` a random function, `advCTUFIdeal1_le_ompr`; the `K`-key step by guessing,
    `advCTUFIdeal_le_sum`; `Assumptions/CTUFOpenOMPR.lean`). Plain CT-UF, without openings, is
    false for UOV (`ctuf_pqov_broken`). **With simultaneous extraction** (`omuf_le_num_sim`,
    `omuf_le_num_ompr_sim`, `ROM/MoussakaOMUFSim.lean`, `ROM/SimJoint.lean`,
    `Assumptions/SimLinks.lean`): `ε_IR^sim` in place of `qI·ε_I + qR·ε_R`, each query of the run
    charged once for both relations (their statements are DST-separated), plus per proof its
    verifier's queries and the failure terms `failEps ≈ 2⁻¹¹⁷·⁹`: at `2⁶⁴` queries and `2³⁰`
    proofs per relation `≈ 2⁻⁶⁰·⁵` instead of `2⁻²⁹·⁶`;
  - Unbound Moussaka unforgeability per `(ctx_iss, ctx_red)` (Thm U1, `omufU_le`, `omufU_le_num`,
    `ROM/MoussakaUnboundOMUF.lean`): game OMUF-U on the executable spec, Anchors running bound and
    unbound issuance with one key (`uanchorIC_eq_spec`); `Pr[Win] ≤ qI·ε_I + qI·ε_UI + qR·ε_UR +
    AdvBind + AdvCTUF`, `AdvBind` a collision of `Com ∪ UCom`. With simultaneous extraction
    (`omufU_le_num_sim`, `ROM/MoussakaUnboundOMUFSim.lean`; the unbound pair joint, bound issuance
    a third family) `≈ 2⁻⁵⁹·⁶` at `2⁶⁴` queries and `2³⁰` proofs. With CT-UF^open over `Com ∪ UCom`
    and down to OMPR under `hmodel` (`omufU_le_num_open`, `omufU_le_num_ompr` and `_sim` versions,
    `Assumptions/UnboundLinks.lean`). Audit: `Audit/UnboundOMUF.lean`;
  - Unbound Moussaka Cor U2 (`ROM/MoussakaUnboundCor.lean`): on the OMUF-U game, nullifier
    determinism and single use per `(t, ctx_red)` (event `U2`) fail with at most U1's terms
    (`corU2_le_num_sim`, `corU2_le_num_ompr_sim`); honest uniqueness `≤ U²·2⁻¹⁹³ + Adv^prf_U`
    (`honest_nf_distinct`). Prop U3 and Thm U4 (corrected, `Theft/MoussakaUnbound.lean`, `nmU`,
    `noSquat`, `noRedirectU`): one honest token, a fresh accepted operation that is not extracted,
    opens `t`, or carries `Derive(nf_key, ctx_red*)`: `≤ ε_I + ε_R + δ_R + ε_SE + ε_prf + 2⁻¹⁹² +
    Adv^bind_UCom + Adv^spr-k`, weak SE and the PRF (`Adv^prf-t_1`) as hypotheses; key recovery
    reduces to the PRF (`owkAdv_le`). For `U` honest tokens with `M` adaptive honest redemptions
    (`Theft/MoussakaUnboundMany.lean`, `nmUN`, `noSquatN`, `noRedirectUN`): `Pr ≤ U·ε_I + M·ε_R +
    Σ_i δ_i + ε_SE + Σ_h (ε_prf + (M+1)·2⁻¹⁹² + Adv^bind(B₁ h) + Adv^spr-k(B₂ h))`, `ε_SE` weak
    simulation-extractability with `U+M` simulated proofs (`WeakSEN`, `Theft/Many.lean`, a
    hypothesis); key recovery with `M` adaptive nullifier queries reduces to the PRF
    (`owkAdvN_le`). With the Lean prover the zero-knowledge hypotheses are theorems for the unbound
    relations (`Privacy/MoussakaUnboundLean.lean`, `leanPI_zkRO`, `leanPR_zkRO`; `nmU_lean`,
    `nmUN_lean`, …). Bound Moussaka Thm 3 likewise for `U` tokens and `M` redemptions
    (`Theft/MoussakaMany.lean`, `noRedirectN`, `noRedirectN_lean`): `U·ε_I + M·ε_R + Σ_i δ_i +
    ε_SE + Σ_h Adv^ow(inverter h)`. Audits: `Audit/UnboundRest.lean`, `Audit/UnboundMany.lean`,
    `Audit/TheftMany.lean`. Ratatouille Thm 3 for `U` honest Clients and `M` adaptive honest
    spends, the change tokens spent again (`Theft/RatatouilleMany.lean`, `noTheftN`): `Pr ≤
    U·ε_I + M·ε_S + Σ_i δ_i + ε_SE + Σ_j Adv^ow(B_j)`, one one-wayness term per honest commitment
    (`owAdvK`: the inverter sees the nullifier and the commitment function over context and credit
    value); the game runs the spec with the Clients' state chained (`specI_eqN`, `specS_eqN`,
    `fin_issue`, `fin_spend`); off the event an accepted fresh spend opens no honest commitment
    (`not_theftN_spend`, the extraction form of N2a); audit `Audit/TheftManyR.lean`. `WeakSEN` at
    `N = 2` implies `WeakSE2` (`weakSE2_of_weakSEN`), and `WeakSEN ≤ ε_plain + Σ_i ε_hit,i`
    (`weakSEN_of_plain`, `progMovesN_of_slots`; `Theft/ManyPlain.lean`), instantiated for the Lean
    simulators of all three (`weakSEN_ratatouille`, `weakSEN_moussaka`, `weakSEN_moussakaU`); the
    hops' read budgets of the many-token Lean theorems are proved (`Theft/ManyReads.lean`,
    `distN_budget`: `(a₃+x₃, a₅+x₅+312+(U+M−1)·624, a_E+x_E+(U+M)·4607)`), giving
    `noTheftN_lean_reads`/`_plain`, `noRedirectN_lean_reads`/`_plain`, `nmUN_lean_reads`/`_plain`,
    `noSquatN_…`, `noRedirectUN_…`;
  - Ratatouille balance (Thm 1, `balance_le_ufTag`): `N` adaptive issuance and spend calls with
    chosen refunds, `Pr[win] ≤ N·ε_iss + N·ε_spend + Adv^uf-tag(B) + Adv^coll_Com(C)`, `B` an
    explicit UF-Tag forger (with a signability probe) and `C` an explicit `Com` collision finder.
    The probe costs only the Issuer's `derive_preimage` aborts (`ufTagAdv_le_noProbe`,
    `balance_le_noProbe`, `ROM/RatatouilleProbe.lean`; `≤ N·E[δ^{255}] ≈ N·2⁻²⁹⁵·⁸` for pqov, with
    pqov's failure law a paper step). **Down to one-more-UOV** (`balance_le_ompr`,
    `Assumptions/RatatouilleOMPR.lean`): with `Tag` idealized in the standalone UF-Tag game only
    (the named modelling hypothesis `TagIdeal`), the UF-Tag term is at most
    `Adv^ompr(B'; k + 1 + N, N) + (k + 1 + N)·ρ + failAdv(B)`, through det-FDH ≤ A-OMPI
    (`advFDH_le_ompi`) and A-OMPI ≤ OMPR (`advOMPI_le_ompr`; `Assumptions/IdealTag.lean`). **With
    simultaneous extraction** (`balance_le_sim_num`, `balance_le_ufTag_sim`, `balance_le_ompr_sim`,
    `ROM/RatatouilleBalanceSim.lean`): `ε_bal^sim` in place of
    `N·ε_iss + N·ε_spend`, with the same numbers;
  - PomFRIT one-more unforgeability (Thms U1, U2, `pomfrit_U1_bound`, `pomfrit_U2_bound`):
    `hash_to_target` a random oracle that the reduction programs perfectly; the forger's win is at
    most the reduction's advantage against Def. 3.1 (resp. A-OMPR⊕τ) with `Q_T + ℓ + 1` targets
    and `ℓ` preimage queries, plus Lemma P's failure probability, an explicit term; with the
    standalone games, `pomfrit_U1_ompr`, `pomfrit_U2_omprShift`, and Def. 3.1 literally through
    `advOMPR_le_ompr31`. Lemma P's extraction bound with its `Shift` term is in Lean for one
    adaptively chosen statement whose target is any function of `chal1` (`pomfritT_accept_le_major`,
    `ROM/LemmaP.lean`: `(Q₃+1)·2⁻⁷¹` in place of `ε_ext`'s `H₂³` term; per chain
    `pomfritT_extract_major_chain`, `ROM/LemmaPDet.lean`), and its join to the one-more game table
    by table (`ROM/OneMoreLemmaP.lean`: the game as a lazy random oracle `realImpl_run_eq`, `E₁` as
    `e1P`, `pfail_table`, `not_noPick`). **U1 with every term explicit** (`pomfrit_U1_explicit`,
    `pomfrit_U1_ompr_explicit`; `ROM/OneMoreLemmaPIC.lean` … `ROM/OneMoreLemmaPBound.lean`,
    `Assumptions/PomfritLemmaP.lean`): `Pr[PomWin] ≤ Adv^{ompr}(red; Q_T+ℓ+1, ℓ) +
    (ℓ+1)·pfailEps(q', q_E', n')`, assembled from an `E`-independent derived prover (`proverP`),
    extraction from a prefix of the log (`keysOf_knownOf_prefix`), Lemma P's ordering step
    (`e1P_eq_major`, failing only on an order hit at `2⁻¹⁰⁸⁸` per pair), the per-table implication
    (`pfail_events`) and `prEvent_pfail_le`; hypotheses 32-byte key digests and a forger query
    budget (`ForgerBound`), both met by the real objects (`Audit/PomfritLemmaP.lean`). It is a union
    over the `ℓ+1` forgeries. **With simultaneous extraction** (`pomfrit_U1_sim`,
    `pomfrit_U1_ompr_sim`; `ROM/OneMoreLemmaPPrefix.lean`, `ROM/OneMoreLemmaPSim.lean`,
    `Assumptions/PomfritLemmaPSim.lean`): `Pr[PomWin] ≤ Adv^{ompr} + pfailSimEps`, each query of the
    forger's run charged once (as the paper's `ε_ext`), each forgery's own extraction, verification
    and failure terms once per forgery; never worse than the union (`pfailSimEps_le`). At `2⁶⁴`
    queries and `ℓ = 2³⁰` it is `2⁻⁷`, dominated by Lemma P's `(Q₃+ℓ+1)·2⁻⁷¹`; the union bound is
    `2²³` (vacuous) there. **U2 with every term explicit** (tight, under A-OMPR⊕17;
    `pomfrit_U2_sim`, `pomfrit_U2_omprShift_sim`; union over forgeries `pomfrit_U2_explicit`,
    `pomfrit_U2_omprShift_explicit`): `Pr[PomWin] ≤ Adv^{ompr⊕17} + sfailSimEps`, `2⁻⁶²` at `2⁶⁴`
    queries and `ℓ = 2³⁰`, the paper's `ε_ext`, with no `2⁻⁷¹` term. The reduction submits all
    alive trees' prefixes as shifts (`hintS`), and Lemma P's goal weakens to "some alive tree
    extracts", `N = 2` per chain (`pomfritT_accept_le_some`; `ROM/LemmaPSome.lean`,
    `ROM/OneMoreShift{Table,Fail,Bound,Sim}.lean`, `Assumptions/PomfritShift{,Sim}.lean`). G8 is
    closed (`pomfrit.md`). **Lemma P's `2⁵⁷`** (`docs/security/pomfrit-lemmap-tight.md`,
    `Seed/KOSUnique.lean`): U1's `(Q₃+ℓ+1)·2⁻⁷¹` is tight for the widest-group extractor `E₁` and
    for every extractor that does not read `ũ` (paper). Because `hash_to_target` binds `ũ`, the
    prefix group is determined by the first message and `ũ` (`witness_determined`,
    `card_not_kosPar_le`, `pomfrit_disjQuads_le`, `pomfrit_par_count`; bad `chall₁` at most
    `2⁻¹³⁴`); for trees agreeing on the label rows an efficient extractor has no `Shift` term
    (`exists_slope_of_kosGood_affine`, `witness_determined_affine`). Hidden slices (trees that disagree on the label rows; `pomfrit-lemmap-tight.md` §6): an
    accepting set of a minority group has at most `2²⁸` points or lies in one slice of a class of
    trees with the same rows (`card_le_of_nonbit_slope`, `subset_slice_of_fixed`), the response is
    affine there (`claim4Hyp_slice`, gate model `translateOn_gate_slice`), and any two challenges
    of one slice with the same check value certify the witness (`slice_collision_sound`,
    `slice_collision_sound_affine`). Extractors that only evaluate the check value do not find the
    slice (`DTree.card_detect_le`). **The class extractor** (`pomfrit-lemmap-tight.md` §6A; `Seed/SliceDecode.lean`,
    `ROM/LemmaPClass.lean`): an accepting set lies in a slice of one class (trees with the same
    witness and label rows) or has at most `2^{⌊w/2⌋}` points, so the first-phase extractor should
    output the widest class, not the widest prefix group. Decoding is needed only between two
    classes of width ≥ 51, which leave at most one tree; `Dec^cls` (< 2¹⁵ linear systems, < 2²²·¹
    evaluations of the check value: `dec`, `card_decQ_le`, `dec_congr`) is sound without hypothesis
    and complete for level sets of more than 2⁵⁰ points (`dec_cert_sound`, `dec_cert_complete`). Per
    chain, `clsExt` is the free trees' prefix or at most 2⁵⁰ challenges accept (`class_or_small_dec`,
    `extract_or_class`; `per_query_bound_cls`: 2⁻⁷⁸). On paper this gives Lemma P and U1 with
    `(Q₃+ℓ+1)·2⁻⁷⁸ + q₁·2⁻¹³⁴` instead of `(Q₃+ℓ+1)·2⁻⁷¹` (2⁻¹⁴ at 2⁶⁴ queries), with no conjecture
    and no property of `H₅`. Not mechanized: the affine and two-label structure of the executable
    verifier's CRT masks on slices (hypotheses `AffineOn`, `TwoLabelOn`; gate model:
    `translateOn_gate_slice`, `twoLabel_gate`) and the one-more game with `E₁^cls` (G8-cls), so
    `pomfrit_U1_sim` keeps 2⁻⁷¹. The earlier many-label-vector decoding problem was an artefact of
    the widest-group default; the heuristic decoder is needed only below 2⁻⁸⁵, and its wrong-gate
    step rests on an assumption that fails for some level sets of codimension ≥ 4 (`slice.py` R7). Keep `ũ` in `hash_to_target`: it is
    security-relevant. The converse, OMPR ≤ PomFRIT one-more forgery plus a completeness term, is
    in Lean in PomFRIT's real one-more game for a forger with coins and any client given as oracle
    computations (`pomfrit_T6`, `pomfrit_T6_bound`, `Assumptions/BlindPomfrit.lean`; the game for a
    forger with coins is `game` for one without, `gameB_liftF`; the client carries the game's query
    log across sessions, so that the reduction's logged queries are replayed exactly). For
    the Lean client (`leanClient`, the Lean prover as oracle computations, equal per table to
    `Prover.voleGen` / `Prover.proveCommit`, `eval_start`, `eval_finish`) the completeness term is
    `≤ (ℓ+1)·2⁻¹¹³` (`compFail_le`), so `Adv^{ompr}(B; n, ℓ) ≤ Pr[PomWin] + (ℓ+1)·2⁻¹¹³`
    (`pomfrit_T6_lean`, `pomfrit_T6_lean_bound`; `ROM/ProverIC.lean`,
    `Assumptions/PomClientLean.lean`, `BlindPomfritGrind.lean`, `BlindPomfritComplete.lean`,
    `BlindPomfritT6Lean.lean`; `pomfrit.md` G9, closed). It assumes `B`'s own random oracle has
    finite answer types.
- *The UOV assumptions* (`docs/security/uov-assumptions.md`, `Assumptions/`): the assumptions of §3
  of that note as standalone games, generic in key generation, public map and `derive_preimage`
  (`Assumptions/UOV.lean`), with the protocol theorems' UOV terms as their advantages
  (`Assumptions/UOVLinks.lean`). Reductions in Lean: det-FDH ≤ A-OMPI and A-OMPI ≤ OMPR (T1(a),
  T1(c), `Assumptions/IdealTag.lean`); CT-UF^open ≤ OMPR with `Com` a random function, and `K`
  keys by guessing (T4, `Assumptions/CTUFOpenOMPR.lean`); OMPR ≤ OMPR⊕τ, tight
  (`advOMPR_le_shift`), and OMPR⊕τ ≤ `τ^{ℓ+1}`·OMPR by guessing the shifts (P8(a),
  `advOMPRShift_le_guess`, `Assumptions/Shift.lean`); OMPR ≤ one-more forgery plus a completeness
  term for the blinding forger of any client with distinct session labels (T6, generic core,
  `ompr_le_blind`, `Assumptions/Blind.lean`; at PomFRIT, `pomfrit_T6`, and for the Lean client with the completeness term bounded, `pomfrit_T6_lean`); UF-Tag with a signability probe ≤ UF-Tag plus the
  signer's aborts (P9(a), `ufTagAdv_le_noProbe`). The real sampler can abort, so every "tight"
  reduction carries a sampler-failure term `n·E[δ^{255}] ≈ n·2⁻²⁹⁵·⁸`.
- *Audits* (§3, "Audits"). Every headline theorem's hypotheses are instantiated
  (`Audit/Nonvacuous.lean`; for the unbound bounds, the UOV reductions and the shift games also
  `Audit/UnboundROM.lean`, `Audit/IdealTag.lean`, `Audit/OMPRShift.lean`, `Audit/T6Pomfrit.lean`,
  `Audit/SimExtract.lean`), and every privacy game's honest path is shown to reach its
  challenge outputs (`Audit/Liveness.lean`).
- *Also*: the PomFRIT attack on `main` and the (PU) bound for the others (§3); zero knowledge on
  `main` for one proof of the executable prover up to an explicit prediction of `w[0..16)`
  (`zk_rom_ic_main`), and Moussaka 4(a) and Ratatouille unlinkability on `main` with the joint
  (PU) hop, (PU) an explicit term (`anonymity_main`, `unlinkability_main`, §3); one proof on
  `main` with shared tables, `H₂³` visible and a global cipher (`zk_rom_ic_h23_main`); (PU) as a
  game (`PU.puAdv`), Moussaka 4(a) on `main` with the (PU) advantage of explicit predictors as the
  only non-numeric ZK term (`anonymity_main_pu`), and the ideal-permutation bound
  `(c+q)/(2¹²⁸−q) + q/(2⁴⁴⁰−q)` for `Com` (`puAdvPerm_moussaka_le`; Ratatouille `…2⁵⁴⁴…`); Lemma DS (c) on
  one SHAKE oracle (`seedXofDS_le`, §3); the one-query attack on plain CT-UF from the scaling
  symmetry `P(λs) = λ²·P(s)` (`Spec/PqovScale.lean`, `qmap_smul`, `ctuf_scaling_attack`) and the
  counting cores of the OMPR⊕τ and CT-UF^× separations (`combiner_count`, `lottery_count`,
  `rewind_supermartingale`); the algebra of shifted targets on `qmap` (`Spec/PqovShift.lean`:
  `preimage_line`, `preimage_plane`, `qmap_add_of_polar_eq_zero`, `affine_symmetry`); Theorem R of `ompr-shift-algebra.md` with its games
  (`Assumptions/TheoremR.lean`, `thmR`): a reduction OMPR ⇒ OMPR⊕τ that is black-box in the
  adversary only wins against the explicit adversary `A**_D` with probability
  `≤ 2·τ^{−(q+1)} + Adv^{free}(M) + V⁴·2⁻³⁴³`, `M` explicit, for reductions with at most `T`
  messages to `A**_D` (`thmR_V4`; the bad events `badPr_le`, `Assumptions/TheoremRBad.lean`), and
  Corollary R′ (`corR'`); no affine symmetry of pqov's keys translates targets except with
  probability `256⁻¹⁹⁵¹ + 256⁻³²⁸⁵`, and the target map of a symmetry is fixed by `A` (Lemma N;
  `Assumptions/SymmetryCount.lean`, `pr_translation_le`, `pr_not_spanTriv`); Theorem T3 itself over pqov's
  keys with `P1`, `P2` uniform (`Assumptions/SymmetryT3.lean`, `t3`: only the scalings, all keys but
  `256⁻¹²⁸`); OMPR^free as a game (`advOMPRFree`); every OMPR adversary is in the
  reduction class with its advantage (`redExp_liftRed`); the deterministic cores of the protocol notes (§5);
  arithmetizations of all seven relations (§6); executable specs, verifier and prover that match
  the C++ KATs, unbound Moussaka's included (§7, §8).

**On paper only**: removing U1's `2⁻⁷¹` term efficiently in general, the affinity of the
verifier's CRT masks under label agreement, and Lemmas P^∞ / P^lin in the one-more game
(`pomfrit-lemmap-tight.md`); in the permutation model, the CT-UF^open, UF-Tag and OMPR corollaries of the
protocol theorems and PomFRIT's U1/U2 with simultaneous extraction; for the many-token forms of Ratatouille's Thm 3, Moussaka's Thm 3 and unbound Moussaka's Prop U3 / Thm U4 (`noTheftN`, `noRedirectN`, `nmUN`): plain extraction with no simulated proofs (`PlainSEN`) and one programmed-point term per simulated proof (`SlotEvN`), to which `WeakSEN` is reduced (the hops' read budgets are proved), and these theorems with the other hashes read off uniform tables; its Thm U1
with inverse queries, and one joint bound over all three extraction families;
weak simulation-extractability (L8) for the Lean simulators, which Moussaka non-malleability
(Thm 3) and Ratatouille no theft take as the hypothesis `WeakSE2`, the read budgets of their ZK
hops, their collision terms `δ` and `Adv^ow ≤ q_K·2⁻¹²⁷`; Ratatouille's `Com`-binding term `ε_bind^K`, and Lemma 2.1's permutation terms (§5); the UOV
reductions with `Com` or `Tag` a random permutation with inverse access (Lean: random functions),
T1(b, d, e), of T3 the bound `256⁻⁹⁷⁶` (Lemmas C, E, F) and Proposition A for additive maps with several Frobenius components (`ompr-shift-algebra.md` §8.7; `t3` has `256⁻¹²⁸` and one component), T5, P8(b–d), the success of `A**_D` in Corollary R′ (§2.4) and the converse of
`advOMPR_le_ompr31` (`docs/security/uov-assumptions.md` §10); the meta-reduction theorems and the
GPI analysis (`docs/security/uov-open-structure.md`) and the OMPR⊕τ and CT-UF^× separations
(`docs/security/uov-open-reductions.md`), apart from their counting cores;
strong simulation-extractability beyond its Lean core (§2); every quantum statement (§4,
`docs/zk-qrom.md`); the composition of Lemma DS (c) with the privacy games' tables; the bad event
`β` of the linear `N`-pair bounds (`docs/zk.md` §10.8); and, for ZK on `main`, a bound on the
(PU) term itself (one-wayness of Keccak-p[800] in `r`) and the cross-proof `iv` and `H₃`
collisions.

**Modelling assumptions**: SHAKE128/256 are random oracles, AES-128 is an ideal cipher (classical
and quantum); Keccak-p[800,12] one-wayness and binding/hiding of `Com` (computational: `Com` is
evaluated inside the proofs, so no random-oracle bound applies to it, §3); for Moussaka 4(b)'s
averaged abort term, the `P2` part of pqov's keys uniform; one-more-UOV (OMPR, Def. 3.1 with
`derive_preimage`) for all three protocols, and for the Lean chains to it, `Com` (`hmodel`) and
`Tag` (`TagIdeal`) idealized in the standalone UOV games only (§5, Gap 5); the Lean models are tied to the C++ by tests, not proofs (Gap 2).

**Findings and paper corrections** (details in the section or note cited):
- *ZK fails with FAEST's CRT masks*: PomFRIT's Issuer linked redemptions to issuances; fixed on
  `main` since `64fd1a4` by dedicated label rows for PomFRIT (+256 bytes per proof). Moussaka and
  Ratatouille still take the masks from the witness (`REUSE_CRT_WITNESS`), so their ZK rests on (PU)
  (the analysed commit `d5def9c` of branch `voleith-label-rows` had the rows for all five relations,
  with the opt-in flag `CRT_DEDICATED_LABEL_ROWS`; `main`'s patch is the same mechanism with the
  opt-out `REUSE_CRT_WITNESS`). The FAEST v3 spec's own ZK proof has a gap
  (G8 → G9) (§3, `docs/zk.md` §4, §8.3).
- *Cross-protocol key sharing* lets anyone mint Ratatouille credits or forge Moussaka tokens
  (critical, demonstrated; §5).
- *Protocols* (§5): PomFRIT's paper reduction has a gap (repaired by Lemma P), its signatures are
  not unique per message, `hash_to_target` overlaps proof-system domains, and blindness needs the
  "both ⊥" rule; Moussaka nullifier squatting and an invalid one-more-UOV argument
  (restructured); Ratatouille spends are not bound to a session, and its H3 needs the Client's
  validity check against the commitment it sent.
- *Protocol reductions* (§5): Ratatouille Thm 1's UF-Tag reduction must not forward the Issuer's
  signing calls on the duplicate-nullifier path, where `spend_response` signs before the nullifier
  check (F5) and withholds the signature; the fixed reduction needs a signability probe or the
  abort term `E4` (`docs/security/ratatouille.md` §4). Unbound Moussaka's U5(b) proof kept the
  issuance-acceptance bits through the PRF hop; the corrected abort term is `ψ_c ≤ κ + φ_c`, `κ`
  the issuance proof's completeness error (UF7, `docs/security/moussaka-unbound.md`). Unbound Prop U3 used plain extraction where weak SE is needed and an invalid key-recovery argument (the bound holds: `Adv^ow-k ≤ Adv^prf-t_1 + 2⁻¹⁹²`); Thm U4 needs neither `ε_dig` nor CT-UF^open, and its `Adv^ow-kr` is the PRF term (UF8). `main`'s
  README rewrite (`ef3259e`) dropped the warning that a VOLE-IHAT nullifier record must span every
  accepted Anchor Set; a per-set record allows one redemption per set (F8,
  `docs/security/moussaka.md`).
- *UOV assumptions* (`docs/security/uov-assumptions.md`, `uov-open-reductions.md`,
  `uov-open-structure.md`):
  - **CT-UF as stated is false for UOV.** The public map is homogeneous quadratic and every element
    of GF(256) is a square, so one signing query on `μ·Com(x*)`, rescaled, forges on the unqueried
    `Com(x*)` (`ctuf_pqov_broken`). It was this analysis's own intermediate assumption for Moussaka;
    the draft states one-more-UOV, which is unaffected. Moussaka's proof now goes through
    CT-UF^open (`docs/security/moussaka.md` §3.3). With freshness up to scalars, CT-UF is
    equivalent to "OMPR with free non-challenge calls", which no relativizing reduction derives
    from OMPR (oracle separation, paper).
  - **The "tight" reductions T1(c) and T4 were not**: they need padding to exactly `q + 1` claims
    (`q_T + Q` and `q_f + 2q_S + 1` targets) and, with the real aborting sampler, a term
    `n·E[δ^{255}]`; T4's timing term `q_S·(q_f + q_S + 1)·2⁻³⁵⁹·⁹` is unnecessary.
  - Ratatouille Thm 1 omitted the Issuer's abort term (`E4`, `(N_I + N_S)·E[δ^{255}]`), which must
    also cover aborts on forwarded signing calls; T5 lacked the same term; Theorem 4 of
    `ratatouille.md` had `255⁻²⁵⁶` for `δ(sk)^{255}`. The signability probe of the Lean balance
    game costs exactly that term (P9); an Issuer salt (R1) does not remove it.
  - **OMPR ⇒ OMPR⊕τ**: every reduction black-box in the adversary and the trapdoor function, even
    with rewinding, loses at least `τ^{q+1}/2` in a generic model, so guessing is optimal in that
    class (paper); PomFRIT's `Q₃·2⁻⁷¹` stays unless a proof uses UOV's algebra.
  - **The meta-reduction (P7) is now three theorems** (paper): no key-preserving black-box
    reduction from the UOV problem, OW or EUF/SUF-CMA to OMPR or CT-UF (A1), none fully black-box
    to any of OMPR, A-OMPI, CT-UF, CT-UF^open (A2, using the determinism of `derive_preimage`), and
    T2's loss `q_T` is optimal for single-run reductions that use only validity (A3).
  - **OMPR ⇒ OMPR⊕τ with UOV's algebra** (`docs/security/ompr-shift-algebra.md`; Theorem R in Lean with every term
    explicit, `thmR_V4`; Corollary R′ `corR'`): a
    reduction black-box in the adversary only, with any use of the public map and rewinding, wins
    against one explicit adversary with probability `≤ 2·τ^{−(q+1)} + Adv^{free}_{UOV} +
    V⁴·2⁻³⁴³` (Theorem R). So beating the guessing loss by more than a factor 4 needs a break of
    OMPR^free or a reduction that is not black-box in the adversary (such as one using PomFRIT's
    `E₁`). Affine symmetries of `P` never translate targets (`affine_symmetry`). **No symmetries but the
    scalings** (Theorem T3, `ompr-shift-algebra.md` §8; model: `P1`, `P2` uniform; [Lean] `t3`, `Assumptions/SymmetryT3.lean`: for every `O`, all keys but `256⁻¹²⁸` have only the pairs `(λI, λ²I)` among affine pairs with `A`, `T` linear or Frobenius-semilinear and `A` bijective or `T` injective, and only `F·(I, 0)` as infinitesimal pairs, by a route through the oil space and the tensor `S` (`tensor_group`, `tensor_lie`), not the note's; false for a fixed `P1` (`not_t3Good_p1_zero`); paper only: the bound `256⁻⁹⁷⁶` and maps with several Frobenius components; for any `P1` and uniform `P2`: `pr_translation_le` (`≤ 256⁻¹⁹⁵¹ + 256⁻³²⁸⁵`), `pr_not_spanTriv`, `scaling_target`): for
    every oil space and all keys but a fraction `≤ 256^{−976}`, the only pairs `(A, T)` with
    `P∘A = T∘P`, `A` an additive bijection (linear or Frobenius-semilinear, with an affine part), are
    `(λI, λ²I)`, and the only infinitesimal pairs `B(s, Xs) = Y·P(s)` are `F·(I, 0)`; so a public
    symmetry moves a target only inside its class. [Lean] the identities the proof starts from
    (`Spec/PqovSymmetry.lean`: `symmetry_polar`, `symmetry_eigen`, `symmetry_kernel_radical`,
    `infinitesimal_polar`, `infinitesimal_eigen`, `infinitesimal_iff_first_order`); the counting
    is paper. Checked at full size for the infinitesimal statement
    (`scripts/ompr-shift-algebra/lie_fullsize.c`) and exhaustively for the group on toy keys over
    `F₄`. Collinear shifts (C1,
    `ompr-shift-algebra.md` §4): the 17 shifts of A-OMPR⊕17 are a forger's tree prefixes, so
    collinear lists are allowed. They trade one of the 45 equations for a landing on 17 of 256
    points. In the reference cost model (XL–Wiedemann after Thomae–Wolf) this costs `2^142.4`
    against `2^140.3` for direct forgery; the break-even τ is model-dependent (11 to 72), and no use
    of 17 shifts gains more than `2^4.1`. Checked on toy keys
    (`scripts/ompr-shift-algebra/c1_experiments.py`); paper and experiment, not in Lean.
  - Cryptanalysis of OMPR with the oracle (`docs/security/ompr-cryptanalysis.md`): answers of
    `derive_preimage` are uniform points of the good fibre, so they leak the trapdoor only through
    goodness. Two answers sharing a vinegar give an oil vector (`Spec/PqovVinegar.lean`:
    `vinegar_reuse`; good vinegars form a cone, `good_smul_iff`), with probability `2⁻⁴⁵⁷` at
    `2⁶⁴` calls; linear statistics of goodness need `2⁶⁰⁰` answers. No oracle-aided attack beats
    direct forgery (`≈ 2^140.3`); OMPR⊕τ has the same oracle, and shifts chosen after answers add
    only the factor τ. Toy experiments `scripts/ompr-cryptanalysis/ompr_toy.py`; on toy keys
    the oracle does give the oil space, with more calls than brute force.
  - The Lean PomFRIT one-more game computed the target oracle's input at a `chal1` from the AES
    PRG while its verifier used the ideal cipher (fixed); Lemma P's `E₁` needs the reduction to
    query `iv` itself at the target query, which the paper leaves implicit.
  - **GPI**: reliable badness tests give key recovery (heuristic, checked on toy parameters); no
    cheaper test is known; GPI ≈ key recovery (≈ 2²⁰¹ bit operations for uov-Ip) is a conjecture.
    The cost figures are estimates under semi-regularity, and the literature is cited from memory.
- *Extraction* (§1, §9): the sketch's "alive" leaf admitted an attack; bad challenges must be
  charged per `H₂¹`/`H₂²` query; the L2 interface was wrong (F2); Post (C3) fails against inverse
  cipher queries and is tied to the chains' points (F3, `PostP`); the sketch's "AES-CTR as a
  random oracle" model is unfaithful (Q3).
- *Zero knowledge with the fix* (§3): `Pr[Δ' = 0] ≈ 2⁻¹¹⁸·⁷`, not `2⁻¹²⁰` (`2⁻¹²⁰` is a lower
  bound: grinding makes `Δ` uniform on the accepted set only); the redemption and spend collision
  bounds missed `Δ' = 0` and undercounted by one; the "independent `H₃` slices up to `ε_iv`" step
  is not a black-box reduction; a 128-bit `rho` admits a multi-target Grover attack near `2⁵⁰`
  queries (§3, QROM).
- *Privacy proofs* (§3, §5): Moussaka Thm 4(a) and 4(b) need no `2⁻¹⁹²` term; Ratatouille's H1
  misses seed collisions and Moussaka's Thm 4 has no seed-XOF term; hiding of `Com` is
  computational: a `2¹²⁸` brute force over the opening wins it, so `εhide` stays a hypothesis.
- *Moussaka Thm 4(b)* (§3, `docs/security/moussaka.md` F7): it misses an abort term
  `2·(φ₀ + φ₁)` and needs Anchor Sets containing both issuers (`main`'s Client, which finds its
  index itself since `21be618`; for the earlier index-taking Client, its index rule); its Lean random-oracle games were vacuous
  until commit `919a204` (the spec's Anchor checked `main`'s request length, so it refused every
  label-row request; fixed); pqov's `derive_preimage` uses only 255 of its 256 vinegars (`δ²⁵⁵`
  for `δ²⁵⁶`); and `δ ≤ 1/255` holds only on average over the key, not for a fixed key. The
  liveness audit found no other vacuous game and one latent hazard of the same kind (the spec
  Moderator's redemption length, §3 "Audits").

## Layout

```
lean/
  README.md                 this file
  VoleMole.lean             root of the Lean library (imports every module below)
  VoleMole/
    Extraction/             label-based extraction core (the sketch's Core Theorem)
    SeedExtraction.lean     seed-based extraction core (Claims 3–4, case analysis)
    Seed/                   cores of L0–L8 and Q1–Q7 (commitments, KOS, QuickSilver, SE, quantum)
    ZK/                     cores of the zero-knowledge proofs
    Protocols/              cores of the PomFRIT, Moussaka, Ratatouille, domain-separation and
                            UOV-assumption notes
    Arith/                  executable constraint generators + soundness/completeness (in progress)
    Spec/                   executable protocol specs
    Verifier/               executable VOLEitH verifier and prover, and their bridge theorems
    Prob/                   uniform-probability layer: single-challenge bounds, per-chain theorem
    ROM/                    random-oracle model (VCVio): union bound over queries, per-chain terms,
                            the executable verifier against the oracle, domain separation, the
                            privacy games' adversaries as oracle computations, and the protocol
                            games: the verifier as an oracle computation (VerifyIC), the
                            extract-then-reduce glue (ExtractReduce), Moussaka unforgeability
                            (MoussakaOMUF), Ratatouille balance (RatatouilleBalance) and the
                            one-more reductions (OneMore, OneMorePomfrit); simultaneous
                            extraction (SimUnion, SimExtract, SimSpec, MoussakaOMUFSim,
                            RatatouilleBalanceSim); Lemma P (LemmaPDet, LemmaP, OneMoreLemmaP)
    Privacy/                privacy games on the executable specs (blindness, issuer hiding,
                            unlinkability): with zero knowledge and hiding as hypotheses, and
                            for the Lean prover in the random-oracle and ideal-cipher model;
                            (PU) as a game and its ideal-permutation bound (PU, PUKeccak);
                            Lean prover ZK for the unbound relations (MoussakaUnboundLean)
    Theft/                  non-malleability games (no theft, no redirect) on the specs in the
                            zero-knowledge table model, weak SE as a hypothesis; read budgets
                            (Reads); L8's programming step (SimExtract, SimExtractLean); any base
                            hash record and the other hashes as tables (LeanHb, Tables);
                            one-wayness of Com with random tables (ComOW); unbound
                            Moussaka Prop U3 and Thm U4 (MoussakaUnbound, MoussakaUnboundLean);
                            `N` honest proofs and `WeakSEN` (Many); `U` tokens and `M`
                            redemptions (MoussakaMany, MoussakaManyLean, MoussakaUnboundMany);
                            WeakSEN from plain extraction (ManyPlain); hop budgets (ManyReads);
                            Ratatouille for `U` Clients (RatatouilleMany, RatatouilleManyLean);
                            MoussakaManyReads, MoussakaUnboundManyReads
    Assumptions/            the UOV assumptions as standalone games (UOV) and their links to the
                            protocol theorems (UOVLinks); reductions between them: T1(a)/(c)
                            (IdealTag), T4 and the K-key step (CTUFOpenOMPR), A1 and P8(a)
                            (Shift), T6's generic core (Blind) and its PomFRIT instance
                            (BlindPomfrit; Lean client: PomClientLean, BlindPomfritT6Lean); Ratatouille under OMPR (RatatouilleOMPR); Theorem T3 (SymmetryProbes,
                            SymmetryTensor, SymmetryScalar, SymmetryT3); `Com`/`Tag` as random
                            permutations with inverse queries (LazyPerm, CTUFPerm, PermLinks,
                            FDHPerm);
                            simultaneous extraction down to OMPR (SimLinks); shared lazy-sampling, union-bound and simulation
                            lemmas (LazyIdeal)
    Audit/                  non-vacuity checks: the headline theorems' hypotheses instantiated,
                            and the games' honest paths shown to reach the challenge outputs
  vectors/                  test vectors dumped by the C++ (untracked; regenerate with the dumpers)
  docs/
    sketch.md               the maintainer's original design note
    lean-correspondence.md  sketch item → Lean name, and code-correspondence findings
    extraction/             proof of knowledge, simulation-extractability, quantum versions
      README.md             the main theorems and how the lemmas assemble (start here)
      L0-…L8-*.md           classical lemmas
      Q1-…Q7-*.md           quantum (QROM) lemmas
    zk.md, zk-qrom.md       zero knowledge, classical and quantum
    security/               protocol-level security notes
scripts/uov-open-structure/ (repository root) cost estimates and toy experiments for the GPI analysis
```

All `file:line` citations in `docs/` are relative to the repository root. Most refer to commit
`6d7113e` (`main` before `64fd1a4`, which moved PomFRIT to dedicated label rows); those about the
zero-knowledge fix refer to commit `d5def9c` of branch `voleith-label-rows` (opt-in flag
`CRT_DEDICATED_LABEL_ROWS`; merged as `64fd1a4` with the opt-out `REUSE_CRT_WITNESS` instead, the
branch since force-pushed to that version), and those about `21be618` (the Client finds its
Anchor) to `main`.

**Names.** Since `9d9bec8`, `main` calls Moussaka **VOLE-IHAT** and Ratatouille **VOLE-ACT**
(the drafts' names): `src/moussaka/` is `src/ihat/` (`moussaka.cpp` is `ihat.cpp`),
`src/ratatouille/` is `src/act/` (`ratatouille.cpp` is `act.cpp`), the headers are
`vole_mole/ihat.hpp` and `vole_mole/act.hpp`, and the tests and KATs are under `tests/ihat/` and
`tests/act/` (`ihat_kat.txt`, `unbound_ihat_kat.txt`, `act_kat.txt`). The domain-separation
strings (`"mous"`, `"rata"`) and every KAT value are unchanged. This directory keeps the old names
(`Spec/Moussaka.lean`, `docs/security/moussaka.md`, …), and citations of `src/moussaka/…` and
`src/ratatouille/…` refer to the old paths at the commit stated; the Lean executables and the C++
dumpers read the new paths.

## Building and checking

```sh
cd lean
lake exe cache get     # prebuilt Mathlib
lake build             # the whole library; must finish with no warnings
lake env lean VoleMole/Arith/UOV.lean    # check a single file
lake build VoleMole.ROM.Comb             # the random-oracle layer (§9), which needs VCVio
```

Toolchain and Mathlib: `v4.34.0`. [VCVio](https://github.com/dtumad/VCV-io) is pinned to a commit
in `lakefile.toml` and imported only by `VoleMole/ROM/`. It has no prebuilt cache: the first build
of `VoleMole/ROM/` compiles the part of VCVio, PolyFun and cslib it imports (about 120 modules, about
2 minutes with 2 threads). The executables link VCVio's native-backend archives as empty stubs
(`lake` prints `info: … native backend disabled`); nothing here calls them.

The prover is checked against the KAT proofs with `lake exe prover_vectors` (from `lean/`; `lake exe
prover_vectors DIR/tests labelrows` for the KAT files of a `d5def9c` build, `none` for
those before `64fd1a4`), and the zero-knowledge simulator with
`lake exe zk_sim [DIR/tests [main|labelrows|none [FILTER]]]` (about 10
minutes per layout; `FILTER` is a label prefix such as `moussaka` or `ratatouille 0`).

The C++ side of the cross-checks runs with the normal test suite:

```sh
ninja -C build && meson test -C build    # includes `lean-models`
```

## The results

### 1. Proof of knowledge (classical) — `docs/extraction/`

**Statement.** For every classical prover, the proof system is a *straight-line* proof of
knowledge for each of the repo's five relations: an extractor that only reads the prover's oracle
queries (no rewinding, no programming) outputs a valid witness whenever the verifier accepts, except
with probability

    ε_ext = Q·max(d,1)·2⁻¹²⁸ + q₁·ε_KOS + q₂·(ε_QS + 2⁻¹²⁸) + q_c·2⁻⁴⁴⁸ + ε_bind + ε_dead + (q²+q)·2⁻²⁵⁶

which is about 2⁻⁶⁰·⁸ at q = 2⁶⁴ queries. Model: SHAKE as random oracles, AES-128 as an ideal
cipher.

**Proof structure.** `docs/extraction/README.md` assembles it from these lemmas:

| Lemma | Content | Status |
|---|---|---|
| L0 | All hash domains are disjoint; AES inputs of different roles never collide | [paper] + [Lean] `Seed/Commitments.lean` |
| L1 | Committed data (commitment preimages, leaf keys) is well defined and binding | [paper] + [Lean] unique leaf keys and straight-line key extraction from the cipher log (PRF view, forward queries), binding with explicit `ε_bind` `ROM/CipherBind.lean`, `ROM/CipherOpen.lean`; the ordering half of the `H₁` linking, `Coll₁` and Post (C3) `ROM/CipherChain.lean`, `ROM/CipherSame.lean` (PRF view); statement binding for adaptive statements `ROM/StmtBind.lean`, `ROM/AdaptPomfrit.lean` |
| L2 | A leaf the prover cannot open is always the hidden one | [paper] + [Lean] in the corrected form (accepting set hides the committed dead leaves; L2(c), L2(a)) `ROM/CipherSame.lean` |
| L3 | KOS consistency check forces affine VOLE correlations (ε_KOS ≈ 2⁻¹⁵⁴) | [paper] + [Lean] `Seed/KOS.lean` (`Seed/KOSUnique.lean`: `ũ` determines the slope across level sets; slice certificates; `Seed/SliceDecode.lean`: a decoder for slices with its evaluation count) + [test] |
| L4 | QuickSilver with challenge-dependent constraints: either the constraints hold or few challenges accept | [paper] + [Lean] `Seed/QuickSilver.lean` + [test] |
| L5 | A tree whose challenge block varies holds the witness (Claim 4) | [Lean] `SeedExtraction.lean` |
| L6 | Per-chain case analysis: extract, or accept at most max(d,1) challenges | [Lean] `SeedExtraction.lean` |
| L7 | Arithmetization soundness: satisfied constraints imply the relation | [Lean] `Arith/` for all five relations + [test] cross-check (§6); paper `L7-uov.md`, `L7-keccak.md` |

**End-to-end deterministic theorem** ([Lean] `EndToEnd/`). For each of the five relations,
`*_extract` joins L5–L7 with the real constraint system: on a chain satisfying the hypotheses that
L1–L4 provide (stated explicitly in `EndToEnd/Relations.lean`), either some known tree's candidate
decodes to a witness of the actual relation (e.g. `P(s) = h ⊕ r`), or at most max(d,1) challenges
are accepted. The QuickSilver check polynomial is built from the relation's `Arith` system and
matched to the verifier's MAC arithmetic. The probability of each hypothesis (ε_KOS, ε_QS, 1/|F|
for the combination, and L1's binding) is bounded in §9, for the executable verifier in the
random-oracle and ideal-cipher model.

Along the way the analysis corrected the sketch's definition of an "alive" leaf (the original
admitted an attack with probability about τ·q₂·2⁻¹²⁸) and found that bad-challenge terms must be
charged per H₂¹/H₂² query, not per H₂³ query.

### 2. Simulation-extractability (classical) — `docs/extraction/L8-*.md`

**Statement.** Strong simulation-extractability: extraction still works when the prover also sees
simulated proofs, for any accepting proof that differs from all simulated ones. [paper] +
[Lean] `Seed/SimExt.lean`. No malleability attack was found.

### 3. Zero knowledge — `docs/zk.md`, `docs/zk-qrom.md`

**Finding (with FAEST's CRT masks): the proofs are not zero-knowledge.** The free-XOR label offset
of FAEST's CRT masks equals the first 128 witness bits (up to a public value). A verifier who knows
those bits learns the masks. In PomFRIT the Issuer knows them, so it could link redemptions to
issuances: blindness failed.

**Fix:** derive the labels from dedicated VOLE rows (+256 bytes per proof). On `main` since
`64fd1a4` (faest-arch-opt's `REUSE_CRT_WITNESS` patch) PomFRIT does this; Moussaka and Ratatouille
keep the masks from the witness, whose first 128 bits are a uniform secret, and rely on (PU) below.
Commit `d5def9c` (branch `voleith-label-rows` before it was merged) used the rows for all five
relations.

**Statement (on `main`, `docs/zk.md` §4.1).** [Lean] `ZK/Main.lean`, `ZK/Relations.lean`: in the
`main` layout the view `(d, c_i, forced labels)` is witness-independent, but the label offset is
`π(d) − π(w)`; the probability that some of `q` H₅ queries hits a sibling label *equals* a sum of
success probabilities of explicit predictors of `w[0..128)` from the adversary's auxiliary
information, so it is `≤ q·ε_PU` under (PU), stated as a hypothesis on those predictors (also with
the masked responses, and for a token's two proofs jointly). From the `Arith/` witness layouts,
`w[0..16) = r` is the commitment opening for Moussaka issue/redeem and Ratatouille issue/spend
(`moussaka_main_zk`, `ratatouille_main_zk`; (PU) there is one-wayness of Keccak-p[800] in `r`, an
assumption); towards a Moussaka Moderator that never sees `t`, `ε_PU = 2⁻¹²⁸` unconditionally
(`moussakaRedeem_main_zk_uniform`). For PomFRIT the Issuer's `t ⊕ h(σ)` is `r` in every honest run
(`issuerGuess_eq`), so its query hits with probability 1 and the attack test accepts every real
proof (`pomfrit_issuer_hits`, `pomfrit_attack_test`). For the executable prover in the model of
`zk_rom_ic` (`docs/zk.md` §4.2; `ZK/HopsMain.lean`, `ZK/MainSlots.lean`, `ZK/MainGame.lean`,
`Privacy/MainChain.lean`): one proof is `q₃·2⁻¹²⁸ + 221·(4607 + q_E)·2⁻¹²⁸ + Pr[mainPred]`-close
to the simulator, where `mainPred` is an explicit witness-free predictor of `w[0..16)`
(`zk_rom_ic_main`; `≤ (q₅ + 1)·2⁻¹²⁸` when the prefix is uniform and independent of its inputs,
`pr_mem_uniform_le`). Four proofs in sequence are handled jointly by `main_chain_le` (the H5/H6
coupling for all four at once, factor 15, for consistent `H₅` read sets). This gives
`anonymity_main` (Moussaka 4(a): `8·εRF + 15·(PU₀ + PU₁) + 2·εhide`) and `unlinkability_main`
(Ratatouille: the same with `PU(b₁, b₂) + PU(b₁', b₂')`), `PU` the explicit terms `puTerm`,
`puTermR`. [Lean] `ZK/HopsMainIC.lean`: one proof on `main` in the shared-table model of
`zk_rom_ic_h23` (`H₅` on every 37-byte input, `H₂³` programmed and read freely, global cipher):
`zk_rom_ic_h23_main_num`, `q₃·2⁻¹²⁸ + 2⁻¹¹³ + 221·(4607+q_E+4607)·2⁻¹²⁸ + Pr[mainPredIC]`, the last
term `≤ (q₅+1)·2⁻¹²⁸` for a uniform independent prefix. [Lean] `Privacy/PU.lean`,
`Privacy/PUKeccak.lean`, `Privacy/MoussakaMainPU.lean`: (PU) as the game `puAdv`;
`anonymity_main_pu`: `8·εRF + 15·(Σ_{b,c} puAdv Com (predM_c b) + 4(q₅+1)·2⁻¹²⁸) + 2·εhide`; with a
uniform permutation for Keccak-p[800] and a predictor with `q` forward and inverse queries and `c`
candidates, `puAdv ≤ (c+q)/(2¹²⁸−q) + q/(2⁴⁴⁰−q)` (Ratatouille: `2⁵⁴⁴`). A finalization the
adversary makes fail still computes an unshown redemption proof for a dummy token, so `PU_b` is not
exactly a prediction of `r`: the extra `2(q₅+1)·2⁻¹²⁸` per world (`docs/zk.md` §4.2, corrected).
Still [paper]: several proofs on shared tables on `main` (`ε_iv`), the reduction of Ratatouille's
`puTermR` to `puAdv`, Moussaka's `find_issuer` Client and 4(b) on `main`, and (PU) for the real
Keccak-p[800,12], which is an assumption.

**Statement (with the fix).** Adaptive, multi-proof, statistical-in-the-witness zero knowledge in
the classical ROM [paper] + [Lean] `ZK/`. Against quantum distinguishers [paper], with a bound of
about 2⁻¹⁹ at 2³⁰ queries and 2³⁰ proofs. The dominant term, Q_P·√(q/2¹²⁸), is the standard
adaptive-reprogramming loss and has no known matching attack. A 128-bit `rho` does admit a real
multi-target Grover attack around 2⁵⁰ queries. Both are removed by a 256-bit `rho` and a salt in
chal1/chal2 (recommended, not implemented).

**Mechanized for the executable prover, with the fix** ([Lean] `ZK/`, `Privacy/`; `docs/zk.md`
§10). The list at the end of this section says what remains assumed.

*One proof, reduced to per-hop hypotheses* (`docs/zk.md` §10.1; `ZK/Sim.lean` … `ZK/Exec.lean`).
- An executable simulator (`Sim.simulate`; `Sim.simulateRO` also programs `H₂³`). The verifier
  accepts its proofs under the programmed oracle with no assumption beyond `Δ ≠ 0`
  (`simulateRO_accept'`), i.e. except with probability `≤ noHitProb + 1/|A| ≤ 2^{−2¹⁵} + 2⁻¹¹⁴
  ≤ 2⁻¹¹³` over the simulator's coins (`pr_simulateRO_reject_113`; `pr_simulateRO_reject_110`
  is the weaker first-moment form).
- The executable Lean prover equals an ideal-tape prover at its own run's tape
  (`prove_eq_proveIdeal`), and on a uniform tape the ideal-tape prover's output is distributed
  exactly as the simulator's (`proveIdeal_close`; with label rows Θ is moreover uniform and
  independent of the proof, `prove_guess_theta`). So the zero-knowledge advantage of any
  distinguisher equals its advantage on the tape (`zk_reduction`), and `Privacy.ZeroKnowledge`
  holds with error `ε` for statement families with dedicated label rows
  (`labelRows_zeroKnowledge`) under the **tape hypothesis** `TapeHyp … ε` (H1, H4, H6 and the
  grinding answers: the run's tape is `ε`-close to uniform) and deterministic hypotheses (the
  witness satisfies the system for every `chal1` and combination challenge, its size and the
  degree bound, `N_MASK ≤ 32`, and the two correctness facts of
  the completeness theorem, proved for faest-arch-opt's tables; correct interpolation is proved,
  `ZK/Interp.lean`).
- The tape hypothesis is **derived from one hypothesis per hop** by a proved hybrid argument
  (`ZK/Hops.lean`, `HopHyps`, `tapeHyp_of_hops`), so `labelRows_zeroKnowledge_tables` has error
  `ε_rho + ε_grind + ε_bavc + ε_lab`: `H₃`'s answer at the seed input is close to uniform (H1),
  the `H₂³` answers at the grinding points are (grinding), the hidden part of a commitment from a
  uniform root seed is (H4, BAVC hiding: AES), and the `H₅` answers at the sibling labels are,
  through the ideal-tape prover (H6).
- PomFRIT's two-phase zero knowledge, with the instance chosen after step 1, is derived the same
  way (`ZK/TwoPhase.lean`: step 1's fields are uniform and independent of the witness, step 2
  stays uniform given them for every adaptive choice; `twoPhase_close` under the two-phase tape
  hypothesis `TapeHyp2`; `twoPhase_close_tables`; `TapeHyp2` from the hops, with one more term,
  the abort probability `noHitProb`: `ZK/TwoPhaseHops.lean`, `≤ 2^{−2¹⁵}` by `noHitProb_le`).
- For all three protocols the per-relation statements are assembled and every deterministic
  hypothesis is proved (`Privacy/MoussakaLean.lean`, `Privacy/RatatouilleLean.lean`,
  `Privacy/PomFRITLean.lean`); with SHAKE (`*_shake`) only the hop hypotheses and hiding remain,
  each proof's error the sum of the named terms. The hop hypotheses are `Close` bounds for a fixed
  hash record, an idealization; the random-oracle theorems below replace them.

*One proof, in the random-oracle and ideal-cipher model* (`docs/zk.md` §10.1).
- **The hops.** With the hashed domain a uniform table (`ZK/HopsROM.lean`), H1 and grinding hold
  with `ε = 0`, H1 with `≤ q₃·2⁻¹²⁸` against a distinguisher reading `H₃` at `q₃` inputs,
  programming `H₂³` at the grinding points is perfect (the prover's grinding prefix provably does
  not read `H₂³`, `ZK/HopsRead.lean`), and H6 costs `≤ (q₅ + 1)·2⁻¹²⁸` against a distinguisher
  reading `H₅` at `q₅` inputs (`lab_rom_hyp`, `ZK/HopsH6.lean`: the prover reads `H₅` only at the
  active labels, and each query is a guess of the label offset `Θ`, which is independent of the
  proof). H4 is proved in the ideal-cipher model (`ZK/HopsH4Ideal.lean`: the BAVC rebuilt with the
  cipher a uniform table, equal to the executable one at AES, `hiddenOut_eq`; a GGM hybrid over the
  `≤ 221` hidden-path nodes gives `≤ 221·(4607 + q)·2⁻¹²⁸` against a distinguisher reading the
  table at `q` keys, `hide_rom_query`), with the rows uniform functions.
- **Composed** (`zk_rom_ic`, `ZK/HopsJoint.lean`): with `H₃`, `H₂³`, `H₅` independent uniform
  tables (the other domains fixed) and the BAVC's cipher a uniform table in a proof-only
  cipher-parametric prover `proveE` (the executable prover at AES, `proveE_recOf_aes`), one proof
  is `q₃·2⁻¹²⁸ + 221·(4607 + q_E)·2⁻¹²⁸ + (q₅ + 1)·2⁻¹²⁸`-close to the simulator against a
  distinguisher reading `H₃`, `H₅` and the cipher at `q₃`, `q₅`, `q_E` keys; it does not read
  `H₂³`, and only the hidden part of the commitment uses `E`. With `H₂³` visible as well
  (`zk_rom_h23`, `ZK/HopsH23.lean`, with `H₅` a table on every 37-byte input), for the executable
  prover with BAVC hiding assumed: the simulator programs `H₂³` at the grinding points of the
  prefix it recomputes from its own proof as the verifier does (`simulateRO`'s points), and one
  proof is `q₃·2⁻¹²⁸ + Pr[GrindBad] + ε_bavc + (q₅ + 1)·2⁻¹²⁸`-close against a distinguisher that
  also reads `H₂³` without limit, `Pr[GrindBad] ≤ noHitProb + Pr[Δ' = 0]` (the recomputed points
  are the prover's otherwise: `hyb3_vPre`, `ZK/VerifyPre.lean`).
- **Both at once** (`zk_rom_ic_h23`, `ZK/HopsIC.lean`): the executable BAVC, VOLE expansion,
  prover and verifier call their CTR PRG through a class (`HasPrg`, `Verifier/Prg.lean`; AES for
  the executables, which are unchanged), so they run with the cipher a uniform table `E`
  (`icPrg E`, the executable code at `E = aesTable`) and `zk_rom_h23`'s chain holds for every
  cipher; with `H₅` a table on every 37-byte input and the honest recomputation's reads of `E`
  (the reconstructed tree, at most `4607` keys) counted, the executable prover with the ideal
  cipher is `q₃·2⁻¹²⁸ + Pr[GrindBad] + 221·(4607 + q_E + 4607)·2⁻¹²⁸ + (q₅ + 1)·2⁻¹²⁸`-close to
  the programming simulator against a distinguisher reading `H₃`, `H₅`, `E` at `q₃`, `q₅`, `q_E`
  keys and `H₂³` freely.
- **The grinding term is numeric** (`ZK/AcceptCount.lean`, `ZK/GrindNum.lean`): the accepted set
  has `|A| ≥ 2¹¹¹` of the `2¹²⁸` values of `Δ` (a Markov bound on a box of hidden-index tuples,
  with the summed open count evaluated by the kernel), so no grinding answer is accepted with
  probability `≤ 2^{−2¹⁵}`; `W_CRT` is injective, so `Δ' = 0` only at `Δ = 0`, which is the first
  accepted answer with probability `≤ 1/|A|`; hence `Pr[GrindBad] ≤ 2⁻¹¹⁰` (`grindBad_le_110`),
  and `≤ 2⁻¹¹³` with the second moment (next item). `zk_rom_ic_h23_num`, `zk_rom_h23_num` state
  both bounds with `2⁻¹¹³` in its place. The single-proof error is thus
  `εRO(q₃, q₅, q_E) = q₃·2⁻¹²⁸ + 2⁻¹¹³ + 221·(4607 + q_E + 4607)·2⁻¹²⁸ + (q₅ + 1)·2⁻¹²⁸`, about
  `2⁻¹⁰⁷·⁰` at zero budgets.
- **The grinding term by the second moment** (`ZK/AcceptVar.lean`, `ZK/AcceptVarData.lean`,
  `ZK/GrindNum.lean`): Chebyshev's inequality on the same box, with the second moment of the
  open count evaluated by the kernel (pairs of tree nodes: related pairs on a pass over the tree,
  disjoint pairs through the histogram of the `136` distinct leaf-count vectors), gives
  `|A| ≥ 2¹¹⁴` (`card_accSet_ge_114`), so `Pr[Δ' = 0] ≤ 2⁻¹¹⁴` (`pr_hitZero_le_114`) and
  `Pr[GrindBad] ≤ 2^{−2¹⁵} + 2⁻¹¹⁴ ≤ 2⁻¹¹³` (`grindBad_num_114`, `grindBad_le_113`). Every numeric
  error term (`εRO`, `εROP`, `εROPm`, `εROPmP`, `εAd*`, `h23*`) and every headline and privacy
  bound below uses `2⁻¹¹³`. The true `Pr[Δ' = 0] = Pr[hit]/|A|` is `≈ 2⁻¹¹⁸·⁶⁷`
  (`|A| ≈ 0.397·2¹²⁰` by sampling); the paper's `2⁻¹²⁰` treats `Δ'` as uniform on all `2¹²⁰`
  values, but grinding makes the accepted `Δ` uniform on `A` only. The rest of the gap is the box
  (`120¹⁷ ≈ 2¹¹⁷·⁴`) and the slack of a second-moment bound near the mean; an exact count of `A`
  needs a subset-state dynamic program out of the kernel's reach.
- **AES as random permutations** (`ZK/IdealCipherPerm.lean`, `ZK/HopsH4Perm.lean`,
  `ZK/HopsICPerm.lean`, `ZK/ReadsROPerm.lean`): with the cipher a table of independent uniform
  permutations, read by the distinguisher as whole permutations (forward and inverse queries),
  H4 costs `≤ 221·(4607 + q)/(2¹²⁸ − (nHi + 1)) + switchEps` (`hide_rom_query_perm`): the GGM
  hybrid with permutation rows (a hidden node's value is fresh in its parent's permutation, read
  elsewhere at `≤ nHi + 1` inputs) plus the PRP/PRF switching term
  `switchEps = (17·C(2 + VOLE_COL_BLOCKS, 2) + C(nHi + 1, 2))·2⁻¹²⁸` of the hidden leaves' and the
  root's rows (samples without replacement against uniform values; every other hidden row is read
  at most once), `≤ 2⁻¹¹³·²` for the relations' parameters (`nHi = 1`). The headline follows
  (`zk_rom_ic_h23_num_perm`, and as `ZeroKnowledgeRO` on `ShPm p`, `lean_zeroKnowledgeRO_perm`):
  `q₃·2⁻¹²⁸ + 2⁻¹¹³ + 221·(4607 + q_E + 4607)/(2¹²⁸ − (nHi + 1)) + switchEps + (q₅ + 1)·2⁻¹²⁸`.
- **Two phases** (`zk2_rom_ic_h23_num`, `ZK/TwoPhaseRO.lean`, `ZK/TwoPhaseIC.lean`): the same
  single-proof bound holds for PomFRIT's two-phase prover. The simulator programs `H₂³` at the
  prefix it recomputes for the instance picked after step 1; the fallback block is inside
  `Pr[GrindBad]`; the continuation may itself read `H₅` and the cipher, and its reads are added to
  the budget (the Issuer answers after seeing both requests, which read the tables).

*Several proofs on shared tables: the privacy theorems* (`docs/zk.md` §10.2;
`Privacy/ZeroKnowledgeRO.lean`, `ZK/ReadsRO.lean`, `Privacy/MoussakaRO.lean`,
`Privacy/RatatouilleRO.lean`, `ZK/TwoPhaseReadsRO.lean`, `Privacy/PomFRITRO.lean`,
`ZK/CollideRO.lean`, `ZK/CollideRO2.lean`, `Privacy/*Delta.lean`).
- `ZeroKnowledgeRO` is zero knowledge against distinguishers that also see (and read, with
  budgets) the random tables; `zk_rom_ic_h23_num` instantiates it (`lean_zeroKnowledgeRO`), and
  the two-phase theorem is `ZeroKnowledgeROS` (`lean_zeroKnowledgeROS2`: a simulator that may read
  the tables it does not program). The executable prover reads the cipher at `≤ 4607` and `H₅` at
  `≤ 624` keys, the simulator's programming at `≤ 4607` and `≤ 312` (`realRO_rdE`, `realRO_rd5`,
  `progRO_isProg`), and the executable verifier at `≤ 4607` and `≤ 312` (`verRO_rdE`,
  `verRO_rd5`, `ZK/VerifyReadsRO.lean`), which bounds what a reduction that runs the other proofs
  (or verifications) itself reads.
  `hop_ro` is the hybrid step for proofs sharing the tables; each step after the first costs an
  explicit programming-collision term `δ`.
- Moussaka anonymity and Ratatouille unlinkability, with the adversary's guess seeing all tables
  and all four proofs on the same tables: `≤ 8·εRO(q₃, q₅ + 1872, q_E + 13821) + (collision terms
  of both worlds) + 2·εhide` (`anonymityRO_lean`, `unlinkabilityRO_lean`). PomFRIT blindness with
  both sessions on the same tables: `≤ 4·εRO(q₃, q₅ + 1248, q_E + 18428) + δ(A) + δ(A.swap)`
  (`blindnessRO_lean`).
- **The collision terms are bounded in Lean** (`ZK/CollideRO.lean`, `pr_collide_zk`): the real
  prover reads `H₂³` only at its own grinding prefix `chal2 ‖ qs_check ‖ ã` (`72 + 16·(d − 1)`
  bytes), a simulator programs one prefix block, whose last `16·(d − 1)` bytes are its uniform `ã`
  (the simulated opening reconstructs, `reconstruct_openingOf`); for the second issuance
  `δI₁ ≤ noHitProb + 2⁻¹⁰²⁴`, for a redemption or spend (whose statement may depend on the earlier
  `ã`), with a second application of zero knowledge, `δ ≤ 2⁻¹¹³ + εRO(0, 312, 4607) + noHitProb +
  3·2⁻¹⁰²⁴`, and for PomFRIT `δ(A) ≤ noHitProb + 2⁻¹²⁸`. So `anonymityRO_lean_num`,
  `unlinkabilityRO_lean_num`: `≤ 8·εRO(q₃, q₅ + 1872, q_E + 13821) + 4·(2⁻¹¹³ + εRO(0, 312,
  4607)) + 6·noHitProb + 12·2⁻¹⁰²⁴ + 2·εhide` (about `2⁻¹⁰²·³` plus the budget terms), and
  `blindnessRO_lean_num`: `≤ 4·εRO(q₃, q₅ + 1248, q_E + 18428) + 2·noHitProb + 2·2⁻¹²⁸` (about
  `2⁻¹⁰³·⁴` plus the budget terms; `noHitProb ≤ 2^{−2¹⁵}`). The paper bound for redemptions and
  spends (`docs/zk.md` §10.2) missed the `Δ' = 0` part of `GrindBad` and undercounted the earlier
  `ã` by one; both negligible.
- **AES as random permutations in the games** (`docs/zk.md` §10.4; `Privacy/PermRO.lean`,
  `ZK/TwoPhasePerm.lean`). The games, their read algebra and their collision bounds are stated
  once, for every *type of cipher rows* `R` (`ShG R p = Tab2G p × Tab5F × (Blk → R)`, the rows
  read as functions by `CipherRow.row`) with a zero-knowledge structure (`ZKRow R`; for PomFRIT
  also `ZK2Row R`), and instantiated twice: function rows (the PRF view, `Sh p`, the theorems
  above, unchanged) and permutation rows (`Equiv.Perm Blk`: the adversary reads whole
  permutations, forward and inverse). With permutation rows every `εRO` becomes
  `εROPm p = q₃·2⁻¹²⁸ + 2⁻¹¹³ + 221·(4607 + q_E + 4607)/(2¹²⁸ − (nHi + 1)) + switchEps p +
  (q₅ + 1)·2⁻¹²⁸`: `anonymityRO_lean_num_perm`, `unlinkabilityRO_lean_num_perm`
  (`4·εROPm(pI; …) + 4·εROPm(pR or pS; …) + 4·(2⁻¹¹³ + εROPm(pR or pS; 0, 312, 4607)) +
  6·noHitProb + 12·2⁻¹⁰²⁴ + 2·εhide`, about `2⁻¹⁰²·³` plus the budget terms) and
  `blindnessRO_lean_num_perm` (`4·εROPm(pP; q₃, q₅ + 1248, q_E + 18428) + 2·noHitProb +
  2·2⁻¹²⁸`, about `2⁻¹⁰³·⁴`); the two-phase theorem with permutation rows is
  `zk2_rom_ic_h23_num_perm`.

*Statements and interactions that read the tables* (`docs/zk.md` §10.3; `Privacy/Resample.lean`,
`ZK/HopsPatch.lean`, `ZK/IdealCipherP.lean`, `ZK/AdaptRO.lean`, `Privacy/AdaptiveRO.lean`,
`ZK/TwoPhaseAd.lean`, `Privacy/MoussakaRA.lean`, `Privacy/RatatouilleRA.lean`,
`Privacy/PomFRITRA.lean`, `Privacy/PomFRITRAGame.lean`, `ZK/CollideAd2.lean`,
`Privacy/PomFRITRAH.lean`, `Privacy/PomFRITRAHPfx.lean`, `Privacy/MoussakaRAK.lean`,
`Privacy/RatatouilleRAK.lean`). In §10.2's games only the adversary's guess reads the tables. Here
its interaction does too, and for Moussaka and Ratatouille also its key stage.
- `zk_adaptive` covers an adversary that reads the tables (the proof's `H₃` slice, `H₂³`, `H₅`,
  the cipher, at `s₃`, `s₂`, `s₅`, `s_E` keys, adaptively and consistently) before it picks the
  statement and witness. The bound is `εRO(q₃, q₅, q_E) + (s₃ + s₅ + 1 + 221·s_E)·2⁻¹²⁸`, plus, if
  it reads `H₂³`, a second zero-knowledge application and `2·s₂·2⁻¹⁰²⁴` (`ρ` is 16 bytes; the
  simulated block's 128-byte `ã` is uniform). The proof samples the reader's view lazily
  (`Privacy/Resample.lean`) and runs the chain with the tables patched at its queries
  (`ZK/HopsPatch.lean`, `ZK/IdealCipherP.lean`).
- Moussaka anonymity with an interaction (responses, Anchor Sets, digests) that reads every table:
  `anonymityRA_lean_num`, about `2⁻¹⁰¹·⁹` plus the budget terms. Ratatouille unlinkability with an
  Issuer whose two message stages (issuance responses and `d₁`; round 1's response and `d₂`, which
  reads spend 1's proof) read every table: `unlinkabilityRA_lean_num`, about `2⁻¹⁰¹·⁶` plus the
  budget terms.
- Moussaka and Ratatouille with a **key stage that reads the tables** (`Privacy/MoussakaRAK.lean`,
  `Privacy/RatatouilleRAK.lean`; `AdversaryRAK`): `setup` reads the four slices and the shared
  tables, consistently within `KBudget k₃ k₂ k₅ k_E`, and outputs a state that fixes the contexts
  and the challenge Clients' keys (Ratatouille: the key, context and balance); the rest of the
  adversary is the `RA` adversary at that state. The issuance statements are then adaptive, so the
  issuance hops are `hop_roA` with `ZeroKnowledgeROA` for the setup reader, and the redemption
  (spend) hops read through the setup (`SReads.bind`). The setup's reads before the challenge may
  meet the blocks the simulators program later: that is the `H₂³` term of `εAd` in every hop
  (`2·k₂·2⁻¹⁰²⁴` and a second zero-knowledge application). Issuance `1`'s collision term stays
  `noHitProb + 2⁻¹⁰²⁴` (`deltaI1K_le`, `deltaI1RK_le`: issuance `0`'s simulator coins are
  independent of the setup). `anonymityRAK_lean_num`: `4·εAd(9; i₃ + q₃, q₅ + i₅ + 1872,
  q_E + i_E + 13821; k₃, k₂, k₅, k_E) + 4·εAd(9; q₃, q₅ + 1248, q_E + 13821; k₃ + i₃, k₂ + i₂,
  k₅ + i₅ + 624, k_E + i_E + 9214) + 4·((k₃ + i₃)·2⁻¹²⁸ + 2⁻¹¹³ + εROP(0, 312, 4607;
  k₅ + i₅ + 624, k_E + i_E + 9214)) + 6·noHitProb + 12·2⁻¹⁰²⁴ + 2·εhide`, about `2⁻¹⁰¹·⁹` without
  budgets and `2⁻¹⁰¹·⁴` if the key stage reads `H₂³`; `unlinkabilityRAK_lean_num`, the `RA` bound
  with the issuance hops' `εRO` replaced by `εAd(…; k₃, k₂, k₅, k_E)` and `k` added to the spend
  hops' reader budgets, about `2⁻¹⁰¹·⁶` and `2⁻¹⁰¹·¹`; both `_numG` and `_perm`. With `k = 0` each
  is the `RA` bound up to `4·2⁻¹²⁸`.
- PomFRIT blindness with an Issuer whose key, messages and responses read every table but `H₂³`:
  `blindnessRA_lean_num`, `≤ 4·εRO(q₃ + 4i₃, q₅ + 4i₅ + 1872, q_E + 4i_E + 23035) + 2·noHitProb +
  2·2⁻¹²⁸`, about `2⁻¹⁰³·²` plus the budget terms, from the two-phase `zk2_adaptive`: the
  continuation, the Issuer's response to the request computed from step 1's output, reads the
  slice, `H₅` and the cipher at keys depending on that output, and these reads are added to the
  budget of the H1, H4 and H6 hops (`εRO(q₃ + q_k3, q₅ + q_k5, q_E + q_kE)`).
- PomFRIT blindness with an Issuer whose key, messages and responses read every table, **`H₂³`
  included** (joint budget `IBudgetH i₃ i₂ i₅ i_E` over both slices and the shared tables):
  `blindnessRAH_lean_num`, `≤ 4·εRO(q₃ + 6i₃, q₅ + 6i₅ + 1872, q_E + 6i_E + 23035) +
  2·noHitProb + 2·2⁻¹²⁸ + [i₂ > 0]·4·(2⁻¹¹³ + εRO(6i₃, 6i₅ + 2184, 6i_E + 18428) + 2i₂·2⁻¹²⁸)`,
  about `2⁻¹⁰²·³` plus the budget terms. No simulator change: the interaction's `H₂³` reads are
  taken out by lazy sampling of `H₂³` before the hybrids (`pr_resampleC`), `blindnessRA` is
  applied to the Issuer that reads an independent table in place of `H₂³` and whose guess patches
  `H₂³` at the interaction's read set (`AdversaryRA.subst`), and the collision term (a real
  session's grinding block meets the interaction's reads) is a second application of two-phase
  zero knowledge, after which the block's tail is the simulator's uniform 16-byte `ã`
  (`ZK.Sim.pr_tail2A`).
- The same with the collision term **counting prefixes** (`Privacy/PomFRITRAHPfx.lean`): the
  block is all `2³²` keys of one prefix, so the event depends on the read set only through its
  prefixes (`ZK.Sim.pr_tail2A_pfx`: `pr_tail2A` applied to one key per prefix). With the budget
  `IBudgetHB i₃ b₂ i₅ i_E` (the `H₂³` read sets of at most `b₂` prefixes, any number of keys;
  `IBudgetH.toB` gives it with `b₂ = i₂`): `blindnessRAH_lean_num_pfx` (`_numG_pfx`,
  `_num_perm_pfx`), the bound above with `b₂` in place of `i₂` (`pr_bad0H_pfx`, `pr_bad1H_pfx`).
- **With AES as random permutations** (`docs/zk.md` §10.4; `Privacy/PermRA.lean`,
  `ZK/IdealCipherPermP.lean`, `ZK/HopsPatchPerm.lean`, `ZK/TwoPhasePerm.lean`): the adaptive
  layer is stated for every row type with `ZKPRow R` (zero knowledge with the `H₅` and cipher
  tables patched on the reader's keys); with permutation rows the patched table is again a table of
  independent uniform permutations off the patched keys, and the patched GGM hop costs
  `(4607 + q + |PE|)/(2¹²⁸ − (nHi + 1))` (`IC.hopPmP`, `hide_rom_query_permP`, `zk_roP_perm`,
  error `εROPmP`). `anonymityRA_lean_num_perm`, `unlinkabilityRA_lean_num_perm` (the bounds with
  `εROPm`, `εAdPm`, `εROPmP`), `blindnessRAH_lean_num_perm` (the same with `εROPm`) and
  `blindnessRA_lean_num_perm` (`4·εROPm(pP; q₃ + 4i₃,
  q₅ + 4i₅ + 1872, q_E + 4i_E + 23035) + 2·noHitProb + 2·2⁻¹²⁸`, from `zk2_adaptive_perm`); each is
  the function-row bound to within the switching terms (`switchEps ≤ 2⁻¹¹³·²` per error term).
- **Interactions as oracle computations** (`ROM/TableReads.lean`, `ROM/PrivacyReads.lean`): an
  interaction written as a VCVio `OracleComp` over the tables (`TSpec`), run on them (`runT`), is
  a consistent table reader with its query budget (`QBudget`, VCVio's `IsQueryBoundP`):
  `sReads_runT`. So `IBudget` is derived (`AdversaryOC.iBudget`), and `anonymityOC_lean_num`,
  `unlinkabilityOC_lean_num`, `blindnessOC_lean_num`, `blindnessOCH_lean_num` (with `H₂³`
  queries; `sReadsP_runT`) (and `_perm`) state the `*RA` bounds with
  no consistency hypothesis on the interaction (the guess keeps its semantic read budget
  `GBudget`); `zk_adaptive_oc`, `lean_zeroKnowledgeROA_oc` for one proof.

*One shared `H₃` instead of per-proof slices* (`docs/zk.md` §10.5; `ZK/SharedH3.lean`,
`ZK/SharedH3Two.lean`, `ZK/SharedH3RA.lean`, `ZK/SharedH3One.lean`, `Privacy/SharedH3RO.lean`,
`Privacy/SharedH3PomFRIT.lean`, `Privacy/SharedH3RA.lean`, `Privacy/SharedH3PomFRITRA.lean`,
`Privacy/SharedH3PomFRITRAH.lean`, `ZK/SharedH3Tail.lean`,
`ROM/SharedH3Reads.lean`). The games above give each proof its own independent `H₃` slice; the
scheme has one `H₃(wPrefix ‖ μ₁ ‖ ρ ‖ 3)`.
- `H₃` on the seed inputs becomes part of the shared tables (a column per row `ρ`, `RowH R`), and
  each proof reads the column at its prefix `wPrefix ‖ μ₁` (`prove_recOne`: this is the executable
  prover with one `H₃` table). Zero knowledge moves to it by re-sampling the proof's column
  (`ZeroKnowledgeRO.shared`, `zk2_shared`; with the statement chosen from the tables,
  `ZeroKnowledgeROA.shared`, the column exchanged off the reader's rows, `+ s_E·2⁻¹²⁸`), with no
  hypothesis on the prefixes. The adversary's `H₃` reads count with its cipher queries.
- The games: `anonymitySh_num`, `unlinkabilitySh_num` (`8·εRO(q_E + 13824, q₅ + 1872, q_E + 13824)
  + 4·(2⁻¹¹³ + εRO(0, 312, 4607)) + 6·noHitProb + 12·2⁻¹⁰²⁴ + 2·εhide`), `blindnessSh_num`
  (`4·εRO(q_E + 18428, q₅ + 1248, q_E + 18428) + 2·noHitProb + 2·2⁻¹²⁸`), the table-reading
  `anonymityRASh_num`, `unlinkabilityRASh_num`, `blindnessRASh_num` (an interaction that reads a
  later proof's prefix costs `(its rows)·2⁻¹²⁸` per adaptive hop), the oracle-computation
  `*OCSh_num`, all with `_perm`. No prefix-collision (`ε_iv`-type) term.
- PomFRIT with an Issuer that also reads `H₂³` (`Privacy/SharedH3PomFRITRAH.lean`,
  `ZK/SharedH3Tail.lean`): `blindnessRAHSh_num`, `≤ 4·εRO(q_E + 6i_E + 23035, q₅ + 6i₅ + 1872,
  q_E + 6i_E + 23035) + 2·noHitProb + 2·2⁻¹²⁸ + [i₂ > 0]·4·(2⁻¹¹³ + εRO(6i_E + 13824, 6i₅ + 2184,
  6i_E + 18431) + 2i₂·2⁻¹²⁸)`, about `2⁻¹⁰²·³` with `i₂ ≥ 1` and no other budget (as
  `blindnessRAH_lean_num`); the lazy sampling of `H₂³` runs on the coins with the sessions' slices
  their columns (`pr_G0RASh_resample`), and the collision term's second application of two-phase
  zero knowledge re-samples the session's column (`pr_tail2Sh`). For oracle computations
  `blindnessOCHSh_num`; both with `_perm`.
- The paper's `≤ 2⁻¹⁹²` (`2⁻³⁶⁰`) bounds the prefix collision correctly, but it is not what sharing
  `H₃` costs, and its "independent slices" step is not a black-box reduction (§10.5).

*The real Clients' seeds* (`docs/zk.md` §10.6; `Privacy/SeedXOF.lean`, `Privacy/SeedXOFGames.lean`,
`Privacy/SeedXOFNC.lean`, `ROM/SeedXOFReads.lean`). The games above draw the seed XOF's outputs
uniformly. With the real
Clients (uniform 32-byte seeds, the XOF a uniform table: PomFRIT a column per seed over the
contexts `dig(pk) ‖ msg`, Moussaka and Ratatouille keyed by `(DST, seed)`; the adversary at table
`g` an adversary `A g` of the existing game whose run reads at most `q_X` cells, for PomFRIT
counting the cells its key and messages read), `abs_pr_seed_le` and `abs_pr_seedGame_sub_le` lift
every random-oracle game: the 52 `*_seed` theorems (`blindness*_seed`, `anonymity*_seed`,
`unlinkability*_seed` for the RO, RA, Sh, RASh, OC and OCSh games, PomFRIT also RAH, OCH, RAHSh and
OCHSh, Moussaka also the non-colluding NCRO and NCSh games (`Privacy/SeedXOFNC.lean`), each with
`_perm`) add `2·(2q_X + 1)·2⁻²⁵⁶` (PomFRIT) or `2·(2q_X + 2)·2⁻²⁵⁶` (Moussaka, Ratatouille).
No zero-knowledge theorem assumes the hop: the prover takes `ρ` as an input.
Lemma DS (c), the independence of PomFRIT's seed XOF from the proof-system domains it overlaps
(F-DS2), is mechanized on one SHAKE oracle read by every party (`Privacy/SeedXOFDS.lean`): with the
seed-XOF inputs `seedDst ‖ seed ‖ tail` a part of the oracle's input space (`pomfritLayout`), the
honest Clients' XOF answers can be taken independent of the oracle at `≤ (n·q + n²)·2⁻²⁵⁶`
(`seedXofDS_le`; `(2q + 1)·2⁻²⁵⁶` for two Clients, `seedXofDS_two_le`), `q` counting every
evaluation at a seed-XOF-shaped string, the proof system's included; its composition with the
games' separate tables is on paper.

*Moussaka against a Moderator that sees no issuance* (Thm 4(b), corrected; `Privacy/MoussakaNC.lean`,
`docs/security/moussaka.md` §6). Only the two redemption proofs are simulated; nothing is assumed
of the issuance proofs or of `Com`. `anonymityNC`: `≤ 4εR + 2·(φ₀ + φ₁)`, `φ_c` the probability
that Anchor `c`'s `derive_preimage` fails on a uniform Client's commitment. For `main`'s Client,
which finds its index itself (`find_issuer`, since `21be618`; `Privacy/MoussakaNCFind.lean`), the
Anchor Sets must contain both issuers' keys (`Contains`); otherwise the refusal reveals whether a
foreign key verifies the Client's hidden preimage. For the index-taking Client of the API before
`21be618` (`Privacy/MoussakaNC.lean`, `Spec.Moussaka.redeemRequestAt`), the index must come from
the Anchor Set by a sound rule (`IdxSound`: the index holds a key with the issuer's public map, or
is out of range; e.g. the first key with that map, `Audit/Nonvacuous.lean`; a lookup by digest
qualifies only if digests bind keys, which the model does not assume);
`anonymityNC_vinegarRO`: `≤ 4εR + 2·(δ₀²⁵⁶ + δ₁²⁵⁶)` on average over a random-oracle vinegar
hash, for signers that fail only when all 256 vinegars are bad (`hfail`); the signer is abstract
here (`Signer`, `Correct` its only hypothesis, which the always-failing signer, `φ = 1`, also
meets; pqov's signer and completeness are the last item below); `unlinkabilityNC`: `≤ 4εR` for
one Anchor and any Anchor Sets or index rule;
with the Lean redemption prover `anonymityNC_label_rows`, `_shake`, `unlinkabilityNC_label_rows`
(per-proof zero knowledge, down to the tape or hop hypotheses).
- **In the random-oracle and ideal-cipher model** (`Privacy/MoussakaNCRO.lean`,
  `ZK/VerifyReadsRO.lean`, `docs/zk.md` §10.7): the issuance proofs, the honest Anchors' Lean
  **verifier** of them and the redemption proofs all run on the shared tables, which the guess
  sees. The executable verifier reads `H₅` at `≤ 312` keys and the cipher at `≤ 4607`
  (`verRO_rd5`, `verRO_rdE`; `H₂³` at one point, no `H₃`), so each redemption hop's reduction runs
  both issuances and verifications itself (`+ 2496` `H₅`, `+ 23035` cipher reads); running them on
  the tables after the redemptions' programming needs no collision term for them, and the right
  hop's (`deltaNC`) is `≤ noHitProb + 2⁻¹⁰²⁴`. `anonymityNCRO_lean_num`: `≤ 4·εRO(q₃, q₅ + 2496,
  q_E + 23035) + 2·(noHitProb + 2⁻¹⁰²⁴) + 2·(φ₀ + φ₁) + 4·q₃·2⁻¹²⁸` (about `2⁻¹⁰³·²` plus the
  budget terms and the abort term; `4·q₃·2⁻¹²⁸` for the issuance slices the guess sees),
  `unlinkabilityNCRO_lean_num` the same without the abort term, both with `_perm`, and
  `anonymityNCRO_vinegarRO`.
- **With one shared `H₃`** (`Privacy/MoussakaNCSh.lean`, `docs/zk.md` §10.7): `anonymityNCSh_num`,
  `≤ 4·εRO(q_E + 23038, q₅ + 2496, q_E + 23038) + 2·(noHitProb + 2⁻¹⁰²⁴) + 2·(φ₀ + φ₁)` (about
  `2⁻¹⁰³·²` plus the budget terms and the abort term), `unlinkabilityNCSh_num` without the abort
  term, both with `_perm`, and `anonymityNCSh_vinegarRO`. The `4·q₃·2⁻¹²⁸` slice term is gone:
  the issuance proofs read the shared tables, which the final swap does not exchange, so the slot
  slices are read by the guess alone and replacing them by independent ones is exact
  (`sim_fresh_NC_free`); the guess's `H₃` reads are row reads, paid in `q_E`.
- **With the real Clients' seeds** (`Privacy/SeedXOFNC.lean`): `anonymityNCRO_lean_num_seed`,
  `unlinkabilityNCRO_lean_num_seed`, `anonymityNCSh_num_seed`, `unlinkabilityNCSh_num_seed` (and
  `_perm_seed`) add `2·(2q_X + 2)·2⁻²⁵⁶`, given a bound `φ₀ + φ₁ ≤ φ` on the abort term at
  every XOF table (the hypothesis `hφ`; immediate when the Moderator and the Anchors' signers do
  not depend on the table).
- **With the Moderator's choices read off the tables** (`Privacy/MoussakaNCRA.lean`,
  `ROM/PrivacyReadsNC.lean`, `docs/zk.md` §10.7): a setup reads the four slices and the shared
  tables within `(k₃, k₂, k₅, k_E)` (`KBudget`, consistent; as a VCVio oracle computation,
  `QBudget`) and fixes the contexts, keys, Anchor Sets, digests and the Anchors' signers. The
  redemption hops become adaptive (`hop_roA`); the right hop's collision term stays
  `≤ noHitProb + 2⁻¹⁰²⁴`; the abort term is bounded uniformly in the setup's state.
  `anonymityNCRA_lean_num`: `≤ 4·εAd(9; q₃, q₅ + 2496, q_E + 23035; k₃, k₂, k₅, k_E) +
  2·(noHitProb + 2⁻¹⁰²⁴) + 2·(φ₀ + φ₁) + 4·(k₃ + q₃)·2⁻¹²⁸`; `unlinkabilityNCRA_lean_num` without
  the abort term; `_perm`, `anonymityNCOC_lean_num`, and `*_seed`. Not for the shared-`H₃` game.
- **pqov's signer, and completeness** (`Spec/PqovSigner.lean`, `Spec/PqovKey.lean`,
  `Spec/PqovSignerExec.lean`, `Privacy/MoussakaPqov.lean`, `Privacy/PqovDelta.lean`,
  `Privacy/PqovKeys.lean`; `Arith/GF256Field.lean` makes `GF256` a field). `Spec.Pqov.signer`
  models pqov's `ov_preimage_core`: each attempt's system `L_v x = t − P(x₀)` computed from the
  public map's polar form (pqov's `vᵀS`, `t + P₁(v)`), the solution `x₀ + Σ_j x_j ō_j`. It is
  correct for every key whose map vanishes on the oil space (`signer_correct`, `OilSpace`) and
  fails only if every attempt's `L_v` is singular (`signer_fail`). Against pqov's key layout
  (`Spec/PqovKey.lean`, the expanded key's `P1`, `P2`, `P3` blocks): for every key the system
  the model builds from the polar form is pqov's stored `S = (P1 + P1ᵀ)·O + P2`
  (`sysCoef_eq_pqovS`; `ov_calc_l1_mat`) and `P(v, 0) = P₁(v)` (`qmap_vinVec_eq`), and `P`
  vanishes on the oil space of `O` iff `P3 = UT(M + Mᵀ)`, `M = Oᵀ(P1·O + P2)`, which is pqov's
  `calculate_F2_P3` (`oilSpace_iff_P3Pqov`); so the signer is correct for pqov's keys `pqovKey O
  P1 P2` with any `O`, `P1`, `P2` (`oilSpace_pqovKey`). Against the C++: `lake exe spec_kats` runs
  the model (`Spec/PqovSignerExec.lean`: the inverse replaced by an elimination whose solution is
  checked on the model's system, `attemptExec_sound`) with pqov's vinegars on the test key and
  reproduces the C++ `derive_preimage` on the six Moussaka and PomFRIT KAT targets byte for byte.
  pqov uses only 255 of its 256
  vinegars (`ov.c:166` discards a success at `ctr = 255`), so `hfail` holds as stated for the
  256-attempt variant (`pqovRO256_hfail`; `anonymityNC_vinegarRO` applies), and
  `anonymityNC_pqov`, `anonymityNCRO_pqov`, `anonymityNCSh_pqov` give the abort term
  `2·(δ₀²⁵⁵ + δ₁²⁵⁵)` for pqov (`pr_fail_vinegar_lt`), `δ` the fraction of vinegars with singular
  `L_v` (`delta`). For a fixed key `δ` is not the fraction `σ ≤ 1/255` of singular `45 × 45`
  matrices: `L_v = Σ_i v_i S_i` ranges over a space of dimension `≤ 74` (the zero key has
  `δ = 1`, `delta_zero_key`). On average over uniform coefficients `S` it is:
  `E[δ] ≤ 1/255 + 256⁻⁷⁴` (`pr_singular_avg`, `σ` from `|GL₄₅(𝔽₂₅₆)|`), and
  `E[δ^m] ≤ 255⁻ᵐ + 256^m/(255·256⁷⁴)` for `m ≤ 74` (linearly independent vinegars give
  independent uniform systems, `pr_singular_all`, `pr_dependent_le`). For keys of pqov's key
  generation with any oil matrix `O` and `P1` part and uniform `P2` (`pqovKey O P1 P2`; `S` a
  translate of `P2`, `sysCoef_pqovKey`), `E[δ²⁵⁵] ≤ 255⁻³⁷ + 1/(255·256³⁷)`
  (`avg_delta255_pqovKey`), so averaged over the Anchors' `P2` parts
  `anonymityNC_pqov_pqovKeys`, `anonymityNCRO_pqov_pqovKeys` have abort term
  `≤ 4·(255⁻³⁷ + 1/(255·256³⁷)) ≈ 2⁻²⁹³·⁸`, each Anchor signing with its own `O` (`O = 0`, the
  family `keyO0 = pqovKey 0`, `pqovKey_zero`: `avg_delta255_keyO0`, `anonymityNC_pqov_keys`,
  `anonymityNCRO_pqov_keys`). Assumed: `P2` uniform given `(O, P1)` (AES-128-CTR of `pk_seed`
  as a random function, SHAKE256 a random oracle); a fixed key's `δ` is not bounded. Completeness: `Spec.Moussaka.issueResponse` checks `main`'s
  request length `45 + 7272`, while the games' Lean prover emits label-row proofs of `7528`
  bytes, so with it every honest request was rejected as malformed and the random-oracle games
  refused always (their bounds held vacuously; `issueResponse_leanPI_malformed`). The games now
  use the label-row Anchor (`Spec.Moussaka.issueResponseLR`, `45 + 7528`). The Lean issuance
  proofs then pass `leanVI` on the shared tables except with probability `≤ 2⁻¹¹³`
  (`leanI_complete`, `accNC_lean_complete`, `accNC_leanSh_complete`), and the games refuse the
  redemptions with probability `≤ φ₀ + φ₁ + 2·2⁻¹¹³` when both keys are found in both sets
  (`pr_refused_NCRO_le`, `pr_refused_NCSh_le`; with pqov's signers `pr_refused_NCRO_pqov`,
  `≤ δ₀²⁵⁵ + δ₁²⁵⁵ + 2·2⁻¹¹³`).

*Many sessions* (`docs/zk.md` §10.8; `ZK/ReadsMany.lean`, `Privacy/PomFRITMany.lean`,
`Privacy/MoussakaMany.lean`, `Privacy/RatatouilleMany.lean`, `Privacy/PomFRITAdaptive.lean`,
`Privacy/PomFRITAdaptivePfx.lean`, `Privacy/MoussakaAdaptive.lean`, `Privacy/RatatouilleAdaptive.lean`,
`ZK/ReadsPoint.lean`, `Privacy/PomFRITLin.lean`, `ZK/ReadsInterleave.lean`, `Privacy/PomFRITInterleave.lean`,
`Privacy/MoussakaInterleave.lean`, `Privacy/RatatouilleInterleave.lean`, `ZK/ReadsInterleaveOC.lean`,
`Privacy/PomFRITInterleaveOC.lean`, `Privacy/MoussakaInterleaveOC.lean`,
`Privacy/RatatouilleInterleaveOC.lean`). The
games above have the challenge sessions only. Here the adversary also serves `m` further honest
sessions on the same tables (each with its own randomness and `H₃` slices), concurrently with the
challenge (below also adaptively, and with `N` challenge pairs): their first
messages are seen by the adversary's interaction before it answers anyone, their later messages
by the stages after them (Ratatouille's stage 2 sees the further Clients' spends) or by the guess.
- **The proof is a reduction, not a new hybrid**: for each fixed tape `c` of the further sessions
  the game is, tape by tape, the two-session game with a table-reading interaction (`*RA`) for the
  adversary that runs the further sessions itself; the `*RA` theorems apply and averaging over `c`
  finishes. The budget of that adversary is the further sessions' reads, so the further sessions
  must be **consistent** table readers: step 1 of the two-phase prover (`step1_cons`) and the whole
  single-phase prover, `H₂³` at the `2³²` grinding points of its prefix included
  (`realRO_sreads`), are proved to be (`ZK/ReadsMany.lean`, with `SReads.pi`, `Rd5.pi`, `RdE.pi`
  for families of readers). No new collision term: the further sessions are part of the
  distinguisher in every hop.
- PomFRIT (`realGameN`: one challenge pair, `m` further sessions with Issuer-chosen keys and
  messages, every response after every request): `blindnessN_lean_num` `≤ 4·εRO(q₃, q₅ + 5m·624 +
  1872, q_E + 5m·4607 + 23035) + 2·noHitProb + 2·2⁻¹²⁸`, numerically `≤ n·2⁻¹⁰³ +
  4·(q₃ + q₅ + 221·q_E)·2⁻¹²⁸` with `n = m + 2` (`blindnessN_lean_le`): `2⁻⁸³` for `n ≤ 2²⁰`,
  `2⁻⁷¹` for `n ≤ 2³²` (`blindnessN_lean_2pow20`, `_2pow32`).
- PomFRIT with **`N` challenge pairs** (`realGameP`, worlds `Fin N → Bool`, the left-or-right game
  with `N` queries): a hybrid over the pairs (`abs_sub_le_mul_of_steps`), each step the one-pair
  game with the other `2(N − 1)` sessions as further sessions: `blindnessP_lean_num` `≤ N·εPair`,
  numerically `≤ N·(2N·2⁻¹⁰³ + 4·(q₃ + q₅ + 221·q_E)·2⁻¹²⁸)` (`blindnessP_lean_le`): `2⁻⁶⁴` for
  `2N ≤ 2²⁰` sessions, `2⁻⁴⁰` for `2N ≤ 2³²`. Quadratic: each hop pays the other sessions' cipher
  reads in its H4 hop.
- Moussaka (`realGameN`: `m` further Clients issued with the challenge pair and redeeming at
  Anchor Sets the adversary chooses after every issuance request): `anonymityN_lean_num`
  (`anonymityRA_lean_num` at `i₂ = 2³²m`, `i₅ = 624m`, `i_E = 4607m`), numerically `≤ n·2⁻¹⁰² +
  8·(q₃ + q₅ + 221·q_E)·2⁻¹²⁸ + 2·εhide` (`anonymityN_lean_le`): `2⁻⁸²` at `2²⁰`, `2⁻⁷⁰` at `2³²`.
- Ratatouille (`realGameN`: `m` further Clients issued with the challenge pair, each spending once
  with round 1, their spend requests seen by stage 2): `unlinkabilityN_lean_num`, numerically
  `≤ n·2⁻¹⁰¹ + 8·(q₃ + q₅ + 221·q_E)·2⁻¹²⁸ + 2·εhide` (`unlinkabilityN_lean_le`): `2⁻⁸¹` at
  `2²⁰`, `2⁻⁶⁹` at `2³²`.
- Moussaka and Ratatouille with **`N` challenge pairs** (`realGameP`; worlds `Fin N → Bool`, resp.
  `Fin N → Bool × Bool`; the adversary's stages see every pair, and Ratatouille's stage 2 sees a
  pair's round-1 request only if §6's rule runs round 1): the same hybrid (`abs_sub_le_mul_of_worlds`).
  Moussaka's steps are `anonymityN_lean_numG` with the other pairs' Clients as further Clients, the hop's
  guess rebuilding their outcomes with §6's rule on the commitments (`outAt_eq`):
  `anonymityP_lean_num`, numerically `≤ N·(2N·2⁻¹⁰² + 8·(q₃ + q₅ + 221·q_E)·2⁻¹²⁸ + 2·εhide)`
  (`anonymityP_lean_le`). Ratatouille's other pairs have two rounds, so each step is a direct
  reduction to the two-session table-reading game whose Issuer runs the other pairs and masks pair
  `k`'s round-1 request by §6's rule recomputed from its own view (`ok1Of_eq_pub`):
  `unlinkabilityP_lean_num`, numerically `≤ N·(N·2⁻¹⁰¹ + 8·(q₃ + q₅ + 221·q_E)·2⁻¹²⁸ + 2·εhide)`
  (`unlinkabilityP_lean_le`). Both `2⁻⁶³` for `2N ≤ 2²⁰` Clients, `2⁻³⁹` for `2N ≤ 2³²`
  (`_2pow20`, `_2pow32`), plus `N` times the budget and hiding terms.
- **Moussaka and Ratatouille linear in `N`, up to one bad event** (`Privacy/Split.lean`,
  `ZK/ReadsPointRO.lean`, `Privacy/MoussakaLin.lean`, `Privacy/RatatouilleLin.lean`; `docs/zk.md`
  §10.8): `pr_split_le` moves the other pairs to private tables even though their read sets depend
  on the challenge pair's outputs, at the price of the event that the two groups' read sets meet,
  measured in the split world (the single-phase prover reads only points, `rdRO_cons`).
  `anonymityP_lin`, `unlinkabilityP_lin`: `≤ N·(2·2⁻¹⁰² + 2β + …)` if every step's bad event is
  `≤ β`. With `H₄` SHAKE, as in these games, `β` is not known to be small beyond `≈ 4607²·2⁻¹²⁸`
  per pair of proofs; with `H₄` a random oracle, `β ≲ 64(N − 1)·2⁻¹²⁸` on paper, giving
  `≲ n·2⁻¹⁰² + 33n²·2⁻¹²⁸` for `n = 2N` Clients (`2⁻⁸¹·⁴` at `2²⁰`, `2⁻⁵⁹` at `2³²`).
- **Linear or quadratic?** The quadratic term is not inherent (`docs/zk.md` §10.8, "Is the
  quadratic term inherent?"). The H4 hop charges every read of a hidden node's cipher row, at any
  input, and every other session's `4607` reads are such reads with probability `221·2⁻¹²⁸` each,
  so no key-level argument is linear (one joint bad event "some read hits some hidden key" has
  probability `≈ n²·2⁻¹⁰⁸` and really occurs). But the hidden values are the cipher at CTR inputs
  that contain the proof's fresh `iv = H₄(iv_pre ‖ µ)`, so honest sessions interfere only through a
  key **and** an `iv` collision, and the paper argument is linear. (A shared `iv` would make the
  `n²` loss real.)
- **PomFRIT with `H₄` a table: no per-session charge** (`ZK/ReadsPoint.lean`,
  `Privacy/PomFRITLin.lean`; `docs/zk.md` §10.8, "With `H₄` a table"). With `H₄` a uniform table
  of the game (`hb4`; the Issuer may read all of it) and function rows, step 1 reads the cipher
  only at its tree's nodes on the CTR blocks of its own `iv` (`step1_consP`), so by lazy sampling
  (`red_close_redP`) the other sessions move to private tables, and each step is the two-session
  game of a reduction whose interaction reads no table (`AdversaryN.redP`), up to the event that
  a challenge session reads a point the others read: `≤ 4·2⁻¹²⁸` per pair of sessions
  (`pr_Bp_le`: equal `iv_pre`s, an `H₄` collision, equal root seeds, or a node collision with
  equal `iv` lanes). One pair with `m` further sessions: `≤ εPair0 + 16·m·2⁻¹²⁸`
  (`blindnessNH_lean`; numerically `2⁻¹⁰²` at `m ≤ 2²⁰`, `2⁻⁹¹` at `m ≤ 2³²`, plus budget terms,
  `blindnessNH_lean_le`, `_2pow20`, `_2pow32`); `N` pairs: `≤ N·(εPair0 + 32(N − 1)·2⁻¹²⁸)`
  (`blindnessPH_lean`), numerically `≤ N·2⁻¹⁰³ + 32·N²·2⁻¹²⁸ + N·4·(q₃ + q₅ + 221·q_E)·2⁻¹²⁸`
  (`blindnessPH_lean_le`): `2⁻⁸³` for `2N ≤ 2²⁰` sessions, `2⁻⁶⁰` for `2N ≤ 2³²` (`_2pow20`,
  `_2pow32`), against `2⁻⁶⁴` and `2⁻⁴⁰` key-level; `εPair0 = 4·εRO(q₃, q₅ + 1872, q_E + 23035) +
  2·noHitProb + 2·2⁻¹²⁸ ≤ 2⁻¹⁰³ + …` is the two-session bound. Still quadratic: the birthday bound
  of the 128-bit `iv`s and seeds (`n²·2⁻¹²⁵`, from counting equal `iv`s as an `H₅` collision);
  the budget terms are charged once per pair. Moussaka and Ratatouille are not covered: their
  further Clients' redemption statements are chosen after the challenge requests, so their reads
  are not a reader of the private tables alone (§10.8, "Open").
- PomFRIT with an **adaptive schedule** (`Privacy/PomFRITAdaptive.lean`; `realGameAd`): further
  sessions before the challenge, between the challenge requests and responses, and after the
  challenge outcome, one after the other, each one's key, message and response chosen from all
  earlier requests and outcomes. The reduction runs them inside its interaction, which then reads
  `H₂³` (the `RAH` route): **step 2 of the two-phase prover is a consistent reader** (`fullX_sreads`:
  a whole session reads `H₂³` only at its prefix's `2³²` grinding points, and only if the response
  passes the Client's checks; `sigR_h23`, `preX_cons`, `sigR_tables`), sequential sessions compose
  (`runSeq_sreads`), and `blindnessRAH_lean_numG` applies: `blindnessAd_lean_num`, numerically
  `≤ n·2⁻⁹² + 4·(q₃ + q₅ + 221·q_E)·2⁻¹²⁸` for `n` sessions in all (`blindnessAd_lean_le`):
  `2⁻⁷²` at `2²⁰`, `2⁻⁶⁰` at `2³²`. There the per-session `≈ 2⁻⁹³` is the `RAH` collision term
  charging each of a session's `2³²` grinding keys separately. **Counting prefixes**
  (`Privacy/PomFRITAdaptivePfx.lean`): a whole session's `H₂³` reads have one prefix
  (`fullX_sreadsB`, `runSeq_sreadsB`, `red_iBudgetHB`: `IBudgetHB 0 (m₁ + m₂) …`), and
  `blindnessRAH_lean_numG_pfx` gives `blindnessAd_lean_num_pfx`, numerically
  `≤ n·2⁻¹⁰² + 4·(q₃ + q₅ + 221·q_E)·2⁻¹²⁸` (`blindnessAd_lean_le_pfx`; per session
  `≈ 2⁻¹⁰²·³`, the session's `H₅` and cipher reads in the main and the collision term):
  `2⁻⁸²` at `2²⁰`, `2⁻⁷⁰` at `2³²` (`blindnessAd_lean_2pow20_pfx`, `_2pow32_pfx`), within a
  factor 2 of the non-adaptive schedule.
- Moussaka and Ratatouille with an **adaptive schedule** (`Privacy/MoussakaAdaptive.lean`,
  `Privacy/RatatouilleAdaptive.lean`; `realGameAdM`, `realGameAdR`): further sessions one after
  the other before the challenge, between the challenge issuance requests and the adversary's
  answers, (Ratatouille) between round 1's request and stage 2 (only if round 1 runs), and after
  the challenge outcome; each one's contexts and key (Ratatouille: key, context and balance), the
  adversary's response and the Client's Anchor Set and digest (Ratatouille: spend amount) chosen
  from all earlier requests and outcomes, and the challenge contexts and keys (balance) from the
  sessions before the challenge. A whole further session (the issuance request, `finalize_issue`,
  the redemption or spend) is a consistent table reader (`redX_sreads`, `fullXM_sreads`,
  `fullXR_sreads`) and sequential sessions compose (`runSeqM_sreads`, `runSeqR_sreads`); for each
  tape of the further sessions the game is the key-stage game of the reduction whose key stage
  runs the sessions before the challenge, whose interaction runs those in between and whose guess
  runs those after (`realGameAdM_iff`, `realGameAdR_iff`), with budgets `KBudget (0, 2·2³²m₁,
  1248m₁, 9214m₁)` and `IBudget (0, 2·2³²m, 1248m, 9214m)` (`red_kBudget`, `red_iBudget`,
  `red_gBudget`). `anonymityAd_lean_num`, numerically `≤ n·2⁻¹⁰² + 8·(q₃ + q₅ + 221·q_E)·2⁻¹²⁸ +
  2·εhide` (`anonymityAd_lean_le`; `2⁻⁸²` at `2²⁰`, `2⁻⁷⁰` at `2³²`, `_2pow20`, `_2pow32`), and
  `unlinkabilityAd_lean_num`, `≤ n·2⁻¹⁰¹ + …` (`unlinkabilityAd_lean_le`; `2⁻⁸¹`, `2⁻⁶⁹`), for
  `n` Clients in all: the non-adaptive numbers. The `H₂³` reads are counted by keys at
  `2·2⁻¹⁰²⁴` each (the `128`-byte `ã`), so no prefix count is needed (per session `≈ 2⁻¹⁰²·⁵`
  and `≈ 2⁻¹⁰¹·⁸`).
- **Interleaved schedules** (`ZK/ReadsInterleave.lean`, `Privacy/PomFRITInterleave.lean`,
  `Privacy/MoussakaInterleave.lean`, `Privacy/RatatouilleInterleave.lean`; `AdversaryIL`,
  `AdversaryILM`, `AdversaryILR`, `realGameIL`, `realGameILM`, `realGameILR`): the adversary is an
  interactive machine, a step function from the transcript to the next action (`Act`: start a new
  honest session with inputs of its choice, or deliver a message to any pending session), run for
  a number of steps before, between and after the challenge's messages, seeing every result; it
  may start many sessions and answer them in any order. A session's state is its tape (the `j`-th
  started uses tape `j`, at most `n`) and the messages it received. **The interleaving lemma**
  (`Good.run`, `Good.sreads`): if each session's output after the messages `h` is read off a read
  set that grows with `h` (`SessReads`), every stretch of the schedule, whatever the scheduler and
  the fuel, is a consistent reader whose read set is the union of the sessions' current read sets,
  so `n` times one session's budget. A session given as a chain of consistent readers (issuance,
  then redemption or spends, each at the state the earlier steps left) is one (`ChainCons`,
  `ChainCons.sessReads`, `chain_card`). The reductions are those of the adaptive games, with the
  schedule in place of the sequential sessions (`realGameIL_iff`, `realGameILM_iff`: `Iff.rfl`).
  PomFRIT: `IBudgetHB (0, n, 624n, 4607n)` (a session's read set is step 1's keys, then
  `fullKeys`, one prefix), `blindnessIL_lean_num`, numerically `≤ (n + 2)·2⁻¹⁰² + 4·(q₃ + q₅ +
  221·q_E)·2⁻¹²⁸` for `n` further sessions (`blindnessIL_lean_le`; `2⁻⁸²` at `n + 2 ≤ 2²⁰`,
  `2⁻⁷⁰` at `2³²`, `_2pow20`, `_2pow32`), the sequential numbers. Moussaka: key stage and
  interaction both `(0, 2·2³²n, 1248n, 9214n)` (a Client started before the challenge and
  answered after it is read by both), `anonymityIL_lean_num`, `≤ (n + 2)·2⁻¹⁰¹ + 8·(q₃ + q₅ +
  221·q_E)·2⁻¹²⁸ + 2·εhide` (`anonymityIL_lean_le`; `2⁻⁸¹`, `2⁻⁶⁹`; per Client `≈ 2⁻¹⁰¹·¹³`).
  Ratatouille with **Clients that spend up to `K` times**, each spend's change token, finalized on
  the Issuer's response, spent by the next (`tokOf`, `finSX`): budgets `n(K + 1)·(0, 2³², 624,
  4607)`, `unlinkabilityIL_lean_num`, `≤ (n(K + 1) + 2)·2⁻¹⁰¹ + 8·(q₃ + q₅ + 221·q_E)·2⁻¹²⁸ +
  2·εhide` (`unlinkabilityIL_lean_le`; `2⁻⁸¹` at `n(K + 1) + 2 ≤ 2²⁰`, `2⁻⁶⁹` at `2³²`; per proof
  `≈ 2⁻¹⁰¹·⁷⁷`).
- **Interleaved schedules with a table-reading scheduler and a free challenge**
  (`ZK/ReadsInterleaveOC.lean`, `Privacy/PomFRITInterleaveOC.lean`,
  `Privacy/MoussakaInterleaveOC.lean`, `Privacy/RatatouilleInterleaveOC.lean`; `AdversaryILO`,
  `AdversaryILMO`, `AdversaryILRO`, `realGameILO`, `realGameILMO`, `realGameILRO`): each step of the
  scheduler is a VCVio oracle computation over the challenge `H₃` slices and the shared tables,
  within a per-step query bound (`SBudget a₃ a₂ a₅ a_E`, `IsQueryBoundP`), and the challenge starts,
  and its answers (Ratatouille: each stage's) are taken, at the first steps at which the
  scheduler's `go`, `done` hold. **The interleaving lemma with a table-reading scheduler**
  (`GoodO.run`, `GoodO.sreads`): every stretch, stopping early or not, is a consistent reader whose
  read set is the union of the sessions' read sets and the scheduler's per-step query logs,
  consistency by construction (`runT_congr`), `L` steps costing `L·a` (`countP_logO_qb`). The
  earlier adversaries are the special case (`realGameILO_toO`, `realGameILMO_toO`,
  `realGameILRO_toO`). The challenge requests are still revealed together and the answers take
  effect together; neither restricts the adversary (a request revealed earlier gives more; an
  answer has no visible effect before the outcome, which needs all answers). Bounds:
  `blindnessILO_lean_le` `≤ (n + 2)·2⁻¹⁰² + 4·(q₃ + q₅ + 221·q_E)·2⁻¹²⁸ + 52·L·(a₃ + a₂ + a₅ +
  221·a_E)·2⁻¹²⁸`, `anonymityILO_lean_le` `≤ (n + 2)·2⁻¹⁰¹ + 8·(…)·2⁻¹²⁸ + 28·L·(…)·2⁻¹²⁸ + 2·εhide`,
  `unlinkabilityILO_lean_le` `≤ (n(K + 1) + 2)·2⁻¹⁰¹ + 8·(…)·2⁻¹²⁸ + 46·L·(…)·2⁻¹²⁸ + 2·εhide`
  (`L` the total number of steps; `_2pow20`: `2⁻⁸²`, `2⁻⁸¹`, `2⁻⁸¹`; `_2pow32`: `2⁻⁷⁰`, `2⁻⁶⁹`,
  `2⁻⁶⁹`, plus the budget terms): the interleaved bounds plus the scheduler's reads, each charged as
  an interaction read (e.g. `L·(a₃ + a₂ + a₅ + 221·a_E) = 2⁶⁴` adds `2⁻⁵⁸·³`, `2⁻⁵⁹·²`, `2⁻⁵⁸·⁵`).
- All with AES as random permutations (`*N_lean_num_perm`, `blindnessP_lean_num_perm`,
  `anonymityP_lean_num_perm`, `unlinkabilityP_lean_num_perm`, `blindnessAd_lean_num_perm`,
  `blindnessAd_lean_num_perm_pfx`, `anonymityAd_lean_num_perm`, `unlinkabilityAd_lean_num_perm`,
  `blindnessIL_lean_num_perm`, `anonymityIL_lean_num_perm`, `unlinkabilityIL_lean_num_perm`,
  `blindnessILO_lean_num_perm`, `anonymityILO_lean_num_perm`, `unlinkabilityILO_lean_num_perm`),
  and for
  every row type with `ZKRow` (`*_numG`). Hiding of `Com` is assumed for the explicit reductions
  of every composed adversary, uniformly over the further sessions' tapes, the simulator coins,
  the slices and the tables (a worst-case, non-uniform reduction).

*Audits* (`Audit/Nonvacuous.lean`, `Audit/Liveness.lean`).
- **Non-vacuity**: the headline theorems' adversary and parameter hypotheses are instantiated: the
  trivial prover and one-element instance families for soundness, families with many instances
  satisfying `hinj` for the four relations that need it (with the spec-relation versions), a
  concrete issuance witness for completeness and zero knowledge, budget-0 adversaries for the
  privacy games, a non-degenerate sound index rule for Moussaka 4(b), Anchor Sets with both
  issuers for 4(b) with `main`'s Client (`contains_ncq`), and pqov's signer with keys
  of its key generation (any oil matrices) for Moussaka 4(b), with the averaged abort term
  `≈ 2⁻²⁹³·⁸` and the games reaching redemption. `εhide` bounds the explicit reductions built from
  the adversary at every fixed table, slice, simulator coin and further-session tape (a
  worst-case, non-uniform reduction); `εhide = 1` always satisfies it (and makes the bound
  trivial), and an adversary with a constant guess satisfies it with `εhide = 0`.
- **Liveness**: every privacy game is checked for the other kind of vacuity, an honest path that
  never produces the challenge-dependent outputs (as Moussaka 4(b)'s random-oracle games did
  before commit `919a204`, above). Only those games had it: elsewhere the adversary plays every
  Anchor, Issuer and Moderator, the honest Clients check only its responses, and every
  Lean-prover game uses the label-row layout. With a trapdoor key whose signer never fails
  (`keyI`, `skI`: a key of pqov's key generation with `O = 0`), the games reach their challenge
  outputs on every tape: Moussaka 4(a)'s redemptions happen and reveal `nf_b ‖ π` (`allOk_live`,
  `realGameRO_live`) and are accepted by the label-row Moderator with the Lean verifier except
  with probability `≤ 2⁻¹¹³` (`redeem_accepted_RO`); 4(b)'s abort term is `0` for this signer
  (`phi_skI`, refusal `≤ 2·2⁻¹¹³`); Ratatouille runs both rounds and reveals the challenge
  nullifiers when the provers do not abort (`realGame_liveR`), which the Lean provers do with
  probability `≤ 2⁻¹¹³` per proof (`leanPIR_some`, `leanPSR_some`); PomFRIT finalizes both
  sessions and reveals both signatures (`realGame_liveP`, `realGameRO_liveP`). One latent hazard
  of the same kind: the spec's Moderator (`Spec.Moussaka.finalizeRedeem`) checks `main`'s
  redemption length `24 + 8751`, while the Lean redemption proofs have `9007` bytes
  (`leanPR_length`), so it would reject every label-row redemption (`finalizeRedeem_leanPR_none`);
  no game runs an honest Moderator, and `finalizeRedeemLR` (`Spec/MoussakaLabelRows.lean`) is the
  one to use.

`lake exe zk_sim` checks the tape equation, the simulator and the ideal-tape prover on all 18 KAT
runs of each layout.

**What remains assumed or open** for zero knowledge and privacy with the fix (details:
`docs/zk.md` §10.1 "What remains assumed", §10.3, §10.5 and §10.8 "Open", §10.6 "What remains").
- *Modelling steps.* SHAKE128 is a random oracle (a single oracle with L0's domain rule is proved
  equivalent to independent per-domain oracles, `ROM/DomainSep.lean`); AES-128 is an ideal
  cipher. The PRP/PRF switching term is not a gap: zero knowledge and every privacy game are also
  proved with the cipher's rows uniform permutations read forward and backward (`*_perm`).
- *Hiding of `Com`* (Moussaka 4(a), Ratatouille): an assumption, the hypothesis `εhide` on
  explicit reductions. It is computational and cannot be discharged in the random-oracle model
  (`docs/zk.md` §10.9, `Privacy/ComHide.lean`). `Com` is one Keccak-p[800,12] call, not SHAKE,
  and the proved relations evaluate it, so it is not a table of the games. Brute force over the
  128-bit opening wins the hiding experiment against the games' unbounded reductions: advantage
  `1 − p` for Moussaka (`ComHide.Moussaka.hidingAdv_bruteForce`), `≥ 1 − 2⁻¹²⁸` for Ratatouille
  (`ComHide.Ratatouille.hidingAdv_bruteForce_ge`). This is a `2¹²⁸`-work linking attack.
  Heuristically, with `Com` a random function in the standalone experiment, `εhide ≤ (4q + 2)·2⁻¹²⁸`
  (Moussaka, `hidingAdvRO_num`) and `≤ (4q + 16)·2⁻¹²⁸` (Ratatouille, `hidingAdvColRO_num`) for `q`
  reads of the `Com` table. These are not corollaries of the privacy theorems, whose reductions
  read no such table.
- *Lemma DS (c)*: mechanized on the single SHAKE oracle (`seedXofDS_le`); routing an adversary's
  query at a seed-XOF input that is also a proof-system input to that domain's table, i.e. the
  composition with the games' independent tables, is on paper. (For Moussaka and Ratatouille the seed domains are disjoint from
  every other, part (a), checked in Lean by `clean_pairwise`.)
- *Table-reading interactions given as functions of the tables* must be consistent readers
  (`SReads`, a hypothesis); written as VCVio oracle computations, consistency is a theorem and the
  budget is the syntactic query bound (`ROM/TableReads.lean`, `sReads_runT`; the `*OC*` theorems).
  A budget is needed in either form (`not_sReads_slice`). The guess's read budgets and the
  adversary's seed-XOF reads are semantic bounds.
- *PomFRIT and `H₂³`*: an Issuer that reads `H₂³` is covered with a joint budget (`IBudgetH`, with
  per-proof slices and with one shared `H₃`), not with per-slice budgets (`IBudget` with
  `i₂ > 0`); the two-phase
  zero-knowledge theorem with a continuation that reads `H₂³` is not stated (the game does not
  need it).
- *Moussaka's non-colluding mode* with the Moderator's choices read off the tables: done
  (`anonymityNCRA_lean_num`, `anonymityNCOC_lean_num`), but not in the shared-`H₃` game.
- *Moussaka 4(b)'s abort term with pqov's signer*: bounded only on average over the `P2` part of
  the Anchors' keys, with `P2` uniform given `(O, P1)` the modelling step (AES-128-CTR of
  `pk_seed` a random function, SHAKE256 a random oracle); for a fixed key `δ` is not bounded
  (`delta_zero_key`). The executable signer model is tested against the C++, not proved equal
  to it (its elimination is not proved to reject exactly the singular systems).
- *Scope of the games.* Covered: any number of further honest sessions in one concurrent schedule
  per protocol (their first messages before the adversary's first answer, their later ones seen by
  the next stage or the guess), any number of challenge pairs (quadratic bounds), adaptive
  schedules, for Moussaka and Ratatouille through a table-reading key stage, and interleaved
  schedules, the adversary starting and answering further sessions in any order, with a
  scheduler that reads the tables and places the challenge, Ratatouille's
  further Clients spending up to `K` times along their change tokens (§3, "Many sessions";
  `docs/zk.md` §10.8). Not covered in Lean:
  - in the interleaved games, a second challenge session whose inputs are chosen after the first
    one's request (only Moussaka's per-Client key can differ, and no issuance request reads it, so
    this is a mechanical but stack-wide generalization, not done; the privacy notions fix the
    challenge inputs first, and so do the two-session
    games and their hops; requests revealed at different steps and answers given at different
    steps with the inputs fixed are covered, `realGameILO`); Moussaka's and Ratatouille's
    interleaved bounds charge a further Client in both the key stage and the interaction
    (`2⁻¹⁰¹` per Client where the sequential schedule has `2⁻¹⁰²`: the key-stage games' redemption
    hops charge the key stage and the interaction, on the programmed tables, separately; removing
    it needs state-dependent budgets in those hops and sessions resumed from the key stage's state,
    `docs/zk.md` §10.8 "Open");
  - a key stage (`*RAK*`) written as an oracle computation (`OC`) or in the shared-`H₃` and
    seed-XOF games, and likewise PomFRIT's prefix-counting bound (`*_pfx`): these have only the
    function- and permutation-row variants;
  - a bound linear in `N` for `N` challenge pairs: for Moussaka and Ratatouille the bound on the
    bad event `β` of `anonymityP_lin`, `unlinkabilityP_lin` (on paper; it needs `H₄` a random
    oracle), for PomFRIT without the `iv` birthday term and with the budget terms charged once (one
    joint bad event over all proofs, the gate labels' distribution); running the interleaved games'
    further sessions on private tables with `pr_split_le` would also remove their factor about 2;
  - the `H₄`-table games with permutation rows; further sessions in the shared-`H₃`, seed-XOF and
    non-colluding games; a table-reading interaction (`RA` form) in the non-adaptive many-session
    games (`realGameN`, `realGameP`; the interleaved games' scheduler reads the tables);
  - PomFRIT's contexts beyond a finite type (the seed-XOF model), and every quantum statement
    (`docs/zk-qrom.md`).
- *Not gaps, but artifacts of the proofs*: the second `4607` in `εRO` (the honest recomputation's
  cipher reads, `docs/zk.md` §10.1); `Pr[Δ' = 0]` proved `≤ 2⁻¹¹⁴` (second moment) where it is
  `≈ 2⁻¹¹⁸·⁷` (an exact count of the accepted set is out of the kernel's reach), so every bound
  carries `Pr[GrindBad] ≤ 2⁻¹¹³`; and, with one shared `H₃`, the charge of `221·2⁻¹²⁸` per `H₃`
  read where `2⁻¹²⁸` would do. The fixed-record `*_shake` theorems keep the hop hypotheses (`HopHyps`, `HopHyps2`), each an idealization (`Privacy/Basic.lean`); the random-oracle theorems
  supersede rather than discharge them.

The analysis also found a gap in the FAEST v3 specification's own ZK proof (between games G8 and
G9).

### 4. Quantum adversaries (QROM + quantum ideal cipher) — `docs/extraction/Q1…Q7`

| Doc | Result | Status |
|---|---|---|
| Q1 | Key-level compressed oracle for AES as a quantum ideal cipher; online extraction of leaf keys | [paper] + [Lean] `Seed/QuantumCipher.lean` |
| Q2 | Straight-line extraction for quantum provers; leading term ≈ 200·q²·2⁻¹²⁸ (Grover-inherent) | [paper] + [Lean] `Seed/QROM.lean` |
| Q3 | Comparison of AES models; the sketch's "AES-CTR as random oracle" model is unfaithful | [paper] |
| Q4 | Efficient simulation of the quantum ideal cipher (within 2⁻¹⁷²), so the extractor is efficient | [paper] + [Lean] `Seed/CipherSim.lean` |
| Q5 | Simulation-extractability in the QROM (superseded numerically by Q6/Q7) | [paper] + [Lean] `Seed/QSimExt.lean` |
| Q6 | Binding of AES leaf commitments for all q: key-level bound (tight for key-level techniques) and a block-representation bound using point evaluations, `ε_multi ≲ 2⁻¹⁸⁴·q³` | [paper] + [Lean] `Seed/CipherBinding.lean` |
| Q7 | Extraction from many proofs at once; quantum versions of the protocol theorems | [paper] + [Lean] `Seed/QMulti.lean` |

**Numbers.** Total extraction failure: 2⁻⁶⁰·⁴ at 2³⁰ quantum queries, 2⁻⁴⁰·⁴ at 2⁴⁰, 2⁻²⁰·⁴ at 2⁵⁰,
2⁻¹⁰·⁴ at 2⁵⁵, 2⁻⁴·³ at 2⁵⁸, vacuous beyond about 2⁶⁰·². At every query count the bound is the
q²/2¹²⁸ term that Grover search makes unavoidable for any 128-bit scheme. The AES binding term is
now below it throughout (Q6 §11–§13: the "two keys open one commitment" event is a real-world
event, and a block representation of the ideal cipher bounds it by ≈ 2⁻¹⁸⁴·q³ with forward and
inverse queries; paper proof, new, reviewed by a second independent pass in Q6 §14 but not
externally). The review found Theorems 4–5 sound and corrected one term: the transfer term is
`5√(|𝒯|/N)` for `|𝒯|` target commitments, independent of the query count (Theorems 4′/5′; Lean
`openers_le_one_add_pairs`, `transfer_solve`); the original grew like `√(17n·Q_E/N)` for `n`
outputs. Toy checks in `scripts/qrom-block-binding/` (`block_sim_toy.py`: commutator norms on all
blocks, exact state simulation). Weak and strong simulation-extractability at `Q_S = 2³⁰`
simulated proofs (`ε_bind^C ≤ min(Theorem 2, Theorem 5′)`, Q5 §13): 2⁻⁶⁰·⁴ at 2³⁰ queries,
2⁻³⁹·³ at 2⁴⁰, 2⁻³⁰·⁴ at 2⁴⁵, 2⁻²⁰·⁴ at 2⁵⁰, 2⁻⁴·³ at 2⁵⁸ (previously vacuous from about 2⁵⁰);
multi-proof extraction (Q7 Theorem M) at `n = 2²⁰` equals its main term at every `q` tabulated.
Lean has the numbers (`block_SE_at_q45_QS30`, `block_SE_at_q50_QS30`, `block_multiM_at_q50_n20`).

### 5. The protocols — `docs/security/`

| Note | Main results | Main findings |
|---|---|---|
| `pomfrit.md` | One-more unforgeability (classical: proved; [Lean] the U1/U2 reductions, `pomfrit_U1_bound`, `pomfrit_U2_bound`, with Lemma P's failure probability an explicit term, stated with OMPR and OMPR⊕τ as standalone games (`pomfrit_U1_ompr`, `pomfrit_U2_omprShift`); U1 and U2 with every term explicit and simultaneous extraction (`pomfrit_U1_sim`: `2⁻⁷` at `2⁶⁴` queries, dominated by Lemma P's `2⁻⁷¹` per query; `pomfrit_U2_sim`: `2⁻⁶²`, tight; G8 closed); OMPR ≤ PomFRIT for the Lean client with `(ℓ+1)·2⁻¹¹³` (`pomfrit_T6_lean`, G9 closed); quantum: Q7, under new quantum UOV assumptions). Blindness: **fails on `main`**, proved with the ZK fix. | The paper's reduction has a gap (its first-phase extractor is not well defined for multi-tree VOLEitH), repaired by Lemma P at a 2⁻⁷¹ per-query loss ([Lean] `Protocols/PomFRIT.lean`). A holder can make many valid signatures per message (non-minimal grinding counter): deduplicate on the message. |
| `moussaka.md` | One-more unforgeability, double-spend detection, redemption non-malleability, issuer hiding: proved. [Lean] Thm 1 in the ROM and ideal-cipher model (`omuf_le_num`, `ROM/MoussakaOMUF.lean`), down to one-more-UOV with `Com` idealized in the standalone game (`omuf_le_num_ompr`), and with simultaneous extraction (`omuf_le_num_sim`, `omuf_le_num_ompr_sim`). Thm 3 (redemption non-malleability) as a game with weak SE a hypothesis (`noRedirect`, `noRedirect_lean`, `Theft/`); its bound was over-stated, corrected to `ε_hop + ε_SE^red + Adv^ow_Com`. | Nullifier squatting (low). The draft's one-more-UOV argument is invalid as written (it programs `Com` inside the protocol); restructured through CT-UF^open. This note's earlier intermediate assumption, plain CT-UF, is false for UOV (scaling); the draft's assumption is unaffected. `main`'s README no longer says the nullifier record must span every accepted Anchor Set (F8, documentation). |
| `moussaka-unbound.md` | Unbound tokens (late `ctx_red` binding, PR #63, `62be5bc`): one-more unforgeability per `(ctx_iss, ctx_red)`, nullifier determinism, redemption non-malleability (including redirection to another `ctx_red`), issuer hiding and unlinkability, also across redemption contexts. Proved on paper; [Lean] arithmetization soundness and completeness (`Arith/MoussakaUnbound.lean`), end-to-end extraction (`EndToEnd/MoussakaUnbound.lean`), issuer hiding and unlinkability across contexts on the executable spec with `n` adaptively chosen redemption queries: colluding (Thm U5(a)) `≤ 4εI + 2n·εR + 2εprf` (`Privacy/MoussakaUnboundAd.anonymityAd`; non-adaptive: `Privacy/MoussakaUnbound.anonymity`), non-colluding (Thm U5(b), corrected) `≤ 2n·εR + 2·(ψ₀ + ψ₁) + 2εprf` with `ψ_c ≤ κ + φ_c`, and `≤ 2n·εR + 2·(δ₀²⁵⁶ + δ₁²⁵⁶) + 2εprf` over vinegar random oracles (`Privacy/MoussakaUnboundNC.anonymityNC`, `anonymityNC_vinegarRO`), both from per-proof zero knowledge and the PRF advantage of Keccak-p[800,12] as hypotheses; Cor U2 on the U1 game (`ROM/MoussakaUnboundCor.lean`), Prop U3 and Thm U4 corrected, for one honest token (`Theft/MoussakaUnbound.lean`); the executable verifier and prover on its KATs and the random-oracle extraction bounds (fixed and adaptive statements, permutation model, spec relations; `ROM/MoussakaUnbound*.lean`), the deterministic cores of unforgeability (`Protocols/MoussakaUnbound.lean`), domain separation. | Squatting is no longer possible (fixes the base note's F2). Privacy against non-colluding Moderators now needs a PRF assumption on Keccak-p[800,12]. A token keeps no record of the contexts it was redeemed in. The paper proof of U5(b) kept the issuance-acceptance bits through the PRF hop; the corrected abort term also counts the issuance proof's completeness error (UF7). U3/U4 corrections: weak SE needed, key recovery reduces to the PRF, U4 needs no `ε_dig` or CT-UF^open (UF8). |
| `ratatouille.md` | Balance (no inflation), no theft, unlinkability, correctness: proved. [Lean] Thm 1 (balance) in the ROM and ideal-cipher model (`balance_le_ufTag`, `ROM/RatatouilleBalance.lean`), without the probe (`balance_le_noProbe`), and down to one-more-UOV with `Tag` idealized in the standalone game (`balance_le_ompr`), and with simultaneous extraction (`balance_le_sim_num`, `balance_le_ompr_sim`). Thm 3 (no theft) as a game with weak SE a hypothesis (`noTheft`, `noTheft_lean`, `Theft/`); for `U` Clients and `M` spends with chained change tokens (`noTheftN`, `noTheftN_lean_plain`). | Spends are not bound to a session, so a copied spend request can be redeemed first (medium); for the same reason a relay can burn an honest nullifier by squatting, so N2a holds only in its extraction form (corrected). Thm 3's §5 bound had unnecessary terms (corrected). Thm 1's UF-Tag reduction must not forward the Issuer's signing calls on the duplicate-nullifier path (corrected); Thm 1 omitted the Issuer's abort term (corrected). |
| `domain-separation.md` | Every hash/XOF/permutation call lies in a disjoint domain, except below. [Lean] `Protocols/DomainSeparation.lean` | PomFRIT's `hash_to_target` overlaps four proof-system domains (no exploit found; fix: a final domain byte). |
| `uov-assumptions.md` | Relates the protocol-specific UOV assumptions to each other and to standard UOV: all three protocols rest on one-more-UOV (OMPR). [Lean] the counting cores (`Protocols/UOVAssumptions.lean`), the assumptions as games (`Assumptions/UOV.lean`) and T1(a), T1(c), T4 (random-function `Com`), A1, P8(a), T6's generic core, P9(a) (`Assumptions/`). | Several reductions are unavailable; the note states why. Lemma U (CT-UF from OMPR) was wrong; T1(c) and T4 need padding and a sampler-failure term. |
| `ompr-shift-algebra.md` | OMPR versus OMPR⊕17 using UOV's algebra: a reduction black-box in the adversary only (any use of the public map, rewinding) wins with probability `≤ 2·τ^{−(q+1)} + Adv^{free}_{UOV} + V⁴·2⁻³⁴³` (Theorem R; [Lean] `thmR_V4`, `corR'`, `Assumptions/TheoremR*.lean`); collinear shifts trade one equation for a landing on τ of 256 points (at τ = 17 no gain in the reference model, at most `2^4.1` in any; estimates and toy experiments). Theorem T3: no additive or affine symmetry but the scalings, for all keys but `256^{−976}` (paper); [Lean] `t3` (`Assumptions/SymmetryT3.lean`): linear, Frobenius-semilinear and infinitesimal pairs, with affine parts, all keys but `256^{−128}`, `P1` and `P2` uniform; identities in `Spec/PqovSymmetry.lean`; Lemma N for fixed `P1` in `Assumptions/SymmetryCount.lean`; audits `Audit/SymmetryT3.lean`. [Lean] `Spec/PqovShift.lean` (`affine_symmetry`, `preimage_line`, `preimage_plane`), `Assumptions/TheoremR.lean`, `Audit/TheoremR.lean`; toy checks `scripts/ompr-shift-algebra/`. | A6 stays open (attack side: `ompr-cryptanalysis.md`); collinear shifts may gain up to `τ`; at τ = 17 the sign is model-dependent, at most 4 bits. |
| `ompr-cryptanalysis.md` | Attacks on OMPR and OMPR⊕τ that use the `derive_preimage` oracle: the answers are uniform good fibre points, so they carry the trapdoor only through goodness. Key recovery through the oracle needs `2^292.5` calls (vinegar collision) or `2^600` answers (linear statistics; variance proved for uniform `P2`); no call pays for two targets; the two games share the oracle. [Lean] `Spec/PqovVinegar.lean` (`vinegar_reuse`, `sysMat_smul`, `good_smul_iff`); toy experiments `scripts/ompr-cryptanalysis/ompr_toy.py`. | No attack below the oracle-free ones (direct forgery `≈ 2^140`, key recovery `≈ 2^194` multiplications). On toy keys the oracle does give the oil space, with `≈ q^(V/2)` or `≈ q^V/δ` calls. Not a proof; statistics of degree above one, and quantum attacks, are open. |
| `uov-open-reductions.md` | OMPR versus OMPR⊕τ: the tight direction, and no relativizing reduction for the other with loss below `τ^{q+1}/2`; CT-UF up to scalars ≡ OMPR with free non-challenge calls, separated from OMPR. Paper; [Lean] counting cores and the scaling attack (`Spec/PqovScale.lean`). | Plain CT-UF is false for UOV. |
| `uov-open-structure.md` | Meta-reduction theorems A1–A3 (one-more UOV assumptions do not follow from the UOV problem by key-preserving black-box reductions); first cryptanalysis of GPI. Paper only; scripts in `scripts/uov-open-structure/`. | GPI ≈ key recovery is a conjecture; estimates under semi-regularity, citations from memory; weak two-sided distinguishers and key-changing reductions are open. |
| Privacy on the specs ([Lean] `VoleMole/Privacy/`) | The privacy theorems as games on `Spec/*`, each hybrid hop mechanized, from per-proof zero knowledge (`Privacy.ZeroKnowledge`: a simulator from the instance alone, `ε`-close for every valid witness) and, for Moussaka 4(a) and Ratatouille, hiding of `Com` for explicit reductions: PomFRIT blindness (`Privacy.PomFRIT.blindness`, `≤ 4ε`); Moussaka issuer hiding and unlinkability against a Moderator colluding with all Anchors (Thm 4a, `Privacy.Moussaka.anonymity`, `≤ 4εI + 4εR + 2εhide`) and against one that sees no issuance (Thm 4b corrected, `Privacy.Moussaka.anonymityNC`, `≤ 4εR + 2·(φ₀ + φ₁)`, no assumption on `Com`), both also for `main`'s Client that finds its Anchor itself (`Privacy.MoussakaFind.anonymity`, `.anonymityNC`; the other Moussaka games take the index-taking Client of the API before `21be618`); Ratatouille unlinkability of spends from issuances and from each other through change tokens (`Privacy.Ratatouille.unlinkability`, `≤ 4εI + 4εS + 2εhide`). With the executable Lean prover (label rows) down to its tape hypothesis (`*_label_rows`, `blindness_lean`; `*_shake` with the hop hypotheses); for 4(a), Ratatouille and PomFRIT also in the random-oracle and ideal-cipher model with every zero-knowledge term explicit (`*RO_lean_num`), with table-reading interactions (`*RA_lean_num`, `blindnessRAH_lean_num`, `*OC*`), with AES as random permutations (`_perm`), with one shared `H₃` (`*Sh_num`, `blindnessRAHSh_num`) and from the real Clients' seeds (`*_seed`); Moussaka 4(b) also in the random-oracle and ideal-cipher model (`anonymityNCRO_lean_num`, `anonymityNCSh_num`, with `_seed`), with the Moderator's choices read off the tables (`anonymityNCRA_lean_num`, `anonymityNCOC_lean_num`), with pqov's signer (`anonymityNC_pqov`, `anonymityNCRO_pqov`; averaged over pqov's keys `anonymityNCRO_pqov_pqovKeys`, abort term `≈ 2⁻²⁹³·⁸`; the model equals the C++ `derive_preimage` on the KAT targets, `spec_kats`) and reaching redemption (`pr_refused_NCRO_le`); 4(a) and Ratatouille also with table-reading key stages (`anonymityRAK_lean_num`, `unlinkabilityRAK_lean_num`); 4(a), Ratatouille and PomFRIT also with many sessions (`*N_lean_num`, `*P_lean_num`, `blindnessPH_lean`, `blindnessAd_lean_num`, `anonymityAd_lean_num`, `unlinkabilityAd_lean_num`; interleaved schedules, Ratatouille's further Clients spending several times: `blindnessIL_lean_num`, `anonymityIL_lean_num`, `unlinkabilityIL_lean_num`; with a table-reading scheduler and a free challenge: `blindnessILO_lean_num`, `anonymityILO_lean_num`, `unlinkabilityILO_lean_num`; Moussaka and Ratatouille with `N` pairs linear up to a bad event, `anonymityP_lin`, `unlinkabilityP_lin`). Bounds and what remains: §3 | The zero-knowledge hypothesis is false on `main` for PomFRIT (`ZK.pomfrit_issuer_hits`, `ZK.pomfrit_attack_test`); for Moussaka and Ratatouille no efficient simulator satisfies it per proof on `main`, and the joint (PU) hop replaces it ([Lean] `anonymity_main`, `unlinkability_main`, (PU) as an explicit term). PomFRIT note §8.3: the "both ⊥" rule is needed. Moussaka Thm 4(a) needs no `2⁻¹⁹²` term; Thm 4(b) misses an abort term `2·(φ₀ + φ₁)` (negligible, bounded with no assumption on `Com`), needs the Client to take its index from `S`, and needs no `2⁻¹⁹²` term either. Its Lean random-oracle games were vacuous until they used the label-row Anchor (fixed); with pqov's signer its abort term is bounded only on average over the keys (§3). Ratatouille H3 needs the Client's validity check against the commitment it sent. Ratatouille's H1 misses the seed collisions, and Moussaka's Thm 4 has no term for the seed-XOF hop (`docs/zk.md` §10.6) |

**Cross-cutting finding (critical, deployment):** PomFRIT's Issuer signs arbitrary targets, and
all protocols share the UOV key type. If one key serves PomFRIT and another protocol, anyone can
mint Ratatouille credits or forge Moussaka tokens (demonstrated). Keys must be separated by
protocol.

### 6. Arithmetization in Lean — `VoleMole/Arith/`

Goal: replace the paper proof of L7 with executable Lean models of each relation's constraint
generator, mirroring the C++ call by call, with Lean proofs of

- **completeness**: an honest witness satisfies every constraint;
- **soundness**: if the constraints vanish at any committed values, those values are bits and
  encode a witness, except for a 1/|F| fraction of combination challenges;

and a differential test that evaluates the C++ constraints at random *field-valued* inputs (which
pins down the constraint polynomials, not just their values on bits) and compares with Lean.

| Piece | Status |
|---|---|
| `Arith/Basic.lean`: shared constraint-expression interface | done |
| `Arith/UOV.lean`: UOV public-map gadget (`src/uov/circuit.hpp`) | done: generator, completeness, soundness, 1/\|F\| combination bound |
| `Arith/PomFRIT.lean`: PomFRIT redeem, `P(s) = h ⊕ r` | done: generator, completeness, soundness, end-to-end 1/\|F\| bound |
| `Arith/Keccak/`, `Arith/Keccak.lean`: Keccak-p[800,12] segmented gadget (`src/keccak/`) | done: reference permutation (checked on the KATs), inverse layers proved, generator, completeness, soundness (outputs equal Keccak-p[800] of the input) |
| `Arith/Adder.lean`: Ratatouille's 64-bit credit adder | done: exact 65-bit sum |
| `Arith/GF.lean`, `GFEmbedding.lean`: concrete GF(2¹²⁸), GF(256), the embedding | done; embedding proved an injective ring homomorphism in the kernel |
| `Arith/GFField.lean`: `GF128` is the field GF(2¹²⁸) | done, in the kernel: `X¹²⁸ + X⁷ + X² + X + 1` irreducible over GF(2), `GF128 ≃+* GF(2)[X]/(X¹²⁸ + X⁷ + X² + X + 1)`, `Field GF128`, `CharP GF128 2` |
| `Arith/ConcreteField.lean`, `EndToEnd/Concrete.lean`: the soundness corollaries at GF(2¹²⁸) | done: `uov_*`, `*_complete`, `*_sound_card` and the five `EndToEnd` `*_extract` theorems at `F := GF128`, `β := beta`, `K := GF256`, with `IsEmbedding beta`, `beta 0 = 1` and `\|F\| = 2¹²⁸` discharged; the bad-`l` fraction is `≤ 2⁻¹²⁸` |
| C++ dumper (`tests/arith/`) and `lake exe arith_vectors` | done; Lean and C++ constraint values agree on every UOV and PomFRIT record, at bit and random field-valued witnesses |
| `Arith/Moussaka.lean`: Moussaka issue (commitment opening) and redeem (one-hot selector, UOV preimage under the selected anchor key, Keccak commitment) | done: generators, completeness, soundness, 1/\|F\| bound; cross-checked |
| `Arith/Pqov.lean`, `Arith/Concrete.lean`: pqov's `ov_publicmap` equals the model; the relations read as the C++ byte checks on concrete GF(256) | done; cross-checked |
| `Arith/Ratatouille.lean`: Ratatouille issue (commitment opening) and spend (two commitments, tag, conservation `t + x = t' + d` over ℕ with 64-bit ranges, UOV preimage of the tag) | done: generators, completeness, soundness, 1/\|F\| bound; cross-checked |
| `EndToEnd/SpecRelations.lean`: the arithmetized relations back to the spec relations | done for all five: a witness of the arithmetized relation (`EndToEnd/Relations.lean`) decodes to a witness of the spec relation, for well-formed instances (`issueRelW_of_wit`: `\|t\| = 45`, `\|ctx_iss\| = 16`; `redeemRelW_of_wit`: `\|nf\| = 24`, contexts 16, at most 64 Anchors; `issueRel_of_witB`, `spendRel_of_witB`: `t_init, d < 2⁶⁴`; `pomRel_of_wit`: none). The converse of `Privacy/*Lean.lean`'s spec → arithmetized. For Moussaka the spec witness is the re-encoding of the decoded fields (the committed Keccak states recomputed); also the `hinj` lemmas (§9) |

The UOV gadget's hypothesis, that the embedding GF(256) → GF(2¹²⁸) given by the β constants is an
injective ring homomorphism, is discharged in the kernel for the concrete constants
(`VoleMole.Arith.isEmbedding`), and with `Field GF128` the soundness theorems are instantiated at
the concrete field with no hypotheses left (`Arith/ConcreteField.lean`, e.g.
`Moussaka.redeem_sound_card_gf128`; `EndToEnd/Concrete.lean`, e.g. `moussaka_redeem_extract_gf128`). The constants themselves, and the GF(2¹²⁸) and GF(256)
multiplications, are checked against the C++ tables by `arith_vectors`.

`Arith/GFField.lean` proves that the concrete `GF128` operations form the field GF(2¹²⁸), without
`native_decide`: Mathlib's degree criterion (an irreducible factor of `X^(2ⁿ) − X` over GF(2) has
degree dividing `n`) reduces irreducibility of the modulus to `X^(2¹²⁸) = X` and the invertibility
of `X^(2⁶⁴) + X` modulo it, which the kernel computes with `GF128` arithmetic (128 squarings, and a
product with an inverse found offline); evaluation at the root of `GF(2)[X]/(modulus)` is proved
multiplicative symbolically and bijective by counting.

To regenerate and check the vectors (the first `lake build arith_vectors` compiles Mathlib to native
code and takes about 10 minutes; `lean/vectors/` is not committed):

```sh
./build/tests/dump_arith_vectors lean/vectors
cd lean && lake build arith_vectors && lake exe arith_vectors
```

### 7. Executable protocol specs — `VoleMole/Spec/`

Byte-level Lean models of the protocol logic, with the proof system and UOV signing as abstract
parameters (UOV verification is concrete). Cross-checked against the C++ known answers by
`lake exe spec_kats` (about 45 s). UOV public keys are generated in Lean from the KATs' compact
secret keys (pqov key generation, `Verifier/Keygen.lean`); `lean/vectors/uov_keys.txt` (§6) is
compared with them when present but not needed. The model of pqov's `derive_preimage`
(`Spec/PqovSigner.lean`, run by `Spec/PqovSignerExec.lean`) reproduces the C++ responses on the
test key at the six Moussaka and PomFRIT targets (about 5 s each).

| Piece | Status |
|---|---|
| `Spec/SHAKE.lean`: Keccak-f[1600], SHAKE128/256 | done; standard vectors |
| `Spec/PqovSigner.lean`, `Spec/PqovKey.lean`, `Spec/PqovSignerExec.lean`: pqov's `ov_derive_preimage` | done: correct when `P` vanishes on the oil space, which holds for pqov's keys with any oil matrix (`oilSpace_iff_P3Pqov`, `oilSpace_pqovKey`); the system built from the polar form is pqov's stored `S = (P1 + P1ᵀ)O + P2` (`sysCoef_eq_pqovS`); output equal to the C++ `derive_preimage` on the KAT targets (the elimination's rejection of exactly the singular systems is not proved) |
| `Spec/PomFRIT.lean`, `Spec/Moussaka.lean` | done: every party's steps and errors; honest runs succeed; at most one acceptance per nullifier and context over any request sequence; injectivity of the hashed encodings (`H_T` binds d[0..M), Moussaka binds `challenge_digest`); input validation. All deterministic KAT fields match (`tests/pomfrit/pomfrit_kat.txt` is new). Moussaka's redemption requests are also checked by `finalizeRedeem` with the abstract verifier instantiated by the Lean verifier (§8), under the Anchor Set generated from the `anchor_sk` fields, so the digests of all Anchors (not only the issuer's) are checked against the KATs; swapping two non-issuer Anchors is rejected |
| `Spec/Ratatouille.lean` | done: issue, spend, refund, change tokens, every abort path; honest runs succeed; nullifiers accepted once; balance `Σd ≤ ΣT_init + Σx′` per context over adversarial request sequences (soundness and unforgeability as hypotheses); the findings of `security/ratatouille.md` (copied requests, consumed pending state, unbounded refunds, signing before the nullifier check) as theorems, including a concrete run that breaks balance after one leaked response. All deterministic KAT fields match. |

### 8. A Lean VOLEitH verifier and prover (both match the C++ on all KAT proofs, both layouts) — `VoleMole/Verifier/`

Goal: an executable Lean verifier that accepts the real C++ proofs (the KAT files contain them) and
rejects mutated ones, built from the same models the proofs use, and an executable Lean prover that
reproduces them. Plan and milestones: `docs/verifier-plan.md`. Checked by `lake exe
verifier_vectors` against vectors from `tests/voleith/dump_verifier_vectors.cpp`, and by `lake exe
prover_vectors` against the KAT files.

| Milestone | Status |
|---|---|
| SHAKE, AES-128, faest-arch-opt's CTR PRG | done; FIPS-197 and C++ vectors |
| One-tree BAVC (GGM) reconstruction and `vole_commit_check` | done; reproduces a real Moussaka issuance proof byte for byte |
| Proof parsing, `chal1`, ConvertToVOLE, CRT VOLE (lifted rows, masks, lifted Δ) | done; on one real proof of each of the five relations, every value matches the C++ byte for byte |
| KOS VOLE check and `chal2` (`KOS.lean`) | done; matches the C++ for all five relations |
| QuickSilver (`QuickSilver.lean`) | done; the verifier's value for a degree-`d` constraint is `Δ^d·f(q/Δ)`, so the proved `Arith/*` generators are evaluated unchanged at `q·Δ⁻¹`; the UOV gadget is evaluated directly over arrays (`UovEval.lean`), proved equal to the generator's value |
| Full verification (`Verify.lean`, `Relations.lean`, `Kats.lean`) | done; all 18 proofs in the three KAT files are accepted (3 PomFRIT, 6 Moussaka, 9 Ratatouille), with statements built in Lean from the KAT fields and the `Spec/*` instance encoders; 51 mutations (each proof field, each instance field, PomFRIT's refresher) are rejected. Runtime about 25 s (was about 5 min): the UOV public maps are evaluated over arrays with `Combination`'s tables (`UovEval.lean`, ≈ 10 ms per key, proved equal to the `Arith/*` evaluators), `GF128.mul` runs as an unboxed loop proved equal to it (`@[csimp]`, ≈ 0.3 µs), and AES uses round tables |
| Unbound Moussaka (PR #63; `moussakaUnboundIssue`, `moussakaUnboundRedeem` in `Relations.lean`) | done: all 9 proofs of `tests/ihat/unbound_ihat_kat.txt` are accepted and 25 mutations rejected (with the base KATs: 27 accepted, 76 mutations rejected; 7 records in `verifier_kat.txt`, whose intermediate values match the C++); `lake exe prover_vectors` reproduces all 27 KAT proofs byte for byte. Bridge, per-chain extraction and completeness carry over (`moussakaUnbound*_values`, `_accept`, `_extract_chain`, `_complete_shake`) |
| CRT tables (`CrtData.lean`, `CrtGen.lean`, `CrtSearch.lean`) | done: `W_crt` and `M_tree` are recomputed from the moduli; F, G, W_tree, W_gate (copied from faest-arch-opt's build output into `CrtData` as hex literals, which the verifier reads) are checked against their defining bilinear identity on all basis pairs (at run time, and in the kernel for the verifier's own computation: `Bridge/CrtCheck.lean`) and regenerated by a port of `vole_mult_tables.py --preset 128f` (tree moduli, cost search and portfolio, bilinear algorithms including Montgomery's formula and the F₄ towers, interpolation, pruning), which reproduces them exactly |
| UOV keys | done: pqov's key generation (`generate_keypair_pkc`, uov-Ip-pkc: `SHAKE256(sk_seed)` → `pk_seed ‖ O`, `P1 ‖ P2` by AES-128-CTR, `P3 = UT(M + Mᵀ)` with `M = Oᵀ(P1·O + P2)`, `Keygen.lean`, about 0.08 s per key) and `expand_pk` in Lean; the KAT runners derive every key from the compact secret keys. The 64 generated compressed keys equal the C++ ones in `lean/vectors/verifier_keys.txt`, and the expanded `test`/`alt61`/`alt62` keys equal `uov_keys.txt` (both optional cross-checks) |
| Label-rows variant (`Params.labelRows`) | done; the same verifier, with the flag set, accepts all 18 KAT proofs of `d5def9c` (branch `voleith-label-rows`; KATs regenerated there, PomFRIT's too) and rejects the same 51 mutations; every intermediate value of the five dumped proofs matches |
| Hash record (`Hashes.lean`) | done: the verifier takes its hashes as a record `Hs : Hashes`, one function per L0 domain (`Kind`: `H₁`, `H₂⁰`, `H₂⁴`, `H₄`, `H₅`, `H₂¹`, `H₂²`, `H₂³`, the combination); `Hashes.shake` is SHAKE128, which the runners use (same results on both layouts). The UOV combination is hashed by the verifier (`Statement.comb`, `combBytes`). Hashes outside L0 (UOV key digests and expansion, PomFRIT's `hash_to_target` and refresher commitment) stay SHAKE. The bridge theorems below are generic in `Hs`; §9 runs the verifier with the random oracle's answers (`Hashes.ofTable`) |
| Bridge theorems (`Verifier/Bridge/*`) | partly: proved that the executable CTR blocks are `Seed.Commitments.ctrInput` (and its role separation applies to the verifier's tweaks), that the VOLE check is `Seed.kosValue`, that the QuickSilver check value is `EndToEnd.qsCheck` + `Seed.maskPoly` (including the `Δ^d·f(q/Δ)` shortcut), and that acceptance gives `EndToEnd`'s accepting equation at that transcript. The field embedding is constructed (`Bridge/Concrete.lean`, from `Arith/GFField.lean`) and the theorems that assumed one (`accept_hacc`, `map_constraintKeys`, `map_gfInv`, `map_voleHashReceiver`) are restated at it without that hypothesis. Per relation (`Bridge/Relations.lean`): with `GF128` itself as the field, each relation's evaluator is `System.values` of its `Arith/*` system (`betaFast = beta`, cached UOV coefficients unchanged, the array-based UOV evaluation of `UovEval.lean` equal to the generator's), so acceptance by the executable `verify` gives `EndToEnd`'s accepting equation for that system over GF(2¹²⁸) with no hypothesis (`moussakaIssue_accept`, …, `pomfritVerify_accept`), i.e. `hacc` of `*_extract_gf128` at that Δ. |
| Bridge across Δ (`Bridge/Lift.lean`, `Columns.lean`, `Chain.lean`, `ChainRelations.lean`) | done, modulo the probabilistic steps: ConvertToVOLE and the CRT step are read as functions of the challenge blocks with the commitments fixed (the steps take `Δ` as bits and the commitments as arguments: `convertToVoleAt`, `crtReconstructAt`). Proved: each column is `V_{i,b} + Δ_{i,b}·u^{(i)}` with `u^{(i)} = c_i + Σ_j PRG(K_{i,j})` (the hidden leaf's key never read), so each lifted witness row is `C_r + Σ_i u^{(i)}_r·e_i(Δ_i)` (`resp_row`); the executable lift `Δ ↦ Σ Δ_c W_CRT[c]` is additive and injective (`lift_injective`, an explicit left inverse checked by `decide +kernel`); an opening that reconstructs the committed keys makes the run equal to the committed response (`crtReconstruct_eq_respAt`). On a chain (fixed `iv`, `H₅`, `chal1`, `h_V`, `z`; `chal2` determined before Δ), `chain_claim4` gives `Claim4Hyp` and the accepting equation on all of `A` with one remainder `maskPoly d a b ã z` (masks affine by L3); `onChain_of_accept` puts every accepted proof of the chain in `A` with `Δ = chal3`; `*_extract_chain` (five relations) apply `*_extract_gf128`. Assumed: `KOSGood` for `chal1` (L3), `IsFixed` for dead-leaf trees (L2), `hQS`/`hcomb` (L4), `hδ`/`hclaim1` and binding of the leaf commitments (L1). §9 discharges L3, L4 and `hδ` for uniform independent `chal1`, `chal2`, `l` |
| Prover (`Prover.lean`, `ProverKats.lean`) | done: `voleith_vole_gen` + `voleith_prove_commit` with the C++'s seed derivation (`H₃(w_prefix ‖ mu₁ ‖ rho ‖ 3)`, `rho` from the `Spec/*` seed expanders). Each sender step is the verifier's step function at `Δ = 0` (tag columns, gate hashes, lifted rows, masks, VOLEHash), plus the prover-only `u`, `u_mask` (`M_tree`·PRG), the second gate labels and `c_mult`; QuickSilver's `ã` and check value are the coefficients of the verifier's check value as a polynomial in `Δ'`, obtained by evaluating it at `d + 1` points and interpolating (no coefficient decomposition of the constraints); grinding and the BAVC opening as `grind_and_open`. `lake exe prover_vectors` reproduces all 18 KAT proofs byte for byte on `main`, and all 18 of the label-rows KATs with `labelrows`; the Lean verifier accepts every Lean proof, also on random statements of all five relations (issuers' UOV preimages from a test-only oil-space sampler); a non-satisfying witness is refused. About 44 s per layout |
| Zero-knowledge simulator (`ZK/Sim.lean`, `ZK/SimKats.lean`, `docs/zk.md` §10.1) | done: the simulator, `H₂³` programming, the ideal-tape prover and the real run's tape (`tapeOf`), executable. `lake exe zk_sim` checks on all 18 KAT runs of each layout that `proveIdeal (tapeOf …) = prove`, that the verifier accepts the simulated proof with the programmed oracle (proved for every run with `Δ ≠ 0`, `simulateRO_accept'` in `ZK/SimAcceptFull.lean`, so this check is redundant) and rejects it without, and (except PomFRIT) that it accepts the ideal-tape prover's proof on a pseudorandom tape with programmed grinding answers. About 10 minutes per layout |
| Completeness (`Bridge/Prover.lean`, `Bridge/BAVCComplete.lean`, `Bridge/CrtCheck.lean`, `Bridge/CrtComplete.lean`, `Bridge/Complete.lean`) | proved: the VOLE correlation of the prover's output for every `Δ` on columns and lifted rows (`prover_column`, `prover_row`), the VOLE check identity (`voleHash_complete`), QuickSilver completeness for every `Δ' ≠ 0` (`qsProve_complete`, via `EndToEnd.sysCheckPoly` and Lagrange uniqueness), BAVC opening correctness for every seed and `Δ` (`bavcComplete`: the walks are folds, read as functions of the node index; the opened nodes are exactly the unmarked children of marked nodes, and top-down derivation recovers every node off the hidden paths), the CRT masks' VOLE correlation for faest-arch-opt's tables and every `Δ` (`crtComplete`: gate labels and `c_mult` read back, `r̃` bilinear, and the tables' bilinear identity `L_c(a) = a · W_crt[c]` checked in the kernel on all `120 · 128` basis pairs, packed into 120 numbers of `2¹⁶³⁸⁴` bits, ≈ 1 min), and **completeness of `verify` on the prover's output** (`verify_proveCommit_tables`, `verify_prove_tables`, `*_complete_tables` for the five relations, `*_complete_shake` with SHAKE; for PomFRIT also `pomfritVerify` on the final signature, `Privacy.PomFRIT.pomfritVerify_complete_tables`). The general versions (`verify_prove`, `*_complete`: any tables) keep `BAVCComplete` and `CrtComplete` as hypotheses. These deterministic theorems assume that the prover returned a proof and `Δ' ≠ 0` (`Δ' = 0` only at `Δ = 0`, `ZK.Sim.tDL_eq_zero`), and, for a general hash record, its output lengths (SHAKE: `hashesWF_shake`). **Probabilistic completeness** (`ZK/CompleteRO.lean`) removes the first two: in the random-oracle model of §3 (`recH`: `H₃`, `H₂³`, `H₅` uniform tables, `ρ` uniform), the prover fails or `verify` rejects its proof with probability `≤ Pr[GrindBad] ≤ 2⁻¹¹³` (`complete_rom`, for every statement and witness with `ZKHyp`; `complete_rom_ic` with the ideal cipher), per relation `moussakaIssue_complete_rom`, `moussakaRedeem_complete_rom`, `ratatouilleIssue_complete_rom`, `ratatouilleSpend_complete_rom` (the privacy games' label-row statements, for every witness in the relation), and for two phases `complete2_rom` and `pomfritRedeem_complete_rom` (AES as the PRG; whenever the Issuer's valid continuation continues with an instance, the final proof is accepted for it). The error is the grinding term alone: no accepted grinding answer (`≤ 2^{−2¹⁵}`) or a first accepted answer `Δ = 0` (`≤ 2⁻¹¹⁴`) |

### 9. Probabilistic layer — `VoleMole/Prob/` (single challenges) and `VoleMole/ROM/` (random oracle)

Plan: `docs/probabilistic-plan.md`. **Phase A** (`Prob/`, milestones M1–M3, Mathlib only): every
statement is a probability `prU α P` under `PMF.uniformOfFintype`, over the byte strings the random
oracle returns, decoded exactly as the executable verifier decodes them. The samples are uniform and
independent by assumption; phase B justifies this per query.

| Piece | Status |
|---|---|
| `Prob/Uniform.lean` | done: `prU`, count → probability (`prU_eq_card`, `prU_le_of_card_le`), union bound, pushforward along an equivalence, averaging over a product |
| `Prob/Bytes.lean` | done: `Bytes n`; the little-endian words determine the bytes (`word_byte`); `gf128OfBytesEquiv : Bytes 16 ≃ GF128`, `chal1Equiv : Bytes 136 ≃ Seed.Ch GF128 shortKeys` (forward map `chOf`), `chal2Equiv : Bytes 56 ≃ GF128³ × shortKeys` (the `zkCoeff` arguments), `card_shortKeys = 2⁶⁴` (no enumeration); `hδ` deterministically: the `2¹²⁰` admissible `chal3` (`check_format`) decode injectively into blocks (`deltaBlocks_injOn`), and `prU_accept_le` (at most `N` accepted ⇒ probability `≤ N·2⁻¹²⁸`) |
| `Prob/Challenges.lean` | done: L3 over a uniform 136-byte `chal1`, `≤ epsKOS ≤ 2⁻¹⁵⁰` for `≤ 2¹²⁰` challenges (`chain_kos_bad_le`, `epsKOS_le`); the canonical slope `Chain.AV`, `Chain.uCanon`, `slope_eq_uCanon` (L4 §5: every slope on `A ⊆ A_V`, `\|A\| ≥ 2`, is `uCanon`, fixed before `chal2`); L4 over a uniform 56-byte `chal2` (`prU_qs_bad_le`, `≤ ε_QS(n)`), over uniform `l` (`prU_comb_bad_le`, `≤ 2⁻¹²⁸`) and over both independently (`prU_qs_comb_bad_le`) |
| `Prob/ChainRelations.lean` | done: the per-chain theorem for all five relations (`*_chain_prob`, generic `chain_prob`). For a chain whose commitments are fixed before `chal1` and whose `ũ`, `d`, `h_V` are fixed before `chal2` (`Chain.SamePrefix`, `Chain.SameMid`), with `chal1`, `chal2`, `l` uniform and independent: `Pr[L2 ∧ hclaim1 ∧ ¬(extraction ∨ at most max(d,1) admissible chal3 accepted)] ≤ 2⁻¹⁵⁰ + ε_QS(n) + 2⁻¹²⁸` (no `2⁻¹²⁸` term for the issue relations; `ε_QS(n) ≤ 2⁻¹²⁷`, `epsQS_le`). L2 and `hclaim1` remain conjuncts of the event |
| `Prob/Bytes.lean` (M5) | `combEquiv M : Bytes (16·M) ≃ (Fin M → GF128)`, the decoding of `l` |

To make `chal2` and `l` samplable, `Bridge/Chain.lean`'s `Chain` has `chal2` and the constraint
evaluator `vals` as fields (it was `Chain.chal2 := Verifier.chal2 …`), and since the hash record
(§8) also `iv` and the gate hash `h5`; `onChain_of_accept` takes `chal2 = Verifier.chal2 Hs …`,
`vals = st.values chal1 (st.combBytes Hs chal2)`, `iv = ivOf Hs …` and `h5 = Hs.hash .h5` as
hypotheses, and the combined relations' `*_extract_chain` take the system at a free `l` (`*SysL`).

**Phase B** (`ROM/`, milestones M4–M5, VCVio). The SHAKE128 calls are one VCVio oracle specification
indexed by L0 domain (`L0-L2-commitments.md` §2.1) and input string, answered by VCVio's lazy random
oracle; one oracle on byte strings with L0's domain rule is proved equivalent (`ROM/DomainSep.lean`).
The theorems bound an event of an arbitrary adversary `oa : OracleComp spec α` with at most
`q₁`, `q₂`, `Q` queries to `H₂¹`, `H₂²`, `H₂³` (and `n` in total), and then the event "the executable
verifier, with the oracle's hashes, accepts the prover's proof and extraction fails"
(`ROM/Accept.lean`). `#print axioms`: `propext`, `Classical.choice`, `Quot.sound` (VCVio's lemmas
used here add nothing).

| Piece | Status |
|---|---|
| `ROM/Basic.lean` | done: `Pr{let x ← $ᵗ α}[P x] = prU α P` (`prEvent_uniformSample_eq_prU`), so every phase-A bound is a VCVio bound; the domains `Kind` (L0's rows 1–12, `comb M` for `l`; defined with the hash record, `Verifier/Hashes.lean`) with their output lengths; `spec = OracleSpec.ofFn` over `Kind × ByteArray` |
| `ROM/UnionBound.lean` | done: per-domain query counts `IsKindQueryBound` and their weighted budget; the union bound `prEvent_exists_bad_query_le` (VCVio's `prEvent_randomOracle_le_of_bad_queries_weighted`: a bad event may read the whole answer table, provided resampling its own cell bounds it) |
| `ROM/Fresh.lean` | done: the union bound when a fresh query's bad event reads a second cell chosen by its answer, with a charge for that cell being cached (`prEvent_randomOracle_le_of_fresh_bad_queries`, `prEvent_completeTable_le_two_cells`) |
| `ROM/Chains.lean` | done: bad `H₂¹` (KOS), `H₂²` (QS at the canonical witness), `H₂³` (accepted among at most `N`) queries, each bounded by its M2 lemma when its cell is resampled; `prEvent_le_chain_terms`: `Pr[event] ≤ q₁·ε_KOS + q₂·ε_QS(n) + Q·N·2⁻¹²⁸ + ε_bind + ε_dead`, numerically for the issue relations (`q₁·2⁻¹⁵⁰`, `N = 9`); the per-chain deterministic step (`chain_good_of_not_bad`, `*Issue_good_of_not_bad`) |
| `ROM/Comb.lean` | done: the combined relations, with `l` read from the table at `chal2 ‖ dst`: per `H₂²` query `ε_QS(n) + 2⁻¹²⁸ + n·2⁻⁴⁴⁸` (the last term: `chal2 ‖ dst` already queried, L0 §2.2); `prEvent_le_comb_terms`, numerically for Moussaka redemption, Ratatouille spend and PomFRIT (`*_prEvent_le`); `comb_good_of_not_bad`, `moussakaRedeem_good_of_not_bad`, `ratatouilleSpend_good_of_not_bad`, `pomfritRedeem_good_of_not_bad` |
| `ROM/Verifier.lean` | done: the executable verifier against the oracle. `Hashes.ofTable g` (the hashes of an answer table); `verifyQ`, the verifier with each hash a query, equal to `verify (Hashes.ofTable g)` against every complete table (`evalWithAnswerFn_verifyQ`); on an accepted proof its `H₂¹`, `H₂²`, `H₂³` queries at the run's inputs are in the log (`inLog_verifyQ`); at most one query to each of them and 337 in total (`isKindQueryBound_verifyQ`, `isTotalQueryBound_verifyQ`); `game T st oa`: the prover (outputting a proof and the extractor's data) then the verifier |
| `ROM/Accept.lean` | done: **the event is the executable verifier's**: `Pr[accept ∧ ¬Extracted] ≤ (q₁+1)·2⁻¹⁵⁰ + (q₂+1)·(ε_QS(n') [+ 2⁻¹²⁸ + (n+337)·2⁻⁴⁴⁸]) + (Q+1)·N·2⁻¹²⁸ + ε_bind + ε_dead + ε_chain + Σ_k q'_k·εh_k` for all five relations (`moussakaIssue_accept_le`, …, `pomfritRedeem_accept_le`; generic `prEvent_accept_le_chain_terms`, `prEvent_accept_le_comb_terms`), `Extracted` the candidate of `*_extract_chain` from the extractor's keys. `htrace` is proved (`chainBad_of_accept`, `combBad_of_accept`); assumed: binding (a bound on the concrete `bindFail`), the "same chain" step with L2(c) (`SameChainHyp`; `SameChain`, with the committed dead leaves and `hclaim1`), L2(a) (`DeadHiddenHyp`), for the combined relations the combination freshness (`CombFreshHyp`), outside `chainFail`, `deadFail` and per-query hits (`εh`) |
| `ROM/DomainSep.lean` | done: **domain separation ⇒ independent oracles**: one lazy random oracle on byte strings with a domain rule `κ` gives every event of a computation whose queries respect `κ` the probability of the per-domain oracles (`prEvent_route_eq`), and every single-oracle adversary is such a computation (`unroute`, `prEvent_unroute_eq`, with its per-domain query counts) |
| `ROM/SingleOracle.lean` | done: L0's rule (`l0Kind`, the final byte); the verifier's queries respect it (`allQueriesSatisfy_verifyQ`, all five relations: `combOk_*`); the game against one SHAKE oracle has the per-domain game's probabilities (`prEvent_game₁_eq`) |
| `ROM/FreshCache.lean` | done: the union bound when a fresh query's bad event reads the cache of the earlier queries (`freshBadC`, `prEvent_freshBadC_le_of_cached`: `n·ε` for a bound `ε` over every cache of fewer than `N` cells) |
| `ROM/CipherBind.lean` | done (M6, PRF view): **binding of the leaf commitments in the ideal-cipher model**. The cipher a random oracle on cells, the prover querying it, the verifier and the extractor reading it. Collision event `collBad` (two keys with equal blocks at both points of a leaf, charged at the first query of the second key): `prEvent_coll_le`, `≤ 2·q_E²·2⁻²⁵⁶`. Straight-line extraction of the leaf keys from the prover's cipher log (`extractKey`, `keysOf`, `knownOf`); `binds_or_coll_or_dead`: the executable reconstruction's keys off the hidden leaves are the extracted ones, unless a collision or a dead leaf is opened; `prEvent_not_binds_le` |
| `ROM/CipherGame.lean` | done (M6): the joint game (prover on hashes and cipher, `specIC`; `runE` returns the prover's joint log, `cipherLog`/`hashLog` its parts; the extractor `proverIC`; the verifier with `icPrg E`); the bridge from a fixed hash table to the lazy oracle (`prEvent_joint_le_add`); `prEvent_joint_bindFail_le`: `Pr[bindFail] ≤ 2·q_E²·2⁻²⁵⁶ + Pr[DeadOpenOut]`; `moussakaIssue_accept_le_ic`: Moussaka issuance with `ε_bind` replaced by `2·q_E²·2⁻²⁵⁶ + ε_open` |
| `ROM/Queried.lean` | done (M6): **the verifier's chain queries were the prover's**. Log facts (`tableQueryLog_congr`, `mem_tableQueryLog_congr`); the hash ladder `w_i → cw → x → y → z` (`ladder_walk`): an accepted proof with a leaf-hash input the prover did not query makes a verifier query a hit (`Hit₁` and its `H₂¹`, `H₂²` analogues) or leaves `z` unqueried; `prEvent_accept_leafUnqueried_z_le` `≤ (q₁+18)(17q₁+q₂₁)·2⁻²⁵⁶ + (q₂₁+1)q₂₂·2⁻¹⁰⁸⁸ + (q₂₂+1)q₂₃·2⁻⁴⁴⁸` |
| `ROM/FreshGuess.lean` | done (M6): abstract class counting (`card_finOf_mul_le`); **one fresh answer guessed** against the lazy oracle, `K·2^{-8·outLen}` and not charged to every query (`prEvent_fresh_guess_le`); the verifier's fresh `H₂³` answer is `Δ` with probability `≤ 2⁻¹²⁸` (`prEvent_accept_zUnqueried_le`) |
| `ROM/CipherOpen.lean` | done (M6): **`ε_open` bounded**: two fresh cipher cells guessed (`prEvent_two_cells_le`; the GGM derivation reads only points of tweak `< L−1`, `recTree_ic_congr_cells`), the dead leaf whose leaf hash the prover queried (`prEvent_deadQueried_le`, `≤ q₁·2⁻²⁵⁶`); **`prEvent_joint_deadOpen_le`**: `Pr[DeadOpenOut] ≤ (q₁+18)(17q₁+q₂₁)·2⁻²⁵⁶ + (q₂₁+1)q₂₂·2⁻¹⁰⁸⁸ + (q₂₂+1)q₂₃·2⁻⁴⁴⁸ + 2⁻¹²⁸ + q₁·2⁻²⁵⁶`; **`moussakaIssue_accept_le_ic'`**: Moussaka issuance with `ε_bind` explicit |
| `ROM/CipherRelations.lean` | done (M6): the other four relations with `ε_bind` explicit (`ratatouilleIssue_accept_le_ic`, `moussakaRedeem_accept_le_ic`, `ratatouilleSpend_accept_le_ic`, `pomfritRedeem_accept_le_ic`; total hash count `n + 2` for the combined ones) |
| `ROM/LogPrefix.lean` | done (M6): the log before the first query of a cell (`logBefore`), invariant under a change of the table at that cell (`logBefore_tableQueryLog_update`), order of first queries, prefix congruence |
| `ROM/ChainParse.lean` | done (M6): the proof layout offsets and parsers of the `H₂¹`, `H₂²`, `H₂³` inputs with their inverse lemmas (`xPre_chal1Input`, `yHV_chal2Input`, `zCheck_chal3Input`, …) |
| `ROM/CipherChain.lean` | done (M6): chain data read off the logs before each challenge query (`preOf`, `midOf`, `accOf`, committed dead leaves `deadOf`; committed: `chainData_committed`); the hits `chainHit` (`prEvent_chainHit_le`); Post (C3) `PostJ`, `prEvent_joint_postOut_le` `≤ 1024·q_E·q₁·2⁻²⁵⁶` |
| `ROM/CipherSame.lean` | done (M6): without hits and Post, the verifier's chain is the committed one (`chain_ident`: L1.4 ordering, `Coll₁`; `extractKey_pre_eq`); `sameChainHyp_ic` (`hsame`, L2(c)), `deadHiddenHyp_ic` (L2(a)) |
| `ROM/CipherFull.lean` | done (M6): **all five relations with no remaining hypothesis**: `moussakaIssue_accept_le_full`, `ratatouilleIssue_accept_le_full`, `moussakaRedeem_accept_le_full`, `ratatouilleSpend_accept_le_full`, `pomfritRedeem_accept_le_full` (bounds in plan §2f); combination freshness `combFreshHyp_ic` |
| `ROM/AdaptGame.lean` | done (M6, statement binding): the game with an adaptively chosen statement (`gameA`: the prover outputs a proof and a statement index; the extractor and the verifier run at that statement); per table it is the fixed game at the chosen statement (`evalWithAnswerFn_gameA`, `tableQueryLog_gameA`); Post, binding and an opened dead leaf bounded adaptively (`prEvent_joint_postOut_le_A`, `prEvent_joint_bindFail_le_A`, `prEvent_joint_deadOpen_le_A`) |
| `ROM/StmtBind.lean` | done (M6): the statement committed at a chain query, read off the log before it (`stmtAt`: the decoded first `H₂⁰` preimage of the `mu₁` field of the `H₂¹` input, followed back from `H₂²`, `H₂³` inputs); statement hits (`stmtHit`, `≤ (n₂₁+n₀)·2⁻²⁵⁶` per `H₂⁰` query); the identification `stmtAt_ident` |
| `ROM/AdaptChain.lean`, `ROM/AdaptFull.lean`, `ROM/AdaptComb.lean` | done (M6): the adaptive union bounds (`prEvent_accept_le_adaptive_E`, `…_comb_E`: each chain query charged at the statement committed there) and **the four non-delayed relations with adaptively chosen instances**: `moussakaIssue_accept_le_adaptive`, `ratatouilleIssue_accept_le_adaptive`, `moussakaRedeem_accept_le_adaptive`, `ratatouilleSpend_accept_le_adaptive`: the `_full` bound plus `stmtBindEps q = (q₀+3)(q₂₁+q₀+4)·2⁻²⁵⁶`, for instance families with injective encodings (plan §2g) |
| `ROM/AdaptPomfrit.lean` | done (M6): PomFRIT's delayed binding (`μ` in the `H₂²` input, `stmtAtD`, `stmtHitD`, `stmtAtD_ident`); transport of the bad events between statements with equal parameters (`chainBad_transport`, `combBad_transport`); `pomfritRedeem_accept_le_adaptive`: the `_full` bound plus `(q₀+3)(q₂₂+q₀+4)·2⁻²⁵⁶`, for any family of signatures and messages (the `μ` preimage determines the target, which is all the relation reads) |
| `ROM/PermModel.lean` | done (M6, permutation model): the ideal cipher as uniform random permutations (`PTable`), the prover with forward and inverse queries (`specP`); the normalized prover `normP` (inverse queries recorded as forward records, `L0-L2` N1's `H₄` query before each `H₂¹` query), its output (`evalWithAnswerFn_normP`), record congruences (`normP_prefix`, `normP_congr`) and query counts |
| `ROM/PermCount.lean` | done: two fresh values of a uniform permutation table hit one of `K` targets with probability `≤ K/((2¹²⁸−r)(2¹²⁸−r−1))` (`prEvent_perm_two_le`; double counting over the neighbours `τ ∘ σ_k`, `card_sum_mul_le`) |
| `ROM/PermBind.lean` | done: events charged at one record (`prEvent_perm_prefix_le`, forward or inverse); binding's collision event on the records, `≤ 2·q_E²·p²`, `p = 1/(2¹²⁸−q_E)` (`prEvent_perm_coll_le`) |
| `ROM/PermOpen.lean` | done: the permutation game `gameP`, the bridge `prEvent_jointP_le_add`; binding `≤ 2·q_E²·p² + ε_open`; the opened dead leaf `≤ q₁·p'²`, `p' = 1/(2¹²⁸−q_E−4607)` (`prEvent_perm_deadQueried_le_g`); `ε_open ≤ openHashEps q + q₁·p'²` |
| `ROM/PermPost.lean` | done: finding F3 (the PRF view's Post is not small with inverse queries); the point-tied Post `PostP` (half-targets of the chains, with their `iv` from N1), `≤ q_E·4608·q₂₁·p²` (`prEvent_perm_postP_le`); outside it the committed keys are found before the chain (`keysPre_of_not_postP_gen`) |
| `ROM/PermFull.lean`, `ROM/PermAdapt.lean` | done: **all five relations in the permutation model with inverse queries**, fixed statements (`*_accept_le_perm`) and adaptively chosen ones (`*_accept_le_adaptive_perm`): the PRF-view bounds with `2⁻¹²⁸` per fresh cipher value replaced by `p` (`p'` for the dead-leaf guess) and Post by `q_E·4608·q₂₁·p²`; combined relations' hash count `n + q₂₁` (plan §2h) |
| `ROM/SpecSound.lean` | done: **the 20 headline theorems for the spec relations** (`X_spec` for each `*_accept_le_full`, `*_accept_le_perm`, `*_accept_le_adaptive`, `*_accept_le_adaptive_perm`): the same bound for "the decoded witness of no known tree is in the spec relation", with only well-formedness of the instance added (`EndToEnd/SpecRelations.lean`; plan §2i) |
| `Prob/MoussakaUnbound.lean`, `ROM/MoussakaUnbound.lean`, `ROM/MoussakaUnboundAdapt.lean`, `ROM/MoussakaUnboundSpec.lean`, `EndToEnd/MoussakaUnboundSpec.lean` | done (plan §2j): **the unbound Moussaka relations**, `ε_QS(3816)` and `ε_QS(7929)`: the one-chain bounds (`moussakaUnbound*_chain_prob`), `moussakaUnbound{Issue,Redeem}_accept_le_{full,perm,adaptive,adaptive_perm}` and their `_spec` versions, stated for any statement with the unbound relations' parameters and systems (`Unbound.IssueStmt`, `RedeemStmt`) and instantiated at the executable verifier (`Unbound.moussakaUnboundIssue_stmt`, `moussakaUnboundRedeem_stmt`); `hinj` for the C++ encodings (`hinj_moussakaUnboundRedeem`, …) |
| `ROM/VerifyIC.lean`, `ROM/ExtractReduce.lean` | done (plan §2l): the executable verifier as an oracle computation over the hashes and the cipher (`verifyIC`, equal to `verify` per table, `evalWithAnswerFn_verifyIC`; reads the cipher only at its cells, `verify_congr_cells`; budget `verifierIC_verifyIC`), and the protocol-independent glue that bounds a game's event per table by single-proof events (`prEvent_bind_le_sum4_of_table`, the `j`-th prover `proverAt`) |
| `ROM/ProverIC.lean`, `Assumptions/PomClientLean.lean`, `Assumptions/BlindPomfritGrind.lean`, `Assumptions/BlindPomfritComplete.lean`, `Assumptions/BlindPomfritT6Lean.lean` | done (`pomfrit.md` G9): the Lean prover's steps 1 and 2 as oracle computations, equal per table to `Prover.voleGen` / `Prover.proveCommit` (`eval_step1Q`, `eval_proveCommitQ`; PRG calls as recorded cipher queries, `voleGenAt_congrA`, `memoF_map`); the Lean client `leanClient` (`eval_start`, `eval_finish`, `pom_complete`); the grinding bound `prEvent_grindBad_le`; the game at a table (`fail_table`); `compFail_le`, `pomfrit_T6_lean`, `pomfrit_T6_lean_bound` |
| `ROM/MoussakaOMUF.lean`, `ROM/RatatouilleBalance.lean`, `ROM/OneMore.lean`, `ROM/OneMorePomfrit.lean` | done (§5; plan §2k, §2l): Moussaka one-more unforgeability (`omuf_le_num`; the Anchor is the spec's, `anchorIC_eq_spec`), Ratatouille balance (`balance_le_ufTag`; deterministic core `no_win`), and the one-more reduction with a programmed target oracle (`real_eqd_comb`) for PomFRIT's U1 and U2 (`pomfrit_U1_bound`, `pomfrit_U2_bound`) |
| `ROM/SimUnion.lean`, `ROM/SimExtract.lean`, `ROM/SimSpec.lean`, `ROM/MoussakaOMUFSim.lean`, `ROM/RatatouilleBalanceSim.lean`, `ROM/SimJoint.lean`, `ROM/SimJointSpec.lean`, `ROM/MoussakaUnboundSim.lean`, `ROM/SimPerm.lean`, `ROM/PermJoint.lean`, `ROM/SimPermJoint.lean`, `ROM/SimPermJointSpec.lean`, `ROM/MoussakaUnboundSimPerm.lean`, `ROM/MoussakaOMUFSimPerm.lean`, `ROM/RatatouilleBalanceSimPerm.lean`, `Assumptions/SimLinks.lean` | done (plan §2m): **simultaneous extraction**. The union bound over a shared run and per-output continuations (`prEvent_le_shared_suffix`); outputs as prefix runs of a reference run (`PrefixRuns`, `proverAt_prefix`); `prEvent_sim_le`, `prEvent_sim_comb_le`; the four spec relations (`*_sim_spec`); Moussaka Thm 1 (`omuf_le_num_sim`, `_open_sim`, `_ompr_sim`) and Ratatouille balance (`balance_le_sim_num`, `_lean_sim`, `_ufTag_sim`, `_ompr_sim`), each query of the run charged once for both relations (`prEvent_sim_joint_le`, `*_sim_joint_spec`); unbound Moussaka (`moussakaUnbound*_sim_spec`, `moussakaUnbound_sim_joint_spec`; used by Thm U1's game, `omufU_le_num_sim`); permutation model per relation (`prEvent_sim_leP`, `prEvent_sim_comb_leP`) and both relations together, one normalization `normJ p_I p_R π = normP p_I π ∘ addIV p_R` (`prEvent_sim_joint_leP`, `*_sim_joint_specP`), with headline theorems for adversaries with inverse cipher queries (`omuf_le_num_simP`, `balance_le_sim_numP`, `balance_le_lean_simP`), `≈ 2⁻⁶⁰·⁵⁴` at `2⁶⁴` queries and `2³⁰` proofs as in the PRF view |
| `ROM/LemmaPDet.lean`, `ROM/LemmaP.lean`, `ROM/OneMoreLemmaP.lean`, `ROM/OneMoreLemmaP{IC,Ident,Order,Queries,Fail,Bound,Prefix,Sim}.lean`, `Assumptions/PomfritLemmaP.lean`, `Assumptions/PomfritLemmaPSim.lean` | done for U1 (plan §2n, `pomfrit.md` G8): Lemma P per chain (`majP`, `pomfritT_extract_major_chain`); its extraction and `Shift` bound for one adaptively chosen statement with any target function of `chal1` (`pomfritT_accept_le_major`); the one-more game as a lazy random oracle (`realImpl_run_eq`), `E₁` (`e1P`), and each failed forgery as an accepted proof of a derived prover (`pfail_table`, `not_noPick`); the `E`-independent derived prover (`proverP`, `proverP_bounds`), Lemma P's ordering step (`e1P_eq_major`), `pfail_events`, `prEvent_pfail_le`, `pomfrit_U1_explicit`; Lemma P's per-query bad event (`pomBad`, `prEvent_pomBad_le`, `pomBad_trace`), prefix runs (`prefix_of_pfail`), `prEvent_pfail_sim_le`, `pomfrit_U1_sim`. U2: `ROM/LemmaPSome.lean` (`pomfritT_accept_le_some`), `ROM/OneMoreShift{Table,Fail,Bound,Sim}.lean`, `Assumptions/PomfritShift{,Sim}.lean` (`pomfrit_U2_explicit`, `pomfrit_U2_sim`, `pomfrit_U2_omprShift_sim`) |
| `ROM/TableReads.lean`, `ROM/PrivacyReads.lean`, `ROM/SharedH3Reads.lean`, `ROM/SeedXOFReads.lean` | done (privacy side, §3; in `ROM/` because they import VCVio): **table-reading interactions as oracle computations**: an `OracleComp` over the tables (`TSpec`), run on them (`runT`), is a consistent table reader (`SReads`) with its syntactic query budget (`QBudget`, VCVio's `IsQueryBoundP`): `sReads_runT` (consistency by construction, `runT_congr`), `sReadsP_runT` for joint reads; a budget cannot be dropped (`not_sReads_slice`); `zk_adaptive_oc`, `lean_zeroKnowledgeROA_oc`; the games' adversaries `AdversaryOC` and the `*OC_lean_num`, `blindnessOCH_lean_num`, `*OCSh_num`, `blindnessOCHSh_num` theorems and their `_perm`, `_seed` versions (`docs/zk.md` §10.3, §10.5, §10.6) |

The phase-B theorems of `ROM/Accept.lean` hold for every CTR PRG (`[HasPrg]`) and take as
hypotheses binding (`ε_bind`), the "same chain" step with L2(c) (`hsame : SameChainHyp`), L2(a)
(`hL2 : DeadHiddenHyp`) and, for the combined relations, the freshness of the combination cell
(`hcombFresh`), each outside failure events and outside per-query "hits" whose probability is
charged by the union bound (plan §2f; the L2 interface was corrected, finding F2 of plan §2e). In
the joint random-oracle and ideal-cipher game (PRF view, forward cipher queries, fixed statement)
all of them are discharged (`ROM/CipherChain.lean`, `ROM/CipherSame.lean`, `ROM/CipherFull.lean`):
for all five relations `Pr[accept ∧ ¬Extracted]` is bounded by an explicit function of the prover's
query counts, e.g. for Moussaka issuance

    (q₂₁+1)·2⁻¹⁵⁰ + (q₂₂+1)·ε_QS(4008) + (q₂₃+1)·9·2⁻¹²⁸ + 2·q_E²·2⁻²⁵⁶
      + 2·(openHashEps q + q₁·2⁻²⁵⁶) + 1024·q_E·q₁·2⁻²⁵⁶ + chainHitEps q

with `openHashEps q = (q₁+18)(17q₁+q₂₁)·2⁻²⁵⁶ + (q₂₁+1)q₂₂·2⁻¹⁰⁸⁸ + (q₂₂+1)q₂₃·2⁻⁴⁴⁸ + 2⁻¹²⁸` and
`chainHitEps q = (q₁+18)(18q₁+q₂₁+325)·2⁻²⁵⁶ + (q₂₁+1)(q₂₁+q₂₂+2)·2⁻¹⁰⁸⁸ + (q₂₂+1)(q₂₂+q₂₃+2)·2⁻⁴⁴⁸`.
With the statement chosen by the prover (it outputs the statement with its proof; the extractor
runs on the log at that statement), the same bound plus the statement-binding term
`stmtBindEps q = (q₀+3)(q₂₁+q₀+4)·2⁻²⁵⁶` holds for all five relations
(`*_accept_le_adaptive`, `ROM/AdaptFull.lean`, `ROM/AdaptComb.lean`, `ROM/AdaptPomfrit.lean`; plan
§2g): for Moussaka issuance and redemption and Ratatouille issuance and spend for instance
families with injective encodings (`hinj`; `EndToEnd/SpecRelations.lean` proves it for families
with fixed-length fields that are injective on what the encoding hashes: `hinj_moussakaIssue_of`,
`hinj_moussakaRedeem`, `hinj_ratatouilleIssue`, `hinj_ratatouilleSpend`; for redemption and spend
the encoding hashes the keys' digests, so the family must determine its keys from their digests,
e.g. fixed keys), for PomFRIT (delayed binding, `(q₀+3)(q₂₂+q₀+4)·2⁻²⁵⁶`) for any family of
signatures and messages. **The permutation model with inverse queries** (plan §2h):
AES an ideal cipher as uniform random permutations, the prover making forward and inverse
queries, the extractor reading their records (`L0-L2` §3.1, §6): the same five fixed-statement and
five adaptive theorems hold (`*_accept_le_perm`, `*_accept_le_adaptive_perm`), e.g. for Moussaka
issuance

    (q₂₁+1)·2⁻¹⁵⁰ + (q₂₂+1)·ε_QS(4008) + (q₂₃+1)·9·2⁻¹²⁸ + 2·q_E²·p²
      + 2·(openHashEps q + q₁·p'²) + q_E·4608·q₂₁·p² + chainHitEps q,

`p = 1/(2¹²⁸ − q_E)`, `p' = 1/(2¹²⁸ − q_E − 4607)`, with no PRP/PRF switching term; Post had to be
tied to the chains' points (finding F3: the PRF view's Post fails against inverse queries).
All of this holds for unbound Moussaka's two relations too (plan §2j).

## Gaps

What is **not** established, roughly in order of importance:

1. **Most probabilistic arguments for extraction are not machine-checked.** The random-oracle,
   ideal-cipher and quantum-oracle steps of the extraction proofs are paper proofs, except for
   the parts §9 mechanizes (below). The protocol reductions for no theft (Ratatouille Thm 3) and
   redemption non-malleability (Moussaka Thm 3) are mechanized as games on the specs in the
   zero-knowledge table model (`Theft/`, `noTheft`, `noRedirect`; with the Lean prover's zero
   knowledge `noTheft_lean`, `noRedirect_lean`): `Pr ≤ ε_I + ε_S + δ + ε_SE + Adv^ow` for one honest
   Client; for Moussaka and unbound Moussaka also for `U` honest tokens and `M` honest
   redemptions (`noRedirectN`, `nmUN`), and Ratatouille no theft for `U` Clients and `M` spends
   (`noTheftN`), with `WeakSEN` in place of `WeakSE2`; for these the hops' read budgets are proved
   and `WeakSEN` is reduced to plain extraction and per-proof programmed-point terms
   (`*_lean_reads`, `*_lean_plain`, `Theft/ManyReads.lean`, `Theft/ManyPlain.lean`). The hops' read budgets are proved from the adversary's and the
   extractor's budgets, with the Lean verifiers (`noTheft_lean_reads`, `noRedirect_lean_reads`;
   `Theft/Reads.lean`). L8's programming step is mechanized: `WeakSE2 ≤ ε_plain + ε_hit` for an
   extractor that does not read `H₂³` (`weakSE2_of_plain`); the Lean verifier reads `H₂³` only at
   `chal3`'s input (`verRO_h23_eq`), so `ε_hit` is the probability that a fresh forgery's grinding
   prefix equals a simulated proof's (`accOp_moves`), giving `noTheft_lean_plain` and
   `noRedirect_lean_plain` (`Theft/SimExtract*.lean`). The theft theorems also hold with `H₁`, `H₂⁰…H₂²`, `H₄` and `H_comb` read
   off uniform tables: the zero-knowledge hops, the read budgets and the programming step hold for
   every base hash record (`Theft/LeanHb.lean`, `noTheft_leanH_plain`, `noRedirect_leanH_plain`) and
   lift, by averaging over one more shared table (`zkRO_tables`), to `noTheft_leanX_plain` and
   `noRedirect_leanX_plain` (`Theft/Tables.lean`), with the same bound. For Ratatouille `ε_hit` is
   bounded there: with `XTab L M` (`L ≥ 14357`) and a last stage reading the chain tables `H₂⁰`,
   `H₂¹`, `H₂²` by decision trees with `q_μ`, `q₂₁`, `q₂₂` queries (`AdmHit`), `noTheft_leanX_hit`
   (`Theft/HitChain.lean`, `Theft/Hit.lean`, `Theft/HitTheft.lean`) has `Pr[Bad] ≤ εz(pI;q) +
   εz(pS;q) + δ_S + ε_plain + 2·((q_μ+3)·2⁻²⁵⁶ + (q₂₁+3)·2⁻¹⁰⁸⁸ + (q₂₂+3)·2⁻⁴⁴⁸) + Adv^ow`: a hit
   meets the simulated chain at a first level where the inputs differ and the outputs agree
   (`chain_hit`, `qtree_forger`, `pr_hit_le`). Freshness is under the adversary's key (`FreshOk`),
   because the Lean spend statement does not hash `pk`; in the game this is the game's freshness
   (`freshOk_stS`). `ε_hit` for Moussaka (non-injective `t ‖ ctx_iss`, unbounded instances) and
   for the many-client theorems is not done, and plain extraction stays a hypothesis. `ROM/`'s extraction bounds do not carry over as they stand: `PlainSE`'s
   extractor does not see the adversary's queries (an adversary that derives its GGM key from an
   `H₂³` answer is not extractable by it, so the `_plain` theorems say nothing for such
   adversaries), read budgets are certificate sizes and not query bounds, a cipher read is a row and
   not a cell, and `ROM/`'s oracle is lazy (`docs/security/ratatouille.md` §5). `Adv^ow` stays the advantage of the explicit inverter, a computational
   assumption on Keccak-p[800,12]: `Com` is evaluated inside the relations, so it cannot be a table
   of the game, and some inverter wins with probability 1 (`owAdv_one_ratatouille`,
   `owAdv_one_moussaka`). In a random-table model of the standalone experiment a `q`-query
   inverter has advantage `≤ (q+2)·2⁻¹²⁶` (Ratatouille, `owAdvColRO_num`) and
   `≤ (q+2)·2⁻¹²⁸ + (q+1)·2⁻³⁶⁰` (Moussaka, `owAdvRO_num`). Ratatouille's N2a holds only in its extraction
   form: a relay can burn an honest nullifier by squatting (`security/ratatouille.md` §3). Moussaka's unforgeability and Ratatouille's balance are mechanized with simultaneous
   extraction (`omuf_le_num_sim`, `balance_le_sim_num`; plan §2m). One difference from the paper
   remains: the cipher-side failure terms (binding, opened dead leaf, Post) stay per proof (`m·failEps`,
   negligible at `2⁶⁴` queries). PomFRIT's U1 is mechanized with Lemma P's term bounded
   (`pomfrit_U1_explicit`, and with simultaneous extraction `pomfrit_U1_sim`), and so is U2
   (`pomfrit_U2_sim`; plan §2n, `docs/security/pomfrit.md` G8). U1 with the class extractor (`2⁻⁷⁸` per `H₂³` query instead of `2⁻⁷¹`) is paper with a mechanized per-chain core; the one-more game with `E₁^cls` is open (`pomfrit.md` G8-cls). For zero knowledge and privacy with the fix, the classical random-oracle
   and ideal-cipher arguments are mechanized (§3, Gap 7). The quantum arguments are paper proofs;
   mechanizing them is beyond current tools.
   For the Lean verifier (§8), what the end-to-end extraction theorems still assume about the
   executable verifier is exactly these steps: a good `chal1` (L3's `KOSGood`), fixed blocks for
   dead-leaf trees (L2), good `chal2`/`l` (L4's `hQS`, `hcomb`), and binding of the leaf
   commitments with accepted `chal3` landing in the chain's set (L1); `Verifier/Bridge/ChainRelations.lean`.
   §9 machine-checks the single-challenge part: for one chain with uniform independent `chal1`,
   `chal2`, `l`, the L3 and L4 failures have probability `≤ 2⁻¹⁵⁰ + ε_QS(n) + 2⁻¹²⁸`
   (`Prob/ChainRelations.lean`), and, in the random-oracle model, the union over all `H₂¹`, `H₂²`,
   `H₂³` queries with the freshness of `chal2 ‖ dst`, for the executable verifier run against the
   oracle (`ROM/`): "accepts and extraction fails" has probability `≤ (q₁+1)·2⁻¹⁵⁰ +
   (q₂+1)·(ε_QS(n) + 2⁻¹²⁸ + (n+337)·2⁻⁴⁴⁸) + (Q+1)·max(d,1)·2⁻¹²⁸ + ε_bind + ε_dead + ε_chain`,
   also against one SHAKE oracle with L0's domain rule. In the joint random-oracle and
   ideal-cipher model (PRF view, forward cipher queries, fixed statement) the remaining terms are
   mechanized too: binding (`ε_bind`), the "same chain" step (`ε_chain`: L1.4's ordering, `Coll₁`,
   Post/C3) and L2 (`ε_dead`, with the corrected interface of plan §2e F2), so all five relations
   have a bound with no hypothesis beyond the query bounds and well-formed instances
   (`ROM/CipherFull.lean`, plan §2f), and for adaptively chosen statements with the
   statement-binding term `(q₀+3)(q₂₁+q₀+4)·2⁻²⁵⁶` added (`*_accept_le_adaptive`, plan §2g;
   Moussaka and Ratatouille for instance families with injective encodings, `hinj`, proved for
   families with fixed-length fields injective on the hashed fields, `EndToEnd/SpecRelations.lean`);
   both also with AES as random permutations and inverse cipher queries (`*_accept_le_perm`,
   `*_accept_le_adaptive_perm`, plan §2h; no PRP/PRF switching term), and all of them also for the
   spec relations (`*_spec`, `ROM/SpecSound.lean`, plan §2i). All of this holds for the two
   unbound Moussaka relations too, with 3816 and 7929 constraints in `ε_QS`, instantiated at the
   executable verifier (`Unbound.moussakaUnboundIssue_stmt`, `moussakaUnboundRedeem_stmt`;
   `Prob/MoussakaUnbound.lean`, `ROM/MoussakaUnbound*.lean`, `EndToEnd/MoussakaUnboundSpec.lean`;
   plan §2j).
2. **Code ↔ model is tested, not proved.** Each Lean model was written by reading the C++ and is
   tied to it by tests in `tests/voleith/test_lean_models.cpp` (and, when finished, the `Arith`
   cross-check). Compiler behaviour, memory safety and constant-time execution are out of scope.
3. **Arithmetization: small leftovers.** All seven relations (the five base relations and
   unbound Moussaka's two) are modelled and proved (§6), and
   pqov's `ov_publicmap` is proved equal to the modelled public map over any commutative ring
   (`Arith/Pqov.lean`). The soundness corollaries are proved over an abstract field and
   instantiated at the concrete GF(2¹²⁸) with all hypotheses discharged (`Arith/ConcreteField.lean`,
   `EndToEnd/Concrete.lean`); the verifier's evaluators are proved to be the systems' values
   (`Verifier/Bridge/Relations.lean`), and agreement with the C++ is checked by `arith_vectors`. pqov's
   constant-time `ov_publicmap_ct`, which the code calls, is checked against `ov_publicmap` by the
   dumper, not modelled. The step "`l` is uniform because it is a random-oracle output" is proved in
   the random-oracle model (`ROM/Comb.lean`), for `l` read from the oracle table, which is where the
   verifier reads it (`ROM/Accept.lean`).
4. **Idealized models.** AES-128 is an ideal cipher (classical and quantum), SHAKE and Keccak-p are
   random oracles or random permutations. The Keccak-p[800,12] relations additionally need
   one-wayness/binding assumptions on a 12-round permutation that have little cryptanalysis.
5. **New assumptions.** All three protocols rest on one-more-UOV (OMPR, Def. 3.1 with
   `derive_preimage`), and the map from the protocol-specific notions to it is in
   `docs/security/uov-assumptions.md`, partly in Lean (`Assumptions/`). What remains:
   - OMPR itself is not expected to follow from the UOV problem (`uov-open-structure.md` Part A),
     so it needs its own cryptanalysis; the GPI route (loss `q`) rests on a conjecture (Part B).
     A first cryptanalysis of OMPR and OMPR⊕17 with the oracle is in
     `docs/security/ompr-cryptanalysis.md`: no oracle-aided attack beats the direct forgery attack on
     UOV; Conjecture A6 reduces to its forgery-side form (collinear shifts, at most `2^4.1`).
   - The Lean chains to OMPR idealize `Com` and `Tag` in the standalone games. For Moussaka and
     unbound Moussaka the idealization can be a random permutation of the 800-bit KP800 blocks
     with inverse queries (hypothesis `hmodelP`; `omuf_le_num_ompr_perm`,
     `omufU_le_num_ompr_perm`, `Assumptions/PermLinks.lean`), with the permutation terms
     `(q_f+q_i+q_S+1)²·2⁻⁸⁰⁰ + q_i·2⁻²²⁴` explicit (`Assumptions/CTUFPerm.lean`,
     `advCTUFPermAt_le_ompr`; the PRP/PRF switch with inverse queries in
     `Assumptions/LazyPerm.lean`; the lazy permutation is taken as the ideal one). T4's paper
     birthday term left out inverse queries (corrected, `uov-assumptions.md` §5.4). For
     Ratatouille's `Tag` only the switch to the hybrid is in Lean (`advFDHPerm_le_hyb`,
     `Assumptions/FDHPerm.lean`); the chain still uses `TagIdeal` (a random function). PomFRIT's
     U1 and U2 with AES as random permutations with inverse queries are not done.
   - PomFRIT's tight bound needs OMPR⊕17; OMPR ⇒ OMPR⊕17 without the `τ^{q+1}` loss has no
     black-box proof (`uov-open-reductions.md`); by Theorem R (`ompr-shift-algebra.md`; Lean `thmR`) a
     proof must be non-black-box in the adversary or break OMPR^free. In Lean every term of
     Theorem R is explicit (`thmR_V4`), and so is Corollary R′ (`corR'`).
   - T6 at PomFRIT is in Lean for the Lean client, completeness term included
     (`pomfrit_T6_lean`, `(ℓ+1)·2⁻¹¹³`; `pomfrit.md` G9); the converse of `advOMPR_le_ompr31` is not in Lean.
   - The quantum protocol theorems need quantum-oracle versions of these assumptions, which are
     new.
6. **Quantum bounds stop at about 2⁶⁰ queries, the Grover limit of the q²/2¹²⁸ term.** The AES
   binding term no longer limits them (Q6 Theorems 4–5, 4′–5′; paper proof, new, reviewed in Q6 §14 but
   not externally; numeric cores and toy checks only are machine-checked). A tight point-level bound
   (Q6 §7.3, M1/M2; conjectured Θ(q³/2²⁵⁶)) is still unknown but would change no number here.
   Parallel quantum queries are not treated.
7. **Zero knowledge on `main` rests on (PU) for Moussaka and Ratatouille.** PomFRIT's ZK failure is
   fixed on `main` since `64fd1a4` (dedicated label rows for PomFRIT). For Moussaka and
   Ratatouille on `main`, ZK rests on (PU), i.e. on the one-wayness of Keccak-p[800] in `r`
   (except towards a Moussaka Moderator that never sees `t`); the bad-event bound is in Lean
   (`ZK/Main.lean`, `ZK/Relations.lean`), and so is the hybrid chaining around it (H1–H4, the
   H5/H6 coupling for one proof and jointly for a token's proofs, the oracle adversary as read
   sets; `ZK/HopsMain.lean`, `ZK/MainGame.lean`; `docs/zk.md` §4.2), with per-proof tables;
   for one proof the shared-table model with `H₂³` visible and a global cipher is mechanized on
   `main` (`zk_rom_ic_h23_main`); (PU) is a game (`PU.puAdv`), Moussaka's (PU) term is the
   advantage of explicit predictors in it (`anonymity_main_pu`), and it is bounded in the
   ideal-permutation model (`puAdvPerm_moussaka_le`, `puAdvPerm_ratatouille_le`). Not done: the
   joint hop over several proofs on shared tables (`ε_iv`), Ratatouille's `puTermR` as `puAdv`,
   and (PU) for the real 12-round permutation (an assumption; the exhaustive predictor has
   advantage 1). The QROM ZK bound
   is loose (2⁻¹⁹ at 2³⁰) until the 256-bit `rho` and salt are added.
   With the fix, zero knowledge of the executable Lean prover and the three protocols' privacy
   games are mechanized in the classical random-oracle and ideal-cipher model, with every
   zero-knowledge and collision term explicit, AES's rows functions or permutations, one shared
   `H₃` and the real Clients' seeds, and with many sessions (§3). What remains is the list at the
   end of §3: SHAKE as a random oracle and AES as an ideal cipher, the composition of Lemma DS (c)
   for PomFRIT's seed XOF (mechanized on the single SHAKE oracle) with the games' separate tables,
   hiding of `Com` (computational), consistency of interactions given as bare functions of the
   tables, PomFRIT's `H₂³`-reading Issuer under per-slice budgets, Moussaka's non-colluding abort
   term for a fixed key (bounded on average over uniform `P2` parts of pqov's keys only) and a
   table-reading setup in its shared-`H₃` game, a second challenge Client whose key is chosen after
   the first one's request in the Moussaka games (the only input that can differ; no request reads
   it, so this is a mechanical but stack-wide generalization, not done) and the factor about 2 of
   the interleaved Moussaka and Ratatouille bounds; for `N` challenge pairs, linearity is
   mechanized up to one bad event: PomFRIT with `H₄` a table (`blindnessPH_lean`, up to the `iv`
   birthday term `n²·2⁻¹²⁵`), Moussaka and Ratatouille with the other pairs moved to private tables
   by `pr_split_le` (`anonymityP_lin`, `unlinkabilityP_lin`), with the bad event
   `β ≲ 64(N − 1)·2⁻¹²⁸` on paper (it needs `H₄` a random oracle; in the Lean games `H₄` is SHAKE);
   and the quantum versions.
   The abstract privacy theorems (`VoleMole/Privacy/`) take per-proof zero knowledge and hiding of
   `Com` as hypotheses, so they apply to any proof system with the label-row fix; on `main` the
   joint (PU) hop over proofs sharing `r` replaces the per-proof hypothesis: `anonymity_main`,
   `unlinkability_main` (Moussaka 4(a) and Ratatouille; 4(b), the `find_issuer` Client and unbound
   Moussaka's U5 are not done on `main`). Every
   deterministic side condition for the Lean prover is proved (the witness encodings satisfy the
   systems, interpolation, `N_MASK`, the CRT certificate, BAVC and CRT completeness:
   `Privacy/MoussakaLean.lean`, `Privacy/RatatouilleLean.lean`, `Privacy/PomFRITLean.lean`,
   `Verifier/Bridge/BAVCComplete.lean`, `Verifier/Bridge/CrtComplete.lean`).
8. **Open deployment issues** found by the analysis and not yet fixed in the code: cross-protocol
   key reuse, Ratatouille spend binding, PomFRIT's `hash_to_target` domain byte and signature
   multiplicity, Moussaka nullifier squatting, and the README's missing guidance that a VOLE-IHAT
   nullifier record must span every accepted Anchor Set (F8).

Some notes in `docs/` were written at different times and may contain status lines that later
notes superseded. Where they disagree, `extraction/README.md` and this file are the most recent;
for zero knowledge and privacy, `docs/zk.md` §10 is the detailed reference.
