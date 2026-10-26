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
| **[Lean]** | Machine-checked in `VoleMole/`. No `sorry`, no `axiom`, no `native_decide`; `#print axioms` shows only `propext`, `Classical.choice` and `Quot.sound`. Covers the deterministic steps (linear algebra, counting, polynomial degrees, combinatorics, numeric bounds) and some probabilistic ones: the single-challenge and random-oracle bounds for extraction (§9), and zero knowledge and the protocol privacy theorems in the classical random-oracle and ideal-cipher model (§3). |
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
- *Extraction* (§1, §6, §9). For all five relations, the executable Lean verifier "accepts and
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
    (Moussaka 4(b): its adversary's choices do not read the tables);
  - PomFRIT, Moussaka 4(a) and Ratatouille with any number `n` of further honest sessions,
    concurrent, adaptively scheduled or interleaved in any order by a scheduler that reads the
    tables: linear in `n`, at most about `n·2⁻¹⁰¹` (`2⁻⁸¹` at `n = 2²⁰`, `2⁻⁶⁹` at `2³²`;
    Ratatouille's interleaved bound counts proofs) plus budget terms;
  - the same three with `N` challenge pairs: quadratic, an artifact of the proof (`2⁻⁶³` at
    `2²⁰` sessions; PomFRIT with `H₄` a table `N·2⁻¹⁰³ + 32·N²·2⁻¹²⁸`);
  - Moussaka 4(a) and Ratatouille also carry `2·εhide`, the hiding of `Com`, a computational
    hypothesis; Moussaka 4(b) carries the Anchors' abort term, `≈ 2⁻²⁹³·⁸` with pqov's signer on
    average over pqov's keys (not for a fixed key);
  - Moussaka's random-oracle games model the Client of the API before `21be618`, which took its
    issuer's index from an index rule; `main`'s Client finds the index itself (`find_issuer`).
    Thm 4(a) and 4(b) for it are proved from per-proof zero knowledge (`Privacy/MoussakaFind.lean`,
    `MoussakaNCFind.lean`; 4(b) for Anchor Sets containing both issuers), not yet in the
    random-oracle model.
- *Audits* (§3, "Audits"). Every headline theorem's hypotheses are instantiated
  (`Audit/Nonvacuous.lean`), and every privacy game's honest path is shown to reach its
  challenge outputs (`Audit/Liveness.lean`).
- *Also*: the PomFRIT attack on `main` and the (PU) bound for the others (§3); the deterministic
  cores of the protocol notes (§5); arithmetizations of all five relations (§6); executable
  specs, verifier and prover that match the C++ KATs (§7, §8).

**On paper only**: the unforgeability, balance, no-theft and non-malleability reductions of the
protocols (§5), strong simulation-extractability beyond its Lean core (§2), every quantum
statement (§4, `docs/zk-qrom.md`), Lemma DS (c), a bound linear in `N` for `N` challenge pairs
(`docs/zk.md` §10.8), and ZK on `main` beyond the bad-event bound.

**Modelling assumptions**: SHAKE128/256 are random oracles, AES-128 is an ideal cipher (classical
and quantum); Keccak-p[800,12] one-wayness and binding/hiding of `Com` (computational: `Com` is
evaluated inside the proofs, so no random-oracle bound applies to it, §3); for Moussaka 4(b)'s
averaged abort term, the `P2` part of pqov's keys uniform; the protocol-specific UOV assumptions
(§5, Gap 5); the Lean models are tied to the C++ by tests, not proofs (Gap 2).

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
                            the executable verifier against the oracle, domain separation, and
                            the privacy games' adversaries as oracle computations
    Privacy/                privacy games on the executable specs (blindness, issuer hiding,
                            unlinkability): with zero knowledge and hiding as hypotheses, and
                            for the Lean prover in the random-oracle and ideal-cipher model
    Audit/                  non-vacuity checks: the headline theorems' hypotheses instantiated,
                            and the games' honest paths shown to reach the challenge outputs
  vectors/                  test vectors dumped by the C++ for the Arith/ cross-check
  docs/
    sketch.md               the maintainer's original design note
    lean-correspondence.md  sketch item → Lean name, and code-correspondence findings
    extraction/             proof of knowledge, simulation-extractability, quantum versions
      README.md             the main theorems and how the lemmas assemble (start here)
      L0-…L8-*.md           classical lemmas
      Q1-…Q7-*.md           quantum (QROM) lemmas
    zk.md, zk-qrom.md       zero knowledge, classical and quantum
    security/               protocol-level security notes
```

All `file:line` citations in `docs/` are relative to the repository root. Most refer to commit
`6d7113e` (`main` before `64fd1a4`, which moved PomFRIT to dedicated label rows); those about the
zero-knowledge fix refer to commit `d5def9c` of branch `voleith-label-rows` (opt-in flag
`CRT_DEDICATED_LABEL_ROWS`; merged as `64fd1a4` with the opt-out `REUSE_CRT_WITNESS` instead, the
branch since force-pushed to that version), and those about `21be618` (the Client finds its
Anchor) to `main`.

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
| L3 | KOS consistency check forces affine VOLE correlations (ε_KOS ≈ 2⁻¹⁵⁴) | [paper] + [Lean] `Seed/KOS.lean` + [test] |
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
proof (`pomfrit_issuer_hits`, `pomfrit_attack_test`). Still [paper]: H1–H4, H8, the
identical-until-bad coupling of H5 and H6 and the reduction of an oracle adversary to the query
functions (`docs/zk.md` §4.1, "Still on paper").

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
- *Lemma DS (c)*: the independence of PomFRIT's seed XOF from the proof-system domains it
  overlaps (F-DS2) is on paper. (For Moussaka and Ratatouille the seed domains are disjoint from
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
- *Moussaka's non-colluding mode* in the random-oracle and ideal-cipher model
  (`anonymityNCRO_lean_num`, `anonymityNCSh_num`, with seeds `*_seed`) has a table-oblivious
  adversary interaction (no `RA`/`OC` version).
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
    one's request (the privacy notions fix the challenge inputs first, and so do the two-session
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
  - a bound linear in `N` for `N` challenge pairs: for Moussaka and Ratatouille at all, for PomFRIT
    without the `iv` birthday term and with the budget terms charged once (one joint bad event over
    all proofs, the gate labels' distribution);
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
| Q6 | Binding of AES leaf commitments for all q; tightness of key-level techniques | [paper] + [Lean] `Seed/CipherBinding.lean` |
| Q7 | Extraction from many proofs at once; quantum versions of the protocol theorems | [paper] + [Lean] `Seed/QMulti.lean` |

**Numbers.** Total extraction failure: 2⁻⁶⁰·⁴ at 2³⁰ quantum queries, 2⁻⁴⁰·² at 2⁴⁰, 2⁻²³·³ at 2⁴⁵,
vacuous beyond about 2⁵¹·⁷. Up to about 2⁴¹ the bound is dominated by the q²/2¹²⁸ term that Grover
search makes unavoidable for any 128-bit scheme. Beyond that, the AES binding term (a proof
limitation, not an attack) takes over. Strong simulation-extractability: 2⁻⁶⁰·⁴ at 2³⁰ queries and
2³⁰ simulated proofs.

### 5. The protocols — `docs/security/`

| Note | Main results | Main findings |
|---|---|---|
| `pomfrit.md` | One-more unforgeability (classical: proved; quantum: Q7, under new quantum UOV assumptions). Blindness: **fails on `main`**, proved with the ZK fix. | The paper's reduction has a gap (its first-phase extractor is not well defined for multi-tree VOLEitH), repaired by Lemma P at a 2⁻⁷¹ per-query loss ([Lean] `Protocols/PomFRIT.lean`). A holder can make many valid signatures per message (non-minimal grinding counter): deduplicate on the message. |
| `moussaka.md` | One-more unforgeability, double-spend detection, redemption non-malleability, issuer hiding: proved. | Nullifier squatting (low). The draft's one-more-UOV argument is invalid as written; restructured. |
| `moussaka-unbound.md` | Unbound tokens (late `ctx_red` binding, PR #63): one-more unforgeability per `(ctx_iss, ctx_red)`, nullifier determinism, redemption non-malleability (including redirection to another `ctx_red`), issuer hiding and unlinkability, also across redemption contexts. Proved on paper; [Lean] arithmetization soundness and completeness (`Arith/MoussakaUnbound.lean`), the deterministic cores and the ideal-world swap invariance (`Protocols/MoussakaUnbound.lean`), domain separation. | Squatting is no longer possible (fixes the base note's F2). Privacy against non-colluding Moderators now needs a PRF assumption on Keccak-p[800,12]. A token keeps no record of the contexts it was redeemed in. Extraction and verifier statements for the two relations are not mechanized. |
| `ratatouille.md` | Balance (no inflation), no theft, unlinkability, correctness: proved. | Spends are not bound to a session, so a copied spend request can be redeemed first (medium). |
| `domain-separation.md` | Every hash/XOF/permutation call lies in a disjoint domain, except below. [Lean] `Protocols/DomainSeparation.lean` | PomFRIT's `hash_to_target` overlaps four proof-system domains (no exploit found; fix: a final domain byte). |
| `uov-assumptions.md` | Relates the protocol-specific UOV assumptions to each other and to standard UOV. [Lean] `Protocols/UOVAssumptions.lean` | Several reductions are unavailable; the note states why. |
| Privacy on the specs ([Lean] `VoleMole/Privacy/`) | The privacy theorems as games on `Spec/*`, each hybrid hop mechanized, from per-proof zero knowledge (`Privacy.ZeroKnowledge`: a simulator from the instance alone, `ε`-close for every valid witness) and, for Moussaka 4(a) and Ratatouille, hiding of `Com` for explicit reductions: PomFRIT blindness (`Privacy.PomFRIT.blindness`, `≤ 4ε`); Moussaka issuer hiding and unlinkability against a Moderator colluding with all Anchors (Thm 4a, `Privacy.Moussaka.anonymity`, `≤ 4εI + 4εR + 2εhide`) and against one that sees no issuance (Thm 4b corrected, `Privacy.Moussaka.anonymityNC`, `≤ 4εR + 2·(φ₀ + φ₁)`, no assumption on `Com`), both also for `main`'s Client that finds its Anchor itself (`Privacy.MoussakaFind.anonymity`, `.anonymityNC`; the other Moussaka games take the index-taking Client of the API before `21be618`); Ratatouille unlinkability of spends from issuances and from each other through change tokens (`Privacy.Ratatouille.unlinkability`, `≤ 4εI + 4εS + 2εhide`). With the executable Lean prover (label rows) down to its tape hypothesis (`*_label_rows`, `blindness_lean`; `*_shake` with the hop hypotheses); for 4(a), Ratatouille and PomFRIT also in the random-oracle and ideal-cipher model with every zero-knowledge term explicit (`*RO_lean_num`), with table-reading interactions (`*RA_lean_num`, `blindnessRAH_lean_num`, `*OC*`), with AES as random permutations (`_perm`), with one shared `H₃` (`*Sh_num`, `blindnessRAHSh_num`) and from the real Clients' seeds (`*_seed`); Moussaka 4(b) also in the random-oracle and ideal-cipher model (`anonymityNCRO_lean_num`, `anonymityNCSh_num`, with `_seed`), with pqov's signer (`anonymityNC_pqov`, `anonymityNCRO_pqov`; averaged over pqov's keys `anonymityNCRO_pqov_pqovKeys`, abort term `≈ 2⁻²⁹³·⁸`; the model equals the C++ `derive_preimage` on the KAT targets, `spec_kats`) and reaching redemption (`pr_refused_NCRO_le`); 4(a) and Ratatouille also with table-reading key stages (`anonymityRAK_lean_num`, `unlinkabilityRAK_lean_num`); 4(a), Ratatouille and PomFRIT also with many sessions (`*N_lean_num`, `*P_lean_num`, `blindnessPH_lean`, `blindnessAd_lean_num`, `anonymityAd_lean_num`, `unlinkabilityAd_lean_num`; interleaved schedules, Ratatouille's further Clients spending several times: `blindnessIL_lean_num`, `anonymityIL_lean_num`, `unlinkabilityIL_lean_num`; with a table-reading scheduler and a free challenge: `blindnessILO_lean_num`, `anonymityILO_lean_num`, `unlinkabilityILO_lean_num`). Bounds and what remains: §3 | The zero-knowledge hypothesis is false on `main` for PomFRIT (`ZK.pomfrit_issuer_hits`, `ZK.pomfrit_attack_test`); for Moussaka and Ratatouille no efficient simulator satisfies it per proof on `main`, and the joint (PU) hop replaces it (paper). PomFRIT note §8.3: the "both ⊥" rule is needed. Moussaka Thm 4(a) needs no `2⁻¹⁹²` term; Thm 4(b) misses an abort term `2·(φ₀ + φ₁)` (negligible, bounded with no assumption on `Com`), needs the Client to take its index from `S`, and needs no `2⁻¹⁹²` term either. Its Lean random-oracle games were vacuous until they used the label-row Anchor (fixed); with pqov's signer its abort term is bounded only on average over the keys (§3). Ratatouille H3 needs the Client's validity check against the commitment it sent. Ratatouille's H1 misses the seed collisions, and Moussaka's Thm 4 has no term for the seed-XOF hop (`docs/zk.md` §10.6) |

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

## Gaps

What is **not** established, roughly in order of importance:

1. **Most probabilistic arguments for extraction are not machine-checked.** The random-oracle,
   ideal-cipher and quantum-oracle steps of the extraction proofs, and the protocol reductions
   for unforgeability, balance and non-malleability, are paper proofs, except for the parts §9
   mechanizes (below). For zero knowledge and privacy with the fix, the classical random-oracle
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
   spec relations (`*_spec`, `ROM/SpecSound.lean`, plan §2i).
2. **Code ↔ model is tested, not proved.** Each Lean model was written by reading the C++ and is
   tied to it by tests in `tests/voleith/test_lean_models.cpp` (and, when finished, the `Arith`
   cross-check). Compiler behaviour, memory safety and constant-time execution are out of scope.
3. **Arithmetization: small leftovers.** All five relations are modelled and proved (§6), and
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
5. **New assumptions.** The protocol proofs use protocol-specific UOV assumptions (one-more
   preimage resistance and variants; chosen-target unforgeability for Moussaka). The quantum
   protocol theorems need quantum-oracle versions of these that are new. Whether standard OMPR
   implies the τ-shift variant used for PomFRIT's tight bound is open.
6. **Quantum bounds stop at about 2⁵¹·⁷ queries.** Going further needs a point-level
   multi-collision lemma for the compressed ideal cipher (M1–M3 in `Q6-cipher-binding.md` §7.3);
   none is known. Parallel quantum queries are not treated.
7. **Zero knowledge on `main` is false** for PomFRIT, and the fix is on a branch. For Moussaka and
   Ratatouille on `main`, ZK rests on (PU), i.e. on the one-wayness of Keccak-p[800] in `r`
   (except towards a Moussaka Moderator that never sees `t`); the bad-event bound is in Lean
   (`ZK/Main.lean`, `ZK/Relations.lean`), but the hybrid chaining around it (H1–H4, the H5/H6
   coupling, the reduction of an oracle adversary to query functions) is paper. The QROM ZK bound
   is loose (2⁻¹⁹ at 2³⁰) until the 256-bit `rho` and salt are added.
   With the fix, zero knowledge of the executable Lean prover and the three protocols' privacy
   games are mechanized in the classical random-oracle and ideal-cipher model, with every
   zero-knowledge and collision term explicit, AES's rows functions or permutations, one shared
   `H₃` and the real Clients' seeds, and with many sessions (§3). What remains is the list at the
   end of §3: SHAKE as a random oracle and AES as an ideal cipher, Lemma DS (c) for PomFRIT's seed
   XOF, hiding of `Com` (computational), consistency of interactions given as bare functions of
   the tables, PomFRIT's `H₂³`-reading Issuer under per-slice budgets, Moussaka's non-colluding
   mode with table-reading choices and its abort term for a fixed key (bounded on average over
   uniform `P2` parts of pqov's keys only), a second challenge session chosen after the first one's
   request in the interleaved games, a bound linear in `N` for `N` challenge pairs (on paper; the Lean `N`-pair bounds are quadratic,
   for PomFRIT with `H₄` a table only through the `iv` birthday term `n²·2⁻¹²⁵`), and the quantum
   versions.
   The abstract privacy theorems (`VoleMole/Privacy/`) take per-proof zero knowledge and hiding of
   `Com` as hypotheses, so they apply to any proof system with the label-row fix; on `main` the
   joint (PU) hop over proofs sharing `r` replaces the per-proof hypothesis and is paper. Every
   deterministic side condition for the Lean prover is proved (the witness encodings satisfy the
   systems, interpolation, `N_MASK`, the CRT certificate, BAVC and CRT completeness:
   `Privacy/MoussakaLean.lean`, `Privacy/RatatouilleLean.lean`, `Privacy/PomFRITLean.lean`,
   `Verifier/Bridge/BAVCComplete.lean`, `Verifier/Bridge/CrtComplete.lean`).
8. **Open deployment issues** found by the analysis and not yet fixed in the code: cross-protocol
   key reuse, Ratatouille spend binding, PomFRIT's `hash_to_target` domain byte and signature
   multiplicity, Moussaka nullifier squatting.

Some notes in `docs/` were written at different times and may contain status lines that later
notes superseded. Where they disagree, `extraction/README.md` and this file are the most recent;
for zero knowledge and privacy, `docs/zk.md` §10 is the detailed reference.
