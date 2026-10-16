# Straight-line extraction for vole-mole's VOLEitH proofs

This directory holds the proof that the VOLEitH proof system in `src/voleith.hpp`, as instantiated
by the repo's five relations, is a straight-line **proof of knowledge** for the relations' stated
statements. It also covers simulation-extractability.

It builds on the "Full-witness straight-line extraction" section of `lean/docs/sketch.md`, with these
changes:
- AES is modelled as an ideal cipher rather than as a random oracle on seeds.
- The repo's (EM) error terms are used.
- Constraints that depend on chall₂ are handled.
- The relations' arithmetization is proved sound.

Lean proofs live in `lean/VoleMole/SeedExtraction.lean` and `lean/VoleMole/Seed/`.

Status legend: **[Lean]** machine-checked; **[paper]** written proof in this directory;
**[open]** not done.

## Model

- **Hashes.** Every SHAKE-based hash in the protocol is an independent random oracle, made
  independent by domain separation (Lemma L0). This covers H₁ (leaf and tree commitments), H₂⁰…H₂⁴,
  H₃, H₄, H₅, and the UOV combination hash `l = H(chall₂ ‖ dst)`.
- **AES.** AES-128 is an ideal cipher `E : {0,1}¹²⁸ × {0,1}¹²⁸ → {0,1}¹²⁸`, a uniformly random
  permutation for each key. The adversary may query it forward and inverse. Every protocol use of
  AES is `aes_ctr_prg`: block `c` of `PRG(k, iv, twk)` is `E_k(iv ⊞ (c, 0, 0, twk))`.
- **Prover and extractor.** The prover `P*` makes `q` oracle queries in total, `Q` of them to H₂³
  (grinding attempts included). The extractor sees the statement, `P*`'s output and the list of
  `P*`'s oracle queries. It does not program the oracles and does not rewind.
- **Parameters.** These are those of all repo relations: FAEST-EM-128f VOLEitH, i.e. λ = 128,
  τ = 17, w_grind = 8, n_Δ = 120, `one_tree` BAVC, the `aes_ctr` leaf commitment
  `com_{i,j} = PRG(k, iv, i+L−1)[0..2λ)` with seed `sd_{i,j} = k`, and the CRT VOLE.
  - QuickSilver degree `d` is 2 for PomFRIT and 9 for the Keccak-based relations.
  - The witness has ℓ bits.

Notation follows `lean/docs/sketch.md` and `lean/VoleMole/SeedExtraction.lean`. A challenge's decoded blocks
are `Δ' = (Δ_i)_{i<τ}`. The CRT lift is `e(Δ') = W_crt·Δ' = Δ ∈ F_{2^λ}`, and `e_i` is the lift of
block `i`.

## Extractor E

From the query list and an accepting proof `π`:

1. Recompute the verifier's transcript: chall₁, chall₂, chall₃, the decoded `Δ'`, the opened
   seeds, and the hidden-leaf commitments `com_{i,Δ_i}`.
2. For each tree `i`:
   - Look for a cipher query (forward or inverse) that determines one block
     `E_k(x_{c,i}) = com_{i,Δ_i}[c]` for some key `k`, with `x_{c,i} = iv ⊞ (c, 0, 0, i+L−1)`.
     Evaluate the other block `E_k(x_{1−c,i})` yourself and check it.
   - If this succeeds, tree `i` is *known*, with `sd_{i,Δ_i} := k`. (L2 shows that "known" is
     exactly "has no dead leaf".)
   - For a known tree, compute `u_i` with ConvertToVOLE, querying `E` itself, and form the
     candidate `w^{(i)} := u_i[0..ℓ) ⊕ c_i ⊕ d`, where `c₀ := 0`.
3. Output the first candidate that satisfies the relation R itself, checking all components, not
   the chall₂-combination.

## Main theorem (classical: proved, see §Assembly)

**Theorem.** For every classical prover `P*`,

    Pr[V accepts π ∧ R(x, E(π, queries)) fails] ≤ ε_ext

where

    ε_ext = Q·max(d,1)·2^{−λ} + q₁·ε_KOS + q₂·(ε_QS + 2^{−128}) + q_c·2^{−448}
            + ε_bind + ε_dead + (q² + q)·2^{−256}

The query counts are:
- `Q`: H₂³ queries, grinding included;
- `q₁`: H₂¹ queries;
- `q₂`: H₂² queries;
- `q_c`: UOV-combination-hash queries;
- `q`: all queries.

The bad-challenge terms are charged per H₂¹ and H₂² query, not per H₂³ query, because a prover can
grind chall₁ and chall₂ before spending an H₂³ query (found independently by L3, L4 and L8). The
last term binds the statement before chall₂ (L4). For the repo's parameters:
- `ε_KOS ≈ 2^{−154}`;
- `ε_QS ≈ 2^{−128}`;
- `ε_dead ≈ 2^{14.2}·q₂·q_E·2^{−256}`;
- `ε_bind` is negligible (L1).

At `q = 2⁶⁴`, `ε_ext ≈ 2^{−60.8}`, dominated by `Q·9·2^{−128}` and `q₂·2^{−127}`.

Strong simulation-extractability also holds, with additional terms (L8).

## Lemmas

### L0 — Domain separation and oracle uses [paper + Lean: `L0-L2-commitments.md`, `Seed/Commitments.lean`]

**Proved.** There are 12 SHAKE128 domains, separated by their final byte, or by fixed length for
the three H₁ shapes. "Prefix-free" is false (H₂⁰–H₂² have variable-length fields), but
disjointness is all that is needed, and it holds. The four AES roles use disjoint tweak ranges,
and `(c, twk) ↦ iv ⊞ (c, 0, 0, twk)` is injective, so no two roles share an AES input, the dummy
key-0 expansions included. Open item: application-level hashes are DST-prefixed while protocol
hashes are tagged at the end, so formal disjointness between the two families is not shown. It is
irrelevant to the proof of knowledge.

The original requirements:

- All SHAKE invocations reachable from `voleith_*` and the relations' constraint code, for the
  repo's parameters, have pairwise disjoint input domains. This uses fixed domain-separator bytes
  and fixed-length fields, so the inputs are prefix-free.
- The UOV combination hash (`uov::detail::Combination`) is disjoint from all H₂ʲ and from
  QuickSilver's χ derivation.
- AES is used only through `aes_ctr_prg` with the tweaks listed in `lean/docs/lean-correspondence.md`. Within one
  proof those tweaks give pairwise disjoint AES input blocks, apart from the dummy key-0
  expansions.

### L1 — Committed data and binding [paper: `L0-L2-commitments.md`]

Fix `P*`'s query list and an output `π` whose transcript uses chall₁ = H₂¹(…com…). Define:
- `com`, then `h_0..h_{τ−1}`, then `com_{i,j}` as the unique H₁ preimages in the query list;
- a leaf `(i,j)` is *alive* if some key `k` has one block `E_k(x_{c,i}) = com_{i,j}[c]`
  determined by a cipher query made before the chain's H₂¹ query, and `E_k(x_{1−c,i}) =
  com_{i,j}[1−c]` as a cipher value, whether or not that block is ever queried; otherwise it is
  *dead*. Here `iv` is the chain's own `H₄(iv_pre ‖ mu)`.
  - **Correction (L0–L2 worker):** the original definition required both blocks to be queried
    before the chain. Under it, Claim 1 fails with probability about `τ·q₂·2^{−128}`: commit to
    `y₀ ‖ c_r` in many chains and query the second block afterwards.
- for a tree with no dead leaf, `u^{(i)} := u_i ⊕ c_i` and `V_i` from ConvertToVOLE of its seeds.

**Proved:** except with probability

    ε_bind = q₁²/2²⁵⁷ + q₁(q₂+17q₁)/2²⁵⁶ + 10q_E²p² + L·q₂·p²(1+3q_E²p),   p = 1/(2¹²⁸ − q_E), L = 2304,

these objects are well defined: the preimages are unique, and alive leaves have unique keys, even
counting keys that appear only after the chain. If `V` accepts via the chain, they equal what the
verifier recomputes. They are also independent of chall₁ given the transcript before the chain,
which L3 needs.

### L2 — Dead leaves are never opened (Claim 1) [paper: `L0-L2-commitments.md`]

Except with probability `ε_dead`, if `V` accepts `π` then:
- every dead leaf is the hidden leaf of its tree (`Δ_i = j_i`);
- every seed the verifier derives from the opening equals the committed seed.

**Proved**, with `ε_dead = 8·L·q₂·q_E·p²`. The proof covers inverse queries, `iv_pre` chosen
after cipher queries, and the GGM co-path: every opened leaf's seed comes only from opened nodes.
The extractor finds the hidden leaf's key exactly when that leaf is alive.

### L3 — KOS consistency (Claim 2) [paper + Lean core: `L3-kos.md`, `lean/VoleMole/Seed/KOS.lean`]

**Proved**, in a stronger form: all masks are affine. The proof uses the spec's triple argument
(Lemma 10.26 / Corollary 10.27) and no per-tree structure. The mask rows contain H₅ hashes of
inputs that depend on Δ', so they are not affine per tree.
- `ε_KOS = C(|S|,3)·(2^{−512} + (L−1)⁵·2^{−576}) ≈ 2^{−154}` per H₂¹ query, for every relation.
  Ratatouille spend exceeds the spec's row bound of `2¹²`, but the bound is proved for any length.
- Lean: `claim4Hyp_of_kosGood` builds the Claim 4 hypotheses from a good chall₁. The random-oracle
  step is paper only.
- `u*` is a field element; bits come only from L4.

The original requirements:

Let `A` be the accepting set from `lean/docs/sketch.md`: challenges with zero grinding bits, every dead leaf
hidden, a successful opening, and passing checks when everything is computed from the committed
data and `P*`'s fixed messages. Except with probability `ε_KOS` over chall₁:

    ∃ u* ∈ F_{2^λ}^ℓ, V* such that ∀ Δ' ∈ A, ∀ j < ℓ: Q[j](Δ') = V*[j] + u*[j]·e(Δ'),

and likewise for the mask rows that QuickSilver needs.

This must account for:
- the actual universal hash: four λ-bit hashes plus one 64-bit hash, combined via `y0·matrix[i]`;
- the four direct masks;
- prover-chosen mask high bits from `PRG(root, iv, 2³¹−1)`;
- trees with a dead leaf, which are fixed on `A` and contribute constants.

`ε_KOS` must be given as a number for the repo's ℓ.

### L4 — QuickSilver with chall₂-dependent constraints (Claim 3) [paper + Lean core: `L4-quicksilver.md`, `lean/VoleMole/Seed/QuickSilver.lean`]

**Proved.**
- The check polynomial has degree `≤ d`, and its top coefficient is exactly `Σ_k χ_k f_k(w*)`.
  Masks and `ã` reach only degree `d−1`.
- The code's χ is `r₀ s^{n−1−k} + r₁ t^{n−1−k}`, which gives
  `ε_QS = 2^{−128} + (n−1)²·2^{−192}` per H₂² query.
- The chall₂-combination is handled by a joint counting argument, adding `2^{−128} + q_c·2^{−448}`.
- The statement must be bound before chall₂, costing `(q²+q)·2^{−256}`. Lean (classical, ROM +
  ideal cipher, `lean/docs/probabilistic-plan.md` §2g): for all five relations with an adaptively
  chosen statement, `(q₀+3)(q₂₁+q₀+4)·2^{−256}` (`q₀`, `q₂₁` the prover's `H₂⁰`, `H₂¹` queries;
  `2^{−256}` per pair of an `H₂⁰` answer and an earlier `mu₁` field or `H₂⁰` answer;
  `ROM/StmtBind.lean`), and for PomFRIT, whose μ is in the `H₂²` input, `(q₀+3)(q₂₂+q₀+4)·2^{−256}`
  (`ROM/AdaptPomfrit.lean`); `*_accept_le_adaptive`. The charge sits with the `H₂⁰` queries. The
  four non-delayed relations need injective instance encodings on the statement family (they
  contain UOV key digests; Moussaka's issuance encoding `t ‖ ctx_iss` needs `t` of fixed length);
  PomFRIT needs nothing (the μ preimage determines the target, which is all the relation reads).
- Lean: `claim3_of_circuit` and `bits_of_bit_constraints` give `hclaim3` and `hbits` for
  `extraction_cases`.

The original requirements:

Write `w* := u* + d`. The constraint values `f_{chall₂}(w*)` include:
- the bit constraints;
- relation constraints, some of which are chall₂-combinations `Σ_k l_k a_k(w*)` with
  `l = H(chall₂ ‖ dst)`.

Claim: except with probability `ε_QS + 2^{−128}` over chall₂, either
- every *uncombined* constraint holds at `w*` (all bit constraints and all `M` UOV components), in
  which case `w*` is a bit vector and `u*[j] ∈ {0,1}`; or
- `|A| ≤ d`.

Ingredients:
- **[Lean]** `card_le_natDegree` (roots) and `combination_prob` (combinations).
- **[to do]** The Schwartz–Zippel bound for QuickSilver's χ derivation as implemented.
- **[to do]** The fact that the check polynomial's top coefficient is `Σ_k χ_k f_k(w*)`.
- **[to do]** Independence of `l` and `χ`: `l` comes from a separate random oracle (L0).
- **[to do]** That `w*` is fixed before chall₂: `u*` is committed before chall₁, and `d` is an
  input to H₂².

### L5 — A free tree holds the witness (Claim 4) [Lean: `free_tree_holds_witness`, `card_le_one_of_all_fixed`]

Done. The Lean hypothesis `Claim4Hyp.tree_form` matches the code: `Q[j] = W_crt(V[j]) +
Σ_i u^{(i)}[j]·e_i(Δ)`.

### L6 — Per-chain case analysis [Lean: `extraction_cases`, `accepting_card_le`]

Done: on a chain where L1–L4 hold, either some known tree's candidate satisfies the constraints, or
at most `max(d, 1)` admissible chall₃ values are accepted.

### L7 — Arithmetization soundness (constraints ⇒ relation) [Lean: `lean/VoleMole/Arith/`; paper: `L7-uov.md`, `L7-keccak.md`]

**Proved for all five relations**, with no soundness bug found. The pieces:
- the GF(256) embedding is a field homomorphism on all four code paths, tested exhaustively;
- the UOV public-map evaluation is correct;
- Moussaka's selector is one-hot;
- the Keccak-p[800,12] segments force the true trace: the backward map is invertible, and each
  supporting fact is checked by a test over its whole domain;
- the commitment wiring is correct;
- Ratatouille's adder is exact on 65-bit sums.

Now mechanized in `lean/VoleMole/Arith/`: executable models of all five constraint generators with
completeness, soundness for arbitrary field-valued committed values, and the `1/|F|` combination
bound, cross-checked against the C++ by `lake exe arith_vectors`. pqov's key layout is proved too:
the model of `ov_publicmap` equals the `for_each_monomial` layout (`Arith/Pqov.lean`). What remains
outside Lean: the step from the abstract field `F` to `GF128` (no `Field` instance), and
`ov_publicmap_ct` (agreement with `ov_publicmap` is tested).

The original requirements:

For each relation, any bit vector `w` satisfying every uncombined constraint satisfies R(x, Dec(w)):
- **PomFRIT redeem:** `P(s) = h + r`.
- **Moussaka redeem:** UOV preimage under the selected issuer key, selector and parity constraints,
  and Keccak.
- **Moussaka issue:** the Keccak commitment opening.
- **Ratatouille issue:** the Keccak commitment opening.
- **Ratatouille spend:** the Keccak parts, the adder, range checks, and `P(s) = Tag(c, x)`.

Ingredients:
- every witness bit has a bit constraint;
- the GF(256) → GF(2¹²⁸) embedding used for witness bytes and public constants is an injective ring
  homomorphism (exhaustively testable);
- the combined UOV public-map evaluation is correct;
- the Keccak segment constraints are sound.

### L8 — Simulation-extractability [paper: `L8-simulation-extractability.md`]

**Proved: strong SE.** The extractor succeeds on any accepting `(x, b₁, b₂, π)` that differs from
every simulated triple. It runs on the public log (adversary queries plus the verifier's queries
on all proofs), never on the simulator's private queries. The extra terms are:
- `4·q_S·N·2^{−254}` (programming aborts);
- `138·q_S·N_E·2^{−127}` (guessing an unopened GGM key of a simulated proof). This is 0 with the
  punctured simulator from `lean/docs/zk.md`'s H7;
- `q_S·τ·(9+4τ·q₄)·N_E·2^{−254}`;
- `N²·2^{−253}`.

No malleability attack was found: delayed instance, binders, grinding and replay were all checked.
Replay is stopped by nullifiers, not by SE. PomFRIT's blindness needs ZK against the Issuer, which
fails (`lean/docs/zk.md`); SE cannot repair that.

The original requirements:

The extractor still succeeds when `P*` also gets proofs from the ZK simulator (which programs
H₂³), for any accepting proof whose statement and binders differ from every simulated proof.
Expected argument:
- the simulator's hidden-leaf commitments are uniform strings with no seed, so they act as dead
  leaves;
- reusing simulated commitments fixes those trees;
- reusing all of them forces `|A| ≤ 1` at the simulated Δ, which a fresh chain hits with
  probability `2^{−λ}`.

### L9 — Quantum adversaries [in progress: `Q1-*.md`, `Q2-*.md`, `Q4-*.md`; done: `Q3-aes-models.md`]

**Decision (maintainer):** the `aes_ctr` leaf commitment stays, so the quantum proof must work
with AES as a quantum ideal cipher. Q3's suggested switch to faest-arch-opt's `leaf_hash::shake`
was rejected. Q3 also found that `lean/docs/sketch.md`'s "AES-CTR keystream as random oracle" model is
unfaithful: counter windows overlap, so shifted-iv calls produce the same blocks. Q4 handles
efficient simulation of the quantum ideal cipher, which an efficient extractor needs.

The hashes are quantum random oracles. AES is a quantum ideal cipher: the adversary queries
`|k, x, y⟩ ↦ |k, x, y ⊕ E_k(x)⟩` and the inverse, in superposition.

**Plan: a compressed oracle on keys, not on points.** An ideal cipher is a uniformly random function
`π : K → Sym({0,1}¹²⁸)`. Purify it as `⊗_k |u_Sym⟩`, where `|u_Sym⟩` is the uniform superposition
over permutations. A forward or inverse query is a unitary controlled on the key register that
acts only on the register `π(k)`. So after `q` queries the state lies in the span of branches in
which at most `q` key registers differ from `|u_Sym⟩`. The *key database* records which keys were
touched. No permutation-level compressed oracle is needed: extraction only needs the key `k` of a
leaf commitment, and an untouched key's permutation is uniform, so its outputs at the fixed
plaintexts `iv ⊞ (c, 0, 0, twk)` are unpredictable.

- **Q1 — Online-extractable leaf commitments in the quantum ideal-cipher model**
  (`Q1-quantum-ideal-cipher.md`).
  - Make the key-level compressed oracle precise and prove the database bound.
  - Prove a Zhandry-Lemma-5-type bound: outputting `(k, com)` with
    `PRG(k, iv, twk)[0..2λ) = com` for a `k` outside the database succeeds with probability
    `≲ 2^{−2λ}`, up to the usual square-root terms.
  - Prove an extraction measurement `Ext_{iv,twk}(com)`, i.e. "find a database key `k` with
    `π_k(x₀)‖π_k(x₁) = com`", that has the properties the DFMS (Don–Fehr–Majenz–Schaffner,
    EUROCRYPT 2022) online-extraction framework needs:
    - correctness;
    - almost-commutation with oracle queries, with a bound `δ` per query.
- **Q2 — QROM Fiat–Shamir lift** (`Q2-qrom-fiat-shamir.md`). Lift L1–L6 to quantum provers. Use Q1's
  interface as a black box: the commitment `com_{i,j} → k` is online-extractable with errors
  `ε_OE` and `δ`. Combine it with round-by-round (knowledge) soundness of the 7-round protocol
  (Chiesa–Manohar–Spooner 2019; DFMS 2022; FAEST v3 spec §10.11). The QROM loss on the challenge
  rounds is inherently about `q²` (Grover), so expect bounds of the form `O(q²)·2^{−λ}·(…)`.
- **Q3 — Alternative AES models and design options** (`Q3-aes-models.md`). Compare:
  - the key-level quantum ideal cipher (Q1);
  - the seed PRG as a random oracle (`lean/docs/sketch.md`, with its switching loss);
  - an iterated Even–Mansour model of AES with the real key schedule and random public
    permutations (needs permutation superposition oracles, e.g. Majenz–Malavolta–Walter);
  - a design change: if faest-arch-opt offers a SHAKE-based leaf commitment, switching the repo's
    parameter sets to it would make the leaf commitments ordinary random-oracle commitments, which
    are QROM-extractable by DFMS directly. This needs a cost estimate.

## Assembly (classical)

Fix a classical prover `P*`. The analysis goes chain by chain:

1. **Chains.** A *chain* is a first-occurrence H₂¹ query `Θ`, followed by H₂² and H₂³ queries that
   extend it. Discard the following events:
   - L1's binding failures (`ε_bind`);
   - L2's dead-leaf openings (`ε_dead`);
   - a bad chall₁ for some H₂¹ query (`q₁·ε_KOS`, L3);
   - a bad chall₂ for some H₂² query, including the chall₂-combination and statement binding
     (`q₂·(ε_QS + 2^{−128}) + q_c·2^{−448} + (q²+q)·2^{−256}`, L4).
2. **Surviving chains.** On a surviving chain:
   - the committed data is well defined and agrees with any accepting proof (L1, L2);
   - "known" equals "no dead leaf" (L2);
   - L3 gives the per-row affine form on `A`;
   - L5's `tree_form` matches the code;
   - L4 gives Claim 3's dichotomy and `hbits`.

   These are exactly the hypotheses of the Lean theorem `accepting_card_le`
   (`SeedExtraction.lean`). L3's `claim4Hyp_of_kosGood` and L4's `claim3_of_circuit` produce them
   in Lean form. So either some known tree's candidate `w^{(i)}` satisfies every uncombined
   constraint, or at most `max(d,1)` admissible chall₃ values are accepted.
3. **Extractor success.** In the first case the extractor's candidate satisfies R, by L7, and the
   extractor outputs a witness.
4. **Accepting a doomed chain.** In the second case, each H₂³ query on the chain returns a uniform
   λ-bit chall₃. All of `A` has zero grinding bits, so the query is accepted with probability at
   most `max(d,1)·2^{−λ}`. A union over the `Q` H₂³ queries gives `Q·max(d,1)·2^{−λ}`.

**Lean, steps 2–3 per relation** (`VoleMole/EndToEnd/`). `Core.lean` translates `Arith.Expr`
into the verifier's circuit (`toQS`, adding the degree raisings) and proves that the check polynomial
of an `Arith.System` has degree `≤ d` and top coefficient `Σ_k χ_k f_k(w*)`
(`sysCheckPoly_natDegree_coeff`). `extract_or_few` then runs `accepting_card_le` with the real
system. The combination challenge `l` is handled by splitting L4's bad event in two:
`hQS` (system fails at `w*`, yet the ZKHash vanishes: `ε_QS`, `card_qs_bad_le`) and `hcomb` (the
system holds at `w*` for the chain's `l`, yet `w*` is not a witness: `1/|F|`, the relation's
`*_sound_card`, restated as `*_comb_bad`). No linearity-in-`l` argument is needed. `Relations.lean`
has one theorem per relation (`pomfrit_extract`, `moussaka_issue_extract`,
`moussaka_redeem_extract`, `ratatouille_issue_extract`, `ratatouille_spend_extract`): a known
tree's candidate decodes to a witness of the actual relation, or at most `max(d,1)` admissible
chall₃ are accepted. Its docstring lists each hypothesis and the lemma that discharges it.
`Degree.lean` proves the degree bound `≤ 9` for the four Keccak-based systems.

Summing gives `ε_ext`. Simulation-extractability adds L8's terms. The steps that are paper only
are the random-oracle and ideal-cipher probability arguments (L1–L4's freshness steps) and the
union bounds. Every deterministic step is in Lean or is an exhaustive test.

## Quantum assembly (Q1, Q2, Q4–Q7 proved; extraction non-vacuous up to q ≈ 2^51.7)

**Theorem** (Q2, Theorem 7.1). For every quantum prover, with hashes as quantum random oracles
and AES as a quantum ideal cipher:

    Pr[V accepts ∧ E fails] ≤ Σ² + ε_multi + ε_rec (+ ε_Sim)

    Σ = 2√2·[Q₂₁√ε_KOS + Q₂₂√ε_QS + Q_c·2^{−64} + Q₂₃·√max(d,1)·2^{−64}] + collision terms

**Extractor.** It runs `P*` once with compressed oracles: the hashes are compressed per point, and
AES is compressed per key (Q1). After the verifier finishes, it applies Q1's extraction measurement
to the at most τ hidden-leaf commitments and outputs the first candidate satisfying R. There is no
rewinding, no reprogramming and no mid-run measurement.

**New tool: Q2's Lemma T.** It lifts round-by-round arguments to the QROM without needing the
"bad" property to be monotone. FAEST spec §10.11 needs monotonicity, but "extractor fails" is not
monotone.

**The `q²` term.** The leading term is about `200·q²·2^{−128}`: `2^{−60}` at `q = 2³⁰`, and
vacuous at `q = 2⁶⁴`. This loss is inherent: a Grover search over grinding counters achieves about
`4q²d·2^{−128}`. FAEST's own QROM bound (spec Lemma 10.49) is also vacuous at `2⁶⁴`.

**Lean reuse.** The deterministic Lean results (L3–L6) are reused unchanged, applied to each fixed
database. `Seed/QROM.lean` checks the bookkeeping: the telescoping step, the commutator transitions
and the numbers.

**Open:**
- **`ε_multi`** (two touched keys open one leaf commitment). Key-level recording bounds it only up
  to about `2^{37}`–`2^{40}` cipher queries, which caps the theorem. A real attack needs about
  `2^{85}`. Q4 is working on a point-level bound.
- ~~`ε_Sim`~~ **Solved (Q4).** The simulator is `E_k = A_{F(k)} ∘ ρ_k`:
  - `F` is a compressed random function into the affine group `AGL(1, GF(2^128))`; its database is
    the key database;
  - `ρ_k` is the Morris–Rogaway sometimes-recurse shuffle with random round functions.

  It is information-theoretic, with no qPRP assumption. It is within `2^{−172}` of the ideal cipher
  against unbounded queries, and it fits Q1's framework with the exact density `p` (the affine group
  is sharply 2-transitive). So the extractor and the plain-model reductions are efficient.
- **`ε_multi` improved (Q6).** Q6's Theorem 1, an expected-agreement-count argument, holds for
  all `q`. The constant drops from about `1.8·10⁷` to about `484`. Q2's total bound becomes
  `2^{−60.4}` at `2^{30}`, `2^{−40.2}` at `2^{40}`, `2^{−23.3}` at `2^{45}` and `2^{−5.8}` at
  `2^{50}`.
- **Simulation-extractability is now meaningful (Q6 + Q7).** Q6's Theorem 2 counts the simulator's
  classical queries separately, building on Q7's Lemma K (at most 4607 key fetches per proof).
  Strong SE is `2^{−60.4}` at `Q_S = q = 2^{30}`.
- **Key-level techniques are tight (Q6, Theorem 3).** Reaching `2^{57}` needs a point-level
  multi-collision lemma; Q6 §7.3 states three candidates (M1–M3).
- **Multi-proof extraction and the quantum protocol theorems:** see `Q7-qrom-multi-extraction.md`.
- (Historical) **Status of `ε_multi`.** Neither a point-level compressed ideal cipher (Carolan–Majenz) nor
  `E_k = P_{F(k)}` improves it. What's missing is a Liu–Zhandry-style multi-collision bound for the
  compressed ideal cipher.
- **Simulation-extractability in the QROM** is not covered; it needs reprogramming tools.
- Parallel queries are not handled.
