# Security of Ratatouille, as implemented

**Name.** `main` calls this protocol **VOLE-ACT** since `9d9bec8` (code under `src/act/`; domain-separation strings and KATs unchanged). This note keeps the old name and paths; see `lean/README.md`, "Names".

This note fixes the security notions of the Ratatouille Anonymous Credit Token (ACT) and proves
them for the code in `src/ratatouille/*` and `include/vole_mole/ratatouille.hpp` at commit
`6d7113e` (`main`), with explicit bounds. It also covers the fix of commit `d5def9c` (branch
`voleith-label-rows`). That fix was merged as `64fd1a4`, but Ratatouille opts out of it with
`REUSE_CRT_WITNESS`, so on `main` Ratatouille is still at the `6d7113e` bounds (PU).

Sources used:
- the VOLE-ACT draft `draft-authors-mole-vole-act.md`, which the README links as `[act]`. It was
  briefly named `draft-authors-mole-act-ratatouille.md` (draft commit `a8291b0`) and got its old
  name back in `0af2a67`. This note was written against the draft as of 2026-10-13 and has been
  rechecked against draft commit `6736ebe` (2026-11-02). The later changes make the credit
  witnesses bit vectors, with V3 checked by a ripple-carry adder and V4 holding by construction,
  which matches the implementation (§8). They also add a rationale for the constant bits in the
  initial states of `Com` and `Tag` (at least 128), and a changelog;
- the generic ACT draft, now `draft-schlesinger-mole-ec-act.md` (formerly `draft-authors-mole-act.md`,
  then `draft-authors-mole-ec-act.md`), cited as {{ACT}}. The passages cited here are unchanged in
  substance at `6736ebe`;
- `lean/docs/extraction/` (PoK, L7, L8, Q2) and `lean/docs/zk.md` (ZK);
- `lean/docs/security/domain-separation.md`, which proves Lemma DS (its §7: part (a) for every SHAKE
  call Ratatouille makes, part (b) for `Com` and `Tag`).

Both drafts were fetched on 2026-10-14 into the session scratchpad (`papers/act/`).

Line references are `file:line` at `6d7113e`.

## 0. Summary

| Notion | Result | Main terms |
|---|---|---|
| **Balance** (no inflation): accepted spends ≤ issued + refunded, against adaptive malicious clients, honest clients present | **Proved** (Thm 1), classical. [Lean] as a game on the executable spec and the Lean verifier in the ROM and ideal-cipher model, `N·ε_iss + N·ε_spend + Adv^{uf-tag}(B) + Adv^{coll}(C)` (`ROM/RatatouilleBalance.lean`, `balance_le_ufTag`; §4), and with simultaneous extraction `ε_bal^sim + …` (`balance_le_ufTag_sim`, `balance_le_ompr_sim`: each query of the run charged once for both relations, `≈ 2⁻⁶⁰·⁵` against `2⁻²⁹·⁶` at `2⁶⁴` queries and `N = 2³⁰`): `B` a UF-Tag forger (with a signability probe) and `C` a `Com` collision finder, explicit; their advantages stay terms. The probe costs only the Issuer's aborts: `balance_le_noProbe` (`ROM/RatatouilleProbe.lean`) has a probe-free forger plus a failure term `≤ N·δ(sk)^{255}` (`uov-assumptions.md` §5.8). Under one-more-UOV: `balance_le_ompr` (`Assumptions/RatatouilleOMPR.lean`), the UOV term `Adv^{ompr}` of an explicit reduction, with `Tag` a random function in the standalone game (the modelling hypothesis `TagIdeal`) | `ε_ext + Adv^{uf-tag} + q_K²·2^{−257} + N·E[δ^{255}]` |
| **No theft**: an adversary cannot spend an honest client's credits through a request it did not copy verbatim (in the extraction form; a relay can still burn the honest nullifier, §5) | **Proved** (Thm 3), using weak SE and a ZK hop. [Lean] the reduction as a game on the executable spec in the ROM and ideal-cipher table model, `ε_I + ε_S + δ_S + ε_SE + Adv^ow(B)` (`Theft/Ratatouille.lean`, `noTheft`; with the Lean prover's zero knowledge, `noTheft_lean`; with the hops' read budgets proved, `noTheft_lean_reads`); weak SE reduced to plain extraction plus a programmed-point term, both hypotheses (`noTheft_lean_plain`, §5); the same with `H₁`, `H₂⁰…H₂²`, `H₄`, `H_comb` read off uniform tables (`noTheft_leanX_plain`, `Theft/Tables.lean`); `Adv^ow` in a random-table model for the standalone experiment, `(q+2)·2⁻¹²⁶` (`owAdvColRO_num`, `Theft/ComOW.lean`); for `U` honest clients and `M` honest spends with chained change tokens, `U·ε_I + M·ε_S + Σ_i δ_i + ε_SE + Σ_j Adv^ow(B_j)` (`noTheftN`, `Theft/RatatouilleMany.lean`; with the Lean prover, the hops' budgets proved and weak SE reduced to plain extraction, `noTheftN_lean_plain`, §5) | `ε_ZK + ε_SE + q_K·2^{−127}` |
| **No theft by copying** (hijack): anyone who obtains a spend request can redeem it first | **Fails** (F2). Nothing binds a spend to a session, unlike {{ACT}}'s `ctx_spend` and Moussaka's `challenge_digest` | — |
| **Unlinkability/anonymity** against a malicious Issuer: spends and issuances leak only `(pk, ctx_iss, T_init, d)` and whether the client could afford the spend | **Proved** (Thm 2). On `main` it relies on Keccak one-wayness in `r`; with the fix it is standard NIZK. [Lean] a two-round left/right form, from ZK and hiding hypotheses (`Privacy/Ratatouille.lean`); with the executable Lean prover (label rows) down to its tape hypothesis (`Privacy/RatatouilleLean.lean`, `unlinkability_label_rows`); for the Lean prover in the ROM and ideal-cipher model with every zero-knowledge term explicit, `≈ 2⁻¹⁰²·³` plus budget terms and `2·ε_hide` (`unlinkabilityRO_lean_num`), and `≈ 2⁻¹⁰¹·⁶` with a table-reading Issuer (`unlinkabilityRA_lean_num`; §6); also with AES as random permutations (`_perm`) and with one shared `H₃` (`unlinkabilitySh_num`, `unlinkabilityRASh_num`); from the real Clients' OS seeds and seed XOF, each `+ 2·(2q_H + 2)·2⁻²⁵⁶` with `q_H` the Issuer's XOF queries (`unlinkability*_seed`, `lean/docs/zk.md` §10.6; the note's H1 does not charge seed collisions); with a key stage (the Issuer's key, context and balance) that reads the tables too (`unlinkabilityRAK_lean_num`, `≈ 2⁻¹⁰¹·⁶`); with any number `n` of further honest Clients, `≤ n·2⁻¹⁰¹` plus budget terms and `2·ε_hide` (`unlinkabilityN_lean_num`), also adaptively scheduled, each further session's key, context, balance, response and amount chosen from earlier outcomes and the challenge key, context and balance from the sessions before it (`unlinkabilityAd_lean_num`, the same numbers), and interleaved in any order with each further Client spending up to `K` times along its change tokens (`unlinkabilityIL_lean_num`, `≤ (n(K + 1) + 2)·2⁻¹⁰¹`; with a table-reading scheduler that also places the challenge's stages, `unlinkabilityILO_lean_num`, `+ 46·L·(a₃ + a₂ + a₅ + 221·a_E)·2⁻¹²⁸`), and with `N` challenge pairs (`unlinkabilityP_lean_num`; `lean/docs/zk.md` §10.8, §11) | `ε_ZK + q_K·2^{−127}` |
| **Correctness** of issuance, spends, refunds and the 64-bit edge cases | **Proved** (Thm 4); arithmetic checked in Lean | prover abort `≤ (1−p)^{2³²}` |
| **Refund integrity**: refunds are bound to their state and cannot be moved or altered | Proved, as part of Thm 1 and Thm 3 | — |
| **Key separation across protocols** | **Fails if a key is shared with PomFRIT**: unbounded minting (F1, demonstrated) | — |

**Assumptions** (§2):
- the proof-system models of `lean/docs/extraction/README.md`: SHAKE as random oracles, AES-128 as an ideal
  cipher;
- `Keccak-p[800,12]` as an ideal permutation with forward and inverse queries;
- **UOV one-more-preimage on random targets with deterministic `DerivePreimage`** (A-OMPI). A
  plain UOV-inversion reduction is not available (§2.3). This is the assumption that the draft's
  §"Proof status" anticipates;
- an atomic nullifier store per (key, context);
- Lemma DS.

Findings (§7):
- **F1**: sharing a UOV key with PomFRIT lets anyone mint arbitrary Ratatouille tokens.
  Demonstrated.
- **F2**: spend requests are bearer instruments. An on-path party, or the relay that carries the
  request, can redeem it, take the service paid for, and withhold the change, which destroys the
  client's whole balance.
- **F3**: a pending spend or pending token is consumed even when the response fails to verify, so
  one corrupted response loses the balance.
- **F4**: refunds are unbounded. The effective balance `t + x` can exceed `2⁶⁴ − 1`, which forces a
  minimum next spend and gives a malicious Issuer a feasibility side channel.
- **F5**: the `spend_response` API needs the refund before the caller sees `d`, and it signs before
  the nullifier check. This is safe, but error-prone.
- **F6**: on `main`, unlinkability uses Keccak one-wayness twice. With the fix, it uses it once
  (hiding).

No attack on balance or unlinkability was found when keys are separated and the transport is
confidential.

## 1. The protocol as implemented

Parameters: `L = 8` (credits are `uint64_t`), `nf_len = 24`, `ctx_len = 16`, `r_len = 16`, and UOV
`(n, m) = (119, 45)` over GF(256) (`include/vole_mole/ratatouille.hpp:20-34`,
`include/vole_mole/uov.hpp:17-18`).

- `Com(nf, ctx, t, r) = KP800("rata"‖0‖"c0" ‖ r ‖ 0⁹ ‖ ctx ‖ ⟨t⟩₈ ‖ nf ‖ 0²⁰)[0..32)`
  (`commit.hpp:56-76`, `ratatouille.cpp:94-100`). Of the 800 input bits, 288 are fixed.
- `Tag(c, x) = KP800("rata"‖0‖"t0" ‖ 0²⁵ ‖ c ‖ ⟨x⟩₈ ‖ 0²⁸)[0..45)` (`commit.hpp:79-93`,
  `ratatouille.cpp:102-107`). Of the 800 input bits, 480 are fixed.
- **Issuance.**
  - The Client sends `c = Com(nf, ctx, T_init, r)` and `π_iss` for
    `IssueRelation(c, T_init, ctx)`. The instance is hashed as `c ‖ ⟨T_init⟩ ‖ ctx`
    (`issue.hpp:151-155`).
  - The Issuer checks `T_init ≠ 0`, verifies, and returns `s = DerivePreimage(td, Tag(c, 0))`
    (`ratatouille.cpp:170-181`).
  - The Client checks `P(s) = Tag(c, 0)` and holds `(nf, T_init, r, 0, s)` (`:183-195`).
- **Spend of `d`.**
  - The Client checks its token and the arithmetic (`:221-236`). It sends `nf ‖ ⟨d⟩ ‖ c' ‖ π`
    with `c' = Com(nf', ctx, t', r')`.
  - `π` proves `SpendRelation(P, nf, d, c', ctx)`, V1–V4 (`spend.hpp:1-50`). The instance is
    hashed as `PKDigest(P) ‖ nf ‖ ⟨d⟩ ‖ c' ‖ ctx` (`spend.hpp:321-327`).
  - The Issuer verifies with `sk.expanded_public_key()`. It then returns `⟨x'⟩ ‖ s'` with
    `s' = DerivePreimage(td, Tag(c', x'))` for a caller-supplied refund `x'`
    (`ratatouille.cpp:264-284`), together with `nf` and `d` for the caller's nullifier check and
    price check.
  - The Client checks `P(s') = Tag(c', x')` and holds `(nf', t', r', x', s')` (`:286-303`).
- **DerivePreimage** is deterministic. The vinegar is
  `H(target ‖ sk_seed ‖ "pqov-derive-preimage" ‖ ctr)`, so there is one preimage per target
  (`subprojects/pqov/src/ov.c:217-239`, patch `pqov-patches/0001`).
- **Client randomness.** `(nf, r, ρ)` are squeezed from a SHAKE XOF over `DST ‖ seed`, with a fresh
  32-byte OS seed per request (`ratatouille.cpp:63-84, 165-168, 255-262`).

## 2. Model and assumptions

### 2.1 Oracles

- **Proof system.** As in `lean/docs/extraction/README.md` §Model: the SHAKE hashes H₁, H₂⁰…H₂⁴, H₃, H₄, H₅
  and `H_comb` are independent random oracles (Lemma L0), and AES-128 is an ideal cipher.
- **Application hashes.** These are the seed XOF (`RATATOUILLE_*_SEED_DST ‖ seed`), `PKDigest`
  (SHAKE256 of `cpk`, `uov.cpp:83-85`) and pqov's vinegar hash. They are random oracles
  independent of the proof-system oracles. This is **Lemma DS** (domain separation between
  DST-prefixed application inputs and end-tagged proof-system inputs). It is stated as a lemma
  that `lean/docs/security/domain-separation.md` will prove; it is assumed here.
- **`KP800 = Keccak-p[800,12]`** is a uniformly random permutation of {0,1}⁸⁰⁰ with forward and
  inverse oracles. It is independent of SHAKE, which uses Keccak-f[1600]. `q_K` counts all KP800
  evaluations by everyone, including the honest parties, the Issuer and the extractor (at most 3
  per extracted spend).

  Two facts are used repeatedly:
  - **(K1) Inverse queries are useless.** An inverse query returns a uniform input among at least
    `2⁸⁰⁰ − q_K` values. That input has Com structure with probability at most `2^{−287}`, and Tag
    structure with probability at most `2^{−479}`. Excluding this event costs
    `q_K·(2^{−287} + 2^{−479})`, and then every Com or Tag value was produced by a forward query.
  - **(K2) Forward outputs are uniform.** A forward output on a fresh input is uniform among at
    least `2⁸⁰⁰ − q_K` values. So its 256-bit and 360-bit truncations are uniform up to a factor
    `1 + 2^{−700}`.

### 2.2 Commitment properties (derived, not assumed)

- **Binding** (`ε_bind^K`). No two distinct Com-structured inputs have equal 32-byte outputs, and
  no two distinct Tag-structured inputs have equal 45-byte outputs. By (K1) and (K2):

      ε_bind^K ≤ q_K²·2^{−257} + q_K²·2^{−361} + q_K·2^{−286}.

  Note that this binds `nf`, `ctx` and `t` together. So a commitment fixes its nullifier, its
  context and its credit.
- **Hiding** (`ε_hide^K`). Consider `Q_c` honest commitments with uniform secret `r` (and `nf`
  secret, or revealed later). They are jointly indistinguishable from independent uniform 32-byte
  strings, even after their `nf` is revealed, except when some forward query hits a true input. A
  query names one `nf` and one `r`, so it can hit at most one honest commitment, with probability
  `2^{−128}`. Hence:

      ε_hide^K ≤ q_K·2^{−128} + Q_c²·2^{−193} + q_K·Q_c·2^{−543}

  The second term covers honest nullifier collisions, and the third covers inverse queries that
  return a true input.

  [Lean] `lean/VoleMole/Privacy/ComHide.lean` (`lean/docs/zk.md` §10.9) has the forward-query
  part for the four commitments of the unlinkability game, with `Com`'s cells a random-function
  table (one column per `(nf, r)` over the credit value): `≤ (4q + 16)·2^{−128}`
  (`hidingAdvColRO_num`, `hidingAdvAtRO_le`). This is a heuristic for the standalone experiment
  only. `Com` is evaluated inside the issuance and spend relations, so it is not a table of the
  games, and their reductions can compute it. Against such distinguishers, searching the `2^{128}`
  openings wins with advantage `≥ 1 − 2^{−128}`, with no assumption on Keccak
  (`ComHide.Ratatouille.hidingAdv_bruteForce_ge`). So `ε_hide` in the Lean theorems is a
  computational assumption, never a query count.
- **One-wayness in `r`** (what `lean/docs/zk.md` calls `Adv^{ow}_{Com}`) is the same event: for one target,
  it is at most `(q_K + 1)·2^{−128}`.

  [Lean] `lean/VoleMole/Theft/ComOW.lean` has the forward-query part for the experiment of
  Theorem 3 (two honest commitments, any opening of either at any credit value), in the same
  random-function model as `ComHide.lean`: an inverter that reads the table by a decision tree
  with `q` queries wins with probability `≤ (4q + 8)·2^{−128}` (`owAdvColRO_num`; `owAdvRO_le` in
  general). The factor 2 against `q_K·2^{−127}` comes from the column model. As for hiding, this
  is a heuristic for the standalone experiment: in the Lean theorems `Adv^ow` is the advantage of
  an explicit inverter that computes `Com`, a computational assumption (§5).

### 2.3 The UOV assumption, and exactly what is signed

The Issuer evaluates the deterministic map

    Sign(c, x) := DerivePreimage(td, Tag(c, x)) ∈ GF(256)¹¹⁹

on every `(c, x)` that passes verification. Here `c` is any 32-byte string for which the requester
proved knowledge of an opening, and `x` is the Issuer's refund (`0` at issuance). The target is the
first 45 bytes of a KP800 output whose input carries the 7-byte DST "rata‖0‖t0".

**Game UF-Tag.** The adversary gets `P`, both KP800 oracles, and a `Sign` oracle. It wins by
outputting `(c*, x*, s*)` with `P(s*) = Tag(c*, x*)`, where `(c*, x*)` was never queried to
`Sign`. Its advantage is `Adv^{uf-tag}`.

**Assumption A-OMPI (UOV one-more preimage, random targets, deterministic derivation).** Consider
an adversary that:
- gets the uov-Ip map `P`;
- requests fresh uniform targets `y₁, y₂, … ∈ GF(256)⁴⁵` on demand (`q_T` of them);
- may query a preimage oracle `i ↦ DerivePreimage(td, y_i)` (`Q_sig` queries).

It wins by outputting `(i*, s*)` with `P(s*) = y_{i*}` for an index `i*` it never queried to the
preimage oracle. `Adv^{ompi}(q_T, Q_sig)` is negligible. This is PoMFRIT's one-more-preimage
assumption, specialized to UOV and to this preimage sampler.

**Lemma 2.1.** `Adv^{uf-tag} ≤ Adv^{ompi}(q_T, Q_sig) + q_K·2^{−479} + q_K²·2^{−799}`.

*Proof.* B simulates KP800 lazily:
- On a forward query at a fresh Tag-structured input, it requests a fresh `y_i` and answers
  `y_i ‖ z` with uniform `z ∈ {0,1}⁴⁴⁰`.
- It answers every other query (inverse queries included) with fresh uniform values, consistently.
- It answers `Sign(c, x)` by evaluating the Tag input (allocating `y_i` if needed) and querying
  the preimage oracle on `i`.

This is a perfect simulation unless an inverse query returns a Tag-structured input (K1), or two
allocated outputs collide, which is the permutation-versus-function gap. A forgery on an unsigned
`(c*, x*)` is a preimage of an unqueried `y_{i*}`. ∎

[Lean] With `Tag` a **random function** (not a permutation), UF-Tag with the strict win "never
signed" is det-FDH EUF-CMA with `H = Tag`, and the lemma is `uov-assumptions.md` T1(a):
`advFDH_le_ompi` (`lean/VoleMole/Assumptions/IdealTag.lean`), with no loss and `q_T = k + 1` for
`k` hash and signing queries. Then T1(c), `advOMPI_le_ompr`, gives OMPR, with `q_T + Q_sig` targets
and a term `(q_T + Q_sig)·ρ` for the signer's aborts (a correction of T1(c), §5.1 there). The
permutation terms `q_K·2^{−479} + q_K²·2^{−799}` are mechanized too:
`Assumptions/FDHPerm.lean` defines det-FDH with `Tag` the first component of a random
permutation with inverse queries (`advFDHPerm`), and reduces it to the random-function det-FDH
game of a forger that simulates the permutation (`advFDHPerm_le_fdh`), then to OMPR
(`advFDHPerm_le_ompr`):

    Adv^{perm}(A) ≤ Adv^{euf}_{det}(fdhPermRed A; q_f + 1 + q_S, q_S)
                    + (q_f + q_i + q_S + 1)²/2^{800} + q_i·2^{320}/2^{800}

for `q_f` forward, `q_i` inverse and `q_S` signing queries (`uov-assumptions.md` §5.8). The
inverse term is the paper's `q_K·2^{−479}` (here `2^{−480}`, `M` the 40-byte pairs); the switching
term counts the inverse queries too. The step from the concrete KP800 to the ideal `Tag` is a
modelling hypothesis, as the paper's "ideal in the standalone game only": `TagIdeal` (§4) with
`Tag` a random function, or `TagIdealP` with `Tag` a random permutation
(`balance_le_ompr_perm`).

**Why not plain UOV inversion?** A guessing reduction (embed one challenge at a random Tag query)
must answer the other signing queries without `td`. The obvious simulation answers with uniform
`s` and programs `Tag := P(s)`. This differs from `DerivePreimage`'s output distribution:
- the vinegar of a uniform `s` hits a singular oil system with probability about `1/255`;
- the real sampler never outputs such an `s`;
- only `td` can detect it.

So the hop is not statistical. The salted UOV EUF-CMA proofs avoid this by resampling the salt.
Ratatouille has no salt (the draft's NOTE 2). **Recommendation R1:** put a 16-byte Issuer salt in
the 25-byte zero slot of the Tag input (`commit.hpp:79-93`). The salt is returned with `s'` and
carried in the witness. This costs no extra Keccak call. The signing then becomes salted UOV with
`H = Tag`, so balance would reduce to standard UOV EUF-CMA, plus the same abort term as
Theorem 1 (`uov-assumptions.md` §5.5, §5.8). This is not done here.

**Key separation is necessary** (see F1). A-OMPI is about a key used only for Ratatouille, or only
together with protocols whose targets are disjoint, by Lemma DS and KP800 input structure. An
example of the latter is Moussaka, whose targets are KP800 outputs with DST "mous".

### 2.4 Proof-system results used

- **PoK** (`lean/docs/extraction/README.md` main theorem; L8 §4 per-oracle form). One straight-line
  extractor `E` works from the public query log, for all accepted proofs simultaneously (L8 §9.1):

      ε_ext = Q·9·2^{−128} + q₁·ε_KOS + q₂·(ε_QS + 2^{−128}) + q_c·2^{−448} + ε_bind + ε_dead + (q²+q)·2^{−256}

  - The terms are: `ε_KOS ≈ 2^{−154}`; `ε_QS ≈ 2^{−128}`; `ε_dead ≈ 2^{14.2}q₂q_E·2^{−256}`.
  - At `q = 2⁶⁴`, `ε_ext ≈ 2^{−60.8}`.
  - Both Ratatouille relations have degree 9. Their chains are separated by the relation DSTs in
    `mu`, so one `ε_ext` with total query counts covers both.
  - [Lean] for one proof, classical, in the random-oracle and ideal-cipher model, with a fixed or
    adaptively chosen statement: the decoded witness is in `R_iss`, `R_spend`
    (`Spec.Ratatouille.IssueRel`, `SpendRel`) except with the bounds of
    `lean/VoleMole/ROM/SpecSound.lean` (`ratatouilleIssue_accept_le_full_spec`,
    `ratatouilleSpend_accept_le_adaptive_spec`, …; adaptive families with injective encodings,
    proved for fixed-length fields and a key fixed by its digest, `EndToEnd/SpecRelations.lean`).
    Simultaneously for all proofs of a run, per relation (`ratatouilleIssue_sim_spec`,
    `ratatouilleSpend_sim_spec`, `ROM/SimSpec.lean`) and for both relations together
    (`ratatouille_sim_joint_spec`, `ROM/SimJointSpec.lean`; §4): one `ε` at the run's budget, each
    query charged once for both relations as in the paper, plus per proof its verifier's queries
    and the failure terms.
- **L7.** A satisfying witness satisfies V1–V4 exactly: `P(s) = Tag(Com(nf, ctx, t, r), x)`,
  `c' = Com(nf', ctx, t', r')`, and `t + x = t' + d` in ℤ with `t, x, t', d ∈ [0, 2⁶⁴)`. This
  holds because the 65-bit adder is exact (`L7-keccak.md` §4.4). The issue relation gives
  `c = Com(nf, ctx, T_init, r)`.
- **SE** (L8). Strong SE with extra terms `ε_SE := ε_prog + ε_hk + ε_H + ε_eq`. Ratatouille needs
  weak SE with respect to adversarially chosen statements `(pk, nf, d, c', ctx)` (L8 §8).
- **ZK** (`lean/docs/zk.md` §3). The adaptive multi-proof bound:

      ε_ZK = ε_rho + ε_prog + 2ε_hide^AES + ε_lab + ε_iv

  - On `main`: `ε_lab = (Q₅ + n_mult·Q_V)·Pred_R + Q_P·2^{−128}`, with `Pred_R ≤ Adv^{ow}_{Com}`
    ((PU) holds because `w[0..16) = r`; [Lean] `ZK/Relations.lean` `ratatouille_main_zk`, with
    (PU) as a hypothesis on explicit predictors, `lean/docs/zk.md` §4.1; for the executable prover
    in the random-oracle and ideal-cipher model, one proof `zk_rom_ic_main` and the joint hop over
    the game's four proofs `main_chain_le`, `lean/docs/zk.md` §4.2).
  - On `voleith-label-rows`: `ε_lab = (Q₅ + n_mult·Q_V + Q_P)·2^{−128}`, which is standard
    adaptive NIZK. The labels come from dedicated VOLE rows (`CRT_DEDICATED_LABEL_ROWS`, faest
    patch 0005). This adds 256 bytes per proof (7256 and 17575 bytes).

## 3. Security notions

These come from the draft (§Introduction, §Overview, §Spending, §Proof status) and {{ACT}}
(§Credential scheme, §Spending, §Security considerations). Throughout, the Issuer holds one key
and keeps, per (key, `ctx_iss`), an atomic nullifier store. Per the draft, it rejects a recorded
`nf` and records `nf` before releasing the response (`ratatouille.hpp:180-182`).

**N1 Balance (no inflation; the draft's "one-more unforgeability").** In game BAL, the adversary
gets `pk` and adaptively makes three kinds of call:
- **Issue**`(req, T_init, ctx)`: the Issuer runs `issue_response` and records `T_init` as issued.
- **Spend**`(req, ctx, x')`: the Issuer runs `spend_response` with an adversarially chosen refund
  `x'`, applies the nullifier check, and records `d` as spent and `x'` as refunded.
- It may also schedule **honest clients**, see their requests and responses, and relay, delay,
  copy or drop any message.

The adversary wins if, for some `ctx`:

    Σ_{accepted spends under ctx} d  >  Σ_{issuances under ctx} T_init + Σ_{accepted spends under ctx} x'.

This covers "no client spends more than issued and refunded", "no double spend via nullifiers",
and "no inflation via refunds". The amounts are integers, and nothing wraps.

**N2 No theft (non-frameability).** The adversary must not get a spend accepted that consumes a
state certified to an honest client:
- **N2a**: through a request whose statement differs from every honest request;
- **N2b**: through a verbatim copy of an honest request.

{{ACT}} gets N2b from `ctx_spend`, which binds the proof to the Moderator's challenge.

**Correction to N2a.** As worded, N2a fails: an adversary that sees an honest spend request before
the Issuer does (the relay of F2) learns `nf`, gets its own token `Com(nf, ctx, T, r*)` issued,
and spends it first. The store then holds `(ctx, nf)`, and the honest spend is rejected. That
consumes the honest state through a request whose statement differs from the honest one
(nullifier squatting, as Moussaka's F2). It needs the same position as F2's copying and gains
nothing over it. What Theorem 3 proves is the extraction form: every accepted request with a fresh
statement has an extracted witness that opens no honest commitment, so a spend with the honest
`nf` spends a separately certified state, never the honest one (§5).

**N3 Unlinkability/anonymity.** Let the adversary be a malicious Issuer. It may use a malformed
`pk`, and it chooses `T_init`, `ctx`, refunds and responses. It schedules honest clients to issue
and to spend amounts `d` that it chooses. It must not distinguish:
- **Real**: honest clients run the real algorithms;
- **Ideal**: every honest outgoing message is produced by a simulator from the leakage
  `ℒ = (pk, ctx, T_init)` for issuance, or `(pk, ctx, d)` for a spend.

In both worlds the clients keep their real states. So whether a client can afford a requested
`d`, or rejects a malformed response, is identical in both. This captures the draft's goal that a
spend is unlinkable "to the issuance or to any other spend by the same Client", up to the public
amounts and feasibility ({{ACT}} says the same: "hides its Credential's balance beyond the public
amounts and the predicates they establish").

**N4 Correctness.** Honest runs succeed:
- an issued token holds `(T_init, 0)`;
- a spend of `d` from `(t, x)` with `d ≤ t + x` and `t + x − d < 2⁶⁴` is accepted;
- the change token holds `(t + x − d, x')`.

**N5 Refund integrity.** A refund is credited only to the state it was signed for, and only in the
amount signed. A client that finalizes gets exactly the Issuer's `x'`, or rejects.

**N6 Context binding.**
- A token issued under `ctx` can be spent only under `ctx`.
- Its change stays under `ctx`.
- A proof verifies only for the key and context it was made for.

## 4. Balance (N1, N5)

**Theorem 1.** Assume keys are separated (§2.3). For every classical adversary in BAL, with all
honest-client activity included in the query counts:

    Adv^{bal} ≤ ε_ext(N_I + N_S; q₁, q₂, Q)
              + Adv^{ompi}(q_T, N_I + N_S)
              + q_K²·2^{−257} + q_K²·2^{−361} + q_K·2^{−286}
              + (N_I + N_S)·E[δ^{255}] + q_v·2^{−256}

`N_I` and `N_S` count the issuance and spend requests verified. The last line is `Pr[E4]`: `δ(sk)`
is the fraction of bad vinegars for the key, `q_v` counts the adversary's SHAKE256 queries, and
`E[δ^{255}] ≤ 2^{−295.8}` (`uov-assumptions.md` §1, §5.8). Earlier versions of this note omitted
this term as negligible.

With `q, q_K ≤ 2⁶⁴`, the non-UOV part is about `2^{−60.8} + 2^{−129}`.

*Proof.* Build B against UF-Tag (then apply Lemma 2.1). B runs the game:
- it forwards every Issuer signing call to `Sign`;
- it runs honest clients itself, so it knows their witnesses;
- it routes all KP800 queries to its oracle.

At the end, B runs `E` on the public log (adversary, honest provers and verifier) for every
accepted issuance and spend. The issuance proofs extract `(nf_i, r_i)`. The spend proofs extract
`(t_j, r_j, x_j, s_j, nf'_j, t'_j, r'_j)`. No ZK or SE hop is needed: the combined system B∘A is
a single prover for the PoK theorem.

Let `S` be the multiset of signed pairs: `(c_i, 0)` per issuance and `(c'_k, x'_k)` per spend
response. Discard four events:
- (E1) some accepted proof's extracted witness fails the relation (`ε_ext`, all proofs at once);
- (E2) a KP800 binding failure (`ε_bind^K`);
- (E3) some spend's `(Com(nf_j, ctx, t_j, r_j), x_j) ∉ S`. Then
  `(Com(nf_j, ctx, t_j, r_j), x_j, s_j)` is a UF-Tag forgery (`Adv^{uf-tag}`);
- (E4) an Issuer `DerivePreimage` abort on a target it evaluates: a signing call (a spend of a
  state whose signing failed is no UF-Tag forgery, since its pair was queried) or a
  duplicate-path call (F5, below). In the vinegar ROM, `Pr[E4] ≤ (N_I + N_S)·E[δ^{255}] +
  q_v·2^{−256}` (`uov-assumptions.md` §5.8).

Outside these events, the following facts hold for each accepted spend `j`:
1. **Parent.** `c_j := Com(nf_j, ctx, t_j, r_j)` with refund `x_j` was signed. By binding (¬E2),
   the opening of the signed `c` equals the extracted opening. For an issuance parent `i`, this
   gives `t_j = T_i`, `x_j = 0` and the same `ctx`. For a spend parent `k`, it gives
   `t_j = t'_k`, `x_j ∈ {refunds signed for c'_k}`, and `ctx_k = ctx` (V2 of `k` puts `ctx` into
   `c'_k`).
2. **Injectivity.** Distinct accepted spends under one `(pk, ctx)` have distinct `nf` (the store).
   `nf` is bound into `c_j`, so their parent commitments are distinct, and hence their parent
   events are distinct. This holds even if:
   - the adversary reuses a `c'` across requests;
   - the Issuer signs one `c'` with several refunds (retries).

   In both cases, all states with that commitment share one nullifier.
3. **Conservation.** `t_j + x_j = t'_j + d_j` in ℤ (L7).

These are exactly the hypotheses of the Lean structure `Chain`
(`lean/VoleMole/Protocols/Ratatouille.lean`), with `X_k` the refund signed for `c'_k`. The theorem
`balance_identity_le` gives

    Σ_j d_j + Σ_{signed, never spent} value  ≤  Σ_i T_i + Σ_k X_k,

with equality (`balance_identity`) when each spend gets one response. In words: spent plus
outstanding equals issued plus refunded. `balance_le` drops the outstanding term. The argument is
per `ctx`, because parents share the spender's `ctx` (fact 1). ∎

**What the proof says about the specific questions.**
- *Double spend.* The only defence is the store, keyed on the public `nf`. Since `nf` is bound
  into `c`, one certified state is consumed once, whatever refunds were attached to it.
  - `nf'` enters only `c'` (`spend.hpp:155-162` maps it from the witness, and only into
    `SPEND_COM_NEXT_TO_WIT`).
  - So the Issuer cannot block or predict the next nullifier, and a client choosing a bad `nf'`
    only harms itself: a reused or spent `nf'` gives an unspendable change token.
- *Refunds.* A refund enters only through `Tag(c', x')`, which the Issuer signs. Moving a refund
  to another state needs a Tag collision or a forgery. Inflating it needs a forgery.
- *Arithmetic.*
  - The relation is exact over ℤ, so no wrap at `2⁶⁴` can create credits (L7).
  - Effective balances up to `2⁶⁵ − 2` are allowed, and the accounting in ℕ handles them.
  - At the protocol level, the only consequence of the no-wrap property is F4: a client whose
    `t + x ≥ 2⁶⁴` must spend at least `t + x − (2⁶⁴ − 1)` next.
  - `T_init = 0` is rejected on both sides (`ratatouille.cpp:86-90`), as the draft requires.
  - `d = 0` (refresh) and `d = 2⁶⁴ − 1` are both accepted.
- *Context binding (N6).*
  - `ctx` is in `Com`. V1 uses the instance `ctx`, and V2 puts the same `ctx` into `c'`.
  - `ctx`, `pk` (via `PKDigest`) and every public value are in `mu`.
  - So a token moves to another context only if binding fails.
  - Per-context nullifier stores are therefore sound. A store shared across contexts is also
    sound.
  - The issuance proof does not bind `pk` (the draft's TODO). This is harmless: the Issuer checks
    `T_init` itself, and an issuance request relayed to another Issuer gives that Issuer's
    signature on the same commitment.

**Lean** (`lean/VoleMole/Protocols/Ratatouille.lean`, checked with `lake env lean`, no `sorry`, no
`axiom`; `#print axioms` lists only `propext`, `Classical.choice` and `Quot.sound`):
- `Chain`, `balance_identity_le`, `balance_identity`, `balance_le`: the accounting above.
- `change_correct`: the Client's 64-bit test at `ratatouille.cpp:228-236` accepts iff
  `d ≤ t + x ∧ t + x − d < 2⁶⁴`, which is exactly when V3/V4 has a witness. Its `t_next` is then
  `t + x − d`.
- `overflow_iff`: the carry flag `lo < t` is exact.

**[Lean] Theorem 1 as a game** (`lean/VoleMole/ROM/RatatouilleBalance.lean`; the generic glue in
`lean/VoleMole/ROM/ExtractReduce.lean`; Appendix A).
- *The game* (`balQ`, `Win`). An adversary (`RoundAdv`: a VCVio computation against the hashes and
  the cipher per call, deterministic given the oracles) makes `N` adaptive calls to the Issuer of
  `Spec/Ratatouille.lean`: `issueResponse`, and `issuerSpend` (`spend_response` with the nullifier
  store as `ratatouille.hpp` prescribes) with a refund it chooses. The Issuer verifies with the
  executable Lean verifier against the random oracle and the ideal cipher (statements
  `ratatouilleIssue`, `ratatouilleSpend` with its key `pkU`, either proof layout) and signs with
  any signer `σ : Target → Option Preimage`. The adversary wins if, in some context,
  `Σ d > Σ T_init + Σ x'` over the accepted calls. Honest Clients are covered: an adversary that
  runs their code is an adversary of the game.
- *The bound* (`balance_le`; `balance_le_lean` with the Issuer's verifications re-run by
  `verifyIC`, no hypothesis on the verifier; `balance_le_ufTag` with the forgery term as a UF-Tag
  advantage, which is the standalone UF-Tag-with-probe advantage of `Assumptions/UOV.lean`,
  `ufTagAdv_eq`, `balance_le_ufTagProbe`):

      Pr[win] ≤ N·ε_iss(Q) + N·ε_spend(Q) + Adv^{uf-tag}(B) + Adv^{coll}_{Com}(C)

  - `ε_iss`, `ε_spend` (`epsIss`, `epsSpend`) are the single-proof bounds of
    `ratatouilleIssue_accept_le_adaptive_spec` and `ratatouilleSpend_accept_le_adaptive_spec`
    (`ROM/SpecSound.lean`), at the budget `Q` of `N` calls: `N(e_A + e_V)` cipher queries,
    `N(n_A + n_V)` hash queries and `N(q_A + q_V)` per kind, for `q_A`, `n_A`, `e_A` per call of
    the adversary and `q_V`, `n_V`, `e_V` per verification (for `verifyIC`:
    `extractorQueries + verifierQueries` per kind, `2 + verifierTotal = 339` in all, and
    `verifyCellBound p = 9212 + 2304·(2 + voleColBlocks)` cipher queries). They apply to
    the `j`-th prover (`proverAt`, `provI`, `provS`): the game up to call `j`, re-run with the
    Issuer, then the `j`-th request as its proof and statement. `hinj` holds for the Issuer's fixed key with a
    32-byte digest.
  - `B` (`forger`, `bOut`; the event `ForgeEv`, `forgeAdv`): the first spend `j`, verified on a
    fresh nullifier, whose extracted witness has `P(s) = Tag(c, x)` for its parent
    `c = Com(nf, ctx, t, r)`, on a pair `(c, x)` that no call before `j` released a signature on.
    `B` stops there and reports the pairs it signed before `j`. The UF-Tag game (`TagForger`,
    `UFWin`, `ufTagAdv`): the forger gets the signer `σ` on pairs, wins with a valid signature on
    a pair none of whose signing queries was answered, and must use `σ` only through its signing
    log and its *probe log* (pairs on which it only learns whether `σ` succeeds). `B` is such a
    forger (`bOut_reads`: if `σ'` agrees with `σ` there, `B`'s output is the same; through
    `yT_signer`, the run's first calls depend on `σ` only through these, and `games_congr`, the
    extraction games depend on the run only through its first calls), and it wins whenever the
    reduction's forgery event holds (`forge_ufwin`, `forgeAdv_le_ufTag`).
  - `C` (`collAdv`, `CollEv`): two extracted openings (an issuance's, a spend's parent or change)
    with one commitment and different `(nf, ctx, t)`.
- *The proof.* Per pair of tables (`win_imp`): if no request's extraction game fails, `B` and `C`
  fail, then `no_win`: the Issuer's ledger world of `Spec/Ratatouille.lean`, run with the
  extracted witnesses, satisfies `World.Hyp` at every call (the witness is in `R_spend`; its
  parent pair was released at an earlier call `k`, whose extracted opening equals the parent's
  by the absence of a collision, so the parent's entry is in the ledger), and its invariant gives
  spent `≤` issued + refunded. `prEvent_bind_le_sum_of_table` turns the per-table implication into
  the sum: the game and the single-proof games are different computations against one lazy
  random oracle, compared through a common eager table on a finite key set.
- *The Issuer's verifications inside the `j`-th prover.* The `j`-th prover re-runs the Issuer's
  verifications, and they must be cipher queries so that the extractor sees them (as the paper's
  extractor reads the Issuer's queries); the executable verifier reads the cipher as a table
  (`icPrg E.cipher`). `balance_le` takes any `VerifierIC` implementation; `ROM/VerifyIC.lean`
  (shared with Moussaka's Theorem 1) writes one, `verifyIC` (it derives the BAVC tree with
  cipher queries, queries the cells the verifier's PRG reads, then runs the hash-query verifier),
  proves that it is the executable verifier on every pair of tables
  (`evalWithAnswerFn_verifyIC`, through `verify_congr_cells`) and bounds its queries
  (`verifierIC_verifyIC`). The game itself
  verifies with the executable verifier (`verifyQ`).
- *What stays assumed.*
  - `Adv^{uf-tag}(B)` and `Adv^{coll}(C)` are the success probabilities of the two explicit
    reductions, not bounds: UF-Tag (from A-OMPI by Lemma 2.1) and `Com` binding are assumptions.
    The UF-Tag game has the signability probe: on the duplicate-nullifier path the Issuer computes
    a signature and withholds it, but its response still reveals whether `derive_preimage`
    succeeded (an exception against a rejection), so `B` needs that bit. Without the probe, `B`
    would need the abort term `E4` (the signer fails on a probed target), as the paper discards
    it.
  - *The probe costs exactly `E4`* (`uov-assumptions.md` §5.8, Proposition 9;
    `ROM/RatatouilleProbe.lean`). The probe reveals only whether `derive_preimage` aborts, which
    happens with probability `δ(sk)^{255}` per fresh target. It does not reveal whether a target
    is "good": all targets have the same number of good preimages. `ufTagAdv_le_noProbe`:
    `Adv^{uf-tag+probe}(B) ≤ Adv^{uf-tag}(B.noProbe τ) + failAdv(B)`, where `B.noProbe τ` answers
    every probe "yes" and never probes, and `failAdv(B)` is the probability that the signer fails
    on a pair `B` signed or probed. `B` logs at most `N` pairs (`forger_logs_le`), and for a signer
    with independent failures the failure event has probability `≤ N·Pr[fail]` per table
    (`pr_failOut_le`). `balance_le_noProbe` is Theorem 1 in this form. So, under A-OMPR, the
    probe route and the `E4` route give the same bound: Theorem 1 above, with
    `Adv^{ompr}(q_T, N_I + N_S)`. Two steps remain on paper: that pqov's signer in the vinegar ROM
    has this law, and the average over the tables.
  - *Under one-more-UOV, in Lean* (`Assumptions/RatatouilleOMPR.lean`, `balance_le_ompr`,
    `balance_le_ompr_rate`):

        Pr[win] ≤ N·ε_iss + N·ε_spend + Adv^{ompr}(B'; k + 1 + N, N) + (k + 1 + N)·ρ(σ)
                  + failAdv(B) + Adv^{coll}_{Com}(C),

    the OMPR game at the Issuer's key, `B' = ompiRed (fdhRed A')` explicit, `ρ(σ)` the probability
    that the signer errs on a uniform target (`δ(sk)^{255}` for pqov). The chain:
    `ufTagAdv_le_strict` (the probe-with-failures win of `B` is a strict win of `B.noProbe τ` or a
    failure: `Adv^{uf-tag+probe}(B) ≤ Adv^{uf-tag}_{strict}(B.noProbe τ) + failAdv(B)`), then the
    **modelling hypothesis** `TagIdeal`, then T1(a) and T1(c) of `uov-assumptions.md` §5.1
    (`advFDH_le_ompr`). `TagIdeal` says that the strict UF-Tag advantage of `B.noProbe τ` against
    the concrete KP800 is at most the det-FDH advantage (`Tag` a random function) of an
    ideal-model forger `A'` with at most `k` hash and signing queries and `N` signing queries.
    It is the paper's "Tag ideal in the standalone game only" made explicit: the protocol game and
    its proofs evaluate the concrete `Tag`, so no theorem can replace it by an oracle there. It is
    a hypothesis of the theorem, not proved, and it is the only one left
    (`Audit/IdealTag.lean` instantiates all the others for `balA0`). Against the paper's Theorem 1
    with A-OMPR: `N` counts `N_I + N_S`, `q_T` is `k + 1` (plus `N` padding targets), the
    `(k + 1 + N)·ρ` term is new (T1(c) with an aborting signer), and the permutation terms
    `q_K·2^{−479} + q_K²·2^{−799}` are absent because `Tag` is modelled as a random function.
  - *`Tag` a random permutation with inverse queries* (`Assumptions/RatatouillePerm.lean`,
    `balance_le_ompr_perm`, `balance_le_ompr_rate_perm`; with simultaneous extraction
    `balance_le_ompr_sim_perm`, `balance_le_ompr_rate_sim_perm`). The same chain with the
    modelling hypothesis `TagIdealP`: the strict UF-Tag advantage of `B.noProbe τ` is at most the
    det-FDH advantage of a forger `A'` with `Tag` the first component of a random permutation of
    `T × Z` (forward and inverse queries, `q_f`, `q_i`, `q_S`), then `advFDHPerm_le_ompr`
    (`uov-assumptions.md` §5.8). The OMPR term has `k + 1 + q_S` targets with
    `k = q_f + 1 + 2q_S`, and the permutation terms
    `(q_f + q_i + q_S + 1)²·2^{−800} + q_i·2^{−480}` (the paper's `q_K²·2^{−799} + q_K·2^{−479}`)
    appear. `TagIdealP` stays a hypothesis (`Audit/PermFDH.lean` instantiates the others).
  - *Simultaneous extraction* (`ROM/RatatouilleBalanceSim.lean`, `balance_le_sim_num`,
    `balance_le_lean_sim`, `balance_le_ufTag_sim`; under OMPR `balance_le_ompr_sim`,
    `balance_le_ompr_rate_sim`, `Assumptions/SimLinks.lean`). The `j`-th prover's run is a prefix
    of the run of all `N` calls (`proverAt_prefix`, `prefixRuns_I`, `prefixRuns_S`), and the
    extraction-failure terms are sums of per-query bad events, so all requests' extraction
    failures, of both relations, are bounded together, each query of the run charged once
    (`ROM/SimExtract.lean`, `ROM/SimJoint.lean`, plan §2m):

        Pr[win] ≤ ε_bal^sim(Q, N) + Adv^{uf-tag}(B) + Adv^{coll}_{Com}(C),
        ε_bal^sim = (q₂₁+2N)·2⁻¹⁵⁰ + (q₂₂+2N)·(ε_QS(12282) + 2⁻¹²⁸ + (n+339)·2⁻⁴⁴⁸)
                    + (q₂₃+2N)·9·2⁻¹²⁸ + chainHitEpsCombSim q M 2N + stmtBindEpsSim q 2N
                    + 2N·failEps q q_E,

    at the budget `Q` of `N` calls above (`q = N(q_A + q_V)` per kind, `q_E`, `n`). A query of the
    run is charged by the relation whose statement is committed there (the DSTs `rata0i0`,
    `rata0p0` make that at most one), so at the larger of the two relations' charges, the spend
    one at `H₂²`. Per request only the extraction game's own verifier queries (`+2N`) and the
    failure terms (binding, an opened dead leaf, Post; `failEps ≈ 2⁻¹¹⁷·⁹` at `2⁶⁴` queries)
    remain. At `2⁶⁴` queries per kind and `N = 2³⁰` calls: `N·ε_iss + N·ε_spend ≈ 2⁻²⁹·⁶`; each
    relation's simultaneous bound added (`prEvent_simIss_le`, `prEvent_simSp_le`, the run charged
    once per relation) `≈ 2⁻⁵⁹·⁶`; `ε_bal^sim ≈ 2⁻⁶⁰·⁵⁴`. Against the paper's single `ε_ext` (L8
    §9.1) one difference remains: the failure terms stay per request (`2N·failEps ≈ 2⁻⁸⁶·⁹`
    here), because the single-proof development bounds them on average over the cipher table
    rather than per query. The per-request union bound (`balance_le`, `N·ε_iss + N·ε_spend`) is
    kept.
  - *Simultaneous extraction with AES as random permutations* (`ROM/RatatouilleBalanceSimPerm.lean`,
    `balance_le_sim_numP`, `balance_le_lean_simP`; plan §2m). The same game with an adversary
    that makes forward and inverse cipher queries (`RoundAdvP`, `balQP`), the Issuer reading the
    cipher forward. The bound `ε_bal^simP` is `ε_bal^sim` with the permutation model's failure
    terms (`failEpsP`, Post `q_E·4608·q₂₁·p²` dominating, `p = 1/(2¹²⁸ − q_E)`) and the total
    hash count `n + 2q₂₁` in the `2⁻⁴⁴⁸` term: `≈ 2⁻⁶⁰·⁵⁴` at `2⁶⁴` queries and `N = 2³⁰`
    (`2N·failEpsP ≈ 2⁻⁸⁴·⁸`). The forger's and collision finder's terms stay as probabilities
    of the permutation-model run (`forgeAdvP`, `collAdvP`); the UF-Tag and OMPR corollaries are
    not redone there: they need a UF-Tag forger whose common randomness is the permutation table,
    with `bOut_reads` redone for the jointly normalized provers (Moussaka's analogue is done,
    `Assumptions/PermSimLinks.lean`).

**Correction (minor) to the proof of Theorem 1.** "It forwards every Issuer signing call to
`Sign`": `spend_response` signs before the caller's nullifier check (F5), so on the
duplicate-nullifier path the Issuer computes a signature on `(c', x')` and withholds it. If `B`
forwards that call, `(c', x')` is in `B`'s signing log, and an adversary that later spends a
state with that pair is no UF-Tag forgery, yet that state was never released, so fact 1 fails.
`B` must check the store before signing. Its simulation then differs from the Issuer only when
`derive_preimage` fails on a duplicate-path pair (an exception instead of a rejection), which is
the event `E4`. Spending a UF-Tag signing query on that pair instead would not work: a later spend
of that state is then no forgery (`uov-assumptions.md` §5.8). The Lean forgery event (`Forge`) is stated with released signatures, and the Lean
`B` probes the duplicate-path pairs instead of signing them.

## 5. No theft (N2) and honest clients

Status: the reduction is mechanized, also with `H₁`, `H₂⁰…H₂²`, `H₄` read off uniform tables.
There the programmed-point term `ε_hit` is bounded (`noTheft_leanX_hit`). Plain extraction and
`Adv^ow` stay a hypothesis and an explicit term (below, "Lean").

**Theorem 3 (N2a).** Consider an honest client with secret coins `(nf, r)` for its issued state
`c = Com(nf, ctx, T_init, r)` and `(nf', r')` for its change `c' = Com(nf', ctx, t', r')`.
Consider accepted adversarial requests whose statements differ from every honest statement. The
probability that the extracted witness of one of them is not a witness, or opens `c` or `c'`
(through an issuance's opening, a spend's parent opening or its change opening), is at most

    ε_ZK(Q_P) + ε_SE + Adv^ow,   Adv^ow ≤ q_K·2^{−127} with KP800 ideal (§2.2).

Off this event, an accepted fresh spend with the honest `nf` has a valid witness whose parent is a
commitment other than `c` and `c'` with a valid signature: it spends a separately certified state.
It may burn the honest nullifier (§3, correction to N2a), but it does not spend the honest credits.

*Proof sketch.*
1. Replace honest proofs by simulated ones (`ε_ZK`).
2. Apply weak SE (L8). An accepted adversarial proof for a fresh statement extracts.
3. In the simulated world, `r` and `r'` enter only `Com` and the KP800 input, never a proof. So an
   opening of `c` or `c'` is an inversion of `Com` from the commitments (any opening counts: one
   that differs from the client's is a collision). With KP800 ideal this costs a forward query at
   the true input (`q_K·2^{−128}` per honest commitment, as in §2.2), or a prediction among at
   least `2¹²⁸ − q_K` candidates.

This also covers copying an honest issuance commitment `c` or change commitment `c'` into the
adversary's own issuance or spend. ∎

**Correction to the bound.** An earlier version of this section stated the bound as
`ε_ZK(Q_P) + ε_SE + ε_ext + q_K·2^{−127} + ε_bind^K + Adv^{ompi}`. The terms `ε_ext`, `ε_bind^K`
and `Adv^{ompi}` are not needed: weak SE already gives a witness, and the event is about the
honest openings, not about signatures. The table's bound in §0 is the right one.

**Lean** (`lean/VoleMole/Theft/`).
- The game (`Theft/Ratatouille.lean`, `theftReal`). One honest client runs the executable spec
  (`issueOf`, `finalizeIssue`, `spendOf`), with the real provers on the tables of the
  zero-knowledge model (`Privacy/ZeroKnowledgeRO.lean`: private `H₃` slices and shared tables
  that simulators program). The adversary (`Thief`) chooses `pk`, `ctx`, `T_init`, the issuance
  response and the amount `d` from the messages it sees. It may be the Issuer. Its last stage
  reads the tables and outputs an issuance or a spend request with its own context.
- The event (`Bad`) is: accepted by the verifiers with key `pk`, fresh statement, and the
  extractor's witness is not a witness or opens `c` or `c'`. A verbatim copy is not fresh
  (`Audit/Theft.lean`, `copy_not_freshS`), so F2 is excluded. Off the event, `not_theft_spend`
  gives the witness and that its parent and new commitment are not `c`, `c'`.
- **`noTheft`**: `Pr[Bad] ≤ ε_I + ε_S + δ_S + ε_SE + Adv^ow(inverter)`.
  - `ε_I`, `ε_S`: zero knowledge (`ZeroKnowledgeRO`) at the two hops' distinguishers.
  - `δ_S` (`deltaS`): the real spend proof reads the tables differently after the simulated
    issuance's programming. This is part of the note's `ε_ZK` (its `ε_prog`); Lean keeps it as an
    explicit probability, as `δS₁` in `unlinkabilityRO`.
  - `ε_SE`: `Theft.WeakSE2`, weak SE against adversaries that get one simulated issuance and one
    simulated spend for statements they choose without reading the tables. The extractor sees
    the simulated statements and proofs, the adversary's last stage and the programmed tables,
    as in L8's log. **This is a hypothesis.**
  - `Adv^ow` (`owAdv`): an explicit inverter (`inverter`) gets `nf` and the commitment functions
    `t ↦ Com(nf, ctx, t, r)`, `t ↦ Com(nf', ctx, t, r')`, and must output an opening.
    `sim_opens_le` is step 3: the simulated world needs nothing else.
  The proof is the generic `Theft.theft_le` (`Theft/Basic.lean`): two `hop_ro` hops, then
  `Acc ∧ Fresh ∧ (¬Rel ∨ Opens) ⊆ (Acc ∧ Fresh ∧ ¬Rel) ∪ Opens`.
- **`noTheft_lean`** (`Theft/RatatouilleLean.lean`): the same with the executable Lean prover and
  simulator (`leanPIR`, `leanPSR`). Both zero-knowledge hypotheses are discharged by
  `leanPIR_zkRO` and `leanPSR_zkRO` (label rows, error `ZKRow.εz`). The hops' read budgets
  (`hAI`, `hAS`) and `WeakSE2` are hypotheses there.
- **`noTheft_lean_reads`** (`Theft/Reads.lean`): the hops' read budgets are proved. The verifiers
  are the Lean verifiers on the shared tables (`leanVIR`, `leanVSR`: `verRO`, `H₅` at `312` keys,
  the cipher at `4607`). If the adversary's last stage reads `(a₃, a₅, a_E)` (`StageBudget`: each
  `H₃` slice, `H₅`, the cipher) and the extractor reads `(x₃, x₅, x_E)`, both hops have the budget
  `(a₃ + x₃, a₅ + x₅ + 936, a_E + x_E + 9214)` (`distI_budgetL`, `distS_budgetL`; the real spend
  prover adds `624`/`4607`, the issuance simulator's programming `312`/`4607`). These two
  component budgets replace `hAI`, `hAS`, as `A.Budget` does in the privacy theorems.
- **`noTheft_lean_plain`** (`Theft/SimExtract.lean`, `Theft/SimExtractLean.lean`): `WeakSE2` is
  proved from two simpler statements (`weakSE2_ratatouille`, from the generic
  `weakSE2_of_plain`). This is L8's programming step:
  - `PlainSE`: extraction with no simulated proofs and no programming. The reduction takes the
    simulators' coins as advice, runs the simulators itself and composes the adversary's last
    stage with both programmings (budget `+624` `H₅`, `+9214` cipher keys). This needs an
    extractor that does not read `H₂³` (`extOf e`: it sees the output, the slices, `H₅` and the
    cipher), so that its view is the same with and without the programming.
  - `ProgEv … HitOp`: a fresh forgery whose verifier's `H₂³` query hits a programmed point. The
    Lean verifier reads `H₂³` at one point, `chal3`'s input (`verRO_h23_eq`), so an operation
    accepted on the programmed tables and rejected on the unprogrammed ones has that point
    programmed (`accOp_moves`). The programmed keys are the grinding keys of a simulated proof's
    recomputed prefix (`progRO_moved`). So the event means the forgery's
    `chal2 ‖ qs_check ‖ ã` equals a simulated proof's, for a fresh statement: a chain collision.

  The bound is `εz(pI; q) + εz(pS; q) + δ_S + ε_plain + ε_hit + Adv^ow(inverter)`.
  `Audit/Theft.lean` instantiates `noTheft_lean_reads` and `noTheft_lean_plain` for a trivial
  adversary.
- **`noTheft_leanH_plain`**, **`noTheft_leanX_plain`** (`Theft/LeanHb.lean`, `Theft/Tables.lean`):
  the same theorem with the other hashes random.
  - The proofs above use nothing about SHAKE. `Theft/LeanHb.lean` restates the Lean prover,
    verifiers, simulator programmings, the hop budgets and the programming step for any base
    record `Hb` with outputs of the right lengths (`leanPIRH`, `leanVIRH`, `leanProgIRH`,
    `leanPIRH_zkRO`, `distI_budgetLH`, `accOp_movesH`; `noTheft_leanH_plain`). At
    `Hb = Hashes.shake` these are the objects above (by `rfl`).
  - `Theft/Tables.lean` adds one more uniform component `x : X` to the shared tables
    (`ShX R p X = H₂³ × ((H₅ × cipher) × X)`) and takes the base record `Hb x` from it. Zero
    knowledge at every `x` gives zero knowledge with `x` uniform and visible (`zkRO_tables`, by
    averaging), with the same error. So both hops lift for free: `leanPIRX_zkRO`,
    `leanPSRX_zkRO`, `distI_budgetX`, `distS_budgetX`.
  - `noTheft_leanX_plain`: `Pr[Bad] ≤ εz(pI; q) + εz(pS; q) + δ_S + ε_plain + ε_hit +
    Adv^ow(inverter)` with the same `q`. The adversary and the extractor read `x` freely in the
    hops (`StageBudgetX`: the budgets hold at every `x`). `PlainSE` and `ProgEv … HitOpX` are now
    probabilities over uniform `x` too, against classes `Adm₀`, `Adm` of the caller's choice; the
    class for `PlainSE` must contain the last stage composed with both programmings (`hadm`;
    `StageBudgetX.comp_progT` for the read budgets). The adversary's choices before its last
    stage still do not read the tables, so they do not depend on `x`.
  - `XTab L M`, `hbX`: a concrete `X`. `H₁`, `H₂⁰`, `H₂⁴`, `H₄`, `H₂¹`, `H₂²` and `H_comb` are
    uniform tables on all inputs of at most `L` bytes, and SHAKE on longer inputs (`hbX_wf`,
    `hbX_h1`, `hbX_mu`, `hbX_h21`, `hbX_h22`). `Audit/Theft.lean` instantiates
    `noTheft_leanX_plain` at `hbX`.
- **`noTheft_leanX_hit`** (`Theft/HitChain.lean`, `Theft/HitLevel.lean`, `Theft/Hit.lean`,
  `Theft/HitTheft.lean`; the bound is generic, `Hit.progEv_chain`, for any two proof systems whose
  programmings are `SimProg`, and Ratatouille is an instance, `Hit.Rata.progEv_hit`):
  `noTheft_leanX_plain` at `X = XTab L M` with `ε_hit` bounded,

      Pr[Bad] ≤ εz(pI; q) + εz(pS; q) + δ_S + ε_plain
        + 2·((q_μ+3)·2^{−256} + (q₂₁+3)·2^{−1088} + (q₂₂+3)·2^{−448}) + Adv^ow(inverter),

  for `L ≥ 14357` (`Lmin`) and a last stage that reads the tables `H₂⁰`, `H₂¹`, `H₂²` of `x` by
  decision trees with `q_μ`, `q₂₁`, `q₂₂` queries, at every value of everything else (`AdmHit`;
  the other tables are read freely). The proof:
  - *Chain structure* (`Theft/HitChain.lean`). The verifier's prefix is `H₂²(cin2) ‖ …`, its
    `H₂²` input is `H₂¹(cin1) ‖ … ‖ 10`, its `H₂¹` input is `mu₁ ‖ … ‖ 9` with `mu₁ =
    H₂⁰(muIn st)` (`vPre_some`, `cin2_some`, `cin1_some`, `mu1_eq`). Each level reads its hash
    at one point (`vPre_congr22`, `vPre_congr21`, `vPre_congrMu` and the `cin*_congr*` lemmas).
    `chain_hit`: if the forgery's grinding point is a block of a simulator's prefix, then at the
    first level where the forgery's input and the simulation's differ the two outputs agree
    (for `H₂²`: the first 56 bytes of the programmed block, which covers a simulation that
    failed), or both statements have the same `H₂⁰` input.
  - *Sizes.* The forgery's chain inputs have at most `14357` bytes (`size_cin1_le`,
    `size_cin2_le`; the spend relation's `H₂¹` input), so with `L ≥ 14357` they are table points.
    The issuance and spend `H₂⁰` inputs have `64` and `88` bytes and fixed-length fields
    (`muIn_stI_inj`, `muIn_stS_inj`).
  - *Lazy sampling* (`Theft/HitLevel.lean`). Per simulation and level the forgery's point is computed
    by a tree with the adversary's queries plus two (the simulations' points, which fix the
    programmed `H₂³` table: `progT_fst_congr`, `qtree_forger`), and it must hit a target the
    table fixes at a point it does not output: `≤ (q + 3)/|Y|` (`pr_hit_le`, `pr_level_le`). Two
    simulations and three levels give `epsHit`.
  - *Freshness under the adversary's key.* The Lean spend statement does not hash the key `pk`
    (`Privacy.Ratatouille.stS`; the instance encoding is `nf ‖ d ‖ c' ‖ ctx`). Two spend
    statements that differ only in `pk` have the same chain, and the bound would need the QS
    check to separate them. So the bound is for `FreshOk`, which compares a spend with the
    simulated spend's statement under the adversary's key. In the theft game the Client's spend
    is under the adversary's key, so `FreshOk` is `FreshOp` there (`freshOk_stS`), and
    `noTheft_ok` is `noTheft` with weak SE for `FreshOk` (`sim_se_le_ok`). The plain-extraction
    hypothesis keeps `FreshOp` (`PlainSE.fresh_mono`).
  `Audit/Theft.lean` instantiates `noTheft_leanX_hit` for the trivial thief (`AdmHit 0 0 0`).
- **`owAdvColRO_num`** (`Theft/ComOW.lean`): one-wayness of `Com` in a random-table model, for
  the standalone experiment. `Com`'s cells are a uniform table keyed by `(nf, r)`, each a column
  over the credit value. The inverter sees the two commitments (columns) and the nullifiers, reads
  the table by a decision tree with `q` queries (`QTree`) and outputs a cell with a credit value
  and a commitment with a credit value. It wins with probability `≤ (4q + 8)·2^{−128} =
  (q + 2)·2^{−126}` (`owAdvRO_le`: a query at a true cell, by `ComHide.abs_pr_hideReal_unif_le`,
  plus a preimage among the cells read, `pr_tree_bad`). The note's `q_K·2^{−127}` differs by the
  factor 2 of the column model (a query reads a whole column). This is the counterpart of
  `hidingAdvColRO_num` (§2.2). It does not bound `owAdv` of `noTheft` (next item).
- What is not covered:
  - `PlainSE` (plain extraction) in the model of `noTheft_leanX_plain`. `ROM/` proves plain
    extraction where every hash is a lazy random oracle and the prover is an oracle computation
    with query bounds (`ratatouilleIssue_accept_le_adaptive_spec`, `balance_le_sim_num`). Four
    things separate the two statements; none is done:
    1. *The extractor's view.* `PlainSE`'s extractor (`extOf e`) sees the adversary's output, the
       `H₃` slices, `H₅`, the cipher and `x`. It sees neither `H₂³` nor the adversary's queries.
       `ROM/`'s extractor reads the prover's cipher-query log. With read budgets on the extractor
       (needed for the hops), an adversary that derives its GGM root key from an `H₂³` answer
       cannot be extracted by `extOf e`, so for such adversaries `ε_plain` is not small. The game
       must give the extractor the last stage's query log (the last stage as an oracle
       computation that returns its log), and `weakSE2_of_plain` must be restated for it.
    2. *Read budgets are not query bounds.* `StageBudget` (`Rd3`, `Rd5`, `RdE`) asks for a small
       set of cells that determines the output (certificate size), table by table. `ROM/` needs a
       query bound (a decision tree). The adversary must be an oracle computation over the
       tables, as in `ROM/TableReads.lean` (`TSpec`, `runT`, `QBudget`), extended with queries to
       `x`.
    3. *Cipher rows against cipher cells.* A read of the cipher table here returns a whole row
       (a function or permutation of the block, `2¹²⁸` cells). `ROM/` counts single cells
       (`CTable = Cell → Blk`), and its binding term `2·q_E²·2^{−256}` is per cell. The adversary
       must query cells; a cell query reads one row, so the hop budgets still follow.
    4. *Lazy oracle against finite tables.* `ROM/` samples the hashes lazily on `Kind ×
       ByteArray`; here the tables are finite (`H₂³` on grinding points, `H₅` on 37-byte inputs,
       `x` on short inputs) with SHAKE elsewhere. The bridge needs that the verifier, the prover
       and the simulators' recomputation query only table points (sizes of every hash input), and
       `prEvent_randomOracle_eq_eager` on that support.
  - `ε_hit` is bounded for Ratatouille (`noTheft_leanX_hit` above), for Moussaka with one token
    (`noRedirect_leanX_hit`, `security/moussaka.md` §5.3: for well-formed statements and a
    freshness on the hashed fields) and for Ratatouille with `U` Clients and `M` spends
    (`noTheftN_leanX_hit`, below). It is not bounded for Moussaka with `U > 1` tokens or for
    unbound Moussaka: their many-token theorems (`noRedirectN_lean_plain`, `nmUN_lean_plain`)
    still use SHAKE for the chain hashes and keep the terms `SlotEvN` as hypotheses. The generic
    steps are there (`Theft/ManyTables.lean`, `Hit.progMovesN_chain`); what is missing is each
    game at a value of the extra table and its freshness for well-formed statements.
  - `Adv^ow ≤ q_K·2^{−127}` for the inverter of `noTheft`. In the games `Com` is concrete code:
    the issuance and spend relations evaluate Keccak-p[800,12], and the zero-knowledge theorems
    need the honest witness to satisfy that concrete relation. So `Com` cannot be a random table
    of the game, and the inverter (which runs the adversary and the extractor) is any function:
    some inverter wins with probability `1` (`Audit/Theft.lean`, `owAdv_one_ratatouille`).
    `Adv^ow` is therefore a computational assumption on Keccak-p[800,12] for the explicit
    inverter, as `ε_hide` is for the privacy theorems (`Privacy/ComHide.lean`). The
    random-table bound is `owAdvColRO_num` above, for the standalone experiment only.
  - The theorems above have one honest client with one issuance and one spend; `U` clients and
    `M` spends are below. In both games the adversary's choices of `T_init`, `ctx` and `d` do
    not read the tables (as in `unlinkabilityRO`), and it outputs one request.
  - A bound on `δ_S` for the Lean prover (as `deltaS1R_le`).

**`U` honest clients and `M` honest spends: [Lean]** (`Theft/Many.lean`,
`Theft/RatatouilleMany.lean`, `Theft/RatatouilleManyLean.lean`). Theorem 3 for many clients whose
change tokens are spent again.

*The game THEFT^{U,M}* (`theftRealN`). Slot `j < U + M` has its own coins `(nf_j, r_j)`.
- Slots `0 … U − 1`: client `h` requests a token worth `T_init h` under `ctx h` (`specI_eqN`:
  the slot is `issueOf`). The adversary (`ThiefN`, one key `pk`) answers client `h` from all `U`
  requests, and the client finalizes (`fin_issue`: `finalizeIssue`).
- Slots `U … U + M − 1`: the adversary chooses, from every request seen so far, a client and an
  amount `d`. The client spends `d` from its **current** token: its issued token, or the change
  token of its last spend. The slot's coins make the change commitment (`specS_eqN`: the slot is
  `spendOf` on the client's token). The adversary answers with a refund and a signature chosen
  from the requests including this one, and the client finalizes its change token (`fin_spend`:
  `finalizeSpend`). As in the C++, a spend the client refuses keeps the token, and a prover abort
  consumes it. A spend of a change token reveals the nullifier of the slot that made it
  (`Audit/TheftManyR.lean`, `change_chains`, `next_spend`).
- These choices do not read the tables. At the end the adversary reads the tables and outputs
  one Issuer operation.

The clients' state is a function of the log of honest statements and proofs, in public form
(`St`, `PTok`, `stOf`: for each client the slot whose coins made its token's commitment, and
`t`, `x`, `s`). So the simulated world uses the coins of slot `j` only through `nf_j` and the
commitment function `(ctx, t) ↦ Com(nf_j, ctx, t, r_j)`.

*The event* (`BadN`): the operation is accepted with `pk`, its statement differs from every
honest statement of its relation in the log (`FreshOpN`), and the extracted witness is not a
witness or opens the commitment of **some** honest slot (`comAt`: the commitment in the statement
slot `j` proves, an issued state or a change state). Off the event an accepted fresh spend has a
witness whose parent commitment and change commitment are no honest commitment
(`not_theftN_spend`). This is the extraction form of N2a (§3): a spend that carries an honest
nullifier spends a separately certified state.

- **`noTheftN`**: `Pr[BadN] ≤ U·ε_I + M·ε_S + Σ_i δ_i + ε_SE + Σ_j Adv^ow(inverter j)`.
  - The `U + M` zero-knowledge hops are the generic ones of `Theft/Many.lean` (`theftN_le`), with
    the two proof systems as one on the sum of the instance types (`sumProveO`, `zk_sumO_inl`,
    `zk_sumO_inr`, `Theft/ManyPlain.lean`). `δ_i` is the collision term of hop `i` (`deltaNR`).
  - `ε_SE`: weak SE with `U + M` simulated proofs (`Theft.WeakSEN`), **a hypothesis**.
  - `Adv^ow(inverter j)` (`owAdvK`): the inverter of slot `j` gets `nf_j` and the commitment
    function `(ctx, t) ↦ Com(nf_j, ctx, t, r_j)`, holds the other slots' coins, and must output a
    context, a credit value and an opening of that commitment (`inverterN`, `sim_opens_leN`).
    The sum has `U + M` terms, one per honest commitment (a union bound over the commitment that
    is opened). Two differences from `owAdv` of the one-client theorem: the inverter sees the
    nullifier of a change commitment (it is public once the change is spent), and it chooses the
    context and the credit value (the adversary chooses the client and the amount adaptively).
    As for one client, `Adv^ow` is an assumption on the explicit inverter: some inverter wins
    with probability `1` (`Audit/TheftManyR.lean`, `owAdvK_one`).
- **`noTheftN_lean`**: with the Lean prover, `ε_I = εz(pI)`, `ε_S = εz(pS)` (`leanPIR_zkRO`,
  `leanPSR_zkRO`).
- **`noTheftN_lean_reads`**: the hops' read budgets are proved (`distPI_budgetL`,
  `distPS_budgetL`), from the generic `distN_budget` (`Theft/ManyReads.lean`). If the
  adversary's last stage reads `(a₃, a₅, a_E)` (`StageBudgetN`: each of the `U + M` slices, `H₅`,
  the cipher) and the extractor `(x₃, x₅, x_E)`, every hop has the budget

      q = (a₃ + x₃,  a₅ + x₅ + 312 + (U + M − 1)·624,  a_E + x_E + (U + M)·4607).

  Hop `i` runs the `U + M − i − 1` later real proofs (`624`/`4607` each, `realFrom_rd5`,
  `realFrom_rdE`), the verifier (`312`/`4607`) and the programming of the `i` earlier simulations
  (`312`/`4607` each, `simPre_isProg`). At `U + M = 2` this is the budget of
  `noTheft_lean_reads`.
- **`noTheftN_lean_plain`**: `WeakSEN` is proved from two simpler statements
  (`weakSEN_ratatouille`, from the generic `weakSEN_of_plain` and `progMovesN_of_slots`,
  `Theft/ManyPlain.lean`):
  - `PlainSEN`: extraction with no simulated proofs and no programming, against the last stage
    composed with `U + M` programmings (budget `+(U + M)·312` `H₅` keys, `+(U + M)·4607` cipher
    keys), for an extractor that does not read `H₂³` (`extOfN e`).
  - `SlotEvN i … HitKeyR`, one term per simulated proof `i`: the fresh forgery's verifier reads
    `H₂³` at a grinding key whose prefix is the recomputed prefix of simulated proof `i`. A key
    that the composition of the programmings moves is moved by one of them (`simPre_moved`), and
    the programming of one proof moves only grinding keys of its recomputed prefix
    (`progRO_moved`).

  The bound is `U·εz(pI; q) + M·εz(pS; q) + Σ_i δ_i + ε_plain + Σ_i ε_hit,i +
  Σ_j Adv^ow(inverter j)`. `PlainSEN` and the `SlotEvN` terms are hypotheses, for the reasons
  given above for `PlainSE` and `ε_hit`.
- **`noTheftN_leanX_plain`**, **`noTheftN_leanX_hit`** (`Theft/RatatouilleManyHit.lean`): the
  many-Client theorem in the model of `noTheft_leanX_plain`, and with the programmed-point terms
  bounded.
  - *The extra table.* The game on `ShX R pI X` at a value `x` of the extra table is the game
    of the adversary `atTN A x` with the base record `Hb x` (`PN_atX`, `pgP_atX`, `badN_atX`), so
    every hop's distinguisher has the budget of `noTheftN_lean_reads` at every `x`
    (`distPI_budgetX`, `distPS_budgetX`; generic: `distN_at`, `distN_budgetX`,
    `Theft/ManyTables.lean`). The zero-knowledge hops lift as for one Client
    (`leanPIRX_zkRO`, `leanPSRX_zkRO`). `WeakSEN` is replaced by `PlainSEN` and the programming
    term `ProgMovesN`, both over uniform `X` (`weakSEN_of_plain`).
  - *Freshness.* The programming term is for `FreshOkN` (each logged spend statement is compared
    under the adversary's key). Every spend statement of the game has the adversary's key
    (`xN_pk`), so on the simulated log the game's freshness is `FreshOkN` (`freshOkN_of_log`,
    `sim_se_leN_ok`). `PlainSEN` keeps `FreshOpN`.
  - *The bound* (`Theft/HitMany.lean`). `slotEvN_chain`: for simulated proof `i` of `N`, the
    forgery's point at each level is computed by a tree with the adversary's queries plus `N`
    (the `N` simulations' points fix the programmed `H₂³` table: `seLog_fst_congr`,
    `QTree.of_cells`, `qtree_forgerN`), so `ε_hit,i ≤ (q₂₂+N+1)·2^{−448} + (q₂₁+N+1)·2^{−1088} +
    (q_μ+N+1)·2^{−256}` (`epsHitN`), and `ε_moves ≤ N·epsHitN` (`progMovesN_chain`,
    `progMovesN_hit`).
  - With `XTab L M'`, `L ≥ 14357`, a last stage that reads the chain tables with `q_μ`, `q₂₁`,
    `q₂₂` queries (`AdmHitN`) and `N = U + M`:

        Pr[BadN] ≤ U·εz(pI; q) + M·εz(pS; q) + Σ_i δ_i + ε_plain
          + N·((q₂₂+N+1)·2^{−448} + (q₂₁+N+1)·2^{−1088} + (q_μ+N+1)·2^{−256})
          + Σ_j Adv^ow(inverter j),

    `q = (a₃ + x₃, a₅ + x₅ + 312 + (N − 1)·624, a_E + x_E + N·4607)`. `PlainSEN` stays a
    hypothesis, against a class that contains the last stage composed with `N` programmings
    (`hadm`). `Audit/TheftManyR.lean` instantiates it for the trivial adversary.
- `WeakSEN` at two proofs implies `WeakSE2` (`weakSE2_of_weakSEN`, `Theft/ManyPlain.lean`), with
  the same error. The converse is not claimed.
- `Audit/TheftManyR.lean`: the four theorems instantiated for a trivial adversary, for every
  `U ≥ 1` and `M`; `replay_not_freshNR`, `changed_freshNR`.
- Scope. The `U` issuances come first. One Issuer key. `ctx h` and `T_init h` are fixed in
  advance; the spend queries are adaptive; `M` is fixed in advance. The adversary outputs one
  request. Not done: the many-client theorem with the other hashes read off uniform tables (as
  `noTheft_leanX_plain`), and a bound on the `δ_i`.

**N2b fails (F2).** A verbatim copy of an honest request verifies, and whoever submits first wins.
This does not break balance: the copied spend consumes the honest token's credits, which Thm 1
counts. But the copier gets the service paid for, and it receives `(x', s')`. It cannot use `s'`,
because it lacks the opening of `c'`, but it can withhold it. The client's change `t + x − d + x'`
is then lost, since the store now holds `nf`. See §7.

## 6. Unlinkability (N3)

**Theorem 2.** Let `Q_P` be the number of honest proofs (issuance and spend) and `Q_c = Q_P` the
number of honest commitments. Let `q_H` be the adversary's queries to the seed XOF. Then, for
every classical malicious Issuer:

    Adv^{unlink} ≤ ε_ZK(Q_P) + ε_hide^K + q_H·Q_P·2^{−256}

**Simulator.**
- For an issuance: output a uniform `c` and a simulated proof for `(c, T_init, ctx)`.
- For a spend: output a uniform `nf`, the given `d`, a uniform `c'` and a simulated proof for
  `(pk, nf, d, c', ctx)`.
- The client still finalizes against the commitment string it sent.

*Proof.*
1. **H1: derived randomness.** `(nf, r, ρ)` from the seed XOF are replaced by uniform values. The
   cost is the event that the adversary queries `DST ‖ seed` (`q_H·Q_P·2^{−256}`), plus Lemma DS
   for independence from the proof-system oracles.
   - **Correction.** The cost must also include the event that two seeds of one domain collide.
     Two issuances, or two spends, with equal seeds get equal `(nf, r, ρ)`, while H1 gives them
     independent values, so the two games differ there. The correct cost is
     `(Σ_d n_d·q_d + Σ_d C(n_d, 2))·2^{−256}` for `n_d` requests in domain `d` (issue, spend)
     and `q_d` XOF queries in that domain. This is at most `(q_H·Q_P + Q_P²/2)·2^{−256}`.
     **[Lean]** (`lean/docs/zk.md` §10.6): `(2q_H + 2)·2^{−256}` per world in the four-request
     game, `unlinkability*_seed`.
2. **H2: simulated proofs.** Every honest proof is replaced by a simulated one (`ε_ZK`, adaptive
   statements, `lean/docs/zk.md` §2). This is valid for a malformed `pk`: ZK needs only that the honest
   witness satisfies the relation for the given `pk`, and the client guarantees that by checking
   `P(s) = Tag(c, x)` before proving (`ratatouille.cpp:221`).
3. **H3: random commitments.** Every honest commitment is replaced by an independent uniform
   string, keeping the client's private `(nf, t, r)` (`ε_hide^K`). This works because, after H2,
   the opening enters nothing but `Com`. `nf` stays uniform and independent until it is revealed,
   because it entered only the replaced commitment.

In H3 every message is a function of `ℒ` and fresh randomness. The values that depend on the hidden
state are `t`, `x`, `r`, `s`, `nf'`, `t'` and `r'`. Of these, `s` and the refund `x` reach the
adversary only as witnesses of simulated proofs. So H3 is the ideal world. ∎

**[Lean] `lean/VoleMole/Privacy/Ratatouille.lean`.** A left/right form of N3 on
`Spec/Ratatouille.lean`'s `issueRequestWithSeed`, `finalizeIssue`, `spendRequestWithSeed` and
`finalizeSpend`, with the seed XOF's outputs drawn uniformly (`issueRequestWithSeed_eq`,
`spendRequestWithSeed_eq`; H1 for the random-oracle games below: `lean/docs/zk.md` §10.6). A malicious Issuer (any key, context,
responses, refunds and amounts) issues a token worth `T_init` to each of two Clients; in round 1
Client `b₁` spends `d₁` and finalizes its change token; in round 2 Client `b₂` spends `d₂` from its
current token (the change token if `b₂ = b₁`). A round runs only if every candidate token is valid
and affords the amount, else it is refused for both (feasibility is leakage).
- H2, one proof at a time: `issue_close`, `spend_close`, from zero knowledge as the hypothesis
  `Privacy.ZeroKnowledge` (including the grinding abort; the distinguisher may know the witness).
  **On `main` no efficient simulator satisfies this per-proof hypothesis** (a distinguisher that
  knows `r = w[0..16)` runs the test of `lean/docs/zk.md` Prop. 4.1); there the (PU) argument above
  replaces it: [Lean] `Privacy/RatatouilleMain.lean` (below). With the label-row fix it is
  `lean/docs/zk.md`'s theorem.
- After H2, `simGame_iff` (from `view_map`): the spec world is a *public* world whose tokens hold
  `(nf, t, x, s)` and the commitment the Client sent, with no opening.
- H3: `hiding_hop`, with `ε_hide^K` as the hypothesis `hidingAdv ≤ εhide` for the explicit
  reduction (the four honest commitments, each evaluated at the credit value the run produces, and
  their nullifiers).
- In the ideal world the four worlds `(b₁, b₂)` have the same distribution exactly
  (`idealGame_eq`): each spend reveals a nullifier that appears nowhere else.
- `unlinkability`: any two worlds differ by at most `4εI + 4εS + 2εhide`. So a spend is unlinkable
  to its issuance (`b₁`) and to an earlier spend of the same Client through the change token
  (`b₂ = b₁` against `b₂ ≠ b₁`).
- **On `main` (no label rows), with the joint (PU) hop** (`Privacy/RatatouilleMain.lean`,
  `lean/docs/zk.md` §4.2): the same game with `main`'s statements (proof sizes `Sizes.main`) and
  the executable prover in the model of `zk_rom_ic` (each proof with its own uniform tables; the
  Issuer's guess sees each proof's `H₃`, `H₅` and cipher, reads `H₃` and the cipher at `q₃`, `q_E`
  keys and `H₅` with consistent read sets; its responses, refunds and amounts do not read the
  tables): `unlinkability_main`, any two worlds differ by at most
  `8·(q₃·2⁻¹²⁸ + 221·(4607 + q_E)·2⁻¹²⁸) + 15·(PU(b₁, b₂) + PU(b₁', b₂')) + 2·εhide`, where `PU`
  (`puTermR`) is the probability, with all four proofs simulated, that the guess's `H₅` read set on
  some proof's table contains a candidate for that proof's witness prefix (the opening of the
  token it spends or issues, a change token's included). Bounding it is (PU), one-wayness of
  Keccak-p[800] in the openings, an assumption. The joint hop is needed: round 2 may spend round
  1's change token, whose opening round 1's proof commits to. Not covered there: several proofs
  on shared tables (cross-proof `iv` collisions) and an Issuer reading `H₂³`; for **one** proof
  both are covered on `main` by `zk_rom_ic_h23_main` (`ZK/HopsMainIC.lean`, `lean/docs/zk.md`
  §4.2).
  **(PU) as a game** (`Privacy/PU.lean`, `Privacy/PUKeccak.lean`, `lean/docs/zk.md` §4.3):
  `puAdv com P = Pr[r ∈ P(n, com n r, aux)]` for a predictor with `c` candidates.
  `Com(nf, ctx, t, r)` is one call of Keccak-p[800,12] on the encoded state, truncated to 32
  bytes (`ratatouille_com_eq_comP`), and with a uniformly random permutation in its place a
  predictor with `q` forward and inverse queries has advantage at most
  `(c + q)/(2¹²⁸ − q) + q/(2⁵⁴⁴ − q)` (`puAdvPerm_ratatouille_le`): the generic `(q + 1)·2⁻¹²⁸`
  of the (PU) paragraph below, for one commitment. For Keccak-p[800,12] itself (PU) is an
  assumption. Unlike for Moussaka (`anonymity_main_pu`), `puTermR` is **not** yet reduced to
  `puAdv`: with all proofs simulated the game is a function of the commitment columns
  `t ↦ Com(nf, ctx, t, r)` (`simGame_iff`) and the change token's credit value is the Issuer's
  choice, so the reduction needs the game's single use of each column made explicit. As for
  Moussaka, the spend proofs that are computed but not shown (a failed finalization, a refused
  round) are not predictions of a secret; their part of `puTermR` would be bounded by
  `(q₅ + 1)·2⁻¹²⁸` each through the simulator's uniform `d` (`pr_thetaMain_le`; mechanized for
  Moussaka only).
- The spec's proof sizes are a parameter (`Spec.Ratatouille.Sizes`: `main`'s, or the label-row
  layout's 256 bytes longer proofs). **[Lean] `lean/VoleMole/Privacy/RatatouilleLean.lean`**:
  `unlinkability_label_rows`, the same bound with the executable Lean prover and verifier as the
  primitives (`leanPrim`, label rows), assuming only the tape hypotheses (`TapeHyp`,
  `lean/docs/zk.md` §10.1), hiding and the hash record's output lengths (proved for SHAKE,
  `unlinkability_label_rows_shake`, which also derives the tape hypotheses from one hypothesis per
  hop, `ZK/Hops.lean`, so `εI`, `εS` are sums `ε_rho + ε_grind + ε_bavc + ε_lab`; BAVC and CRT
  completeness are proved): the C++ witness encodings
  (`encodeIssueWitness`, `encodeSpendWitness`) satisfy the issuance and spend systems for every
  combination (`issue_holds`, `spend_holds`: committed Keccak states, the carries of `t + x` and
  `t' + d` as `carries` computes them, `carries_testBit`, and `R_iss`, `R_spend`).
- **[Lean] In the random-oracle and ideal-cipher model** (`lean/VoleMole/Privacy/RatatouilleRO.lean`,
  `lean/docs/zk.md` §10.2): the Issuer's guess also sees the random tables (`H₃` per proof, `H₂³`,
  `H₅`, the cipher) and the four proofs share them. `unlinkabilityRO` (any `ZeroKnowledgeRO`
  proof systems with bounded reads) and `unlinkabilityRO_lean` (the Lean prover, SHAKE, AES as an
  ideal cipher): any two worlds differ by at most
  `8·εRO(q₃, q₅ + 3·624, q_E + 3·4607) + 2·δI₁ + Σ_w (δS₁ w + δS₂ w) + 2·εhide`, with the explicit
  programming-collision terms `δ`, bounded in Lean (`lean/VoleMole/Privacy/RatatouilleDelta.lean`,
  zk.md §10.2): `δI₁ ≤ noHitProb + 2⁻¹⁰²⁴`, `δS₁ ≤ 2⁻¹¹³ + εRO(0, 312, 4607) + noHitProb +
  2·2⁻¹⁰²⁴`, `δS₂ ≤ … + 3·2⁻¹⁰²⁴`, so **`unlinkabilityRO_lean_num`**: any two worlds differ by at
  most `8·εRO(q₃, q₅ + 1872, q_E + 13821) + 4·(2⁻¹¹³ + εRO(0, 312, 4607)) + 6·noHitProb +
  12·2⁻¹⁰²⁴ + 2·εhide` (about `2⁻¹⁰²·³` plus the budget terms). The simulated world is
  `Ratatouille.view` for an Issuer that also sees the tables, programmed as a function of the
  requests it sees and the simulator coins (`Vtab`, `simGameR_iff`), so `simGame_iff`,
  `stage_ideal` and `idealGame_iff` are reused unchanged, with the coins and tables fixed in the
  hiding reduction and in the exchange of the nullifiers (`idealGameR_eq`). A spend programs
  `H₂³` only if its round runs. Here the Issuer's choices of responses and amounts do not read the
  tables (only its guess does); the next item lifts this.
- **[Lean] With an Issuer whose interaction reads the tables**
  (`lean/VoleMole/Privacy/RatatouilleRA.lean`, zk.md §10.3). Each of the Issuer's two message
  stages reads the four slices and the shared tables, consistently, with a budget per stage
  (`AdversaryRA.IBudget i₃ i₂ i₅ i_E`). Stage 1 is the issuance responses and `d₁`, read on the
  tables after the issuance simulations. Stage 2 is the response to round 1 and `d₂`; it reads
  round 1's request, on the tables after round 1's simulation. The game (`viewRA`) is `viewR` with
  the messages fixed to this transcript. With real slots, every message and proof reads the
  uniform tables. The issuance hops count both stages, the three real proofs and the guess as the
  distinguisher. The spend hops are `hop_roA` with the adaptive theorem
  (`ZK.Sim.lean_zeroKnowledgeROA`), and their collision terms are `pr_collide_adaptive`:
  - round 1's statement (its token and `d₁`) is read by stage 1 through the two issuance
    programmings: `(i₃, i₂, i₅ + 624, i_E + 9214)`;
  - round 2's is read by the whole transcript, stage 2 also through round 1's programming:
    `(2i₃, 2i₂, 2i₅ + 1560, 2i_E + 23035)`.

  The simulated world is `Ratatouille.view` for the Issuer at fixed coins, slices and tables
  (`atRA`). Its messages read the tables as functions of the requests it has seen, and `view_congr`
  shows the two Issuers agree. So hiding and `idealGame_iff` apply unchanged.
  **`unlinkabilityRA_lean_num`**: any two worlds differ by at most

      4·εRO(2i₃ + q₃, q₅ + 2i₅ + 1872, q_E + 2i_E + 13821)
        + 2·εAd(9; i₃ + q₃, q₅ + i₅ + 1248, q_E + i_E + 13821; i₃, i₂, i₅ + 624, i_E + 9214)
        + 2·εAd(9; q₃, q₅ + 936, q_E + 13821; 2i₃, 2i₂, 2i₅ + 1560, 2i_E + 23035)
        + 6·i₃·2⁻¹²⁸ + 4·(2⁻¹¹³ + εROP(0, 312, 4607; 2i₅ + 1560, 2i_E + 23035))
        + 6·noHitProb + 12·2⁻¹⁰²⁴ + 2·εhide.

  This is about `2⁻¹⁰¹·⁶` at zero budgets (`2⁻¹⁰¹·²` if the interaction reads `H₂³`), against
  `2⁻¹⁰²·³` for `unlinkabilityRO_lean_num`. The difference is the simulations' programmings,
  which the spend hops count as the reader's reads.
  **With AES as random permutations** read forward and inverse (`lean/docs/zk.md` §10.4):
  `unlinkabilityRO_lean_num_perm`, `unlinkabilityRA_lean_num_perm`, the same bounds with `εROPm`,
  `εROPmP`, `εAdPm` (the PRP/PRF switching term included); numerically the same to two
  decimals.
  **Consistency for free**: for an Issuer whose two stages are VCVio oracle computations over
  the tables (`AdversaryOC`, `lean/VoleMole/ROM/PrivacyReads.lean`), `IBudget` is a theorem from
  the syntactic query bound (`QBudget`): `unlinkabilityOC_lean_num`,
  `unlinkabilityOC_lean_num_perm`, the same bounds with no consistency hypothesis
  on the interaction (the guess keeps its semantic read budget).
- **[Lean] With one shared `H₃` and with the real seeds.** The games are also proved with one
  `H₃(wPrefix ‖ μ₁ ‖ ρ ‖ 3)` in the shared tables instead of per-proof slices, with no
  prefix-collision term (`unlinkabilitySh_num`, `unlinkabilityRASh_num`, `unlinkabilityOCSh_num`,
  `_perm`; zk.md §10.5; bounds in §11), and H1 is mechanized for all of them
  (`unlinkability*_seed`, `+ 2·(2q_g + 2)·2⁻²⁵⁶`, `q_g` the Issuer's XOF reads; zk.md §10.6).
- **[Lean] The games are live** (`lean/VoleMole/Audit/Liveness.lean`). Every Lean-prover game uses
  `Sizes.labelRows`, the size of the Lean proofs, so `vecOf` keeps every proof the prover returns,
  and no honest step verifies a proof (the Issuer is the adversary). With an Issuer holding a
  trapdoor key (`pkR`, the map of a key of pqov's key generation with `O = 0`), an honest
  issuance finalizes to a valid token and an honest spend to a valid change token (`iss_live`,
  `sp_live`); if the provers do not abort, both rounds run on every tape, round 1 revealing the
  nullifier of Client `b₁`'s token and round 2 that of Client `b₂`'s current token
  (`realGame_liveR`); the Lean provers of the random-oracle games abort with probability
  `≤ 2⁻¹¹³` per proof (`leanPIR_some`, `leanPSR_some`).

**A precision found while mechanizing H3.** "The client still finalizes against the commitment
string it sent" is not enough on its own: before its next spend the Client checks its token with
`Com` recomputed from the opening (`ratatouille.cpp:221`, `TokenS.Valid`), and in H3 that check
would fail for the uniform string. The hybrid Client must check validity against the commitment
it sent; before H3 the two checks coincide (`simGame_iff`).

**`main` versus the fix.**
- **`main`.** lean/docs/zk.md's generic form `ε_lab = (Q₅ + n_mult·Q_V)·Pred_R + Q_P·2^{−128}` with
  `Pred_R ≤ (q_K + 1)·2^{−128}` is a product of query counts, and it is vacuous at
  `Q₅ ≈ q_K ≈ 2⁶⁴`.
  - In the ideal-permutation model it can be sharpened. Let K be the event that some KP800 query
    hits a true `Com` input of an honest proof's prefix `r`; then `Pr[K] ≤ q_K·2^{−128}`.
  - Outside K, each `r` is uniform among at least `2¹²⁸ − q_K` values given the view.
  - Each H₅ query names one `iv` (one proof, up to `ε_iv`) and one candidate `r`.
  - So:

        ε_lab^{main} ≤ (Q₅ + n_mult·Q_V)·2^{−127} + q_K·2^{−128} + Q_P·2^{−128}.

  - The same `r` is the prefix of two proofs: a token's issuance proof and its first spend proof.
    A later state's `r` is the prefix only of its own spend proof (the previous spend held it at
    offset 96). The per-query bound is unaffected.
  - So on `main`, Theorem 2 holds with security about `2^{−127}` per query, **but it rests on
    modelling KP800 as ideal in two places**: hiding (H3) and (PU) inside the ZK hop.
- **Fix (`voleith-label-rows`).** `ε_lab^{fix} = (Q₅ + n_mult·Q_V + Q_P)·2^{−128}`, independent of
  the witness. KP800 is then needed only for hiding. The proofs become witness-indistinguishable
  even for a verifier who knows `r`, for example after a client compromise or under a
  standard-model analysis of Keccak in which one-wayness and hiding differ. The numerical bound is
  essentially unchanged for Ratatouille. The gain is structural (F6).

**What the Issuer learns at spend time.**
- **Learns:** `nf` (fresh, uniform, independent of everything it has seen), `d` (public by
  design), `c'` (hiding), `ctx`, `pk`, timing, and the refund `x'` it chooses.
- **Does not learn:** `t`, the carried refund `x`, `t'` or `nf'`. Refunds are therefore private
  when spent, though not when granted.
- **Feasibility leakage.** The leakage `ℒ` hides *which* outstanding token was spent. It does not
  hide *whether* some client could afford `d`, which is inherent to an ACT.
  - The anonymity set of a spend is the set of outstanding tokens under `(pk, ctx)` with
    `t + x ≥ d` and `t + x − d < 2⁶⁴`.
  - Because refunds are unbounded (F4), a malicious Issuer can push a targeted client to
    `t + x ≥ 2⁶⁴` and so impose a lower bound on its next `d`. {{ACT}} prevents this by bounding
    refunds with `t ≤ s + a` and proving `c + a < 2^L`.
- **Partitioning** by `pk` or `ctx` is visible, as in {{ACT}}. Clients must use the published key,
  and contexts must be coarse.

## 7. Findings

**F1 (critical if keys are shared). Cross-protocol minting via PomFRIT.**
- PomFRIT's Issuer is a raw preimage oracle on Client-chosen targets:
  `issue_response(sk, request) = sk.derive_preimage(request)` (`src/pomfrit/pomfrit.cpp:188-190`).
  It uses the same `uov::SecretKey` type, with no domain separation.
- A PomFRIT client sends `y = Tag(Com(nf, ctx, 2⁶⁴−1, r), 2⁶⁴−1)` and gets a Ratatouille token
  worth `2⁶⁵ − 2` credits, with no Ratatouille issuance.
- Demonstrated in `<scratchpad>/demo/cross_key.cpp`, which builds against `build/libvole-mole.a`.
  Output:

      Ratatouille Issuer accepted a spend of d = 18446744073709551615 credits that it never issued
      change token: credit = 18446744073709551615, refund = 0

- Only `uov.hpp:64-67` warns, generically. `ratatouille.hpp` and the README's Security
  considerations say nothing.
- **Fix:** document that a Ratatouille key must not be used for PomFRIT (or any raw-target
  signing), or enforce it with distinct key types. A per-protocol salt or tweak in `Tag`
  (R1) does not help, because PomFRIT signs arbitrary targets.

**F2 (medium). No spend-session binding; a hijacked request burns the whole balance.**
- `SpendRelation`'s statement is `(pk, nf, d, c', ctx)` (`spend.hpp:321-327`). No `msg` is passed
  to VOLEitH. {{ACT}} binds `ctx_spend` (the challenge digest), and Moussaka binds
  `challenge_digest` (`moussaka.hpp:74-84`).
- **Consequences.** Any party that sees the request bytes can submit them first: a relay, an
  origin forwarding to the Moderator, or a TLS-terminating proxy. It then:
  - takes the service that `d` pays for (redirecting the payment to its own challenge or
    session);
  - receives `(x', s')` and can withhold it.

  The client cannot resubmit, because `nf` is recorded. So it loses its change `t + x − d + x'`,
  not just `d`.
- This does not break balance (Thm 1), and Ratatouille's draft does the same.
- **Fix:** add a `ctx_spend` or challenge digest to the spend statement, as Moussaka does. Also,
  or alternatively, have the Issuer store responses by `nf` so that the client can re-fetch them
  ({{ACT}} §Refund Finalization).

**F3 (low). Finalization consumes state on failure.**
- `finalize_spend` moves `impl_` out before verifying (`ratatouille.cpp:291-299`), and so does
  `finalize_issue` (`:188-192`). After one corrupted or malicious response, the client cannot
  retry with a corrected one.
- For a spend, the old token is already consumed and `nf` is recorded, so the balance is lost.
- {{ACT}} instead lets the client keep `state` and ask again.
- **Fix:** consume only on success, or return the pending state on failure.

**F4 (low). Unbounded refunds.**
- `spend_response` and `finalize_spend` accept any `x' < 2⁶⁴`, so `t + x` may exceed `2⁶⁴ − 1`.
  This is documented at `ratatouille.hpp:59-61`.
- Balance is unaffected (§4). But the client must then spend at least `t + x − (2⁶⁴ − 1)`, which
  causes a feasibility leak (§6) and may lock the token where prices are fixed (for example, the
  example's `d == price` policy, `examples/ratatouille.cpp:49`).
- An honest Issuer that refunds `x' ≤ d` never triggers this. By induction, `t + x ≤ T_init` stays
  below `2⁶⁴`.
- **Fix:** have `finalize_spend` reject `t' + x' ≥ 2⁶⁴`, or adopt {{ACT}}'s allowance `a`.

**F5 (informational). API ordering.**
- `spend_response` takes `refund` before the caller learns `d`, so a refund that depends on `d`
  requires parsing `request[24..32)` by hand.
- It signs before the caller's nullifier check (`ratatouille.cpp:281-282`). The draft's "record
  before sending" makes this safe if callers follow it. But suppose a caller leaks `response` on
  its duplicate-`nf` path, for example by logging it or returning it in an error. A client can
  make a second valid request from the same token with a fresh `c'₂`. It would then get
  `Tag(c'₂, x')` signed: a second change token with a fresh nullifier, which is a double spend.
  Thm 1's injectivity hypothesis is exactly the store.
- **Fix:** make the store a callback inside `spend_response`, or return the response only through
  an explicit commit step.

**F6 (informational). On `main`, Ratatouille ZK is conditional on KP800 one-wayness in `r`.** See
§6. The fix makes ZK unconditional. No practical attack exists on `main`: guessing `r` costs
`2¹²⁸` per target.

No issue was found in:
- the DST layout, the instance encodings, or the Com and Tag layouts against the draft;
- the arithmetic (Lean);
- range checks, the adder, or `nf` binding (L7);
- deterministic `DerivePreimage` (one preimage per target, domain-separated from `ov_sign`);
- `rho` freshness.

## 8. Deviations from the drafts

Against `draft-authors-mole-vole-act.md`:

| Item | Draft | Implementation | Effect |
|---|---|---|---|
| Com, Tag layouts and DSTs `c0`, `t0`, `i0`, `p0` | §KP800 | identical (`commit.hpp:56-93`, `dst.hpp:47-54`) | none |
| Instance encodings | `c‖⟨T⟩‖ctx`; `PKDigest‖nf‖⟨d⟩‖c'‖ctx` | identical (`issue.hpp:151-155`, `spend.hpp:321-327`) | none |
| Extra DSTs | — | `l0` (UOV combination), `s0`/`s1` (seed XOFs) | needs Lemma DS |
| Randomness | `nf, r ← uniform` | squeezed from a 32-byte seed by SHAKE (`ratatouille.cpp:69-84`) | computational (H1 of Thm 2) |
| DerivePreimage | TODO: `Expand_v(t‖seed_sk‖ctr)` | `H(t‖sk_seed‖"pqov-derive-preimage"‖ctr)` | adds separation from `ov_sign` (good) |
| Range checks on `d`, `x'` | explicit steps; since draft `6fd8ff3`, credits are `8·L`-bit witnesses, so V4 holds by construction and V3 is a ripple-carry adder | implicit (fixed 8-byte fields) | none |
| SpendRequest checks | `d ≤ t+x`, `t' < 2^{64}` | overflow-aware test, equivalent (Lean `change_correct`) | none |
| Nullifier check | caller, atomic, record before responding | caller (`ratatouille.hpp:180-182`) | as draft; see F5 |
| VOLEitH `msg` | optional, unused | none | F2 |
| ZK labels | (FAEST v3) | `main`: v3 CRT labels keyed by `w[0..16)`; fix: dedicated rows | F6 |

Against {{ACT}} (generic ACT), Ratatouille deviates in these ways:
- it has no `ctx_spend` (F2);
- it has no top-up allowance or refund bound `t ≤ s + a` (F4);
- refunds are separate tag inputs, not added to the balance;
- it is publicly verifiable (any holder of `pk` can verify spends; only the Issuer can sign);
- it has no refund re-fetch (F3).

The draft's own §"Proof status" asks for exactly the two reductions given here: unlinkability
from ZK and hiding (Thm 2), and one-more unforgeability from extractability, binding and a UOV
assumption (Thm 1, with A-OMPI).

## 9. Correctness (N4)

**Theorem 4.**
- **Issuance.** For `T_init ∈ [1, 2⁶⁴)`, an honest run yields `(T_init, 0)`.
- **Spend.** For `d ≤ t + x` and `t + x − d < 2⁶⁴`, `spend_response` accepts. Its outputs are the
  same `nf`, the same `d` and the response. `finalize_spend` returns a token with credit
  `t + x − d` and refund `x'` (Lean `change_correct`).
- **Failure.** Each case fails only with:
  - the VOLEitH prover's grinding abort `(1 − p)^{2³²}` (lean/docs/zk.md §7.3), which throws;
  - a `DerivePreimage` failure (all 255 vinegars giving a singular system, probability
    `δ(sk)^{255}`, about `255^{−255}` at `δ = 1/255`, and `E[δ^{255}] ≤ 2^{−295.8}` on average over
    keys), which throws.
- **Refund integrity (N5).** A client that finalizes holds exactly the Issuer's `x'`: altering it
  needs a signature on `Tag(c', x'')`, which falls under Thm 1 (E2, E3) and Thm 3.

*Proof.* Use perfect completeness of VOLEitH and QuickSilver on a satisfying witness (lean/docs/zk.md H3)
and determinism of `Tag`. The witness satisfies V3 by `change_correct`. ∎

## 10. Quantum adversaries

- **Balance.** Q2's Theorem 7.1 replaces `ε_ext` by `Σ² + ε_multi + ε_rec`, with
  `Σ² ≈ 200·q²·2^{−128}`. This is meaningful only for `q ≲ 2⁵⁵` hash queries and `q_E ≲ 2³⁷`
  cipher queries (the `ε_multi` cap).
  - **Simultaneous extraction.** Q2 proves extraction for one output. Extraction from all
    `N_I + N_S` proofs at once is Theorem M of `lean/docs/extraction/Q7-qrom-multi-extraction.md`,
    and Q7 §5 states Theorem 1 in the QROM with it (paper).
  - The signing oracle is classical, and its answers do not depend on extracted witnesses, so the
    reduction is compatible with measuring at the end.
- **Binding.** BHT/Zhandry give `O(q_K³·2^{−256})` and `O(q_K³·2^{−360})`, assuming the quantum
  permutation model's inverse access is harmless. That is the classical (K1) fact, but there is no
  quantum tool for an invertible random permutation with structured inputs. **Modelling gap:**
  treat Com and Tag as independent quantum random oracles (heuristic).
- **UOV.** A-OMPI must hold against quantum adversaries with superposition access to `Tag`. That
  is, it must be stated with quantum-accessible random targets, which is UF-Tag with `Tag` as a
  QRO. This is a new assumption (the draft's §Proof status says the same). R1 (a salt) would allow
  the Kosuge–Xagawa-style QROM proof of salted hash-and-sign UOV.
- **Theft (N2a).** This needs SE in the QROM, which is open (Q2 §11 gap 3).
- **Unlinkability.**
  - ZK in the QROM is proved on paper with the label-row fix (`lean/docs/zk-qrom.md`, about
    `2⁻¹⁹` at `2³⁰` queries and proofs); Theorem 2 is not restated with it, and nothing of it is
    mechanized.
  - Hiding degrades to `O(q_K²·Q_c·2^{−128})` (multi-target Grover).
  - On `main`, the (PU) condition degrades the same way; the fix removes that term.
  - The unlinkability adversary is the Issuer, so store-now-decrypt-later linking of
    recorded transcripts falls under this bound.

## 11. Gaps

- A-OMPI is a protocol-specific assumption. There is no reduction to UOV inversion (§2.3); R1
  would give a reduction to standard salted UOV EUF-CMA.
- Theorem 1 in Lean (`ROM/RatatouilleBalance.lean`, `balance_le_lean`, §4) still leaves:
  - `Adv^{uf-tag}(B)` and `Adv^{coll}(C)` are the explicit reductions' success probabilities,
    for a UF-Tag game with a signability probe (`TagForger`; `B` is mechanized as a forger of
    it). Lemma 2.1 (UF-Tag from A-OMPI) is in Lean with `Tag` a random function
    (`advFDH_le_ompi`, and to OMPR `balance_le_ompr`, §4), from the modelling hypothesis
    `TagIdeal` (concrete KP800 versus the ideal `Tag`), which stays a hypothesis; with `Tag` a
    random permutation with inverse queries, its permutation terms
    (`q_K·2^{−479} + q_K²·2^{−799}`) are in Lean too (`balance_le_ompr_perm`, hypothesis
    `TagIdealP`). The binding bound `ε_bind^K` stays on paper: it needs KP800 as an ideal
    permutation, while the Lean `Com` is the concrete Keccak-p[800]. The probe is no real strengthening: `balance_le_noProbe`
    (`ROM/RatatouilleProbe.lean`) removes it at the cost of the signer's failures on at most `N`
    logged pairs, the paper's `E4` (`uov-assumptions.md` §5.8). That pqov's signer fails with
    probability `δ(sk)^{255}` independently per target is the paper step (Lemma D);
  - the extraction step is simultaneous (`balance_le_sim_num`, §4: each query of the run charged
    once for both relations), but its failure terms (binding, an opened dead leaf, Post) stay per
    request, `2N·failEps`;
  - adversaries are deterministic given the oracles (randomized ones by averaging over their
    coins) and make a fixed number `N` of calls with a per-call query budget.
- Theorem 3 (no theft, N2a): the reduction is in Lean (`noTheft`, `noTheft_lean`, §5). The read budgets of the zero-knowledge hops are proved from the adversary's and the extractor's budgets (`noTheft_lean_reads`). Weak SE is reduced to plain extraction and a programmed-point (chain-collision) term (`noTheft_lean_plain`). The theorem also holds with `H₁`, `H₂⁰…H₂²`, `H₄` and `H_comb` read off uniform tables (`noTheft_leanX_plain`: the zero-knowledge hops are uniform in the base hash record and lift by averaging). The chain-collision term is bounded there for adversaries that read the chain tables with bounded queries (`noTheft_leanX_hit`: `2·((q_μ+3)·2^{−256} + (q₂₁+3)·2^{−1088} + (q₂₂+3)·2^{−448})`, freshness under the adversary's key since the Lean spend statement does not hash `pk`). Plain extraction stays a hypothesis: carrying `ROM/`'s extraction bound over needs the extractor to see the last stage's query log, the last stage as an oracle computation with cell queries to the cipher, and the lazy-to-eager step (§5, "What is not covered"). `Adv^ow` stays the advantage of the explicit inverter: `Com` is evaluated inside the relations, so it cannot be a random table of the game, and some inverter wins with probability `1` (`owAdv_one_ratatouille`). In a random-table model of the standalone experiment a `q`-query inverter has advantage `≤ (q+2)·2^{−126}` (`owAdvColRO_num`). The game has one honest client with one issuance and one spend, adversarial choices that do not read the tables, and one output request. For `U` honest clients and `M` honest spends, with change tokens spent again, the reduction is `noTheftN` (`Theft/RatatouilleMany.lean`, §5): `U·ε_I + M·ε_S + Σ_i δ_i + ε_SE + Σ_j Adv^ow(B_j)`, with weak SE for `U + M` simulated proofs (`WeakSEN`). With the Lean prover the hops' budgets are proved and `WeakSEN` is reduced to plain extraction and one programmed-point term per simulated proof, all hypotheses (`noTheftN_lean_reads`, `noTheftN_lean_plain`). With the other hashes uniform tables the programmed-point terms are bounded, `N·((q₂₂+N+1)·2^{−448} + (q₂₁+N+1)·2^{−1088} + (q_μ+N+1)·2^{−256})` for `N = U + M` (`noTheftN_leanX_hit`); plain extraction stays a hypothesis.
- KP800 as an ideal permutation is a model. Commitment binding and hiding inherit it. In the Lean
  privacy theorems hiding stays a computational hypothesis (`ε_hide`, §2.2).
- Lemma DS is proved on paper, with the separation table checked in Lean
  (`lean/docs/security/domain-separation.md`, `Protocols/DomainSeparation.lean`); SHAKE as a
  random oracle remains the modelling step.
- In the QROM: simultaneous extraction (Q7) and ZK (`lean/docs/zk-qrom.md`) are on paper only;
  SE for Theorem 3 is open; there is no quantum tool for an invertible permutation.
- Thm 3 uses SE in the classical model only. N2b (copying) is not provided at all (F2).
- The UF-Tag reduction counts `q_T ≤ q_K` Tag inputs. Issuer aborts in `DerivePreimage` are the
  term `(N_I + N_S)·E[δ^{255}] + q_v·2^{−256}` of Theorem 1. R1 does not remove that term, and
  the F5 fix removes only the probe (`uov-assumptions.md` §5.8).
- Unlinkability (N3) in Lean (§6; `lean/docs/zk.md` §10):
  - mechanized as a two-round game in `lean/VoleMole/Privacy/Ratatouille.lean`, with zero
    knowledge and hiding as hypotheses; for the executable Lean prover in the ROM and ideal-cipher
    model with every zero-knowledge term explicit (`unlinkabilityRO_lean_num`), with a
    table-reading Issuer (`unlinkabilityRA_lean_num`; as oracle computations,
    `unlinkabilityOC_lean_num`), with AES's rows uniform permutations read forward and inverse
    (`_perm`), with one shared `H₃(wPrefix ‖ μ₁ ‖ ρ ‖ 3)` and no prefix-collision term
    (`unlinkabilitySh_num`: `8·εRO(q_E + 13824, q₅ + 1872, q_E + 13824) + 4·(2⁻¹¹³ + εRO(0, 312,
    4607)) + 6·noHitProb + 12·2⁻¹⁰²⁴ + 2·εhide`; `unlinkabilityRASh_num`, with
    `4·(i_E + 9214)·2⁻¹²⁸ + 4·(2i_E + 23035)·2⁻¹²⁸` for spends whose fresh `ρ` meets a row the
    Issuer read; `unlinkabilityOCSh_num`), and with H1 (the seed XOF) mechanized: the XOF a
    uniform table keyed by `(DST, seed)`, uniform seeds, the Issuer reading at most `q_g` cells
    (`unlinkability*_seed`, each `+ 2·(2q_g + 2)·2⁻²⁵⁶`). Lemma DS for the seed domains (part (a))
    is the same modelling step as for the other tables.
  - with many Clients (`Privacy/RatatouilleMany.lean`, `lean/docs/zk.md` §10.8): any number of
    further honest Clients on the same tables, each issued with the challenge Clients and spending
    once with round 1 (their spend requests seen by the Issuer's stage 2), as a reduction to the
    table-reading game (`unlinkabilityN_lean_num`, `≤ n·2⁻¹⁰¹ + 8·(q₃ + q₅ + 221·q_E)·2⁻¹²⁸ +
    2·εhide` for `n` Clients in all: `2⁻⁸¹` at `2²⁰`, `2⁻⁶⁹` at `2³²`); `N` challenge pairs (each
    with its own two rounds, the Issuer's stages seeing every pair, round 1's requests only where
    §6's rule runs round 1), a hybrid over the pairs, each step a reduction to the table-reading
    game whose Issuer runs the other pairs (`unlinkabilityP_lean_num`, `≤ N·(N·2⁻¹⁰¹ + 2·εhide)`
    plus budget terms: `2⁻⁶³` at `2²⁰` Clients, `2⁻³⁹` at `2³²`; quadratic by an artifact of the
    proof). With the other pairs moved to private tables by the interleaved lazy-sampling lemma
    `pr_split_le` (`Privacy/RatatouilleLin.lean`; `lean/docs/zk.md` §10.8, "Linear in `N`"), the
    step charges no other pair's reads: **`unlinkabilityP_lin`**, `≤ N·(2·2⁻¹⁰² + (N − 1)·2⁻¹²⁸ +
    8·(q₃ + q₅ + 221·q_E)·2⁻¹²⁸ + 2·εhide + 2β)` (`unlinkabilityP_lin_le`) with `β` the split
    world's bad event (a proof of pair `k` and a proof of another pair reading a common `H₅` key or
    cipher point); `β ≲ 64(N − 1)·2⁻¹²⁸` is on paper only (it needs `H₄` a random oracle; in the
    Lean games `H₄` is SHAKE), giving `≲ n·2⁻¹⁰² + 33·n²·2⁻¹²⁸` for `n = 2N` Clients.
  - with a key stage that reads the tables (`Privacy/RatatouilleRAK.lean`, `lean/docs/zk.md`
    §10.3): the Issuer's key, context and balance fixed by a setup that reads the slices and the
    shared tables (`AdversaryRAK`, `KBudget`), the issuance hops adaptive (`hopI0RAK`, `hopI1RAK`,
    `leanPIR_zkROA`; `deltaI1RK_le`), the spend hops reading through the setup
    (`unlinkabilityRAK_lean_num`, `_numG`, `_perm`); and adaptive schedules
    (`Privacy/RatatouilleAdaptive.lean`, `AdversaryAdR`, `realGameAdR`): further sessions (issuance
    and one spend) one after the other before the challenge, before stage 1, between round 1's
    request and stage 2 and after the outcome, each chosen from earlier outcomes, run by the
    reduction in its key stage, stages and guess (`fullXR_sreads`, `runSeqR_sreads`;
    `unlinkabilityAd_lean_num`, `≤ n·2⁻¹⁰¹ + 8·(q₃ + q₅ + 221·q_E)·2⁻¹²⁸ + 2·εhide`,
    `unlinkabilityAd_lean_le`; `2⁻⁸¹` at `2²⁰`, `2⁻⁶⁹` at `2³²`); and interleaved schedules with
    Clients that spend several times (`Privacy/RatatouilleInterleave.lean`, `ZK/ReadsInterleave.lean`,
    `AdversaryILR`, `realGameILR`): the Issuer, an interactive machine, starts further Clients and
    sends pending ones their next message in any order; a Client's first message is the issuance
    response and the first spend's amount, its later ones the response to its last spend (the
    change token, `finalize_spend`, is spent next: `tokOf`, `finSX`) and the next amount, up to `K`
    spends; a Client is a chain of `1 + K` consistent readers (`ChainCons`), the schedule a
    consistent reader by the interleaving lemma (`Good.run`), and
    `unlinkabilityIL_lean_num`, `≤ (n(K + 1) + 2)·2⁻¹⁰¹ + 8·(q₃ + q₅ + 221·q_E)·2⁻¹²⁸ + 2·εhide`
    for `n` further Clients (`unlinkabilityIL_lean_le`; `2⁻⁸¹` at `n(K + 1) + 2 ≤ 2²⁰` proofs,
    `2⁻⁶⁹` at `2³²`); also with a scheduler that reads the tables (each step a VCVio oracle
    computation within a per-step query bound) and places the challenge's start and stages
    (`Privacy/RatatouilleInterleaveOC.lean`, `ZK/ReadsInterleaveOC.lean`, `AdversaryILRO`,
    `realGameILRO`; `unlinkabilityILO_lean_num`, `+ 46·L·(a₃ + a₂ + a₅ + 221·a_E)·2⁻¹²⁸` for `L`
    steps, `unlinkabilityILO_lean_le`, `_2pow20`, `_2pow32`).
  - what remains: SHAKE as a random oracle, AES as an ideal cipher, the consistency of a
    table-reading Issuer given as a bare function of the tables, and hiding (computational); a
    bound on the bad event `β` of the linear `N`-pair reduction (`unlinkabilityP_lin` is linear in
    `N` up to `β`; `β ≲ 64(N − 1)·2⁻¹²⁸` needs `H₄` a random oracle and is on paper); in the
    interleaved game, the factor about 2 against the sequential
    schedule (`lean/docs/zk.md` §10.8 "Open": it would disappear with the further Clients on
    private tables); a second challenge Client with inputs chosen after the first one's request is
    not a separate question here, since both challenge Clients share the Issuer's key, context and
    balance, fixed before the first request (zk.md §10.8 "Open"); further Clients in the
    shared-`H₃` and seed-XOF games.
- `Protocols/Ratatouille.lean` covers the accounting and the 64-bit arithmetic;
  `ROM/RatatouilleBalance.lean` composes them with extraction (above). Binding and forgery stay
  explicit terms.

## Appendix A. Lean names for Theorem 1

`lean/VoleMole/ROM/ExtractReduce.lean` (protocol independent):
- `prEvent_le_of_table`, `prEvent_le_sum_of_table`, `prEvent_bind_le_sum_of_table`: an event of
  one computation against the lazy random oracle, bounded per table by events of others
  (through `prEvent_eq_extendTable`: lazy = eager on a finite key set).
- `RoundAdv`, `roundsM`, `roundsT`, `roundsT_trace`, `evalWithAnswerFn_roundsM`: an adversary's
  `n` calls to an honest party, as a computation and per table.
- `proverAt`, `evalWithAnswerFn_proverAt`, `isKindQueryBoundIC_proverAt`,
  `isQueryBoundP_proverAt`: the `j`-th prover and its budget.
- `prEvent_bind_le_sum4_of_table`: the same with two indexed families and two events of one
  further run (Moussaka's `omuf_le` uses it).
- `gameA_out`, `gameA_transcript`, `extWit`, `extWit_spec`: the single-proof game's output per
  table, and the extracted witness; `gameA_congr`, `proverAt_congr`: congruences.
- `VerifierIC`: a cipher-querying implementation of the executable verifier, as a hypothesis.

`lean/VoleMole/ROM/SimUnion.lean`, `ROM/SimExtract.lean`, `ROM/SimSpec.lean`, `ROM/SimJoint.lean`,
`ROM/SimJointSpec.lean` (protocol independent): simultaneous extraction
(`prEvent_le_shared_suffix`, `prEvent_le_shared_suffix₂`, `prEvent_sim_le`,
`prEvent_sim_comb_le`, `prEvent_sim_joint_le`, `PrefixRuns`, `ratatouilleIssue_sim_spec`,
`ratatouilleSpend_sim_spec`, `ratatouille_sim_joint_spec`).
`lean/VoleMole/ROM/RatatouilleBalanceSim.lean`: `proverAt_prefix`, `prefixRuns_I`, `prefixRuns_S`,
`SimIss`, `SimSp`, `SimIS`, `prEvent_simIS_le`, `balance_le_sim`, `balance_le_sim_num`, `balance_le_lean_sim`,
`balance_le_ufTag_sim`; `Assumptions/SimLinks.lean`: `balance_le_ompr_sim`,
`balance_le_ompr_rate_sim`.

`lean/VoleMole/ROM/VerifyIC.lean` (protocol independent, shared with Moussaka):
- `verifyIC`, `evalWithAnswerFn_verifyIC`, `verify_congr_cells`: the verifier with the cipher as
  queries, which is `verify` per table.
- `verifyCellBound`, `verifierIC_verifyIC`: its budget; `VerifierIC` holds.

`lean/VoleMole/ROM/RatatouilleBalance.lean`:
- `romPrim`, `serveP`, `serveM`, `balQ`, `balT`, `Win`: the game.
- `provI`, `provS`, `gameI`, `gameS`, `failI`, `failS`, `annI`, `annS`: the extraction games of
  the `j`-th request and the extracted witnesses.
- `Forge`, `ComColl`, `ForgeEv`, `CollEv`, `forgeAdv`, `collAdv`: the reductions' events.
- `TagForger`, `UFWin`, `ufTagAdv`: the UF-Tag game with a signability probe; `signLog`,
  `probeLog`, `yT_signer`, `games_congr`, `bOut`, `bOut_reads`, `forger`: `B` and its legitimacy;
  `forge_ufwin`, `forgeAdv_le_ufTag`: `B` wins on the forgery event.
- `no_win`: the deterministic core (no failure, no win), through `Spec.Ratatouille.World.step_inv`.
- `ext_issue`, `ext_spend`, `win_imp`: per table, a win is a failure.
- `pr_failI_le`, `pr_failS_le`: the single-proof bounds for the `j`-th prover.
- `balance_le`: Theorem 1 for any `VerifierIC`; `balance_le_lean`: with `verifyIC`;
  `balance_le_ufTag`: with `Adv^{uf-tag}(B)`.

`lean/VoleMole/ROM/RatatouilleProbe.lean` (the probe, `uov-assumptions.md` §5.8):
- `patch`, `FailOut`, `failAdv`, `run_patch_of_not_fail`, `failOut_iff_patch`: the failure event,
  read off the run against a signer that never fails.
- `TagForger.noProbe`, `TagForger.ProbeFree`, `noProbe_probeFree`, `ufWin_noProbe`,
  `ufTagAdv_le_noProbe`: the probe-free forger and its bound.
- `withFail`, `pr_eval_pt`, `pr_exists_list_le`, `pr_failOut_le`: the union bound for a signer with
  independent failures.
- `signRec_probeRec_le`, `logs_length_le`, `forger_logs_le`: one logged pair per call.
- `balance_le_noProbe`: Theorem 1 with the probe-free forger and `failAdv(B)`.
- `Audit/Nonvacuous.lean`: `balance_le_lean`'s hypotheses instantiated (`balA0`).

`lean/VoleMole/Assumptions/IdealTag.lean` (protocol independent; `uov-assumptions.md` §5.1):
- `ompiLazy`, `ompi_lazy_eqd`, `advOMPI_eq_lazy`: A-OMPI with targets drawn on demand.
- `fdhRed`, `fdhComb`, `fdh_step`, `fdh_inv`, **`advFDH_le_ompi`**: T1(a), det-FDH (UF-Tag with
  `Tag` a random function) ≤ A-OMPI.
- `ompiRed`, `ompiComb`, `padC`, `pad_spec`, `ompi_step`, `ompi_inv`, `ompiWin_imp`,
  **`advOMPI_le_ompr`**, `advOMPI_le_ompr_rate`, `badTargets`, `failRate`: T1(c), A-OMPI ≤ OMPR.
- `advFDH_le_ompr`, `advFDH_le_ompr_rate`: both.

`lean/VoleMole/Assumptions/RatatouilleOMPR.lean`:
- `StrictWin`, `ufTagStrictAdv`, `ufTagStrictAdv_le`, `strictWin_noProbe`, `ufTagAdv_le_strict`:
  UF-Tag with the strict win, from the probe game.
- `ratTrap`, `FDHAdv`, `TagIdeal`: the Issuer's trapdoor and the modelling hypothesis.
- **`balance_le_ompr`**, `balance_le_ompr_rate`: Theorem 1 under one-more-UOV.
- `Audit/IdealTag.lean`: their hypotheses instantiated, except `TagIdeal` (`tagIdeal_of_eq_zero`).

`lean/VoleMole/Assumptions/FDHPerm.lean`, `Assumptions/RatatouillePerm.lean` (`Tag` a random
permutation with inverse queries):
- `advFDHPerm`, `advFDHPerm_le_hyb`: the game and its hybrids.
- `simCF`, `fdhPermRed`, `combF_step`, `combF_inv`, `hyb_le_fdh`, **`advFDHPerm_le_fdh`**,
  `advFDHPerm_le_ompr`, `advFDHPerm_le_ompr_rate`: down to det-FDH and OMPR.
- `TagIdealP`, **`balance_le_ompr_perm`**, `balance_le_ompr_rate_perm`,
  `balance_le_ompr_sim_perm`, `balance_le_ompr_rate_sim_perm`: Theorem 1 under OMPR.
- `Audit/PermFDH.lean`: their hypotheses instantiated, except `TagIdealP`
  (`tagIdealP_of_eq_zero`).
