# Security of Ratatouille, as implemented

This note fixes the security notions of the Ratatouille Anonymous Credit Token (ACT) and proves
them for the code in `src/ratatouille/*` and `include/vole_mole/ratatouille.hpp` at commit
`6d7113e` (`main`), with explicit bounds. It also covers the fix of commit `d5def9c` (branch
`voleith-label-rows`). That fix was merged as `64fd1a4`, but Ratatouille opts out of it with
`REUSE_CRT_WITNESS`, so on `main` Ratatouille is still at the `6d7113e` bounds (PU).

Sources used:
- the draft, now named `draft-authors-mole-act-ratatouille.md` (the README links to the old name,
  `draft-authors-mole-vole-act.md`, which returns 404);
- the generic ACT draft `draft-authors-mole-act.md`, cited as {{ACT}};
- `lean/docs/extraction/` (PoK, L7, L8, Q2) and `lean/docs/zk.md` (ZK);
- `lean/docs/security/domain-separation.md`, which proves Lemma DS (its §7: part (a) for every SHAKE
  call Ratatouille makes, part (b) for `Com` and `Tag`).

Both drafts were fetched on 2026-10-14 into the session scratchpad (`papers/act/`).

Line references are `file:line` at `6d7113e`.

## 0. Summary

| Notion | Result | Main terms |
|---|---|---|
| **Balance** (no inflation): accepted spends ≤ issued + refunded, against adaptive malicious clients, honest clients present | **Proved** (Thm 1), classical | `ε_ext + Adv^{uf-tag} + q_K²·2^{−257}` |
| **No theft**: an adversary cannot spend an honest client's credits through a request it did not copy verbatim | **Proved** (Thm 3), using weak SE and a ZK hop | `ε_ZK + ε_SE + q_K·2^{−127}` |
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
`H = Tag`, so balance would reduce to standard UOV EUF-CMA. This is not done here.

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
    (PU) as a hypothesis on explicit predictors, `lean/docs/zk.md` §4.1).
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

**N3 Unlinkability/anonymity.** Let the adversary be a malicious Issuer. It may use a malformed
`pk`, and it chooses `T_init`, `ctx`, refunds and responses. It schedules honest clients to issue
and to spend amounts `d` that it chooses. It must not distinguish:
- **Real**: honest clients run the real algorithms;
- **Ideal**: every honest outgoing message is produced by a simulator from the leakage
  `ℒ = (pk, ctx, T_init)` for issuance, or `(pk, ctx, d)` for a spend.

In both worlds the clients keep their real states. So whether a client can afford a requested
`d`, or rejects a malformed response, is identical in both. This captures the draft's goal that a
spend is unlinkable "to the issuance or to any other spend by the same Client", up to the public
amounts and feasibility ({{ACT}} says the same: "hides its balance beyond the public amounts and
the predicates they establish").

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

`N_I` and `N_S` count the issuance and spend requests verified.

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
- (E4) an Issuer `DerivePreimage` abort (negligible, see Thm 4).

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

## 5. No theft (N2) and honest clients

**Theorem 3 (N2a).** Fix an honest client's certified state `σ` (a commitment it created, with
secret `r`). Consider accepted adversarial spend requests whose statements differ from every honest
statement. The probability that one of them has an extracted parent equal to an honest state is
at most

    ε_ZK(Q_P) + ε_SE + ε_ext + q_K·2^{−127} + ε_bind^K + Adv^{ompi}.

*Proof sketch.*
1. Replace honest proofs by simulated ones (`ε_ZK`).
2. Apply weak SE (L8). An accepted adversarial proof for a fresh statement extracts.
3. A witness whose parent is an honest commitment contains its opening `r`. But in the simulated
   world, `r` enters only `Com` and the KP800 input, never a proof. So producing it means a
   forward query at the true input (`q_K·2^{−128}` over all honest states, as in §2.2), or a
   prediction among at least `2¹²⁸ − q_K` candidates.

This also covers copying an honest issuance commitment `c` or change commitment `c'` into the
adversary's own issuance or spend. ∎

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
  replaces it and is on paper. With the label-row fix it is `lean/docs/zk.md`'s
  theorem.
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

Against `draft-authors-mole-act-ratatouille.md`:

| Item | Draft | Implementation | Effect |
|---|---|---|---|
| Com, Tag layouts and DSTs `c0`, `t0`, `i0`, `p0` | §KP800 | identical (`commit.hpp:56-93`, `dst.hpp:47-54`) | none |
| Instance encodings | `c‖⟨T⟩‖ctx`; `PKDigest‖nf‖⟨d⟩‖c'‖ctx` | identical (`issue.hpp:151-155`, `spend.hpp:321-327`) | none |
| Extra DSTs | — | `l0` (UOV combination), `s0`/`s1` (seed XOFs) | needs Lemma DS |
| Randomness | `nf, r ← uniform` | squeezed from a 32-byte seed by SHAKE (`ratatouille.cpp:69-84`) | computational (H1 of Thm 2) |
| DerivePreimage | TODO: `Expand_v(t‖seed_sk‖ctr)` | `H(t‖sk_seed‖"pqov-derive-preimage"‖ctr)` | adds separation from `ov_sign` (good) |
| Range checks on `d`, `x'` | explicit steps | implicit (fixed 8-byte fields) | none |
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
  - a `DerivePreimage` failure (every counter value giving a singular system, about
    `255^{−256}`), which throws.
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
- KP800 as an ideal permutation is a model. Commitment binding and hiding inherit it. In the Lean
  privacy theorems hiding stays a computational hypothesis (`ε_hide`, §2.2).
- Lemma DS is proved on paper, with the separation table checked in Lean
  (`lean/docs/security/domain-separation.md`, `Protocols/DomainSeparation.lean`); SHAKE as a
  random oracle remains the modelling step.
- In the QROM: simultaneous extraction (Q7) and ZK (`lean/docs/zk-qrom.md`) are on paper only;
  SE for Theorem 3 is open; there is no quantum tool for an invertible permutation.
- Thm 3 uses SE in the classical model only. N2b (copying) is not provided at all (F2).
- The UF-Tag reduction counts `q_T ≤ q_K` Tag inputs. Issuer aborts in `DerivePreimage` are
  treated as negligible.
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
    proof).
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
    bound linear in `N` (the lazy-sampling reduction of PomFRIT with `H₄` a table,
    `Privacy/PomFRITLin.lean`, does not apply as it stands, since the further Clients' spend
    statements are chosen by the Issuer); in the interleaved game, a second challenge Client whose
    inputs are chosen after the first one's request, and the factor about 2 against the
    sequential schedule (`lean/docs/zk.md` §10.8 "Open"); further
    Clients in the shared-`H₃` and seed-XOF games.
- The Lean file covers the accounting and the 64-bit arithmetic only. Extraction, binding and
  forgery are paper arguments.
