# Moussaka: security analysis of the implementation

This note states and proves the security properties of vole-mole's Moussaka implementation. It
covers `src/moussaka/*.{cpp,hpp}` and `include/vole_mole/moussaka.hpp` at commit `6d7113e`
(`main`). Moussaka is the Issuer-Hiding Anonymous Token (IHAT) of the Moussaka draft. The README
link (`README.md:24`, `[mous]`) still points to `draft-authors-mole-vole-ihat.md`, which was renamed
to `draft-authors-mole-ihat-moussaka.md` (draft commit "crypto: Align draft names"). The old link
now returns 404. This note uses the renamed draft as of 2026-10-13, together with the MoLE
architecture draft (`draft-jms-mole-architecture.md`), which states the goals that an IHAT must
meet.

Line citations refer to `main`. `moussaka.cpp` is `src/moussaka/moussaka.cpp`.

Contents:
- §0 Verdict
- §1 The protocol as implemented
- §2 Deviations from the draft
- §3 Model and assumptions
- §4 One-more unforgeability
- §5 Nullifiers, double spending, selector, and context binding
- §6 Anonymity: issuer hiding and unlinkability
- §7 Malicious Anchor Sets and rogue keys
- §8 Quantum adversaries
- §9 Findings and attacks
- §10 `main` versus the `voleith-label-rows` fix
- §11 Open gaps
- Appendix A: demonstrations
- Appendix B: Lean

---

## 0. Verdict

| Property | Holds? | Bound (classical) | Assumptions |
|---|---|---|---|
| One-more unforgeability, per issuance context (Thm 1) | **Yes** | `ε_ext^iss + ε_ext^red + ε_dig + Adv^bind_Com + K·Adv^ct-uf_UOV,Com` | PoK (extraction README), binding of `Com`, chosen-target unforgeability of UOV on `Com`-images (implied by one-more-UOV, heuristically) |
| One nullifier per signed commitment; double-spend detection (Cor 2) | **Yes**, if the Moderator keeps one record per `(ctx_iss, ctx_red)` across all Anchor Sets (`moussaka.hpp:141-146`) | as Thm 1 | as Thm 1 |
| Redemption non-malleability: no redirect to another `challenge_digest`, Anchor Set or `ctx_red` (Thm 3) | **Yes** | `ε_SE^red + Adv^bind + K·Adv^ct-uf + U·Adv^ow-r + ZK hops` | weak SE (L8), plus the above, plus one-wayness in `r` |
| Issuer hiding and unlinkability vs a Moderator **colluding with all Anchors**, with adversarial keys (Thm 4a) | **Yes, computationally**; [Lean] from uniform seed outputs (`Privacy/Moussaka.lean`, `anonymity`); with the executable Lean prover (label rows) down to its tape hypothesis (`Privacy/MoussakaLean.lean`, `anonymity_label_rows`); for the Lean prover in the ROM and ideal-cipher model with every zero-knowledge term explicit, `≈ 2⁻¹⁰²·³` plus budget terms and `2·Adv^hide_Com` (`anonymityRO_lean_num`), and `≈ 2⁻¹⁰¹·⁹` with a table-reading interaction (`anonymityRA_lean_num`; Appendix B); also with AES as random permutations (`_perm`) and with one shared `H₃` (`anonymitySh_num`, `anonymityRASh_num`); from the real Clients' OS seeds and seed XOF, each `+ 2·(2q_X + 2)·2⁻²⁵⁶` (`anonymity*_seed`, `lean/docs/zk.md` §10.6); with a key stage (contexts, keys) that reads the tables too (`anonymityRAK_lean_num`, `≈ 2⁻¹⁰¹·⁹`); with any number `n` of further honest Clients, `≤ n·2⁻¹⁰²` plus budget terms and `2·Adv^hide_Com` (`anonymityN_lean_num`), also adaptively scheduled, each further session's contexts, key, response and Anchor Set chosen from earlier outcomes and the challenge contexts and keys from the sessions before it (`anonymityAd_lean_num`, the same numbers), and interleaved in any order (`anonymityIL_lean_num`, `≤ (n + 2)·2⁻¹⁰¹`; with a table-reading scheduler that also places the challenge, `anonymityILO_lean_num`, `+ 28·L·(a₃ + a₂ + a₅ + 221·a_E)·2⁻¹²⁸`), and with `N` challenge pairs (`anonymityP_lean_num`; `lean/docs/zk.md` §10.8; §11 item 5) | `2·ε_ZK^joint + 2·Adv^hide_Com` (the `2^{−192}` is not needed, §6) | ZK (lean/docs/zk.md), hiding of `Com` |
| The same vs a Moderator that sees no issuance (Thm 4b) | **Yes**, with no Keccak assumption, up to an abort term the note missed (§6); [Lean] from uniform seed outputs (`Privacy/MoussakaNC.lean`, `anonymityNC`, `unlinkabilityNC`), with the vinegar hash a random oracle (`anonymityNC_vinegarRO`), and with the executable Lean prover down to its tape or hop hypotheses (`anonymityNC_label_rows`, `_shake`); in the ROM and ideal-cipher model with every proof and the honest Anchors' Lean verifier on the shared tables, `≈ 2⁻¹⁰³·²` plus budget terms and `2·(φ₀ + φ₁)` (`anonymityNCRO_lean_num`, `unlinkabilityNCRO_lean_num`, also `_perm`), also with one shared `H₃` (`anonymityNCSh_num`) and from the real Clients' seeds (`*NC*_seed`; Appendix B); with a model of pqov's `derive_preimage` as the Anchors' signer (`anonymityNC_pqov`, `anonymityNCRO_pqov`), averaged over keys of pqov's key generation with `O = 0` (`anonymityNCRO_pqov_keys`, abort term `≈ 2⁻²⁹³·⁸`), and the games shown to reach redemption (`pr_refused_NCRO_le`; Appendix B) | `2·Σ ε_ZK^red + 2·(φ₀ + φ₁)`, `φ_c ≤ δ_c^{255}` on average over the vinegar random oracle (pqov uses 255 vinegars, §6), `E[δ_c^{255}] ≤ 255^{−37} + 1/(255·256^{37}) ≈ 2^{−295.8}` on average over the key (`δ ≤ 1/255` holds on average over the key, not per key) (`0` for one Anchor; no `2^{−192}`) | ZK of the redemption proofs only; the Client takes its index from `S` |
| Issuer hiding under a Moderator-chosen Anchor Set | **Only relative to the Anchors in the set that are honest and in common use** (§7) | n/a | Anchor-Set consistency outside the library |

Main findings (§9):
- **F1 (high, deployment).** If an Anchor's UOV key is also used as a PomFRIT Issuer key, anyone
  can mint unlimited Moussaka tokens for any `ctx_iss`. PomFRIT's `issue_response`
  (`pomfrit.cpp:188-190`) signs raw targets without a proof. This was demonstrated with the public
  API only (Appendix A). Nothing in the API or documentation forbids the reuse.
- **F2 (low).** Nullifier squatting. An adversary that sees an honest `nf` before the Moderator does
  can buy its own token with that `nf`, redeem it first, and get the honest token rejected as a
  double spend. Demonstrated.
- **F3.** The draft's one-more-UOV proof sketch programs `Com` as a random oracle *inside* the
  protocol. That is invalid as written, because the VOLEitH proofs evaluate the concrete
  Keccak-p[800,12] circuit. §4 restructures the proof so that idealised reasoning is applied only
  to a standalone assumption.
- **F4.** Privacy against a colluding Anchor has a margin of exactly 128 bits classically (64-bit
  Grover). Privacy against everyone has at most a 64-bit Grover margin, through AES-128 hidden-leaf
  keys. On `main`, lean/docs/zk.md's formal ZK bound multiplies `Q₅` by `Adv^ow`, which is vacuous at
  `q = 2^64`. The fix removes this.

No attack was found on the implementation itself: soundness, the selector, constant-time index
handling, or transcript binding.

---

## 1. The protocol as implemented

**Parameters.**
- UOV over `GF(256)` with `n = 119` and `m = 45` (`uov.hpp:17-18`; pqov "uov-Ip", UOV spec R3).
- `NF_BYTES = 24`, `CTX_BYTES = 16`, `R_BYTES = 16`, `CHALLENGE_DIGEST_BYTES = 32`, and
  `MAX_ANCHORS = 64` (`moussaka.hpp:24-29`, `commit.hpp:21`).
- VOLEitH with the FAEST-EM-128f v3 parameters (`issue.hpp:132-136`, `redeem.hpp:147-151`).

**Commitment.** `Com(nf, ctx_iss, ctx_red, r) = KP800(state)[0..45)`, where `state` is the 100-byte
string below (`commit.hpp:33-48`, `moussaka.cpp:89-96`):

```
"mous" ‖ 0x00 ‖ "c0"  ‖ r ‖ 0^9 ‖ ctx_iss ‖ ctx_red ‖ nf ‖ 0^12
 7 bytes (DST)          16   9     16        16       24   12
```

- There are 576 free input bits and 224 fixed bits.
- The output is the 360-bit UOV target.
- `KP800` is Keccak-p[800,12], a permutation: one call, no sponge.

**Client randomness.**
- A 32-byte OS seed is expanded as `SHAKE128(MOUSSAKA_ISSUE_SEED_DST ‖ seed)` into `nf ‖ r ‖ ρ_iss`
  (`moussaka.cpp:58-71`).
- Redemption uses a fresh OS seed: `ρ_red = SHAKE128(MOUSSAKA_REDEEM_SEED_DST ‖ seed')`
  (`:74-85`, `:230`).

**Issuance.**
1. The Client sends `(t, π_iss)`. `π_iss` proves `IssueRelation`: instance `(t, ctx_iss)`, witness
   `(r, ctx_red, nf, s5, s9)`, with bit constraints on every witness bit (`issue.hpp:1-21`,
   `:164-192`).
2. The Anchor verifies `π_iss` and returns `s = DerivePreimage(sk, t)` (`moussaka.cpp:127-136`).
   `DerivePreimage` is deterministic: the vinegar is
   `SHAKE256(t ‖ sk_seed ‖ "pqov-derive-preimage" ‖ ctr)` with at most 256 retries
   (`subprojects/pqov/src/ov.c:226-238`, `:24`), so one key yields one preimage per target.
3. The Client checks `P(s) = t` (`moussaka.cpp:177`).

**Redemption.**
- The Client first checks, in constant time over all `u`, that `anchors[i].eval(s) = Com(nf, ctx_iss,
  ctx_red, r)` (`moussaka.cpp:196-211`). It then consumes the token (`:214`) and sends `nf ‖ π_red`.
- `RedeemRelation` (`redeem.hpp:1-36`, `:165-272`):
  - instance: `(anchors, nf, ctx_iss, ctx_red, challenge_digest)`;
  - witness: `(r, s, s5, s9, b)`, with `b ∈ {0,1}^64`;
  - constraints:
    - bit constraints on `r`, `s` and the states;
    - `b[u]` is a bit for `u < n`, and `b[u] = 0` for `u ≥ n` (`:223-232`);
    - parity `(⊕_{k≤u} b[k])·b[u+1] = 0` for `u < 63`, and weight `⊕ b = 1` (`:234-242`);
    - `l(Σ_u b[u]·P_u(s)) = l(KP800(state))`, for a random linear combination `l` of the 45
      components derived from chall₂ (`:251-270`).
- The Moderator runs `voleith_verify` and returns `nf` (`moussaka.cpp:278-289`). Double-spend
  detection is the caller's job.

**Transcript binding.**
- `mu = H₂⁰(instance ‖ DST ‖ 0x08)` (`voleith.hpp:100-122`).
- The issue instance is `t ‖ ctx_iss`, fixed-length (`issue.hpp:165-166`).
- The redeem instance is `⟨64⟩₄ ‖ ⟨n⟩₄ ‖ digest(P₀) ‖ … ‖ digest(P_{n−1}) ‖ nf ‖ ctx_iss ‖ ctx_red ‖
  challenge_digest` (`redeem.hpp:182-200`). Here `digest = SHAKE256-256` of the compressed key bytes
  (`uov.cpp:82-85`).
- The constraint system uses the expanded map of the same `PublicKey` object, so maps and digests
  cannot diverge through the API.

---

## 2. Deviations from the draft

| # | Draft | Implementation | Security effect |
|---|---|---|---|
| D1 | `challenge_digest` is a separate "message" input to `VOLEitH.Prove`. The instance encoding omits it | `challenge_digest` is the last field of the hashed instance (`redeem.hpp:199`) | None: both bind it into `mu`. Interoperability: the draft doesn't say where "message" enters, so implementations can disagree on the transcript |
| D2 | Selector `b ∈ F_q^N` | `b ∈ {0,1}^64`, padded with zero-constrained entries (`redeem.hpp:223-232`). The draft's NOTE anticipates this | None. Lean `selector_one_hot`: the parity and weight constraints force one-hot over **any** field, so the draft's `F_q` version is sound even without bit constraints |
| D3 | `P[i](s) = Com(…)` componentwise | One random linear combination `l` of the 45 components, `l = H(chall₂ ‖ "mous"‖0‖"l0")` (`redeem.hpp:253`) | Soundness loss `2^{−128} + q_c·2^{−448}` (L4) |
| D4 | `Com` circuit unspecified (TODO) | Two committed intermediate states, after 5 and 9 rounds (`issue.hpp:5-20`) | Covered by L7 (Keccak segments) |
| D5 | Anchor Set: `0 < N ≤ MAX_ANCHORS` | Also rejects duplicate keys by digest (`moussaka.cpp:138-151`) | Hygiene only (§7) |
| D6 | `RedeemRequest` does not check the token | The Client checks validity for index `i` in constant time (`moussaka.cpp:196-211`) | Better: no proof is made for a false statement. No leak of `i` |
| D7 | `nf`, `r` sampled directly | Derived with `ρ_iss` from one OS seed through SHAKE128 (`moussaka.cpp:58-71`) | None in the ROM up to the seed-XOF hop: `(2q_X + 2)·2^{−256}` per world in Theorem 4's game (an XOF query at a Client's seed gives its `nf`; two seeds of one domain collide), which Theorem 4 does not charge; [Lean] `anonymity*_seed`, `lean/docs/zk.md` §10.6. This needs the application-hash vs proof-hash disjointness (Lemma DS, §3.1) |
| D8 | "samples a solution `s`" (older text) / "DerivePreimage" | Deterministic in `(sk, t)` | Needed: two preimages of one target from different vinegars are not known to be harmful, but determinism makes the UOV oracle a function (§3.3) |
| D9 | Security claim: one-more-UOV (PoMFRIT Def. 8) | — | This note uses a weaker assumption, CT-UF (§3.3), which follows from one-more-UOV heuristically |
| D10 | DST template "as in Ratatouille" | DST is *appended* to the instance in `mu` (`voleith.hpp:118`). Application hashes *prepend* DSTs | Covered by Lemma DS (§3.1) |

There are no deviations in the commitment layout, the issuance relation, or the API flow.

---

## 3. Model and assumptions

### 3.1 Proof-system results used

Let `q` be the adversary's total number of oracle queries, with the per-oracle counts of
`lean/docs/extraction/README.md`.

- **PoK (classical, straight-line, simultaneous).** For relation `R ∈ {iss, red}`, the README's
  extractor `E` succeeds on every accepting proof in a run, except with probability
  `ε_ext^R = Q·9·2^{−128} + q₁ε_KOS + q₂(ε_QS + 2^{−128}) + q_c·2^{−448} + ε_bind + ε_dead +
  (q²+q)·2^{−256}`, which is about `2^{−60.8}` at `q = 2^{64}` (README §Main theorem, L8 §9.1–9.2
  for per-oracle counts and simultaneity). `E` needs only the query log, with no rewinding and no
  programming. With L7, the extracted witness satisfies the **stated** relation: the Keccak
  opening, the one-hot selector, and `P_u(s) = Com(…)` in all 45 components.
  [Lean] for one proof, classical, in the random-oracle and ideal-cipher model, with a fixed or
  adaptively chosen statement: the decoded witness is in the spec relation (`IssueRelW`,
  `RedeemRelW`) except with the bounds of `lean/VoleMole/ROM/SpecSound.lean`
  (`moussakaIssue_accept_le_full_spec`, `moussakaRedeem_accept_le_adaptive_spec`, …; for `t` of 45
  bytes, `nf` of 24, contexts of 16; adaptive families with injective encodings, proved for
  fixed-length fields and fixed Anchors' digests, `EndToEnd/SpecRelations.lean`).
- **Weak SE w.r.t. adaptively chosen statements** (L8, Theorem L8): `ε_SE^R = ε_ext^R + ε_prog +
  ε_hk + ε_H + ε_eq`.
- **ZK** (lean/docs/zk.md §3). On `main`:
  - `ε_ZK = ε_rho + ε_prog + 2ε_hide + ε_lab + ε_iv` with
    `ε_lab = (Q₅ + n_mult·Q_V)·Pred_R + Q_P·2^{−128}`;
  - for Moussaka, `Pred_R` is the probability of predicting `r` (the first 16 witness bytes of both
    relations: `issue.hpp:58`, `redeem.hpp:74`). [Lean] `ZK/Relations.lean`: `w[0..16) = r` from
    the `Arith/` layouts, and the sibling-label bad event of both proofs jointly is
    `≤ (#H₅ queries)·Pred_R` for explicit predictors (`moussaka_main_zk`); towards a Moderator
    that never sees `t`, `Pred_R = 2^{−128}` unconditionally (`moussakaRedeem_main_zk_uniform`;
    `lean/docs/zk.md` §4.1).

  On the fix (`voleith-label-rows`, `CRT_DEDICATED_LABEL_ROWS`), standard adaptive NIZK holds with
  `ε_lab = (Q₅ + n_mult·Q_V + Q_P)·2^{−128}`, with no `Pred` term.
- **Lemma DS** (`lean/docs/security/domain-separation.md` §7: part (a), unconditional, for every
  SHAKE call Moussaka makes; part (b) for `Com`). The DST-prefixed
  application hashes (`SHAKE128(DST ‖ seed)` at `moussaka.cpp:58-85`) and the end-tagged
  proof-system hashes have disjoint input domains, and so does the combination hash. So all are
  independent random oracles. Two other hashes are separate from the start:
  - SHAKE256, used for key digests and UOV vinegar, is a different function;
  - `Com` uses Keccak-p[800], not Keccak-f[1600].
- `ε_dig`: the probability that two distinct key byte strings handled in the run share a SHAKE256
  digest. This is at most `q_{256}²·2^{−257}` in the ROM. It is listed separately because the
  redeem statement binds maps only through digests (`redeem.hpp:193-195`). If two distinct Anchor
  Sets had equal digest lists, a prover could pick the set after seeing chall₂, which L4's "statement
  bound before chall₂" step excludes only if the digests are collision-free.

### 3.2 The commitment `Com`

The VOLEitH relations evaluate the **concrete** Keccak-p[800,12] circuit. So `Com` cannot be a
programmable oracle inside the protocol proofs (F3). We therefore state its properties as concrete
assumptions, in the standard model. The generic (random-permutation, forward and inverse) estimates
below are evidence for these assumptions. They are not part of any reduction.

- **Binding.** `Adv^bind_Com(A) = Pr[A → x ≠ x' ∈ D : Com(x) = Com(x')]`, where `D` is the
  576-bit input space.
  - Generic: `≲ q²/2^{361} + q·2^{576}/(2^{800}−q) ≈ q²/2^{361} + q/2^{224}`.
  - The second term is an inverse query that happens to land in `D`.
  - At `q = 2^{64}` this is `≈ 2^{−160}`.
- **One-wayness in `r`.**
  - `Adv^ow-r_Com(A) = Pr[A(nf, ctx_iss, ctx_red, t) → r' : Com(nf, ctx_iss, ctx_red, r') = t]`,
    for uniform `r` and `t = Com(nf, ctx_iss, ctx_red, r)`, where `A` chooses
    `nf, ctx_iss, ctx_red` first.
  - Generic: `≲ (q+1)/2^{128}`.
- **Hiding (2-instance).**
  - `Adv^hide_Com(A)`: `A` chooses `(ctx_iss, ctx_red)`. For uniform `r₀, r₁, nf₀, nf₁`, it gets
    `t_c = Com(nf_c, ctx_iss, ctx_red, r_c)` for `c ∈ {0,1}`.
  - It must distinguish being given `(nf₀, nf₁)` from being given independent uniform
    `(nf₀*, nf₁*)`.
  - Generic: `≲ 2(q+1)/2^{128}`.
  - This is the hiding notion needed when the opening `r` is the only secret and `nf`, the
    contexts and `t` are all known to a colluding party.
  - [Lean] `lean/VoleMole/Privacy/ComHide.lean` (`lean/docs/zk.md` §10.9). With `Com`'s cells a
    random-function table read at `q` cells, the advantage is `≤ (4q + 2)·2^{−128}`
    (`hidingAdvRO_num`), the generic estimate above for forward queries. Against unbounded
    distinguishers the advantage is `1 − p` (`ComHide.Moussaka.hidingAdv_bruteForce`: search all
    `2^{128}` openings, `p` the chance that a fresh `nf` admits one, `≈ 2^{−192}` heuristically).
    This assumption cannot be discharged in the ROM. `Com` is evaluated inside the issuance and
    redemption relations, so it is not a table of the privacy games, and their reductions compute
    it. `2·Adv^hide_Com` in Thm 4(a) stays a computational term.

All three margins are generic. Keccak-p[800,12] has 12 of 22 rounds. Structural attacks on a
12-round inverse with 224 fixed input bits, or on 360-bit output truncation, are outside this note.
The draft defers to the Ratatouille draft for this choice.

### 3.3 UOV

Let `P_k` be the public maps of `K` honest Anchors and `Sign_k(y) = DerivePreimage(sk_k, y)` for any
`y ∈ F_{256}^{45}`.

- **CT-UF (chosen-target unforgeability on `Com`-images), `K` keys.**
  - `A` gets `P_1..P_K` and oracles `Sign_1..Sign_K` on **arbitrary** targets.
  - It wins if it outputs `(k, x*, s*)` with `x* ∈ D`, `P_k(s*) = Com(x*)`, and `Com(x*)` never
    queried to **any** `Sign_j`.
  - `Adv^ct-uf_{UOV,Com,K} ≤ K·Adv^ct-uf_{UOV,Com,1}`: the reduction generates the other `K−1`
    keys itself.
  - This is EUF-CMA of "UOV-FDH with hash `Com` and deterministic retry signing". The signing
    oracle may be queried on any target, as in the protocol, where an issuance proof shows
    knowledge but places no other restriction on `t`.
- **One-more-UOV** (draft; PoMFRIT Def. 8, restated because the paper was not retrievable here).
  - `A` gets `P` and `Q` uniform targets `y_1..y_Q`, and the oracle `Sign` on arbitrary targets.
  - After `ℓ` distinct oracle targets, it outputs `ℓ+1` pairs `(j, s_j)` with distinct `y_j` and
    `P(s_j) = y_j`.
  - Note that `Sign` is the real, deterministic `DerivePreimage`.
- **Lemma U (heuristic link).** Model `Com` as a random permutation **for the standalone CT-UF game
  only**. This is legitimate there, because CT-UF contains no proof that evaluates `Com`'s circuit.
  Then
  `Adv^ct-uf_{UOV,Com,1} ≤ Adv^om-uov(Q = q_P^fwd, ℓ ≤ q_Sign) + q_P^inv·2^{−223.9} + q_P²·2^{−360}`.
  - *Proof.* Answer each fresh forward query on `x ∈ D` with `y_j ‖ z`, for the next challenge
    target `y_j` and a uniform 440-bit `z`, resampling on a range collision.
  - Answer other forward queries, and all inverse queries, uniformly. An inverse answer that lands
    in `D` is a bad event, with probability `≤ 2^{576}/(2^{800}−q)` per query.
  - Forward `Sign` queries go to the one-more oracle.
  - A CT-UF forgery's target is a challenge target that was never queried. Together with the `ℓ`
    oracle answers, it gives `ℓ+1` solutions.
  - The last term covers repeated challenge targets. ∎
  - **Correction (`lean/docs/security/uov-assumptions.md`): Lemma U is wrong as stated.** CT-UF lets the
    adversary ask `Sign` about a target that is not a `Com` image, e.g. `Sign(0)`. The reduction must
    then spend a one-more call that yields no challenge preimage, so it never reaches "one more".
  - **The fix: use CT-UF^open,** where the adversary must also open every target it had signed.
    Moussaka's `B₂` already extracts those openings, so Theorem 1 holds unchanged with CT-UF^open in
    place of CT-UF. The repaired Lemma U is tight from OMPR (`uov-assumptions.md`).
- **Plain UOV problem.** Reducing CT-UF to the plain UOV problem (`P`, one random target, no oracle)
  needs the hash-and-sign-with-retry signing simulation. The naive simulator ("sample `s`, program
  `Com(x) := P(s)`") differs from real signing by `Pr[L_v singular] ≈ 1/255` per signing query,
  because real preimages never have a "bad" vinegar. A tight argument needs the refined analysis of
  the UOV specification or of Kosuge–Xagawa's probabilistic hash-and-sign with retry. That
  analysis is **not re-derived here**, so the main theorems are stated under CT-UF.

---

## 4. One-more unforgeability

MoLE's security goal (architecture draft, "Security Goals"):
- an accepted Endorsement "corresponds to exactly one Endorsement granted by a trusted Anchor";
- attackers control Clients and possibly *other* Anchors, but have no CRQC.

**Game OMUF.**
- The challenger generates `K` honest Anchor keys. `A` gets the public keys and these oracles:
  - `Issue(k, req, ctx_iss)`: run `issue_response(sk_k, req, ctx_iss)` (`moussaka.cpp:127`). If it
    accepts, put `t = req[0..45)` into the set `L_{ctx_iss}`.
  - `Redeem(S, req, ctx_iss, ctx_red, cd)`, for an Anchor Set `S` made only of honest keys: run
    `finalize_redeem`. If it accepts with `nf`, record `(ctx_iss, ctx_red, nf)` in a **single**
    store `R`, shared across all `S`.
- `A` controls everything else: other Anchors, and all Clients.
- `A` wins if, for some `ctx_iss*`, the number of distinct `(ctx_red, nf)` recorded in `R` with
  `ctx_iss*` exceeds `|L_{ctx_iss*}|`.

**Theorem 1.** For every classical `A`,

```
Adv^omuf(A) ≤ ε_ext^iss + ε_ext^red + ε_dig + Adv^bind_Com(B₁) + K·Adv^ct-uf_{UOV,Com,1}(B₂).
```

- `B₁` and `B₂` run `A` once, plus `E` on every accepted proof at the end (straight-line).
- `B₂` makes exactly as many `Sign` queries as `A` makes accepted `Issue` queries.

With Lemma U, `K·Adv^ct-uf ≤ K·(Adv^om-uov + q/2^{223.9} + q²/2^{360})`.

*Proof.*
1. **Simulation.** `B₂` gets CT-UF keys and oracles. It answers `Issue(k, (t, π), ctx)` by verifying
   `π` (public) and returning `Sign_k(t)`. This equals `DerivePreimage(sk_k, t)`, so the
   simulation is perfect. No extraction is needed during the run. `Redeem` is public verification.
2. **Extraction.** At the end, run `E` on every accepted issuance proof and every accepted
   redemption proof (§3.1 simultaneity). Outside an event of probability
   `ε_ext^iss + ε_ext^red + ε_dig`:
   - each accepted issuance `(t_q, ctx_q)` yields `x_q = (nf_q, ctx_q, ctx_red_q, r_q)` with
     `Com(x_q) = t_q`;
   - each accepted redemption `j` with `(S_j, nf_j, ctx_iss_j, ctx_red_j)` yields `(r_j, s_j, b_j)`.
     By L7 and Lean `selector_one_hot`, `b_j = e_{u_j}` for some `u_j < |S_j|`, and
     `P_{S_j[u_j]}(s_j) = t_j := Com(x_j)` with `x_j = (nf_j, ctx_iss_j, ctx_red_j, r_j)`.
3. **Binding case.** Suppose two distinct inputs among `{x_q} ∪ {x_j}` have equal commitments.
   Then `B₁` outputs that collision.
4. **Otherwise.** Fix the winning `ctx_iss*` and let `J` be its distinct accepted `(ctx_red, nf)`.
   - Distinct `j ∈ J` have distinct `x_j`, hence distinct `t_j`. So `j ↦ t_j` is injective on `J`.
   - `|J| > |L_{ctx_iss*}|`, so Lean `exists_unsigned_of_card_lt` gives `j` with
     `t_j ∉ L_{ctx_iss*}`.
   - If `t_j ∈ L_{ctx'}` for some `ctx' ≠ ctx_iss*`, then `x_j` (context `ctx_iss*`) and the
     extracted `x_q` (context `ctx'`) collide, which is case 3. So `t_j` was never submitted to any
     `Sign_k`.
   - `B₂` outputs `(S_j[u_j], x_j, s_j)`, a CT-UF forgery. ∎

**Remarks.**
- *Counting refinement.* The same argument bounds, for each `(ctx_iss, ctx_red)`, the accepted
  nullifiers by the signed commitments whose extracted opening carries that `ctx_red`. The Anchor
  never sees `ctx_red`, so this is a statement about the extractor's view only.
- *Same `t` at several Anchors.* A Client may submit one `t` to several Anchors (the draft's NOTE
  "nothing ties issuance to the Anchor"). It then holds several preimages of one `t`, but by binding
  only one `nf`. The count by distinct `t` is the right one. Rate limits per Anchor are unaffected,
  because each submission is a separate `Issue` query.
- *Trust in Anchors.* A malicious Anchor *in* `S` can mint tokens for `S` at will, by design. A
  malicious Anchor *outside* `S` gives no advantage, beyond F1 when keys are shared across
  protocols.
- *Redemption-proof extraction is essential, issuance-proof extraction is not.* The issuance proof
  is used only to bind `ctx_iss` (case 3). Without it, a Client could have a commitment to one epoch
  signed in another. The Anchor's rate limit per `ctx_iss` relies on it.

---

## 5. Nullifiers, double spending, selector, and context binding

### 5.1 Nullifiers

**Corollary 2.** On the good event of Theorem 1:
1. **Determinism.** Every accepted redemption's `nf` equals the `nf` committed in a commitment that
   some honest Anchor signed (with `ctx_iss` checked by that Anchor). Each signed `t` determines a
   unique `(nf, ctx_red)` by binding.
2. **Single use.** A Moderator that records `(ctx_iss, ctx_red, nf)` and rejects repeats accepts at
   most one redemption per signed `t`.
   - The record must be global across Anchor Sets. A token is valid under every `S` that contains
     an Anchor `u` with `P_u(s) = t`, and the proof hides which set member was used
     (`moussaka.hpp:141-146`, README "Security considerations").
   - A per-`S` record allows one redemption per set.
3. **Honest uniqueness.** `U` honest tokens have pairwise distinct `nf` except with probability
   `U²·2^{−193} + U²·2^{−257}`. The second term is an OS-seed collision. `nf` is the first 24 bytes
   of `SHAKE128(DST ‖ seed)`, which is uniform in the ROM.
4. **No in-circuit derivation.** `nf` is chosen by the Client at issuance and is not a PRF of a
   committed key. So any party can request a token with **any** `nf` it knows. See F2. The draft's
   NOTE (issue 45, `nf = PRF(K, ctx_red)` in-circuit) would also prevent squatting.
5. **Linkage through reuse.** The same token redeemed twice exposes the same `nf`. `ctx_red` binds
   the token to one redemption context. The `Token` object is consumed by `redeem_request`
   (`moussaka.cpp:214`). The MoLE protocols draft uses a fixed `ctx_red` for all Moderators in its
   Rollatini profile. A Moussaka profile copying this would make one token valid at every
   Moderator, so the Client must burn it after one use (architecture draft, "Clients … MUST burn
   them").

### 5.2 The selector

`redeem.hpp:223-242` constrains:
- `b[u] ∈ {0,1}` for `u < n`, and `b[u] = 0` for `u ≥ n`;
- `(⊕_{k≤u} b[k])·b[u+1] = 0` for `u < 63`;
- `⊕_u b[u] = 1`.

Lean `selector_one_hot` proves that, over any field, the parity and weight constraints alone imply
`b = e_i` for a unique `i < n` with `b_i = 1`. *Proof idea.* Let `i` be the first nonzero entry.
Then the prefix sum is `b_i ≠ 0` from `i` on, so every later entry is 0, and the weight constraint
gives `b_i = 1`. So `Σ_u b[u]·P_u = P_i`, and padding entries contribute nothing, because they are
pinned to 0 and also skipped in `lq` (`redeem.hpp:259-262`). The Lean `example` shows why parity
is needed: three set bits also have weight `1` in `GF(2)`. This agrees with L7.

### 5.3 Context binding and redemption non-malleability

| Value | Bound at issuance | Checked at redemption | Guarantee |
|---|---|---|---|
| `ctx_iss` | public in `π_iss`'s instance and inside `t` | in the instance and in the Keccak input | A token for epoch `e` is not accepted under `e' ≠ e` (binding, Thm 1, case 3) |
| `ctx_red` | inside `t` only (witness of `π_iss`, hidden from the Anchor by ZK and hiding) | in the instance and in the Keccak input | A token for redemption context `M` is not accepted under `M' ≠ M` (binding). The Anchor learns nothing about `M` (§6) |
| `challenge_digest` | not committed | in the instance (D1) | Non-malleability (Thm 3) |
| Anchor Set | — | digests and size in the instance; maps in the constraints | Non-malleability (Thm 3), using `ε_dig` |

**Game NM (redirect).**
- `A` is the Moderator and may act as any Anchor.
- Honest Clients obtain tokens and redeem them on request, under the Anchor Set and
  `challenge_digest` that `A` chooses (each token once).
- `A` wins if `finalize_redeem` accepts some `(S', nf_h, ctx_iss, ctx_red', cd')` that differs
  from every honest redemption statement, and whose extracted commitment equals the commitment `t_h`
  of an honest token.

The last condition excludes F2, where `A` uses its own, separately signed commitment.

**Theorem 3.** For `U` honest tokens,

```
Pr[A wins NM] ≤ ε_SE^red + ε_dig + Adv^bind_Com + K·Adv^ct-uf + U·Adv^ow-r_Com + ε_hop,
```

where `ε_hop` is the cost of replacing the honest proofs by simulated ones (§6, `ε_ZK^joint`).
Moreover:
- if the extracted commitment `t' ≠ t_h`, and `t'` was not signed, this is a CT-UF forgery (the
  `K·Adv^ct-uf` term);
- if `t'` was signed, it was submitted by `A` itself, which is F2 and is accounted for by Theorem 1.

*Proof.*
1. Hop to simulated honest proofs (`ε_hop`).
2. Weak SE (L8): the new statement differs from every simulated one, so `E` extracts `(r', s', u')`
   with `Com(nf_h, ctx_iss, ctx_red', r') = t_h`.
3. By binding, `ctx_red' = ctx_red_h` and `r' = r_h`.
4. In the simulated world, `r_h` enters `A`'s view only through `t_h`, so outputting it breaks
   `Adv^ow-r` (guess which of the `U` tokens: factor `U`). ∎

The architecture and protocols drafts note one limit that remains: a Moderator that relays
*another* Moderator's challenge is not stopped by `challenge_digest`.

---

## 6. Anonymity: issuer hiding and unlinkability

MoLE's privacy goals (architecture draft, "Privacy Goals"):
- Endorsement grant and redemption are unlinkable, even if the Anchor and the Moderator collude;
- redemption is Anchor-hiding "to both the Anchor and the Moderator";
- both should hold against a future CRQC (harvest now, analyse later).

**Game ANON^mode.**
- `A` chooses `ctx_iss`, `ctx_red` and two Anchor public keys `pk⁰, pk¹`. These are arbitrary byte
  strings. They may be equal (pure unlinkability), adversarially generated, or rogue.
- Honest Clients `C₀`, `C₁` each run `issue_request(ctx_iss, ctx_red)`.
  - *colluding*: `A` receives both issuance requests, plays the Anchor, and returns `s⁰`, `s¹`.
  - *non-colluding*: honest Anchors with keys `pk⁰`, `pk¹` respond, and `A` sees nothing.
- If either `finalize_issue` fails, the game outputs a random bit. A selective failure is visible
  and inherent.
- The challenger flips `b`. "Left" is `C_b`'s token and "right" is `C_{1−b}`'s.
- `A` may ask, once per side, for that token to be redeemed under an Anchor Set `S` and digest `cd`
  of its choice. `S` must contain the issuing key of *both* tokens, at indices that the Client
  takes from `S` itself; otherwise the request is refused for both. Without this rule, a refusal
  reveals the issuer: this is the partitioning leak of §7.
- `A` outputs `b'`. Let `Adv = |2·Pr[b' = b] − 1|`.

The four ZK proofs in play are two issuance and two redemption proofs. On `main`, these hops are
**not** independent: both relations put the same `r` first in the witness, which is what (PU) is
about. lean/docs/zk.md bounds each proof separately, with `Pred_R` measured in a world with simulated proofs.
For the joint hop, take the bad event "`A` queries H₅ at a sibling label of any of the four proofs"
and evaluate it in the hybrid where **all** proofs are simulated. That is the standard
identical-until-bad argument, and it avoids circularity. In that hybrid, `r₀` and `r₁` enter `A`'s
view only through `t₀` and `t₁`. So:

```
ε_ZK^joint(main) = Σ_{4 proofs} (ε_rho + ε_prog + 2ε_hide + ε_iv) + 4·(Q₅ + n_mult·Q_V)·Pred + 4·Q_P·2^{−128}
ε_ZK^joint(fix)  = Σ_{4 proofs} (ε_rho + ε_prog + 2ε_hide + ε_iv) + 4·(Q₅ + n_mult·Q_V + Q_P)·2^{−128}
```

On `main`, `Pred ≤ Adv^ow-r_Com` in the colluding mode, where `A` knows `t`. In the non-colluding
mode `Pred = 2^{−128}`, because `r` is independent of `A`'s view.

**Theorem 4.** For every classical `A`:

```
(a) colluding:      Adv^anon ≤ 2·ε_ZK^joint + 2·Adv^hide_Com + 2^{−192}
(b) non-colluding:  Adv^anon ≤ 2·ε_ZK^joint|_{2 redemption proofs, Pred = 2^{−128}} + 2^{−192}
```

(b) is wrong as stated: it misses an abort term (below). The corrected statement, mechanized
(`Privacy/MoussakaNC.lean`), is

```
(b') non-colluding:  Adv^anon ≤ 2·ε_ZK^joint|_{2 redemption proofs} + 2·(φ₀ + φ₁),
     φ_c = Pr_{nf, r}[DerivePreimage_{sk_c}(Com(nf, ctx_iss, ctx_red, r)) fails]
     E_vin[φ_c] ≤ δ(sk_c)^{255}   (on average over the vinegar hash SHAKE256, a random oracle;
                                   pqov's DerivePreimage fails only when its first 255
                                   vinegars are bad; no assumption on Com),
     E_key[δ^{255}] ≤ 255^{−37} + 1/(255·256^{37}) ≈ 2^{−295.8}
                                  (on average over the key's P2 part; Lean for O = 0),
```

(In Lean, `anonymityNC` takes the signer abstract; `Spec/PqovSigner.lean` models pqov's
`DerivePreimage` and proves it correct and failing only on singular systems, and
`Privacy/MoussakaPqov.lean`, `Privacy/PqovDelta.lean` give the bounds above: Appendix B. The
always-failing signer is also `Correct`, with `φ_c = 1`, so the abstract theorem needs the
concrete signer to be meaningful.)

and with one Anchor (`pk⁰ = pk¹`, pure unlinkability) `Adv^anon ≤ 2·ε_ZK^joint|_{2 redemption
proofs}`, with no abort term and for any index rule. The game is as above, with the Client taking
its index from `S` (the index holds its issuer's map or is out of range).

*Proof (a).*
1. In each world, replace all four proofs by simulated ones (`ε_ZK^joint` per world).
   - This uses ZK for **adversarially chosen statements**: `S` (rogue keys included), `cd` and the
     Anchor responses are chosen by `A`.
   - lean/docs/zk.md's two-phase definition allows this (its sampler includes `A`'s first stage). The
     simulator needs only the statement, and the honest witness satisfies the relation.
   - The constant-time validity check (`moussaka.cpp:196-211`) and the witness encoding
     (`redeem.hpp:119-123`) do not branch on `i`. The proof size is fixed.
2. Now `A`'s view consists of:
   - `t₀, t₁`, and its own `s⁰, s¹`;
   - the simulated proofs, which are functions of the statements only;
   - the revealed nullifiers, in left/right order;
   - `S`, `ctx`, `cd`.
3. `b` enters only through which `nf` is paired with which `t`.
4. Replacing `(nf₀, nf₁)` by independent uniform values costs `Adv^hide_Com`. This is legitimate in
   the standard model, because no proof evaluates `Com` on the honest inputs any more. After the
   replacement the two worlds are identical.
5. The `2^{−192}` term covers `nf₀ = nf₁`. ∎

*Proof (b).* As in (a), but `A` never sees `t₀` and `t₁`. After the hop, the nullifiers are
independent uniform strings in both worlds. No Keccak assumption is used. ∎

The last step is where (b) fails: the redemptions happen only if both issuances succeeded, and
success is not independent of the nullifiers. *Proof (b').*
1. Replace the two redemption proofs by simulated ones (`2·ε_ZK^red` per world). The issuance
   proofs are never shown to `A` and are not simulated: nothing is assumed of the issuance proof
   system, not even completeness.
2. Now the view is a function of the refusal bit `g = good₀(x₀) ∧ good₁(x₁)`, the two nullifiers
   (in left/right order) and the simulator coins. `x_c = (nf_c, r_c, ρ_c)` is Client `c`'s tape and
   `good_c(x)` says that Anchor `c` accepted the request, `DerivePreimage_{sk_c}(t)` succeeded,
   and the token is redeemable at its index in both sets. `t` and `r` appear nowhere else, so no
   hiding is needed.
3. If the Client takes its index from `S` (the key at the index has its issuer's map, or the
   index is out of range), then, unless `DerivePreimage_{sk_c}` fails on `t_c`, `good_c(x)` equals
   `acc(x) ∧ K_c`. Here `acc(x)` (length and proof check) is the same function for both Anchors,
   and `K_c` (the key is found in both sets) is a constant. Replacing `g` by the symmetric
   `acc(x₀) ∧ acc(x₁) ∧ K₀ ∧ K₁` is identical until a `DerivePreimage` fails: `φ₀ + φ₁` per world.
4. The resulting hybrid is symmetric in the two Clients' tapes. Swapping them exchanges the worlds,
   so the worlds are equal (no `2^{−192}`: the swap needs no distinctness).
5. `φ_c`. `DerivePreimage` is deterministic: its vinegars are `SHAKE256(t ‖ sk_seed ‖ … ‖ ctr)`.
   It tries `ctr = 0, …, 255` but uses only the first 255: `ov_preimage_core` increments
   `n_attempt` before each attempt and returns `-1` when `MAX_ATTEMPT_VINEGAR <= n_attempt`
   after the loop (`subprojects/pqov/src/ov.c:166`), which also discards a success at
   `ctr = 255` (upstream pqov; harmless). So it fails iff the first 255 vinegars are all bad
   (`lean/docs/security/uov-assumptions.md` §2 says 256). With SHAKE256 a random oracle (Lemma D),
   the vinegars at any fixed `t` are uniform, so for every fixed `(nf, r)` the failure
   probability is `δ(sk_c)^{255}`, whatever `Com(nf, …, r)` is, and `E[φ_c] ≤ δ(sk_c)^{255}` with
   no statement about `Com`. The figure `δ ≤ 1/255` is the fraction `σ` of singular `45 × 45`
   matrices over GF(256); it is not a bound for a fixed key, since `L_v = vᵀ S` ranges over a
   space of dimension `≤ 74` of matrices (a key with `S = 0` has `δ = 1`). It holds on average over
   the key: `S = (P1 + P1ᵀ)O + P2` is uniform for uniform `P2`, and for `v ≠ 0` so is `L_v`, hence
   `E[δ] ≤ σ + 256^{−74}`; for `m ≤ 74` linearly independent vinegars the systems are independent
   and uniform, hence `E[δ^m] ≤ σ^m + 256^m/(255·256^{74})`, and with `m = 37`,
   `E[δ^{255}] ≤ E[δ^{37}] ≤ 255^{−37} + 1/(255·256^{37}) ≈ 2^{−295.8}`. (The adversary makes no SHAKE256 query at `sk_seed` in this game, so Lemma
   D's `q_v·2^{−256}` term does not arise.)
6. One Anchor: `good₀ = good₁` as functions, so the refusal bit is already symmetric and step 3 is
   not needed, for any index rule. ∎

Why the abort term is needed in general: with `pk⁰ ≠ pk¹`, the targets on which `DerivePreimage`
fails differ between the Anchors. Conditioned on both issuances succeeding, the laws of `nf₀` and
`nf₁` can then differ, and the pairing of nullifiers to sides is no longer exchangeable. The term is
negligible, but it is not zero. Why the index rule is needed: with an arbitrary rule that points
Client `c` at a foreign key `P'`, the refusal reveals whether `P'(s_c) = t_c` for the Client's
hidden `s_c`, and nothing here bounds that event.

**[Lean] `lean/VoleMole/Privacy/Moussaka.lean`, Theorem 4(a).** The game above on
`Spec/Moussaka.lean`'s `issueRequest`, `finalizeIssue` and `redeemRequest`, with the seed XOF's
outputs `(nf, r, ρ_iss)` and `ρ_red` drawn uniformly (`issueRequest_eq`, `redeemRequest_eq`), any
Client-side index rule `idx`, and the refusal rule above (`allOk`). The seed-XOF hop to the real
Clients is mechanized for the random-oracle games of Appendix B (`lean/docs/zk.md` §10.6).
- Step 1, one proof at a time: `issue_close`, `redeem_close`, from zero knowledge as the hypothesis
  `Privacy.ZeroKnowledge` (simulator from the statement; `ε`-close for every statement and valid
  witness, against distinguishers that may know the witness). **On `main` no efficient simulator
  satisfies this per-proof hypothesis** (a distinguisher that knows `r = w[0..16)` computes Θ and
  runs the test of `lean/docs/zk.md` Prop. 4.1); there the joint (PU) hop over the four proofs
  replaces it and stays on paper. With the label-row
  fix it is `lean/docs/zk.md`'s theorem. The hypothesis is needed only for well-formed instances
  (`IssueRelW`, `RedeemRelW`: contexts of 16 bytes, `nf` of 24, an Anchor Set of at most 64 keys,
  as the C++ types and the Anchor Set's validation enforce).
- Steps 2–3: `simGame_iff`: with all proofs simulated, the view is a function `hview` of
  `t₀, t₁`, the nullifiers and the simulator coins; `r` enters nothing else.
- Step 4: `hiding_hop`, with `Adv^hide_Com` as the hypothesis `hidingAdv ≤ εhide` for the explicit
  reduction `reduction` (the adversary with the simulator coins fixed). After it the worlds
  coincide exactly (`idealGame_eq`).
- `anonymity`: `|Pr[A accepts | b = 0] − Pr[A accepts | b = 1]| ≤ 4εI + 4εR + 2εhide`, the
  `2·ε_ZK^joint + 2·Adv^hide_Com` of Theorem 4(a) with `ε_ZK^joint` taken as the sum of the four
  per-proof errors.

Remarks from the mechanization:
- **The `2^{−192}` term of Theorem 4(a) is not needed.** After the hiding hop the two revealed
  nullifiers are a fresh independent pair in either order, which is exchangeable whether or not
  they collide.
- **Theorem 4(b) misses an abort term**: corrected to (b') above and mechanized below. An
  earlier version of this remark said that bounding the abort probability needs a statement about
  `Com`'s outputs. It does not: `DerivePreimage`'s vinegars are a random-oracle hash of the target,
  so its failure probability at every fixed target is `δ^{256}` (`pr_fail_vinegar`). So "no Keccak
  assumption" is exact.

**[Lean] `lean/VoleMole/Privacy/MoussakaNC.lean`, Theorem 4(b').** The non-colluding game on
`Spec/Moussaka.lean`'s `issueRequest`, `issueResponse` (the honest Anchor verifies the issuance
proof, then runs `derive_preimage`: any `Signer` correct for its key, which may be
adversarially chosen), `finalizeIssue` and `redeemRequest`. The seed-XOF outputs are uniform. The
adversary (`AdversaryNC`) chooses the contexts, both keys and, per side, `S` and `cd`, and sees
only the two redemption requests or the refusal. The refusal rule is that of 4(a).
- Step 1: `hopL_NC`, `hopR_NC`, `real_sim_NC`, from `Privacy.ZeroKnowledge` for `RedeemRelW` via
  `redeem_close`. No hypothesis on the issuance proof system `PI`.
- Step 2: `simNC_iff`. Step 3: `good_eq_of_derive`, `sim_hyb_NC` (`IdxSound idx`: the Client's
  index holds its issuer's map, or nothing). Step 4: `hybNC_eq`.
- **`anonymityNC`**: `|Pr[W₀] − Pr[W₁]| ≤ 4εR + 2·(φ false + φ true)`, `φ c` = `phi`: the
  probability over uniform `(nf, r)` that `sk c` fails on `Com(nf, ctx_iss, ctx_red, r)`.
- **`unlinkabilityNC`**: one Anchor, any index rule: `≤ 4εR`.
- **`anonymityNC_vinegarRO`** (step 5): with each Anchor's signer failing only when all 256
  vinegars of a uniform table at the target are bad (`hfail`), averaged over the tables
  `≤ 4εR + 2·(δ₀^{256} + δ₁^{256})`, `δ_c` the fraction of bad vinegars (`pr_fail_vinegar`,
  from `pr_eval` and `pr_forall_fin`). With pqov's signer (255 usable vinegars):
  `anonymityNC_pqov`, `≤ 4εR + 2·(δ₀^{255} + δ₁^{255})` (Appendix B).
- The honest Anchor checks the request length of the label-row layout (`45 + 7528` bytes,
  `Spec.Moussaka.issueResponseLR`), the layout of the Lean prover of the random-oracle games
  below; `main`'s `45 + 7272` would make every honest label-row request malformed.
- With the executable Lean prover for redemption (label rows): `anonymityNC_label_rows` (tape
  hypothesis), `anonymityNC_label_rows_shake` (hop hypotheses: `εR = ε_rho + ε_grind + ε_bavc +
  ε_lab`), `unlinkabilityNC_label_rows`.
- As in 4(a), the per-proof zero-knowledge hypothesis holds with the label-row fix only. On `main`
  no efficient simulator satisfies it against witness-knowing distinguishers, and the note's joint
  hop with `Pred = 2^{−128}` (which is valid here, since `r` is independent of `A`'s view) stays
  on paper.
- **In the random-oracle and ideal-cipher model** (`lean/VoleMole/Privacy/MoussakaNCRO.lean`,
  Appendix B; the analogue of `anonymityRO_lean_num`): `A`'s guess also sees the tables, and the
  honest Anchors run the Lean **verifier** on the issuance proofs over the same tables. In each
  redemption hop the reduction recomputes the refusal bit, so it runs the two issuance proofs and
  their verifications; this needs the verifier's read budgets (`312` `H₅`, `4607` cipher keys,
  `ZK/VerifyReadsRO.lean`). A real issuance proof or verification reading `H₂³` at a point a
  simulated redemption programmed needs **no collision term**: the hybrids run the issuances on the
  tables after the redemptions' programming (the first hybrid, with nothing programmed, is the real
  game), so it is part of the reduction. `anonymityNCRO_lean_num`: `≤ 4·εRO(q₃, q₅ + 2496,
  q_E + 23035) + 2·(noHitProb + 2⁻¹⁰²⁴) + 2·(φ₀ + φ₁) + 4·q₃·2⁻¹²⁸`, about `2⁻¹⁰³·²` plus the budget
  terms and the abort term; the `4·q₃·2⁻¹²⁸` lets the guess see the issuance slices (the swap
  exchanges the Clients' tapes). With one shared `H₃`, as in the scheme
  (`lean/VoleMole/Privacy/MoussakaNCSh.lean`): `anonymityNCSh_num`, `≤ 4·εRO(q_E + 23038,
  q₅ + 2496, q_E + 23038) + 2·(noHitProb + 2⁻¹⁰²⁴) + 2·(φ₀ + φ₁)`, also about `2⁻¹⁰³·²`; the slice
  term disappears (the issuance proofs read the shared tables, which the swap does not exchange),
  and the guess's `H₃` reads are row reads inside the zero-knowledge error. With the real Clients'
  seeds (`Privacy/SeedXOFNC.lean`): `anonymityNCRO_lean_num_seed`, `anonymityNCSh_num_seed`
  (and the unlinkability and `_perm` versions), `+ 2·(2q_X + 2)·2⁻²⁵⁶`.
- `Spec.Moussaka.finalizeIssue` accepts a response of any length (in C++, `s` is a 119-byte
  `std::array`), so the spec admits tokens with `|s| ≠ 119`, for which `redeemRequest` would prove
  a witness outside `RedeemRel`. The game types the adversary's responses as 119 bytes, as the C++
  does. Harmless for the C++; noted for the spec.

**What the bounds mean.**
- *Issuer hiding* is (a) or (b) with `pk⁰ ≠ pk¹` and one redemption. The Moderator, even colluding
  with all Anchors and choosing the other keys, cannot tell whose token it sees.
- *Unlinkability* is the case `pk⁰ = pk¹`.
- `ctx_red` hiding from the Anchor follows from the same hops: `ctx_red` is in the issuance witness
  and in `t`, behind 128 bits of `r`.

**Magnitudes at `q = 2^{64}`** (generic estimates of §3.2):
- `Adv^hide ≈ 2^{−63}`. This is the generic 128-bit level, with no margin. The cause is `r_len = 16`
  together with a colluding Anchor that knows `t`.
- On `main`, lean/docs/zk.md's `4(Q₅ + n_mult·Q_V)·Adv^ow-r` is a *product* of two query counts. At
  `Q₅ ≈ q ≈ 2^{64}` it is vacuous (F4). Generically, the two searches (H₅ queries and Keccak
  evaluations) test one guess of `r` each, so the probability is additive, `≈ (Q₅ + q)·2^{−128}`.
  But that sharper form is a heuristic, not what lean/docs/zk.md proves.
- On the fix, the bound is `≈ 2^{−60}`, with no Keccak term.

---

## 7. Malicious Anchor Sets and rogue keys

1. **Rogue or malformed keys do not break hiding *within* a set.**
   - Any 46591-byte string expands to a public map (`uov.cpp:73-80`; `expand_pk` always succeeds).
   - ZK holds for every true statement, whatever the other keys are (Thm 4).
   - An adversary that knows the honest Client's `s`, because it issued the token, can craft a key
     `P'` with `P'(s) = t`. The token is then valid at two indices. This changes nothing, since `b`
     is hidden.
   - Duplicate keys are rejected by digest (`moussaka.cpp:144-150`). Distinct compressed keys give
     distinct maps (16-byte `pk_seed` expanded by AES-CTR, and a canonical upper-triangular `P3`). So
     the check is hygiene, not a security requirement: duplicates would neither leak `i` nor help
     forge.
2. **What a malicious Moderator *can* do is partition**, and this is outside the cryptography.
   - `1 ≤ n` is allowed (`moussaka.cpp:139`), and `n = 1` gives no issuer hiding, as the
     architecture draft says.
   - A minimum `n` would not help. The Moderator can pad `S` with dummy keys of its own, or with keys
     of Anchors that no Client uses, and the Client cannot tell.
   - The Client must also refuse a set that omits its Anchor (the protocols draft says so;
     `moussaka.cpp:192-194` and `:208-211` throw). Each refusal tells a Moderator that serves
     different sets to different Clients (or one at a time) "issuer ∉ S".
   - So issuer hiding is meaningful only relative to the honest, actually used Anchors in a set that
     all Clients see consistently (architecture draft, "Configuration Consistency and Partitioning
     Attacks").
   - The library offers no consistency check, and no API for one. The Client should accept only a
     consistent, published set.
3. **Per-Client keys and contexts.**
   - An Anchor that issues to Client X under a key `pk_X` used only for X lets a colluding Moderator
     test, with sets that include or omit `pk_X`, whether a refusing Client is X.
   - Likewise, a per-Client `ctx_iss` links directly, because `ctx_iss` is public at both ends. The
     anonymity set is "tokens with equal `(ctx_iss, ctx_red)` whose issuer is in `S`".
   - Clients must check that `ctx_iss` is a common epoch value, and that Anchor keys come from the
     consistent registry.
4. **Unforgeability under a malicious set** is not a goal. A Moderator that includes a weak or
   foreign key accepts whatever that key's owner signs.

---

## 8. Quantum adversaries

MoLE needs **security** (unforgeability) only against pre-CRQC attackers. It needs **privacy**
against a future CRQC that analyses recorded transcripts.

**Unforgeability in the QROM** (not required by MoLE):
- The structure of Theorem 1 survives. `B₂` needs no mid-run extraction, because the CT-UF oracle
  takes targets. All extraction happens after the run.
- What changes:
  - `ε_ext^R` becomes Q2's Theorem 7.1: `Σ² + ε_multi + ε_rec`, with leading term
    `≈ 200·q²·2^{−128}`. This is `2^{−60}` at `q = 2^{30}` and vacuous at `2^{64}`.
  - `ε_multi` is open above about `2^{40}` cipher queries.
  - Q2 is stated for one proof. Simultaneous extraction from the `Q_iss + Q_red` outputs is
    `lean/docs/extraction/Q7-qrom-multi-extraction.md`'s Theorem M, and Q7 §6 states Theorem 1 in
    the QROM with it (paper).
  - QROM SE is Q5 (paper), but Theorem 3 is not restated with it (Q7 §6), so Theorem 3 has no
    quantum version.
  - `Com` generic quantum bounds:
    - binding `≲ q³/2^{360}` (BHT) `+ q²/2^{224}` (Grover on the inverse, `2^{112}` work);
    - one-wayness and hiding in `r`: `≲ q²/2^{128}`, a `2^{64}` Grover search.
  - Lemma U needs programming a quantum random *permutation* with inverse access. There is no
    general tool for this, so the link from CT-UF to one-more-UOV is heuristic. Quantum CT-UF is a
    standalone assumption.

**Privacy against a CRQC:**
- ZK against quantum distinguishers (QROM programming of H₂³ and H₅) is proved on paper in
  `lean/docs/zk-qrom.md`, with the label-row fix: about `2⁻¹⁹` at `2³⁰` queries and `2³⁰` proofs
  (the dominant term is the adaptive-reprogramming loss, README §3). It is not mechanized, and
  Theorem 4 is not restated with it.
- Generic quantum attacks bound privacy at NIST level 1, with no margin:
  - **Hidden-leaf keys.** Each proof contains the commitments `com_{i,Δ_i} = E_k(x₀) ‖ E_k(x₁)` of
    its unopened leaves (AES-128). A Grover search of about `2^{64}` iterations recovers one hidden
    key `k`. One known tree gives the full witness (the README extractor's candidate
    `w^{(i)} = u_i ⊕ c_i ⊕ d`), so this reveals `b` (the issuer), `s` and `r`. It works against a
    **non-colluding** Moderator too, on both `main` and the fix. Classically this is the `2^{128}`
    `ε_hide` term.
  - **Opening search.** For a colluding Anchor, which knows `t`, a Grover search over `r` of about
    `2^{64}` Keccak-p[800,12] iterations links `nf` to `t`.
- This matches level 1 by definition (AES-128 key search). It should be stated in the
  documentation, since MoLE names CRQC-era privacy as a goal.

---

## 9. Findings and attacks

**F1 — Cross-protocol key reuse allows unlimited forgery (high, deployment/API).**
- *Mechanism.*
  - Moussaka Anchors and PomFRIT Issuers use the same key type, `uov::SecretKey`.
  - `pomfrit::issue_response(sk, t)` returns `DerivePreimage(sk, t)` for **any** 45-byte `t`, with
    no proof (`src/pomfrit/pomfrit.cpp:188-190`).
  - A Client computes `t = Com(nf, ctx_iss, ctx_red, r)` locally, for any `ctx_iss` (any epoch),
    and sends `t` to the PomFRIT endpoint. It then finalizes a valid Moussaka token
    (`moussaka.cpp:177` checks only `P(s) = t`).
  - This bypasses the Moussaka Anchor's `ctx_iss` check and rate limit.
- *Demonstrated* with the public API only (Appendix A, demo 1): `ACCEPTED`.
- *Scope.*
  - Ratatouille key reuse is not exploitable this way. It signs `Tag(c, ·)` behind a proof, and a
    forgery would need a 360-bit cross-function collision.
  - Different Moussaka `VERSION`s are separated by the DST.
- *Documentation gap.* The only warning is in `uov.hpp:64-68`, and it is about full UOV
  signatures.
- *Fix.* Document "an Anchor key MUST be used only for Moussaka". Better, domain-separate at the
  signing layer: hash a protocol tag into the target, or check a tag in `issue_response`. Or bind
  the Anchor key into the issuance instance (the draft's NOTE).

**F2 — Nullifier squatting (low, griefing).**
- *Mechanism.*
  - An adversary that learns an honest `nf_h` before the honest redemption is processed creates
    its own commitment to `nf_h` and gets it signed by any honest Anchor, spending its own quota.
    Examples of such an adversary: a relaying origin, or a network attacker on an unencrypted path.
  - It redeems first. The honest token is then rejected as a double spend.
  - The adversary gains no extra token, so Theorem 1's count is respected.
- *Demonstrated* in Appendix A, demo 2: `adversary … ACCEPTED; honest token then REJECTED`.
- *Fix.* Derive `nf` inside the circuit from a committed secret (the draft's issue 45), or have the
  Moderator bind the redemption to the channel.

**F3 — The draft's proof sketch for one-more-UOV programs `Com` inside the protocol.**
- The sketch answers "`B` asks `Com(nf, r)`" with challenge targets. But the redemption and
  issuance proofs evaluate the concrete Keccak-p circuit, and the extractor returns `x` with
  `KP800(x)|₃₆₀ = t` for the *real* permutation. So the programmed values do not match what is
  proved.
- §4 repairs this:
  - first reduce to the standalone assumptions CT-UF and binding, using only the extractor;
  - then idealise `Com` only inside the CT-UF game (Lemma U).
- The draft's earlier "tagged `c ‖ x`" discussion has the same issue.

**F4 — Privacy margins (informational).**
- Against colluding Anchors, privacy is exactly 128-bit (`r_len = 16`) classically and 64-bit with
  Grover. The AES-128 hidden-leaf bound caps privacy against everyone at 64-bit Grover.
- On `main`, lean/docs/zk.md's formal `Pred` term multiplies two query counts (§6).
- *Cheap improvement.* The 9 zero bytes after `r` (`commit.hpp:34`) could carry a longer `r`, at
  72 more witness bits.
  - The trade-off is fewer fixed input bits (224 → 152). That lowers the generic inverse-forgery
    cost to `2^{152}`, or a `2^{76}` Grover search.
  - A middle ground, such as `r_len = 20`, keeps both above level 1.
- The fix (§10) is the more important change for the formal ZK bound.

**F5 — Partitioning through the Anchor Set and contexts (inherent, deployment).** See §7. The
library accepts any set with `1 ≤ n ≤ 64` and any `ctx_iss`. This is consistent with the drafts,
which delegate consistency to deployment.

**F6 — Interoperability (D1, D10).** `challenge_digest`'s place in the transcript, and the DST
position, are not pinned down by the draft.

**Checked and found sound:**
- the constant-time index check and witness encoding;
- the selector (Lean);
- transcript binding: fixed-length or length-prefixed fields, and SHAKE256 digests, so `ε_dig` is
  needed;
- deterministic `DerivePreimage`, domain-separated from `ov_sign` (`ov.c:217-224`);
- token consumption: `Token` moved, not copyable outside `TokenAccess`;
- `finalize_issue` rejects invalid `s`.

The issuance proof binds `(t, ctx_iss)` but not the Anchor. Replaying an honest request to another
Anchor gives only a signature on someone else's `t`, which is useless without `r`, so this is
harmless.

---

## 10. `main` versus the `voleith-label-rows` fix

| | `main` | fix (`CRT_DEDICATED_LABEL_ROWS`, branch `voleith-label-rows`; proofs grow to 7528 / 9007 bytes) |
|---|---|---|
| ZK notion | (PU)-ZK: `Pred_R` = predicting `r` | Standard adaptive NIZK |
| `ε_lab` per proof | `(Q₅ + n_mult·Q_V)·Pred + Q_P·2^{−128}` | `(Q₅ + n_mult·Q_V + Q_P)·2^{−128}` |
| Thm 4(a), colluding | needs `Adv^ow-r` inside ZK *and* `Adv^hide`. The formal bound is vacuous at `q ≈ 2^{64}` | needs only `Adv^hide` (`≈ 2^{−63}` generic) |
| Thm 4(b'), non-colluding | `Pred = 2^{−128}`, no Keccak assumption, `+ 2·(φ₀ + φ₁)` | same, with a cleaner bound ([Lean] `anonymityNC`; in the ROM and ideal-cipher model `anonymityNCRO_lean_num`) |
| Joint hop over proofs sharing `r` | needed (§6) | not needed: the hops are independent |
| Thms 1 and 3 | unchanged (ZK enters Thm 3 only through `ε_hop`) | unchanged |
| Quantum privacy | AES-128 Grover cap (§8) | same cap |

---

## 11. Open gaps

1. Lemma DS (application vs proof-system hash disjointness) is proved on paper, with the
   separation table checked in Lean (`lean/docs/security/domain-separation.md`,
   `Protocols/DomainSeparation.lean`); SHAKE as a random oracle remains the modelling step.
2. CT-UF → plain UOV problem: the signing simulation with retry (§3.3) is not re-derived. The
   theorems rest on CT-UF, or on one-more-UOV via the heuristic Lemma U, as the draft does.
3. `Com`'s binding, one-wayness and hiding are assumptions about 12-round Keccak-p[800]. Only
   generic estimates are given.
4. QROM: Theorem 3 has no quantum version (QROM SE is Q5, not applied here); ZK is on paper only
   (`lean/docs/zk-qrom.md`), and Theorem 4 is not restated with it; multi-output extraction and
   Theorem 1 are in `lean/docs/extraction/Q7-qrom-multi-extraction.md` (paper). `ε_multi` caps Q2
   at about `2^{40}` cipher queries.
5. Privacy in Lean (Appendix B; `lean/docs/zk.md` §10).
   - *Theorem 4(a)* is mechanized for a fixed-size game (two Clients, one redemption per side),
     in the ROM and ideal-cipher model with every zero-knowledge term explicit
     (`anonymityRO_lean_num`), with a table-reading interaction (`anonymityRA_lean_num`; as oracle
     computations, `anonymityOC_lean_num`), with AES's rows uniform permutations read forward and
     inverse (`_perm`), with one shared `H₃` (`anonymitySh_num`, `anonymityRASh_num`) and from the
     real Clients' seeds (`anonymity*_seed`, `+ 2·(2q_X + 2)·2⁻²⁵⁶`); and with many Clients
     (`lean/docs/zk.md` §10.8): any number of further honest Clients on the same tables, issued
     with the challenge Clients and redeeming at Anchor Sets chosen after every issuance request
     (`anonymityN_lean_num`, `≤ n·2⁻¹⁰²` plus budget terms and `2·εhide` for `n` Clients in all),
     also adaptively scheduled, Clients started before, during and after the challenge from
     earlier outcomes, the challenge contexts and keys chosen by a key stage that reads the
     tables (`anonymityRAK_lean_num`; `anonymityAd_lean_num`, the same `≤ n·2⁻¹⁰²`), also
     interleaved, Clients started and answered in any order (`anonymityIL_lean_num`, `≤ (n + 2)·2⁻¹⁰¹`;
     with a scheduler that reads the tables and places the challenge, `anonymityILO_lean_num`),
     and `N` challenge pairs (`anonymityP_lean_num`, `≤ N·(2N·2⁻¹⁰² + 2·εhide)` plus budget terms:
     `2⁻⁶³` at `2²⁰` Clients, `2⁻³⁹` at `2³²`; quadratic by an artifact of the proof).
   - *Theorem 4(b)*, corrected to (b′) with the abort term `2·(φ₀ + φ₁)`, is mechanized for the
     same game from per-proof zero knowledge of the redemption proofs (with the Lean prover down to
     its tape and hop hypotheses; the abort term `≤ 2·(δ₀^{256} + δ₁^{256})` in the vinegar
     random-oracle model, `Privacy/MoussakaNC.lean`), and in the ROM and ideal-cipher model with
     the honest Anchors' Lean verifier on the shared tables (`anonymityNCRO_lean_num`), with one
     shared `H₃` (`anonymityNCSh_num`) and from the real Clients' seeds (`*NC*_seed`), each with
     `_perm`; with a model of pqov's signer (`2·(δ₀^{255} + δ₁^{255})`; averaged over keys of
     pqov's key generation with `O = 0`, `≤ 4·(255^{−37} + 1/(255·256^{37}))`), and with the games
     shown to reach redemption (`Privacy/MoussakaPqov.lean`, `Privacy/PqovDelta.lean`).
   - *What remains*: SHAKE as a random oracle and AES as an ideal cipher; the hiding of `Com` for
     4(a) (computational, §3.2); the consistency of a table-reading interaction given as a bare
     function of the tables (a theorem for oracle computations); for 4(b), adversary choices that
     read the tables (no `RA`/`OC` version); in the interleaved game, a second challenge Client
     whose contexts or key are chosen after the first one's request, and the factor about 2
     against the sequential schedule (`lean/docs/zk.md` §10.8 "Open"); a bound linear in `N` (the lazy-sampling reduction that
     gives one for PomFRIT with `H₄` a table does not apply as it stands, since the further
     Clients' redemption statements are chosen after the challenge requests); further Clients in
     the shared-`H₃`, seed-XOF and non-colluding games.
6. Whether lean/docs/zk.md's `Pred` product can be made additive on `main`. It is moot with the fix.
7. Timing side channels beyond the index check (OS RNG, allocation) are out of scope.

---

## Appendix A: demonstrations

These are in `$SCRATCH/demo/moussaka_attacks.cpp`, outside the repo, where `$SCRATCH` is
`/tmp/claude-1016/-home-claude-scm-vole-mole/93cbb905-f2d6-4f97-8011-866bcdeb7a31/scratchpad`.
They were built against `build/libvole-mole.a` (`main`):

```
demo1 (PomFRIT-signed target accepted as Moussaka token): ACCEPTED
demo2: adversary token with squatted nf ACCEPTED; honest token then REJECTED (double spend)
```

- Demo 1 uses only the public API:
  1. `moussaka::issue_request`;
  2. truncate the request to `t`;
  3. `pomfrit::issue_response(sk, t)`;
  4. `finalize_issue`, `redeem_request`, `finalize_redeem`.
- Demo 2 uses `detail::commit` and `detail::prove_issue_request` to choose `nf`, which any custom
  Client can do.

## Appendix B: Lean

`lean/VoleMole/Protocols/Moussaka.lean`, checked with `lake env lean`, with no `sorry` and no
`axiom`:
- `selector_one_hot` (any field) and `selector_one_hot_gf2`: the parity and weight constraints imply
  one-hot with entry 1 (§5.2).
- An `example` showing that the weight constraint alone fails over `GF(2)`.
- `exists_unsigned_of_card_lt`: the pigeonhole step of Theorem 1.

`lean/VoleMole/Privacy/Moussaka.lean` (Theorem 4(a), §6): `anonymity` (`≤ 4εI + 4εR + 2εhide`
from per-proof zero knowledge and the hiding of `Com` for the explicit reduction), with the hops
`issue_close`, `redeem_close`, `simGame_iff`, `hiding_hop`, `idealGame_eq`. `#print axioms`:
`propext`, `Classical.choice`, `Quot.sound`.

`lean/VoleMole/Privacy/MoussakaNC.lean` (Theorem 4(b'), §6): `anonymityNC` (`≤ 4εR + 2·(φ₀ + φ₁)`
from zero knowledge of the redemption proofs, signers correct for their keys and a sound index
rule; nothing assumed of the issuance proofs or of `Com`), `unlinkabilityNC` (one Anchor, any index
rule, `≤ 4εR`), `anonymityNC_vinegarRO` (`≤ 4εR + 2·(δ₀^{256} + δ₁^{256})` averaged over the
Anchors' vinegar tables), `anonymityNC_label_rows`, `anonymityNC_label_rows_shake`,
`unlinkabilityNC_label_rows` (the Lean prover for redemption), with the hops `real_sim_NC`,
`simNC_iff`, `sim_hyb_NC`, `hybNC_eq`. `#print axioms`: `propext`, `Classical.choice`,
`Quot.sound`.

`lean/VoleMole/Privacy/MoussakaLean.lean`: `anonymity_label_rows`, Theorem 4(a) with both proof
systems the executable Lean prover with dedicated label rows (the statements of
`Verifier/Relations.lean`), assuming only the tape hypotheses (`TapeHyp`, `lean/docs/zk.md`
§10.1), the hiding of `Com` and the hash record's output lengths (proved for SHAKE,
`anonymity_label_rows_shake`, which also derives the tape hypotheses from one hypothesis per hop,
`ZK/Hops.lean`, so `εI`, `εR` are sums `ε_rho + ε_grind + ε_bavc + ε_lab`; BAVC and CRT
completeness are proved, `Verifier/Bridge/`): the
witness encodings satisfy the
issuance and redemption systems for every combination (`issue_holds`, `redeem_holds`, from the
`Arith/Moussaka.lean` completeness theorems), and the other deterministic hypotheses are proved
(`zkHypI`, `zkHypR`).

`lean/VoleMole/Privacy/MoussakaRO.lean`: Theorem 4(a) **in the random-oracle and ideal-cipher
model**, where the adversary's final guess also sees the random tables (`H₃` per proof, `H₂³`,
`H₅`, the cipher) and the four proofs share them (`lean/docs/zk.md` §10.2). `anonymityRO` (any
proof systems that are `ZeroKnowledgeRO`, with bounded reads) and `anonymityRO_lean` (the
executable Lean prover with SHAKE for the other hashes and AES as an ideal cipher):

    |Pr[W₀] − Pr[W₁]| ≤ 8·εRO(q₃, q₅ + 3·624, q_E + 3·4607) + 2·δI₁ + Σ_b (δL b + δR b) + 2·εhide,

`εRO q₃ q₅ q_E = q₃·2⁻¹²⁸ + 2⁻¹¹³ + 221·(4607 + q_E + 4607)·2⁻¹²⁸ + (q₅ + 1)·2⁻¹²⁸` the
single-proof bound of `zk_rom_ic_h23_num`, at the budget of the reductions (each runs the later
proofs for real, `624` `H₅` and `4607` cipher reads each, and applies the earlier simulations'
`H₂³` programming, `312` and `4607` reads each). The `δ` are explicit programming-collision
probabilities of the hybrids (a real proof reads `H₂³` at a point an earlier simulation
programmed), bounded in Lean (`lean/VoleMole/Privacy/MoussakaDelta.lean`, `ZK/CollideRO.lean`,
zk.md §10.2): `δI₁ ≤ noHitProb + 2⁻¹⁰²⁴` (`deltaI1_le`), `δL b ≤ 2⁻¹¹³ + εRO(0, 312, 4607) +
noHitProb + 2·2⁻¹⁰²⁴` and `δR b ≤ … + 3·2⁻¹⁰²⁴` (`deltaL_le`, `deltaR_le`: the redemption
statement may depend on the simulated requests' `ã`, so the bound applies zero knowledge a second
time, to "the recomputed prefix's last `128` bytes are among the earlier simulations' `ã`"). So
**`anonymityRO_lean_num`**:

    |Pr[W₀] − Pr[W₁]| ≤ 8·εRO(q₃, q₅ + 1872, q_E + 13821) + 4·(2⁻¹¹³ + εRO(0, 312, 4607))
                        + 6·noHitProb + 12·2⁻¹⁰²⁴ + 2·εhide,

about `2⁻¹⁰²·³` plus `8·(q₃ + q₅ + 221·q_E)·2⁻¹²⁸` and `2·εhide` (`noHitProb ≤ 2^{−2¹⁵}`). The
earlier paper bound for a redemption (`εRO + 2⁻¹⁰²³ + 2·noHitProb`) missed the `Δ' = 0` part of
the grinding failure (`Pr[GrindBad] ≤ 2⁻¹¹³` instead of `noHitProb`, by the second-moment
bound on the acceptance set, `grindBad_le_113`). Restrictions of the model: the
adversary's interaction (contexts, keys, responses, Anchor Sets, digests) does not read the
tables, only its guess does (the zero-knowledge theorem is for statements fixed before the
tables; lifted below); the four `H₃` slices are independent (exact unless two proofs share `(μ₁, wPrefix)`,
`≤ 2⁻¹⁹²`; lifted below: with one shared `H₃` no such term); the seed XOF's outputs are uniform
(lifted at the end of this appendix); hiding is for the reduction with the
simulator coins and the tables fixed.

**With an interaction that reads the tables** (`lean/VoleMole/Privacy/MoussakaRA.lean`, zk.md
§10.3). Here the responses, Anchor Sets and digests are functions of the two requests, the four
`H₃` slices and the shared tables (programmed by the issuance simulations, in the hybrids). As a
function of each slice and the shared tables, the transcript reads at most `i₃` slice keys, `i₂`
`H₂³` keys, `i₅` `H₅` keys and `i_E` cipher keys, consistently (`AdversaryRA.IBudget`; any
deterministic query algorithm). The redemption statements are then read off the tables. The
redemption hops use zero knowledge for statements chosen from the tables (`zk_adaptive`,
`lean_zeroKnowledgeROA`). It costs `s₃·2⁻¹²⁸` for the 16-byte `ρ`, `(s₅ + 1 + 221·s_E)·2⁻¹²⁸`
for the reader's `H₅` and cipher reads in H6 and H4, and, if the reader reads `H₂³`, a second
application of zero knowledge plus `2·s₂·2⁻¹⁰²⁴`. The transcript reads through the two issuance
programmings, so the reader's budget is `(i₃, i₂, i₅ + 624, i_E + 9214)`. The collision terms are
bounded the same way (`pr_collide_adaptive`). **`anonymityRA_lean_num`**:

    |Pr[W₀] − Pr[W₁]| ≤ 4·εRO(i₃ + q₃, q₅ + i₅ + 1872, q_E + i_E + 13821)
                        + 4·εAd(9; q₃, q₅ + 1248, q_E + 13821; i₃, i₂, i₅ + 624, i_E + 9214)
                        + 4·(i₃·2⁻¹²⁸ + 2⁻¹¹³ + εROP(0, 312, 4607; i₅ + 624, i_E + 9214))
                        + 6·noHitProb + 12·2⁻¹⁰²⁴ + 2·εhide,

about `2⁻¹⁰¹·⁹` without budgets (`2⁻¹⁰¹·⁶` if the interaction reads `H₂³` at all). So the
restriction to a table-oblivious interaction is not needed: there is no attack, and the cost is
of the same order. For an interaction written as a VCVio oracle computation over the tables
(`AdversaryOC`, `lean/VoleMole/ROM/PrivacyReads.lean`), consistency is a theorem and the budget
the syntactic query bound (`QBudget`): `anonymityOC_lean_num`, `anonymityOC_lean_num_perm`, the
same bounds with no consistency hypothesis on the interaction (the guess keeps its semantic
read budget).

**With one shared `H₃`** (`lean/VoleMole/Privacy/SharedH3RO.lean`, `SharedH3RA.lean`,
`lean/VoleMole/ROM/SharedH3Reads.lean`, zk.md §10.5). In the scheme the four proofs hash with one
`H₃(wPrefix ‖ μ₁ ‖ ρ ‖ 3)`; the four slices are its restrictions to the four prefixes. The games are
proved again with `H₃` in the shared tables (each row carries `H₃`'s column at that `ρ`) and each
proof reading the column at its prefix, computed from the witness and instance it proves (the
redemption prefixes through the adversary's Anchor Sets and digests). No prefix-collision term is
needed: in each hop the replaced proof's column is re-sampled, and another proof with the same
prefix reads it at its own `ρ` (one row, inside `εRO`'s slice-read term).
**`anonymitySh_num`**: `8·εRO(q_E + 13824, q₅ + 1872, q_E + 13824) + 4·(2⁻¹¹³ + εRO(0, 312, 4607))
+ 6·noHitProb + 12·2⁻¹⁰²⁴ + 2·εhide` (the adversary's `H₃` reads count in `q_E`); with a
table-reading interaction (which may read `H₃` at a redemption's prefix before choosing it),
**`anonymityRASh_num`**: `4·εRO(q_E + i_E + 13824, q₅ + i₅ + 1872, q_E + i_E + 13824) +
4·εAd(9; q_E + 13822, q₅ + 1248, q_E + 13822; 0, i₂, i₅ + 624, i_E + 9214) + 4·(2⁻¹¹³ +
εROP(0, 312, 4607; i₅ + 624, i_E + 9214)) + 8·(i_E + 9214)·2⁻¹²⁸ + 6·noHitProb + 12·2⁻¹⁰²⁴ +
2·εhide` (the `RA` bound above with no slice reads, the row budgets in the slice-read slots, and
`8·(i_E + 9214)·2⁻¹²⁸` for a redemption's fresh `ρ` meeting a row the interaction read);
`anonymityOCSh_num` and `_perm` likewise. So the `≤ 2⁻¹⁹²` step is not needed; it is not wrong as
a bound on the prefix collision, but "independent slices up to `2⁻¹⁹²`" is not a black-box reduction
from one `H₃` (the slices' locations involve the Clients' secret `r`, `nf`).

**AES as random permutations** (`lean/docs/zk.md` §10.4, `Privacy/PermRO.lean`,
`Privacy/PermRA.lean`). The `RO` and `RA` theorems also hold with the cipher's rows uniform permutations that
the adversary reads forward and inverse: `anonymityRO_lean_num_perm`, `anonymityRA_lean_num_perm`,
the same bounds with every `εRO` (`εROP`, `εAd`) replaced by its permutation counterpart `εROPm`
(`εROPmP`, `εAdPm`), whose hop denominators are `2¹²⁸ − (nHi + 1)` and which carry the PRP/PRF
switching term `switchEps ≤ 2⁻¹¹³·²`; numerically the same to two decimals.

**The seed-XOF hop** (`lean/VoleMole/Privacy/SeedXOF.lean`, `Privacy/SeedXOFGames.lean`,
`ROM/SeedXOFReads.lean`, zk.md §10.6). With the real Clients (uniform 32-byte OS seeds, the seed
XOF a uniform table keyed by `(DST, seed)`, the adversary reading at most `q_X` cells), each of the
random-oracle theorems above holds with `+ 2·(2q_X + 2)·2⁻²⁵⁶`: `anonymityRO_lean_num_seed`,
`anonymityRA_lean_num_seed`, `anonymitySh_num_seed`, `anonymityRASh_num_seed`,
`anonymityOC_lean_num_seed`, `anonymityOCSh_num_seed`, each with `_perm_seed`. Theorem 4 has no
term for this hop (D7); the cost covers an XOF query at a Client's seed and two seeds of one domain
colliding. The abstract non-colluding game (`Privacy/MoussakaNC.lean`) keeps uniform seed
outputs; the random-oracle ones get the hop below (`Privacy/SeedXOFNC.lean`).

**Theorem 4(b′) in the random-oracle and ideal-cipher model** (`lean/VoleMole/Privacy/MoussakaNCRO.lean`,
`lean/VoleMole/ZK/VerifyReadsRO.lean`, zk.md §10.7). The non-colluding game on the spec
(`realGameNCRO`): each Client's `issue_request` with the Lean issuance prover on the shared tables
(its own `H₃` slice), the honest Anchor's `issue_response` with the **Lean verifier on the same
tables** (`leanVI`, the executable `Verifier.verify` with `H₂³`, `H₅` and the cipher the tables),
then `derive_preimage` (any signer correct for its key); `finalize_issue`, §6's refusal rule, and
the redemptions with the Lean redemption prover on the tables. The adversary's guess sees the
redemptions or the refusal, the four `H₃` slices and the tables, with read budgets
(`AdversaryNCRO.Budget`); its choices do not read the tables.
- The verifier's reads (`ZK/VerifyReadsRO.lean`): `H₅` at `≤ 312` keys (`verRO_rd5`), the cipher at
  `≤ 4607` (`verRO_rdE`), `H₂³` at one point (`verify_h23_congr`), no `H₃`.
- Step 1 (`hopL_NCRO`, `hopR_NCRO`): the redemptions simulated, with the issuances and the
  verifications run on the tables after the simulations' programming (`gameNCROS`,
  `realGameNCRO_iff`), so the reductions run them at a cost of `2·(624 + 312) + 624 = 2496` `H₅`
  and `2·(4607 + 4607) + 4607 = 23035` cipher reads; the right hop's collision term `deltaNC ≤
  noHitProb + 2⁻¹⁰²⁴` (`deltaNC_le`; the redemption statements do not depend on the tables:
  `tokW`, `okW`, `tokDNC_eq_tokW`).
- The issuance slices the guess sees made independent (`sim_fresh_NC`, `2·q₃·2⁻¹²⁸`; an issuance
  proof reads its slice only at its randomness, `realRO_h3_val`).
- Steps 3–4 as in `Privacy/MoussakaNC.lean` (`fresh_hyb_NC`: `φ₀ + φ₁`; `hybFresh_eq`; one Anchor:
  `simFresh_eq_one`).
- **`anonymityNCRO_lean_num`**:

      |Pr[W₀] − Pr[W₁]| ≤ 4·εRO(q₃, q₅ + 2496, q_E + 23035) + 2·(noHitProb + 2⁻¹⁰²⁴)
                          + 2·(φ₀ + φ₁) + 4·q₃·2⁻¹²⁸,

  about `2⁻¹⁰³·²` plus `4·(2q₃ + q₅ + 221·q_E)·2⁻¹²⁸` and the abort term;
  `anonymityNCRO_lean_num_perm` (AES as uniformly random permutations, `εROPm`);
  `anonymityNCRO_vinegarRO` (abort term `2·(δ₀^{256} + δ₁^{256})` averaged over the vinegar
  tables); **`unlinkabilityNCRO_lean_num`**, `_perm`: one Anchor, any index rule, without the
  abort term; the generic `anonymityNCRO`, `unlinkabilityNCRO` for any proof systems with read
  budgets. `#print axioms`: `propext`, `Classical.choice`, `Quot.sound`.
- **With one shared `H₃`** (`lean/VoleMole/Privacy/MoussakaNCSh.lean`, zk.md §10.7): the issuance
  and redemption proofs read `H₃` at their prefixes off the shared tables (`realGameNCSh`), the
  guess reads `H₃` through the rows. For an issuance prover that ignores its slot slice the slice
  hop is an exact relabelling (`pr_slice_free`, `sim_fresh_NC_free`; `anonymityNCRO_free`), and
  the redemption hops use `ZeroKnowledgeRO.shared` at the row budget (`q_E + 23038`: each shared
  proof reads its row `ρ` too). **`anonymityNCSh_num`**:

      |Pr[W₀] − Pr[W₁]| ≤ 4·εRO(q_E + 23038, q₅ + 2496, q_E + 23038) + 2·(noHitProb + 2⁻¹⁰²⁴)
                          + 2·(φ₀ + φ₁),

  about `2⁻¹⁰³·²` plus the budget terms and the abort term; `_perm`, `anonymityNCSh_vinegarRO`,
  `unlinkabilityNCSh_num` (`_perm`).
- **With the real Clients' seeds** (`lean/VoleMole/Privacy/SeedXOFNC.lean`, zk.md §10.6): each of
  `anonymityNCRO_lean_num`, `unlinkabilityNCRO_lean_num`, `anonymityNCSh_num`,
  `unlinkabilityNCSh_num` (and `_perm`) with `+ 2·(2q_X + 2)·2⁻²⁵⁶` (`*_seed`; given a bound
  `φ₀ + φ₁ ≤ φ` on the abort term at every XOF table, the hypothesis `hφ`). Theorem 4(b′) has no seed-XOF term either (D7); as for
  4(a), the hop is not free.
- **pqov's signer and completeness** (`lean/VoleMole/Spec/PqovSigner.lean`,
  `lean/VoleMole/Privacy/MoussakaPqov.lean`, `lean/VoleMole/Privacy/PqovDelta.lean`,
  `lean/VoleMole/Arith/GF256Field.lean`). The theorems above take the signers abstract
  (`Signer.Correct` only, which the always-failing signer meets with `φ = 1`) and hold for any
  issuance verifier; these files make them concrete.
  - *The signer.* `Spec.Pqov.signer pk O vin tries` models `ov_preimage_core` over `GF256` (a
    `Field` instance from the embedding into GF(2¹²⁸)): attempt `ctr` solves
    `L_v x = t − P(x₀)`, `x₀ = (v, 0)`, `L_v[k][j] = B(x₀, ō_j)_k` with `B` the polar form of the
    public map and `ō_j = (O_j, e_j)` (pqov's `vᵀS_k`, `t + P₁(v)` by the UOV identities; the
    byte-level routines are not modelled), and returns `x₀ + Σ_j x_j ō_j`. `signer_correct`: correct
    for every key whose map vanishes on the oil space (`OilSpace`). `signer_fail`: it fails only
    if every attempt `ctr < tries` has `det L_v = 0`. pqov uses `tries = 255`
    (`ov.c:166`, §6 step 5); `deriveRef` uses pqov's vinegar derivation `vinShake`.
  - *In the games.* `pqovRO` reads the vinegars from the vinegar tables. With 256 attempts it
    satisfies `hfail` as stated (`pqovRO256_hfail`), so `anonymityNC_vinegarRO` applies to it; with
    pqov's 255, `pr_fail_vinegar_lt` gives `E[φ_c] ≤ δ_c^{255}` and `anonymityNC_pqov`,
    `anonymityNCRO_pqov`, `anonymityNCSh_pqov` the abort term `2·(δ₀^{255} + δ₁^{255})`.
  - *`δ`* (`delta pk O`, the fraction of vinegars with `det L_v = 0`). `L_v = Σ_i v_i S_i`
    (`sysMat_eq_sum`) is linear in `v`, so a fixed key bounds nothing (`delta_zero_key`: `δ = 1`).
    Over uniform coefficients `S`: `pr_singular_avg`, `E[δ] ≤ 1/255 + 256^{−74}` (`pr_det_zero`:
    `σ = 1 − |GL₄₅(𝔽₂₅₆)|/256^{2025} ≤ 1/255`; `pr_comp_addHom`: `S ↦ L_v` is a surjective
    additive map for `v ≠ 0`); `pr_singular_all`, `pr_dependent_le`: `E[δ^m] ≤ σ^m +
    256^m/(255·256^{74})` for `m ≤ 74`. For the keys `keyO0 P1 P2` (pqov's key generation with
    `O = 0`: `P3 = 0`; `oilSpace_keyO0`; `sysCoef_keyO0`: `S` is the `P2` part) with `P2` uniform:
    `avg_delta_keyO0`, `avg_delta255_keyO0` (`E[δ^{255}] ≤ 255^{−37} + 1/(255·256^{37})`), and
    averaged over the Anchors' keys `anonymityNC_pqov_keys`, `anonymityNCRO_pqov_keys`: abort term
    `≤ 4·(255^{−37} + 1/(255·256^{37})) ≈ 2^{−293.8}`. For real keys (`O` uniform, `P3` computed)
    `S = (P1 + P1ᵀ)O + P2` is uniform by the same argument; that is not mechanized.
  - *The request length (finding).* `Spec.Moussaka.issueResponse` checks `main`'s length
    `45 + 7272`; the Lean prover of the random-oracle games emits label-row proofs of `7528` bytes
    (`leanPI_length`), so with it every honest request was malformed (`issueResponse_leanPI_malformed`)
    and the random-oracle games of Theorem 4(b′) always refused: their bounds held vacuously. The
    games now use `Spec.Moussaka.issueResponseLR` (`lean/VoleMole/Spec/MoussakaLabelRows.lean`,
    `45 + 7528`).
  - *Completeness.* `leanI_complete`: the Lean issuance proof has the label-row length and passes
    `leanVI` on the shared tables except with probability `≤ 2⁻¹¹³` (`complete_rom`; the verifier
    reads no `H₃`); `accNC_lean_complete`, `accNC_leanSh_complete` (one shared `H₃`): each honest
    Anchor rejects its Client's request with probability `≤ 2⁻¹¹³`. `pr_refused_le`,
    `pr_refused_NCRO_le`, `pr_refused_NCSh_le`: with both issuers' keys found at the Clients'
    indices in both sets, the redemptions are refused with probability `≤ φ₀ + φ₁ + 2·2⁻¹¹³`;
    `pr_refused_NCRO_pqov`: `≤ δ₀^{255} + δ₁^{255} + 2·2⁻¹¹³` with pqov's signers. `#print axioms`:
    `propext`, `Classical.choice`, `Quot.sound`.
- **With many Clients** (`lean/VoleMole/Privacy/MoussakaMany.lean`, `ZK/ReadsMany.lean`, zk.md
  §10.8): the adversary also serves `m` further honest Clients on the same tables (their issuance
  requests seen with the challenge requests, their redemptions at Anchor Sets chosen after them);
  for each tape of the further Clients the game is `realGameRA` of the adversary that runs them
  (`AdversaryN.withClients`), whose interaction reads their issuance proofs consistently
  (`realRO_sreads`: `H₅`, the cipher and `H₂³` at the `2³²` grinding points of each prefix).
  **`anonymityN_lean_num`**: `anonymityRA_lean_num` at `i₂ = 2³²m`, `i₅ = 624m`, `i_E = 4607m`
  and the guess's budget `(q₃, q₅ + 2·624m, q_E + 2·4607m)`; in numbers `≤ n·2⁻¹⁰² +
  8·(q₃ + q₅ + 221·q_E)·2⁻¹²⁸ + 2·εhide` (`anonymityN_lean_le`; `2⁻⁸²` at `n = 2²⁰`, `2⁻⁷⁰` at
  `2³²`: `anonymityN_lean_2pow20`, `_2pow32`); `anonymityN_lean_num_perm`.
- **With a key stage that reads the tables** (`lean/VoleMole/Privacy/MoussakaRAK.lean`, zk.md
  §10.3): `AdversaryRAK`, the contexts and the challenge Clients' keys fixed by a setup that reads
  the slices and the shared tables (consistently, `KBudget k₃ k₂ k₅ k_E`), the rest the
  table-reading adversary at that state. The issuance statements are adaptive, so the issuance hops
  are `hop_roA` with `ZeroKnowledgeROA` (`hop0RAK`, `hop1RAK`, `leanPI_zkROA`; `deltaI1K_le`:
  still `noHitProb + 2⁻¹⁰²⁴`), the redemption hops read through the setup (`sReads_SxLK`,
  `sReads_SxRK`; `deltaLAK_le`, `deltaRAK_le`). **`anonymityRAK_lean_num`**: `4·εAd(9; i₃ + q₃,
  q₅ + i₅ + 1872, q_E + i_E + 13821; k₃, k₂, k₅, k_E) + 4·εAd(9; q₃, q₅ + 1248, q_E + 13821;
  k₃ + i₃, k₂ + i₂, k₅ + i₅ + 624, k_E + i_E + 9214) + 4·((k₃ + i₃)·2⁻¹²⁸ + 2⁻¹¹³ +
  εROP(0, 312, 4607; k₅ + i₅ + 624, k_E + i_E + 9214)) + 6·noHitProb + 12·2⁻¹⁰²⁴ + 2·εhide`;
  `_numG`, `_perm`.
- **With an adaptive schedule** (`lean/VoleMole/Privacy/MoussakaAdaptive.lean`, zk.md §10.8;
  `AdversaryAdM`, `realGameAdM`): `m₁` further sessions before the challenge, `m₂` between the
  challenge issuance requests and the answers to the challenge Clients, `m₃` after the outcome, one
  after the other, each one's contexts, key, response, Anchor Set and digest chosen from all earlier
  requests and outcomes, the challenge contexts and keys from the first `m₁`. A whole session is a
  consistent table reader (`redX_sreads`, `fullXM_sreads`, `runSeqM_sreads`), and for each tape the
  game is `realGameRAK` of the adversary that runs the sessions (`realGameAdM_iff`).
  **`anonymityAd_lean_num`**; in numbers `≤ n·2⁻¹⁰² + 8·(q₃ + q₅ + 221·q_E)·2⁻¹²⁸ + 2·εhide`
  (`anonymityAd_lean_le`; `2⁻⁸²` at `n = 2²⁰`, `2⁻⁷⁰` at `2³²`: `anonymityAd_lean_2pow20`,
  `_2pow32`); `anonymityAd_lean_num_perm`.
- **With an interleaved schedule** (`lean/VoleMole/Privacy/MoussakaInterleave.lean`,
  `ZK/ReadsInterleave.lean`, zk.md §10.8; `AdversaryILM`, `realGameILM`): the adversary is an
  interactive machine that, step by step, starts a new honest Client with contexts and a key of its
  choice or delivers its answer (response, Anchor Set, digest) to any pending Client, seeing every
  issuance and redemption request; it may keep many Clients pending across the challenge. A Client
  is a chain of two consistent readers (`ChainCons`: `issX_req_sreads`, then `redX_sreads`), and by
  the interleaving lemma (`Good.run`, `Good.sreads`) each stretch of the schedule reads at most `n`
  Clients' keys. For each tape the game is `realGameRAK` of the adversary that runs the schedule
  (`realGameILM_iff`), with key-stage and interaction budgets `(0, 2·2³²n, 1248n, 9214n)`.
  **`anonymityIL_lean_num`**; in numbers `≤ (n + 2)·2⁻¹⁰¹ + 8·(q₃ + q₅ + 221·q_E)·2⁻¹²⁸ + 2·εhide`
  for `n` further Clients (`anonymityIL_lean_le`; `2⁻⁸¹` at `n + 2 = 2²⁰`, `2⁻⁶⁹` at `2³²`;
  `_2pow20`, `_2pow32`), `anonymityIL_lean_num_perm`: twice the sequential bound, a pending Client
  being charged in the key stage and again in the interaction.
- **With a scheduler that reads the tables and places the challenge**
  (`lean/VoleMole/Privacy/MoussakaInterleaveOC.lean`, `ZK/ReadsInterleaveOC.lean`, zk.md §10.8;
  `AdversaryILMO`, `realGameILMO`): each step of the schedule is a VCVio oracle computation over
  the four challenge slices and the shared tables within a per-step query bound (`SBudget`), the
  challenge starts when `go` holds and its answers are taken when `done` holds. By the interleaving
  lemma with the scheduler's query logs in the union (`GoodO.run`, `GoodO.sreads`), key stage
  `(L₁a₃, 2·2³²n + L₁a₂, 1248n + L₁a₅, 9214n + L₁a_E)`, interaction the same with `L₂`.
  **`anonymityILO_lean_num`**; in numbers `≤ (n + 2)·2⁻¹⁰¹ + 8·(q₃ + q₅ + 221·q_E)·2⁻¹²⁸ +
  28·L·(a₃ + a₂ + a₅ + 221·a_E)·2⁻¹²⁸ + 2·εhide` (`anonymityILO_lean_le`, `_2pow20`, `_2pow32`),
  `anonymityILO_lean_num_perm`; the earlier game is the special case (`realGameILMO_toO`).
- **With `N` challenge pairs** (`Privacy/MoussakaMany.lean`, zk.md §10.8; `AdversaryP`,
  `realGameP`, worlds `Fin N → Bool`): the adversary answers every Client and chooses every pair's
  two sides after every issuance request; side `s` of pair `j` redeems Client `w j ^^ s`'s token
  under §6's rule per pair (`outAt`). A hybrid over the pairs (`abs_sub_le_mul_of_worlds`), each
  step `anonymityN` with the other pairs' Clients as further Clients (`AdversaryP.hop`, the tape
  split `splitM`, `realGameP_iff`; the hop's guess rebuilds the other pairs' outcomes from their
  Clients' redemptions with §6's rule on the commitments, `outAt_eq`). **`anonymityP_lean_num`**
  `≤ N·εPairM`; in numbers `≤ N·(2N·2⁻¹⁰² + 8·(q₃ + q₅ + 221·q_E)·2⁻¹²⁸ + 2·εhide)`
  (`anonymityP_lean_le`; `2⁻⁶³` for `2N ≤ 2²⁰` Clients, `2⁻³⁹` for `2N ≤ 2³²`:
  `anonymityP_lean_2pow20`, `_2pow32`); `anonymityP_lean_num_perm`. Quadratic in the number of
  Clients by an artifact of the tree-hiding hop (zk.md §10.8, "Is the quadratic term inherent?").
