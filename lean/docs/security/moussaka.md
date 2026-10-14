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
| Issuer hiding and unlinkability vs a Moderator **colluding with all Anchors**, with adversarial keys (Thm 4a) | **Yes, computationally** | `2·ε_ZK^joint + 2·Adv^hide_Com + 2^{−192}` | ZK (lean/docs/zk.md), hiding of `Com` |
| The same vs a Moderator that sees no issuance (Thm 4b) | **Yes**, with no Keccak assumption | `2·Σ ε_ZK^red` with `Pred = 2^{−128}` | ZK only |
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
| D7 | `nf`, `r` sampled directly | Derived with `ρ_iss` from one OS seed through SHAKE128 (`moussaka.cpp:58-71`) | None in the ROM. This needs the application-hash vs proof-hash disjointness (Lemma DS, §3.1) |
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
- **Lemma DS** (cited, being proved in `lean/docs/security/domain-separation.md`). The DST-prefixed
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
  - Q2 is stated for one proof. Simultaneous extraction from the `Q_iss + Q_red` outputs needs a
    hybrid over the extraction measurements (one commutator term per output). This is plausible,
    but **not proved**.
  - QROM SE is **not covered** (README), so Theorem 3 has no quantum version.
  - `Com` generic quantum bounds:
    - binding `≲ q³/2^{360}` (BHT) `+ q²/2^{224}` (Grover on the inverse, `2^{112}` work);
    - one-wayness and hiding in `r`: `≲ q²/2^{128}`, a `2^{64}` Grover search.
  - Lemma U needs programming a quantum random *permutation* with inverse access. There is no
    general tool for this, so the link from CT-UF to one-more-UOV is heuristic. Quantum CT-UF is a
    standalone assumption.

**Privacy against a CRQC:**
- ZK against quantum distinguishers (QROM programming of H₂³ and H₅) is **open**. `lean/docs/zk-qrom.md` is
  absent at the time of writing.
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

| | `main` | fix (`CRT_DEDICATED_LABEL_ROWS`, worktree `agent-a62889915cc70016f`; proofs grow to 7528 / 9007 bytes) |
|---|---|---|
| ZK notion | (PU)-ZK: `Pred_R` = predicting `r` | Standard adaptive NIZK |
| `ε_lab` per proof | `(Q₅ + n_mult·Q_V)·Pred + Q_P·2^{−128}` | `(Q₅ + n_mult·Q_V + Q_P)·2^{−128}` |
| Thm 4(a), colluding | needs `Adv^ow-r` inside ZK *and* `Adv^hide`. The formal bound is vacuous at `q ≈ 2^{64}` | needs only `Adv^hide` (`≈ 2^{−63}` generic) |
| Thm 4(b), non-colluding | `Pred = 2^{−128}`, no Keccak assumption | same, with a cleaner bound |
| Joint hop over proofs sharing `r` | needed (§6) | not needed: the hops are independent |
| Thms 1 and 3 | unchanged (ZK enters Thm 3 only through `ε_hop`) | unchanged |
| Quantum privacy | AES-128 Grover cap (§8) | same cap |

---

## 11. Open gaps

1. Lemma DS (application vs proof-system hash disjointness) is assumed and cited. Its proof is in
   progress (`lean/docs/security/domain-separation.md`).
2. CT-UF → plain UOV problem: the signing simulation with retry (§3.3) is not re-derived. The
   theorems rest on CT-UF, or on one-more-UOV via the heuristic Lemma U, as the draft does.
3. `Com`'s binding, one-wayness and hiding are assumptions about 12-round Keccak-p[800]. Only
   generic estimates are given.
4. QROM: multi-output extraction, SE (and so Thm 3), and ZK (`lean/docs/zk-qrom.md` absent) are open.
   `ε_multi` caps Q2 at about `2^{40}` cipher queries.
5. Whether lean/docs/zk.md's `Pred` product can be made additive on `main`. It is moot with the fix.
6. Timing side channels beyond the index check (OS RNG, allocation) are out of scope.

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
