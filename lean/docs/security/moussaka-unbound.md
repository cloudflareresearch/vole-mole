# Unbound Moussaka: security analysis of late redemption-context binding

This note analyses the "unbound token" variant of Moussaka added by PR #63 (merged as `62be5bc`, "moussaka: Add
support for late redemption context binding"): `include/vole_mole/ihat.hpp`
(`UnboundToken`, `PendingUnboundToken`, `unbound_issue_request`, `unbound_issue_response`,
`unbound_finalize_redeem`), `src/ihat/commit.hpp` (`UnboundCom`, `Derive`),
`src/ihat/unbound_issue.hpp`, `src/ihat/unbound_redeem.hpp`, the shared circuit pieces in
`src/ihat/circuit.hpp`, and `src/ihat/ihat.cpp`. It builds on
`lean/docs/security/moussaka.md` (the "base note"), whose model, proof-system results and UOV
assumptions it reuses; only what differs is spelled out. Theorem numbers here carry a `U`.

Like the rest of `lean/`, this note was written with heavy assistance from a language model and
has not been reviewed. The [Lean] results are listed in Appendix B.

Contents:
- §0 Verdict
- §1 The protocol as implemented
- §2 Relations and arithmetization
- §3 Model and assumptions
- §4 Unforgeability per redemption context
- §5 Nullifiers, squatting, context binding, non-malleability
- §6 Anonymity: issuer hiding, issuance–redemption and cross-context unlinkability
- §7 Sharing Anchor keys between the two variants
- §8 Quantum adversaries
- §9 Findings
- §10 Open gaps
- Appendix B: Lean

---

## 0. Verdict

| Property | Holds? | Bound (classical) | Assumptions |
|---|---|---|---|
| One-more unforgeability **per `(ctx_iss, ctx_red)`** (Thm U1): for each pair, accepted distinct nullifiers ≤ unbound issuances for `ctx_iss` | **Yes** ([Lean], ROM and ideal cipher, down to OMPR under `hmodel`; §4 Status) | `ε_ext^{u-iss} + ε_ext^{u-red} + ε_ext^{iss} + ε_dig + Adv^bind_{Com∪UCom} + K·Adv^ct-uf-open` | PoK of the two unbound relations (and of the bound issuance relation, if the Anchor also runs it), joint binding of `Com` and `UCom`, CT-UF^open of UOV |
| Determinism of the nullifier: each signed commitment and `ctx_red` determine one `nf` (Cor U2) | **Yes** | as Thm U1 | as Thm U1 |
| No nullifier squatting (Prop U3; base note's F2 does not apply) | **Yes** | `U·(Adv^prf-t + Adv^spr-k)` on top of Thm U1 | PRF of `Derive` with `t` leaked, second preimages of `Derive` in the key |
| Redemption non-malleability, including no redirect to another `ctx_red` (Thm U4) | **Yes** | `ε_SE^{u-red} + ε_dig + Adv^bind + K·Adv^ct-uf-open + U·Adv^ow-kr + ε_hop` | weak SE, the above, one-wayness of `(nf_key, r)` |
| Issuer hiding and unlinkability vs Moderators **colluding with all Anchors**, issuance–redemption **and redemption–redemption across contexts** (Thm U5a) | **Yes, computationally** | `2·ε_ZK^joint + 2·Adv^prf-t_2` | ZK of both unbound relations, PRF of `Derive` with `t` leaked (2 keys) |
| The same vs Moderators that see no issuance (Thm U5b) | **Yes, computationally** (unlike the base note's 4(b)) | `2·ε_ZK^joint|_red + 2·Adv^prf_2 + 2·(ψ₀ + ψ₁)`, `ψ_c ≤ κ + φ_c` (corrected, §6) | ZK of the redemption proofs, PRF of `Derive` (2 keys), Anchor Sets that contain both issuers; `κ = 0` for a complete issuance proof |
| Unlinkability of two redemptions of one token **in the same `ctx_red`** | **No, by design** (same `nf`; rejected as a double spend) | — | — |
| Bound and unbound tokens under the same Anchor keys (§7) | **Yes**: neither variant can be redeemed as the other, and each keeps its own count | as Thm U1 and base Thm 1 | joint binding |

Main findings (§9):
- **UF1 (improvement).** Nullifier squatting (base F2) is no longer possible: the nullifier is a
  one-way function of a committed key, not a value the Client picks.
- **UF2.** Privacy against Moderators that see no issuance is now computational (a PRF assumption
  on Keccak-p[800,12]); the base note's 4(b) needed no Keccak assumption.
- **UF3 (deployment, carried over).** Base F1 applies unchanged: if an Anchor key is also a PomFRIT
  Issuer key, anyone can mint unbound tokens too.
- **UF4 (API).** `UnboundToken::redeem_request` is `const` and keeps no record. A Client that
  redeems the same token twice in one `ctx_red` produces two requests with the same `nf`: the
  second is rejected and links the two attempts. The header documents the rule; nothing enforces it.
- **UF5 (hygiene).** The unbound DSTs differ from the bound ones only in the version byte
  (`UNBOUND_VERSION = 1` against `moussaka::VERSION = 0`). `dsts_are_distinct` catches a clash at
  compile time, so this is not a bug, but bumping `moussaka::VERSION` to 1 will force a rename.
- **UF6 (cost, informational).** One opening `r` now enters `1 + N` proofs (issuance and every
  redemption). On `main` (CRT masks from the witness) the label term of the joint ZK hop is still
  per `H₅` query, not per proof, but every other per-proof term is summed over the `1 + N` proofs.
- **UF7 (proof correction).** The earlier proof of Thm U5(b) kept the Anchors' acceptance bits
  in the refusal bit through the PRF hop. The PRF reduction cannot compute them without the keys.
  The corrected abort term `ψ_c` also counts a rejected honest issuance proof (§6).

No attack was found on the unbound relations or their implementation.

---

## 1. The protocol as implemented

**Parameters** (in addition to the base note's): `NF_KEY_BYTES = 16` (`commit.hpp:53`),
`UNBOUND_ISSUE_PROOF_BYTES = 6864`, `UNBOUND_REDEEM_PROOF_BYTES = 12423` (`ihat.hpp`), both
with the FAEST-EM-128f v3 parameters and the CRT masks taken from the witness
(`REUSE_CRT_WITNESS = true`, `unbound_issue.hpp`, `unbound_redeem.hpp`; `circuit.hpp`
`is_em128f_variant`).

**Commitment** `UCom(k, ctx_iss, r) = KP800(state)[0..45)` (`ihat.cpp:326-332`), with the
100-byte state (`commit.hpp:62-81`)

```
"mous" ‖ 0x01 ‖ "c0" ‖ r (16) ‖ 0⁹ ‖ ctx_iss (16) ‖ k (16) ‖ 0³⁶       offsets 0, 7, 23, 32, 48, 64
```

**Nullifier derivation** `Derive(k, ctx_red) = KP800(state)[0..24)` (`ihat.cpp:334-340`), with
(`commit.hpp:83-98`)

```
"mous" ‖ 0x01 ‖ "d0" ‖ k (16) ‖ 0⁹ ‖ ctx_red (16) ‖ 0⁵²                 offsets 0, 7, 23, 32, 48
```

For comparison, the bound commitment is `"mous" ‖ 0x00 ‖ "c0" ‖ r ‖ 0⁹ ‖ ctx_iss ‖ ctx_red ‖ nf ‖ 0¹²`.
The three Keccak inputs differ in byte 4 or byte 5, so their input sets are disjoint
([Lean] `Arith/MoussakaUnbound.lean`, `encodeUnboundComState_ne_encodeComState`,
`encodeDeriveState_ne_encodeUnboundComState`, `encodeDeriveState_ne_encodeComState`).

**Issuance** (Client `unbound_issue_request`, `ihat.cpp:353-367`; Anchor
`unbound_issue_response`, `:369-380`; Client `PendingUnboundToken::finalize_issue`, `:393-406`).
1. `(k, r, ρ) = SHAKE128("mous\x01s0" ‖ seed)` squeezed into 16 + 16 + 16 bytes, `seed` 32 bytes
   from the OS (`expand_unbound_issue_seed`, `:85-100`).
2. `t = UCom(k, ctx_iss, r)`; request `t ‖ π_iss`, where `π_iss` proves knowledge of `(k, r)` with
   `t = UCom(k, ctx_iss, r)` for the public `(t, ctx_iss)`.
3. The Anchor verifies `π_iss` and returns `s = DerivePreimage(sk, t)`, exactly as for bound tokens.
4. The Client checks `P(s) = t` and keeps `(k, r, s)`.

**Redemption** (`UnboundToken::redeem_request`, `:408-435`; Moderator `unbound_finalize_redeem`).
1. The Client finds its Anchor's index in the Anchor Set `S` in constant time (`find_issuer`,
   `:120-139`, shared with bound tokens); it throws if none matches.
2. `nf = Derive(k, ctx_red)`; `ρ_red = SHAKE128("mous\x01s1" ‖ seed')`.
3. Request `nf ‖ π_red`, where `π_red` proves knowledge of `(r, k, s, b)` with `b` one-hot below
   `|S|`, `Σ_u b_u·P_u(s) = UCom(k, ctx_iss, r)` and `nf = Derive(k, ctx_red)`, for the public
   `(S, nf, ctx_iss, ctx_red, challenge_digest)` (instance hashed as for bound tokens,
   `hash_redeem_instance`, `circuit.hpp`).
4. The token is **not** consumed (the method is `const`): it may be redeemed in any number of
   redemption contexts. The Moderator records `(ctx_iss, ctx_red, nf)` and rejects repeats, across
   every Anchor Set it accepts for these contexts (header comment of `unbound_finalize_redeem`).

**Domain separation of the SHAKE calls.** The unbound DSTs (`dst.hpp`) are the bound ones with
version byte 1. With them, every SHAKE128 domain of the library is still pairwise separated, apart
from the two PomFRIT exceptions of `domain-separation.md` ([Lean]
`Protocols/DomainSeparation.lean`, `clean_pairwise` over 28 domains; the unbound H₂¹, H₂², H₃
lengths `4261, 497, 281` (issuance) and `9493, 824, 608` (redemption) are checked against the C++
by `LeanModels.ProofHashLengthsMatchDomainTable`). In particular the base note's Lemma DS holds
for the unbound relations unchanged.

---

## 2. Relations and arithmetization

**Unbound issuance** (`unbound_issue.hpp`). Witness `r = [0,16)`, `k = [16,32)`, then the committed
Keccak states `s5, s9` of `UCom` (`232` bytes). Constraints: `8·232 = 1856` bit constraints, the
1600 segment constraints of `qs_keccak(…, 32, 360)`, and `out[i] + t_i` for the 360 output bits:
3816 constraints of degree ≤ 9. Relation: `t = UCom(k, ctx_iss, r)`.

**Unbound redemption** (`unbound_redeem.hpp`). Witness `r = [0,16)`, `k = [16,32)`, `s = [32,151)`,
the states of `UCom` at 151, those of `Derive` at 351, the selector at byte 551 (`559` bytes).
Constraints, in order: `8·551 = 4408` bit constraints; the 128 selector constraints
(`qs_add_selector_constraints`, shared with bound redemption); the 1600 segment constraints of
`UCom` and the 1600 of `Derive`; `out_D[i] + nf_i` for the 192 bits of `nf`; and the combined
signature constraint `l(Q(s)) = l(out_C[0..45))`, with `l` from `chal₂` and
`"mous\x01l0"`: 7929 constraints of degree ≤ 9. Relation: `b = e_{u₀}` with `u₀ < |S|`,
`P_{S[u₀]}(s) = UCom(k, ctx_iss, r)` in all 45 components, and `nf = Derive(k, ctx_red)`.

The witness byte `k` feeds both Keccak instances through the two input maps
(`UNBOUND_REDEEM_COM_TO_WIT`, `UNBOUND_REDEEM_DERIVE_TO_WIT`), which is what ties the nullifier to
the signed commitment. [Lean] `Arith/MoussakaUnbound.lean` models both constraint generators and
proves completeness and soundness against these relations (`uIssue_complete`,
`uIssue_sound`, `uRedeem_complete`, `uRedeem_sound`, `uRedeem_sound_card`),
following `Arith/Moussaka.lean`.

Soundness of the arithmetization is the only new ingredient of extraction: the extraction theorem
of `lean/docs/extraction/README.md` is generic in the constraint system, needing the degree bound
(9), bit constraints on every witness bit (or `b_u = 0` for the unused selector bits), and, for
redemption, a combined slot whose failure probability over `l` is `≤ 1/|F|`
(`uRedeem_sound_card`). So `ε_ext^{u-iss}` and `ε_ext^{u-red}` are the base note's
`ε_ext` formulas with the new constraint counts. [Lean] `EndToEnd/MoussakaUnbound.lean` proves the
degree bound (`moussaka_unbound_issue_deg`, `moussaka_unbound_redeem_deg`) and the deterministic
end-to-end theorems `moussaka_unbound_issue_extract` and `moussaka_unbound_redeem_extract`, in the
form of `EndToEnd/Relations.lean`: some known tree's candidate is a bit vector whose decoding
satisfies the unbound relation, or at most 9 admissible `chall₃` are accepted;
`moussaka_unbound_redeem_comb_bad` discharges the combination hypothesis except with probability
`1/|F|` (`moussaka_unbound_redeem_comb_bad_gf128` at GF(2¹²⁸)).

[Lean] The executable verifier and prover cover both unbound relations
(`Verifier/Relations.lean`: `moussakaUnboundIssue`, `moussakaUnboundRedeem`; DSTs with version
byte 1, the bound `hash_redeem_instance` for redemption, Moussaka's proof layout since both set
`REUSE_CRT_WITNESS`). `lake exe verifier_vectors` accepts all 9 proofs of
`tests/ihat/unbound_ihat_kat.txt` (3 issuances, 6 redemptions in two contexts each, up to 64
Anchors), rejects 25 mutations (a flipped byte in each proof field; a changed `t`, `ctx_iss`, `nf`,
`challenge_digest`, the token's other `ctx_red`; the issuance proof as a bound issuance), and
compares the intermediate values of one proof per relation with the C++ (`verifier_kat.txt`).
`lake exe prover_vectors` reproduces all 9 proofs byte for byte and checks the witnesses and `t`,
`nf` against `Spec/MoussakaUnbound.lean`. The bridge theorems carry over: the verifier's
evaluators are the systems' values (`moussakaUnboundIssue_values`,
`moussakaUnboundRedeem_values`), so acceptance gives the accepting equation
(`moussakaUnboundIssue_accept`, `moussakaUnboundRedeem_accept`), the executable verifier's chains
give the extraction theorems above at GF(2¹²⁸) (`moussakaUnbound*_extract_chain`), with uniform
challenges at probability `≤ 2⁻¹⁵⁰ + ε_QS(n) [+ 2⁻¹²⁸]` per chain (`n = 3816`, `7929`;
`Prob.moussakaUnbound*_chain_prob`), and the prover is complete
(`moussakaUnbound*_complete_shake`).

[Lean] The probabilistic steps of extraction are mechanized as for the base relations
(`lean/docs/probabilistic-plan.md` §2j). They are stated once, for any verifier statement with the
C++ parameters (232 and 559 witness bytes, `QS_DEGREE = 9`), DSTs, combination
`(45, "mous\x01l0")` and the `Arith/MoussakaUnbound.lean` systems as evaluator
(`Unbound.IssueStmt`, `Unbound.RedeemStmt`, `Prob/MoussakaUnbound.lean`), and the executable
verifier's statements have these properties (`Unbound.moussakaUnboundIssue_stmt`,
`Unbound.moussakaUnboundRedeem_stmt`), so every bound below is about `moussakaUnboundIssue` and
`moussakaUnboundRedeem`. In the joint random-oracle and ideal-cipher model (PRF view), for a
prover with `q_E` cipher queries and `q_k` hash queries of kind `k` (`n` in all), the executable
verifier accepts and the extractor's candidate is not a witness with probability at most

```
(q₂₁+1)·2⁻¹⁵⁰ + (q₂₂+1)·ε₂ + (q₂₃+1)·9·2⁻¹²⁸ + 2·q_E²·2⁻²⁵⁶
  + 2·(openHashEps q + q₁·2⁻²⁵⁶) + 1024·q_E·q₁·2⁻²⁵⁶ + chainHitEps q [+ comb hits],
ε₂ = ε_QS(3816) (issuance),   ε₂ = ε_QS(7929) + 2⁻¹²⁸ + (n+339)·2⁻⁴⁴⁸ (redemption, ≤ 64 Anchors),
```

the base relations' bound with the unbound constraint counts (`IC.moussakaUnboundIssue_accept_le_full`,
`IC.moussakaUnboundRedeem_accept_le_full`; with the binding, dead-leaf and chain terms as
hypotheses, `moussakaUnbound*_accept_le` and `IC.*_accept_le_ic`). The same holds with AES as
random permutations and inverse queries (`_perm`), for adaptively chosen statements with
`stmtBindEps q = (q₀+3)(q₂₁+q₀+4)·2⁻²⁵⁶` added (`_adaptive`, `_adaptive_perm`; `hinj` holds for
the executable statements when `t` has a fixed length, resp. the family is injective on
`(Anchor digests, nf, ctx_iss, ctx_red, challenge_digest)` with fixed lengths,
`hinj_moussakaUnboundIssue`, `hinj_moussakaUnboundRedeem`), and for the spec relations
`Spec.MoussakaUnbound.IssueRel`, `RedeemRel` (`_spec`; `|t| = 45`, `|nf| = 24`). Against one SHAKE
oracle the side condition is `combOk_moussakaUnbound*`.

---

## 3. Model and assumptions

### 3.1 Proof systems

As base §3.1, for the relations `u-iss` and `u-red`: straight-line simultaneous extraction with
errors `ε_ext^{u-iss}`, `ε_ext^{u-red}`; weak SE `ε_SE^{u-red}`; ZK as in `lean/docs/zk.md`.
Simultaneous extraction is in Lean at the spec relations (`ROM/MoussakaUnboundSim.lean`): per
relation (`moussakaUnboundIssue_sim_spec`, `moussakaUnboundRedeem_sim_spec`) and for both
together (`moussakaUnbound_sim_joint_spec`; the DSTs `mous1i0`, `mous1r0` separate the families).
For `m_I + m_R = m` proofs whose provers share one run, each query of the run is charged once:

    (q₂₁+m)·2⁻¹⁵⁰ + (q₂₂+m)·(ε_QS(7929) + 2⁻¹²⁸ + (n_G+339)·2⁻⁴⁴⁸) + (q₂₃+m)·9·2⁻¹²⁸
      + chainHitEpsCombSim q M m + stmtBindEpsSim q m + m·failEps q q_E,

about `2⁻⁶⁰·⁵` at `2⁶⁴` queries per kind and `2³⁰` proofs per relation (`m·failEps ≈ 2⁻⁸⁶·⁹`).
The bound issuance relation (`ε_ext^{iss}` in Thm U1) is a third family, charged by the base
note's bounds, not jointly with the unbound pair. The game of Thm U1 uses exactly these terms
(§4 Status, `omufU_le_num_sim`). With
the CRT masks taken from the witness (`main`), the label term of the ZK hop is
`(Q₅ + n_mult·Q_V)·Pred_R`, with `Pred_R` the probability of predicting the opening `r`, the first 16
witness bytes of both unbound relations. One `r` now enters `1 + N` proofs; each `H₅` query tests
one guess of `r` against one proof, so the label term of the joint hop is still
`(Q₅ + n_mult·Q_V)·Pred_R` (the union is over queries, not proofs), while the other terms of
`ε_ZK^joint` are summed over the proofs (UF6).

### 3.2 Keccak assumptions

`UCom`, `Derive` and the bound `Com` are evaluated inside the proofs, so, as in base §3.2, they are
not random oracles of the protocol proofs. Their properties are standard-model assumptions; the
random-permutation estimates (forward and inverse queries, `q` of them) are evidence only.

- **Joint binding.** `Adv^bind_{Com∪UCom}(A) = Pr[A → x ≠ x' ∈ D ∪ D_u : f(x) = f(x')]`, where `D`
  is `Com`'s input space (576 free bits), `D_u` is `UCom`'s (384 free bits), and `f` is
  `KP800(·)[0..45)` on either. The two input spaces are disjoint (byte 4), so this covers
  collisions inside one variant and **across** the variants.
  Generic: `≲ q²/2^{361} + q·(2^{576} + 2^{384})/2^{800} ≈ q²/2^{361} + q/2^{224}`.
- **PRF with the commitment leaked (`Adv^prf-t_n`, `n` keys).** `A` chooses `ctx_iss`. For uniform
  `k₁..k_n, r₁..r_n` it gets `t_i = UCom(k_i, ctx_iss, r_i)` and an oracle `O(i, c)`. In the real
  game `O(i, c) = Derive(k_i, c)`; in the ideal game `O(i, c) = F_i(c)` for independent uniform
  functions `F_i : {0,1}^{128} → {0,1}^{192}`. `Adv^prf-t_n` is the distinguishing advantage.
  `Adv^prf_n` is the same without the `t_i`. `Adv^prf-t_n ≤ n·Adv^prf-t_1` by a hybrid.
  Generic: a forward query is informative only if it contains some `k_i` (either a `Derive` input
  or a `UCom` input with the right `r_i`); an inverse query only if it hits one of the
  `Derive`/`UCom` outputs on the 608 (resp. 440) bits the adversary does not see. So
  `Adv^prf-t_n ≲ n·(q + 1)·2^{−128} + n·q·2^{−440}`.
- **Key recovery and one-wayness.** `Adv^ow-kr`: given `t = UCom(k, ctx_iss, r)` and the oracle
  `Derive(k, ·)`, output `(k, r)`. `Adv^ow-kr ≤ Adv^prf-t_1 + Adv^ow_{UCom}` (after the PRF hop the
  oracle is independent of `(k, r)`, and recovering `(k, r)` from `t` alone is one-wayness of
  `UCom` in its 256 secret bits). Generic `≲ (q + 1)·2^{−128}`.
- **Second preimages of `Derive` in the key (`Adv^spr-k`).** Given `(t, ctx_red,
  nf = Derive(k, ctx_red))` and the oracle `Derive(k, ·)`, output `k' ≠ k` with
  `Derive(k', ctx_red) = nf`. Generic `≲ q·2^{−192} + (q + 1)·2^{−128}` (a forward query on a fresh
  `k'` matches 192 bits with probability `2^{−192}`; an inverse query lands in the `Derive` input
  space with probability `≲ 2^{−544}`).

None of these is implied by the base note's assumptions: hiding of `Com` hides a uniform nullifier,
whereas here the nullifiers are PRF outputs whose key is also committed in `t`. The PRF assumption
replaces hiding: with `n = 2` it is the counterpart of base `Adv^hide_Com` in Thm U5.

### 3.3 UOV

As base §3.3, with CT-UF^open over the union domain `D ∪ D_u`: the adversary wins with
`(k, x*, s*)`, `x* ∈ D ∪ D_u`, `P_k(s*) = f(x*)`, `f(x*)` never signed, and must open every target
it had signed to an element of `D ∪ D_u`. The repaired Lemma U of `uov-assumptions.md` goes through
unchanged, since the reduction programs every forward query on the union domain.

---

## 4. Unforgeability per redemption context

**Game OMUF-U.**
- The challenger generates `K` honest Anchor keys. `A` gets the public keys and the oracles
  - `UIssue(k, req, ctx_iss)`: run `unbound_issue_response(sk_k, req, ctx_iss)`; on acceptance add
    `t = req[0..45)` to `L^u_{ctx_iss}`;
  - `Issue(k, req, ctx_iss, ·)`: the bound `issue_response`; on acceptance add `t` to
    `L^b_{ctx_iss}` (the Anchor may run both variants with one key, §7);
  - `URedeem(S, req, ctx_iss, ctx_red, cd)`, `S` made only of honest keys: run
    `unbound_finalize_redeem`; on acceptance with `nf` record `(ctx_iss, ctx_red, nf)` in one store
    `R`, shared across all `S`.
- `A` wins if for some `(ctx_iss*, ctx_red*)` the number of distinct `nf` recorded in `R` with that
  pair exceeds `|L^u_{ctx_iss*}|`.

**Theorem U1.** For every classical `A`,

```
Adv^omuf-u(A) ≤ ε_ext^{u-iss} + ε_ext^{u-red} + ε_ext^{iss} + ε_dig + Adv^bind_{Com∪UCom}(B₁)
              + K·Adv^ct-uf-open_{UOV,1}(B₂),
```

with `B₁, B₂` running `A` once and the extractor on every accepted proof at the end; `B₂` makes as
many signing queries as `A` makes accepted `Issue` and `UIssue` queries.

*Proof.*
1. **Simulation.** As base Thm 1: `B₂` answers both issuance oracles by verifying the proof
   (public) and calling `Sign_k(t)`; redemption is public verification.
2. **Extraction.** At the end, outside `ε_ext^{u-iss} + ε_ext^{u-red} + ε_ext^{iss} + ε_dig`:
   - each accepted `UIssue` `(t_q, ctx_q)` yields `(k_q, r_q)` with `UCom(k_q, ctx_q, r_q) = t_q`;
   - each accepted `Issue` `(t_q, ctx_q)` yields `x_q ∈ D` with `Com(x_q) = t_q` and `ctx_iss`
     field `ctx_q`;
   - each accepted `URedeem` `j` with `(S_j, nf_j, ctx_iss_j, ctx_red_j)` yields
     `(r_j, k_j, s_j, b_j)` with `b_j = e_{u_j}`, `u_j < |S_j|` ([Lean] `selector_one_hot`),
     `P_{S_j[u_j]}(s_j) = t_j := UCom(k_j, ctx_iss_j, r_j)` and `nf_j = Derive(k_j, ctx_red_j)`.
3. **Binding case.** If two distinct inputs among all extracted `UCom` and `Com` inputs have equal
   outputs, `B₁` outputs them.
4. **Otherwise.** Fix the winning `(ctx_iss*, ctx_red*)` and let `J` be one accepted redemption per
   distinct `nf` with that pair.
   - For `j ≠ j'` in `J`: `nf_j ≠ nf_{j'}` and `ctx_red_j = ctx_red_{j'}`, so `k_j ≠ k_{j'}`
     (`Derive` is a function), so the `UCom` inputs differ, so `t_j ≠ t_{j'}` (no collision). So
     `j ↦ t_j` is injective on `J` ([Lean] `Protocols/MoussakaUnbound.lean`,
     `t_injOn_of_derive`).
   - `|J| > |L^u_{ctx_iss*}|`, so some `t_j ∉ L^u_{ctx_iss*}` (`exists_unsigned_of_card_lt`;
     combined: `exists_unsigned_per_context`).
   - If `t_j ∈ L^u_{ctx'}` with `ctx' ≠ ctx_iss*`, the extracted `UCom` inputs of the issuance and
     of `j` differ in the `ctx_iss` field and collide: case 3. If `t_j ∈ L^b_{ctx'}` for any `ctx'`,
     a `Com` input and a `UCom` input collide: case 3 (this is where the joint, cross-variant
     binding is used). So `t_j` was never signed.
   - `B₂` outputs `(S_j[u_j], (k_j, ctx_iss*, r_j), s_j)`, a CT-UF^open forgery (the openings of
     the signed targets are the extracted issuance witnesses). ∎

**Remarks.**
- *What is counted.* A Client holding `n` unbound tokens for `ctx_iss` can redeem at most `n` times
  per `ctx_red`, and arbitrarily often across distinct `ctx_red`. This is the intended semantics of
  late binding. If the deployment needs a global limit, it must use bound tokens or a single
  `ctx_red`.
- *Bound tokens are not counted.* Thm U1 compares the unbound redemptions with **unbound**
  issuances only. Symmetrically, base Thm 1 holds with `L` the **bound** issuances only, when the
  Anchor also runs `unbound_issue_response` (add `ε_ext^{u-iss}` and replace `Adv^bind_Com` by the
  joint term): a bound redemption's extracted commitment is a `Com` image, and an unbound issuance's
  extracted opening is a `UCom` input. ([Lean] the counting step for both stores at once,
  `count_le_per_variant`.)
- *Several Anchors, one `t`.* As in the base note, submitting one `t` to several Anchors yields
  several preimages of one `t`, but by binding one key `k`, so one `nf` per `ctx_red`.
- *Issuance-proof extraction is now essential for the cross-variant step.* Without extraction of
  bound issuance proofs, a `t` signed through the bound path could not be excluded from unbound
  redemption by binding alone. Since both issuance paths verify their proofs before signing, this
  costs nothing in the implementation.

**Status: [Lean]** (`lean/VoleMole/ROM/MoussakaUnboundOMUF.lean`, `ROM/MoussakaUnboundOMUFSim.lean`,
`Assumptions/UnboundLinks.lean`). Game OMUF-U on the executable spec, in the random-oracle and
ideal-cipher model of `lean/VoleMole/ROM/`, built as the base note's Theorem 1 (`moussaka.md` §4
Status) with a second issuance oracle and the unbound Moderator.
- *The game.* `K` honest Anchors with any public keys and any signers; each runs both variants
  with one key. The adversary (`Adversary`) makes `qI` Issue queries one after the other, each
  bound (`OMUF.anchorIC`, `issue_response`) or unbound (`uanchorIC`, `ROM/MoussakaUnboundOMUF.lean:109`;
  per table it is `unbound_issue_response` with the executable verifier, `uanchorIC_eq_spec`), as
  it chooses, then outputs `qR` unbound redemptions for Anchor Sets of honest Anchors. The
  Moderator (`umoderatorIC`, `:137`) is `unbound_finalize_redeem` with the Lean verifier. An
  accepted proof of either variant signs `t`. `Win` (`:193`): for some `(ctx_iss, ctx_red)`, more
  distinct accepted `nf` than distinct `t` accepted through unbound issuance for `ctx_iss`. The
  request lengths are the verifier's proof sizes (`upfLenI_eq`, `upfLenR_eq`; `6864`, `12423` on
  `main`).
- *The reduction* (`omufU_le`). Per table, a win in which every accepted proof is extracted gives
  a collision among the extracted inputs of `Com ∪ UCom` or a forgery (`win_imp`; the
  deterministic steps 3–4 are `Protocols/MoussakaUnbound.lean`, `collision_or_forgery_unbound`).
  The inputs are `XOp = Opening ⊕ UOpening`, with `Com` or `UCom` as commitment (`comX`) and the
  union domain `WFX`. So

      Pr[Win] ≤ Σ_{j<qI} Pr[BadBI_j] + Σ_{j<qI} Pr[BadUI_j] + Σ_{j<qR} Pr[BadUR_j]
                + AdvBind(B₁) + AdvCTUF(B₂),

  three extraction families: bound issuance (`ε_ext^{iss}`), unbound issuance, unbound
  redemption. `AdvBind` is the probability that two distinct well-formed extracted inputs, in one
  variant or across the variants, have one commitment. `AdvCTUF` is the probability that an
  accepted redemption's extracted `UCom` input, with an honest key of its Anchor Set and a
  preimage, commits to a target no Anchor's signer was called on, through either variant.
- *With the soundness theorems* (`omufU_le_num`): `qI·ε_I + qI·ε_UI + qR·ε_UR + AdvBind +
  AdvCTUF`, at the game's budgets (the adversary's `qI + 2` stages plus the `qI + qR` honest
  verifications), under the base note's digest condition `hdig`, `hdinj` (`ε_dig` as a condition
  on the keys).
- *With simultaneous extraction* (`omufU_le_num_sim`). The unbound issuance and redemption proofs
  are charged jointly (`moussakaUnbound_sim_joint_spec`, `m = qI + qR`, `epsUsim`). The bound
  issuance proofs are a third family, charged by their own simultaneous bound
  (`moussakaIssue_sim_spec`, `OMUF.epsIsim`, `m = qI`), as §3.1 says:

      Pr[Win] ≤ ε_I^sim(q', q'_E, qI) + ε_U^sim(q', q'_E, n', qI, qR) + AdvBind(B₁) + AdvCTUF(B₂).

- *With CT-UF^open over `D ∪ D_u`* (`omufU_le_num_open`, `omufU_le_num_open_sim`). The last
  term is the advantage of an explicit forger (`ctufForgerU`) in the standalone CT-UF^open game of
  `Assumptions/UOV.lean` with commitment `comX` and domain `WFX`. Its openings are the extracted
  issuance inputs, a `Com` input for a bound target and a `UCom` input for an unbound one.
- *Down to OMPR* (`omufU_le_num_ompr`, `omufU_le_num_ompr_sim`). Under the project's modelling
  hypothesis `hmodel` (`Com ∪ UCom` ideal in the standalone CT-UF^open game only; as for
  `omuf_le_num_ompr`, not provable), the last term is at most
  `Σ_j (Adv^{ompr}_{key j}(B_j; q_f + 2q_S + 1, q_S) + (q_f + 2q_S + 1)·failPr_{key j})`.
- *Numbers.* At `q' = 2⁶⁴` queries per kind for the whole run (`q'_E = n' = 2⁶⁴`) and
  `qI = qR = 2³⁰`: per proof `ε_I ≈ ε_UI ≈ 2⁻⁶⁰·⁶⁸`, `ε_UR ≈ 2⁻⁶⁰·⁵⁴`, so the per-proof union
  `qI·ε_I + qI·ε_UI + qR·ε_UR ≈ 2⁻²⁹·⁰⁵`. Simultaneously, `ε_I^sim ≈ 2⁻⁶⁰·⁶⁸`,
  `ε_U^sim ≈ 2⁻⁶⁰·⁵⁴`, together `≈ 2⁻⁵⁹·⁶¹`, of which the per-proof failure terms are
  `≈ 2⁻⁸⁶·⁴`. The dominant terms are `(q₂₃ + m)·9·2⁻¹²⁸` and `(q₂₂ + m)·(ε_QS + 2⁻¹²⁸)`.
  Charging the bound issuance proofs separately costs a factor `≈ 1.9` against the base
  Theorem 1's `2⁻⁶⁰·⁵⁴`. To this add `AdvBind` (generic `≈ q²/2³⁶¹ + q/2²²⁴`, §3.2) and the
  OMPR terms.
- *Differences from the paper bound; corrections.* No step of the paper proof of Thm U1 was found
  wrong. The mechanized statement differs in four places:
  - Each Issue position is charged in **both** issuance families (`qI·ε_I + qI·ε_UI`, not
    `q_b·ε_I + q_u·ε_UI`): the adversary picks the variant adaptively, and the prover of the
    other variant at that position outputs a dummy statement. In the simultaneous bound this
    costs `m = qI` in place of `q_b` and `q_u` in the `+m` terms, which is negligible.
  - `ε_ext^{iss}` is not joint with the unbound pair: the run is charged twice (once per bound).
    A joint bound over three families would need a three-family `ROM/SimJoint.lean`.
  - `ε_dig` is a condition on the keys (`hdig`, `hdinj`), not a term. `AdvBind` is a collision of
    the input tuples. That these are distinct Keccak-p[800] states (the input spaces are disjoint
    and injective in their fields) is `Arith/MoussakaUnbound.lean`
    (`encodeUnboundComState_ne_encodeComState`, `encodeUnboundComState_inj`). The game does not
    restate it on states.
  - The factor `K` (`K·Adv^ct-uf-open_1`) is mechanized for the ideal-`Com` game only, as in the
    base note.

  The failure terms stay per proof, as in the base note.

---

## 5. Nullifiers, squatting, context binding, non-malleability

### 5.1 Nullifiers

**Corollary U2.** On the good event of Thm U1:
1. **Determinism.** Every accepted unbound redemption's `nf` equals `Derive(k, ctx_red)` for the key
   `k` committed in a commitment that an honest Anchor signed through `unbound_issue_response`
   (with `ctx_iss` checked). A signed `t` determines `k` by binding, so `(t, ctx_red)` determines
   `nf` ([Lean] `nf_determined`).
2. **Single use per context.** A Moderator that records `(ctx_iss, ctx_red, nf)` and rejects
   repeats accepts at most one redemption per signed `t` and `ctx_red`. The record must span every
   Anchor Set it accepts, as in base Cor 2.
3. **Honest uniqueness.** `U` honest tokens give pairwise distinct `nf` in one `ctx_red` except
   with probability `U²·2^{−193} + U²·2^{−257} + Adv^prf_U`: after the PRF hop the nullifiers are
   independent uniform 192-bit strings; the middle term is a seed collision.
4. **Derive does not include `ctx_iss`.** A Client may reuse one `k` in tokens for several issuance
   contexts; their nullifiers then coincide in every `ctx_red`. This only links that Client's own
   redemptions; since the Moderator keys its record by `(ctx_iss, ctx_red)`, the tokens remain
   separately spendable, and no other Client is affected. Honest Clients draw a fresh `k` per token.

### 5.2 No nullifier squatting

**Game SQUAT.** Honest Clients obtain unbound tokens (the adversary may play the Anchor and see
`t_h`) and redeem them on request, in contexts of the adversary's choice. The adversary wins if a
Moderator accepts a redemption `(S', nf_h, ctx_iss, ctx_red)` that is not an honest request, where
`nf_h` is the nullifier of an honest token `h` in `ctx_red` (revealed or not), and whose extracted
commitment `t'` differs from `t_h`. (`t' = t_h` is the non-malleability case, Thm U4.)

**Proposition U3.** `Pr[A wins SQUAT] ≤ ε_ext^{u-red} + Adv^bind + U·(Adv^prf-t_1 + Adv^spr-k) +
ε_hop`.

*Proof.* Extraction gives `k'` with `Derive(k', ctx_red) = nf_h` and `UCom(k', ctx_iss, r') = t' ≠
t_h`. If `k' = k_h` the adversary has computed `k_h`, which (after replacing the honest proofs by
simulated ones, `ε_hop`) is key recovery from `t_h` and `Derive(k_h, ·)`: at most
`Adv^prf-t_1 + 2^{−128}` (absorbed). Otherwise `k' ≠ k_h` is a second preimage of `nf_h` in the key
([Lean] `squat_cases`: equal nullifiers in one context and distinct keys are exactly a second
preimage). Guessing `h` costs the factor `U`. ∎

In the base protocol `nf` is a value the Client commits to, so anyone who learns an honest `nf` can
buy a token with that `nf` and burn the honest one (base F2). Here the nullifier is a one-way
function of a committed key, so learning `nf_h` does not let anyone else commit to it.

### 5.3 Context binding and redemption non-malleability

| Value | Bound at issuance | Checked at redemption | Guarantee |
|---|---|---|---|
| `ctx_iss` | public in `π_iss`'s instance and inside `t` | in the instance and in `UCom`'s input | a token for epoch `e` is not accepted under `e' ≠ e` (Thm U1, case 3) |
| `ctx_red` | **not at all** | in the instance and in `Derive`'s input | the nullifier is `Derive(k, ctx_red)` for the committed `k`: one per context (Cor U2) |
| `challenge_digest` | not committed | in the instance | non-malleability (Thm U4) |
| Anchor Set | — | digests and size in the instance; maps in the constraints | non-malleability, using `ε_dig` |

**Game NM-U (redirect).** `A` is every Moderator and may play any Anchor. Honest Clients obtain
unbound tokens and redeem them on request under statements `(S, ctx_red, cd)` of `A`'s choice. `A`
wins if `unbound_finalize_redeem` accepts a statement `(S', nf', ctx_iss, ctx_red', cd')` that
differs from every honest redemption statement and whose extracted commitment equals an honest
`t_h`. This covers redirecting an honest redemption to another digest, another Anchor Set, or
**another Moderator** (`ctx_red' ≠ ctx_red`, with the honest Client's nullifier there).

**Theorem U4.** For `U` honest tokens,

```
Pr[A wins NM-U] ≤ ε_SE^{u-red} + ε_dig + Adv^bind_{Com∪UCom} + K·Adv^ct-uf-open + U·Adv^ow-kr + ε_hop.
```

*Proof.* Replace the honest proofs by simulated ones (`ε_hop`; the statements contain
`nf = Derive(k_h, ctx_red)`, which the challenger computes). Weak SE extracts `(r', k', s', u')` with
`UCom(k', ctx_iss, r') = t_h` for the new statement; by binding `(k', r') = (k_h, r_h)`. In the
simulated world `(k_h, r_h)` enter `A`'s view only through `t_h` and the nullifiers
`Derive(k_h, ·)`, so outputting them is `Adv^ow-kr` (guess `h`: factor `U`). ∎

A malicious Moderator therefore cannot spend an honest Client's token at another Moderator, even
though the token is valid there.

---

## 6. Anonymity

**Game ANON-U^colluding.**
- `A` chooses `ctx_iss` and two Anchor public keys `pk⁰, pk¹` (arbitrary; equal for pure
  unlinkability).
- Honest Clients `C₀, C₁` each run `unbound_issue_request(ctx_iss)`; `A` receives both requests,
  plays the Anchor and returns `s⁰, s¹`. If either `finalize_issue` fails, the game ends with a
  random bit (both-or-neither, as in the base note).
- The challenger flips `b`.
- `A` makes any number of adaptive redemption queries `(i, w, S, ctx_red, cd)` with `i, w ∈ {0,1}`:
  the challenger redeems token `i ⊕ (b ∧ w)` under `(S, ctx_red, cd)` and returns the request. `w`
  is the *swap flag*: queries with `w = 0` are always answered by token `i`; queries with `w = 1`
  are answered by token `i` in world 0 and by token `1 − i` in world 1.
  - **Validity.** `S` must contain both `pk⁰` and `pk¹` at the indices the Clients take from `S`;
    otherwise the query is refused (for both tokens alike).
  - **Context rule (inherent).** All queries with the same `ctx_red` must carry the same swap flag.
    Two redemptions of one token in one context have equal nullifiers, so two queries
    `(i, 0, ·, c, ·)` and `(i, 1, ·, c, ·)` would reveal `b` (§0, last row).
- `A` outputs `b'`; `Adv = |Pr[b' = 1 | b = 1] − Pr[b' = 1 | b = 0]|`.

Queries with `w = 1` test **issuance–redemption** unlinkability and issuer hiding (which issuance,
and so which Anchor, produced the token being redeemed). A `w = 0` query in context `c` together
with a `w = 1` query in context `c' ≠ c` tests **redemption–redemption** unlinkability across
contexts: in world 0 they are redemptions of one token, in world 1 of the two different tokens.

**Theorem U5.** For every classical `A`:

```
(a) colluding:      Adv^anon-u ≤ 2·ε_ZK^joint + 2·Adv^prf-t_2
(b) non-colluding:  Adv^anon-u ≤ 2·ε_ZK^joint|_red + 2·Adv^prf_2 + 2·(ψ₀ + ψ₁),   ψ_c ≤ κ + φ_c
```

where `ε_ZK^joint` covers the two issuance proofs and all redemption proofs of the game (§3.1, UF6).
In (b) `A` sees only the redemptions, the Anchors are honest, and every queried Anchor Set contains
both issuers' keys. `ψ_c` is the probability that Anchor `c`'s `unbound_issue_response` returns
nothing on a fresh honest request. It is at most `κ + φ_c`: `κ` is the completeness error of the
issuance proof system on honest requests (`0` for a perfectly complete one), and `φ_c` is the base note's abort
term, the probability that `DerivePreimage_{sk_c}` fails on `UCom(k, ctx_iss, r)` for uniform
`(k, r)` (`E[φ_c] ≤ δ_c^{255}` over the vinegar oracle, no assumption on `UCom`).

*Proof (a).*
1. In each world replace every proof by a simulated one (`ε_ZK^joint` per world). The statements
   are adversarially chosen (`S`, `ctx_red`, `cd`, the responses), which the two-phase ZK definition
   allows. The simulator needs only the statements, which contain `nf = Derive(k_j, ctx_red)` for
   the answering token `j`. With adaptive queries the `j`-th hop fixes the coins of every other
   proof; the statement of proof `j` is then fixed by the earlier answers.
2. Now `A`'s view is a function of `t₀, t₁`, its own responses, the statements, the answers
   `Derive(k_{i⊕(b∧w)}, ctx_red)` of its queries, and the simulator coins. `r₀, r₁` and the
   preimages `s⁰, s¹` enter nothing else.
3. Replace `(Derive(k₀, ·), Derive(k₁, ·))` by independent uniform functions `(F₀, F₁)`
   (`Adv^prf-t_2` per world). The reduction gets `t₀, t₁` and the oracle, and runs everything else:
   no proof evaluates `UCom` or `Derive` on the honest keys any more.
4. **The ideal worlds coincide.** The answer to query `(i, w, ·, c, ·)` is `F_{i ⊕ (b∧w)}(c)`. By the
   context rule `w = W(c)` is a function of `c` (fixed when `c` is first used). The map
   `σ_W(F₀, F₁) = (F′₀, F′₁)`, `F′_i(c) = F_{i ⊕ W(c)}(c)`, is a bijection on pairs of functions
   (an involution), so it preserves their uniform distribution, and the answers in world 1 under
   `(F₀, F₁)` are the answers in world 0 under `σ_W(F₀, F₁)`. Everything else in the view is the
   same in both worlds. With adaptive queries `W` depends on `(F₀, F₁)` through the earlier
   answers. Take `W_F` to be the pattern of the run in world 1 on `F` (the flag of the first query
   in each context). The run in world 0 on `σ_{W_F}(F)` makes the same queries and gets the same
   answers, so it has the same pattern; hence `F ↦ σ_{W_F}(F)` is still a bijection, with inverse
   `G ↦ σ_{W'_G}(G)` for the pattern `W'_G` of the run in world 0 on `G`. This is the eager form of
   the lazy-sampling argument: when a fresh `c` is first queried, its flag is fixed and the
   exchangeable pair `(F₀(c), F₁(c))` is drawn fresh. ([Lean] for a fixed `W`:
   `Protocols/MoussakaUnbound.lean`, `swap_invariant`, `anonymity_unbound`; for adaptive `W`:
   `Privacy/MoussakaUnboundAd.lean`, `run_swapF`, `pr_run_swap`.)
5. Hence `|Pr[b' = 1 | 1] − Pr[b' = 1 | 0]| ≤ 2·ε_ZK^joint + 2·Adv^prf-t_2`. ∎

*Proof (b).* As (a), but `A` sees neither issuance, so the issuance proofs are never shown and not
simulated, and the `t_i` are not leaked: the PRF hop is `Adv^prf_2`. Before that hop the refusal bit
must be removed. With both issuers in every queried set (on `main` the Client finds its Anchor
itself, so this replaces the base note's "indices the Client takes from `S`"), the bit is "both
honest issuances succeeded". Replace it by `true`; the worlds are identical until an honest
issuance fails, `ψ₀ + ψ₁` per world. Step 4 is unchanged. ∎

*Correction (UF7).* An earlier version of this proof replaced the refusal bit by
`acc(x₀) ∧ acc(x₁) ∧ K₀ ∧ K₁`, with `acc(x_c)` the Anchor's verdict on Client `c`'s issuance proof,
and paid only `φ₀ + φ₁`. That bit is not available to the PRF reduction: `acc(x_c)` is the verifier
run on a real proof for the key `k_c`. In the base note's 4(b) this was harmless (no PRF hop
follows; the final swap exchanges whole tapes). Here `acc` has to go as well, which costs `κ`
per Client and is `0` for a complete proof system.

**[Lean] Theorem U5(a) on the executable spec.** The game above on `Spec/MoussakaUnbound.lean`'s
`issueRequest`, `finalizeIssue` and `redeemRequest` (with the C++ `find_issuer`), with the seed
expansions' outputs `(nf_key, r, ρ_iss)` and every `ρ_red` uniform.
- `Privacy/MoussakaUnboundAd.lean`, **`anonymityAd`**: `n` **adaptive** redemption queries
  `(i, w, S, ctx_red, cd)`, each a function of the two issuance requests and the history of earlier
  queries and answers. If a token does not finalize the guess sees nothing; otherwise each query is
  answered if both tokens are redeemable in `S` and every earlier query in its context had its
  flag (`ctxOk`), and refused otherwise. Both conditions are functions of the adversary's view. The
  two worlds differ by at most `4εI + 2n·εR + 2εprf`. The hops: `gameAd_hop₀`, `gameAd_hop₁`
  (issuance proofs), `gameAd_hopRed` (all `n` redemption proofs, from the generic adaptive hybrid
  `interact_close`), `viewAd_redSim` and `prf_hopAd` (the PRF hop), `idealGameAd_eq` (step 4, with
  the table-dependent involution of `pr_run_swap`).
- `Privacy/MoussakaUnbound.lean`, `anonymity`: the same bound for `n` queries fixed after issuance
  (all refused if any breaks the rule). It is the special case of queries that ignore the history,
  up to that refusal convention.

**The hypotheses** (both files):
- **Zero knowledge, per proof.** `ZeroKnowledge IssueRelW (proveR PI) simI εI` and
  `ZeroKnowledge RedeemRelW (proveR PR) simR εR` (`Privacy/Basic.lean`): for every statement and
  witness in the relation, the prover's output under a uniform 16-byte `ρ` and the simulator's
  output are `ε`-close against distinguishers that may know the witness. Each hop replaces one
  proof, so the joint `ε_ZK^joint` of the theorem is the sum `2εI + n·εR` per world. This is the
  form `lean/docs/zk.md` establishes with **dedicated label rows**. On `main` (CRT masks from the
  witness, `REUSE_CRT_WITNESS = true`) no efficient simulator meets it: the label term is a joint
  term over the `H₅` queries (§3.1, UF6), and the joint (PU) hop that replaces it is on paper, as
  for the base protocol. So the mechanized U5 applies to `main` only through that paper step.
- **The PRF.** `prfAdv A.ci (reductionAd …) ≤ εprf` (`Adv^prf-t_2`): given `t₀, t₁`, distinguish the
  table `c, ctx ↦ Derive(k_c, ctx)` from a uniform table. It is stated for the explicit reductions
  (the adversary with the simulator coins fixed, reading the table at the contexts it queries,
  adaptively) and is an assumption on Keccak-p[800,12] (§3.2, §10 item 1), not a theorem.

**[Lean] Theorem U5(b) on the executable spec.** `Privacy/MoussakaUnboundNC.lean`: the Moderator
alone (`AdversaryNC`), with `n` adaptive queries and the rules of (a); honest Anchors run
`issueResponse` (`unbound_issue_response`, `src/ihat/ihat.cpp:369-380`) with signers correct for
their keys; every queried Anchor Set contains both issuers' keys (`Contains`). The issuance proof
system is arbitrary.
- **`anonymityNC`**: `≤ 2n·εR + 2·(ψ₀ + ψ₁) + 2εprf`, from `real_sim_NC` (`n·εR`), `simNC_iff`
  (the view reads the keys only through the nullifier table), `sim_hyb_NC` (the abort term `psi`),
  `prf_hop_NC` (`prfAdvNC`, `Adv^prf_2` of `reductionNC`), `idealNC_eq`.
- `psi_le`: `ψ_c ≤ κ + φ_c` (`kappa`, `phiU`); `kappa_eq_zero`: `κ = 0` if the issuance proof system
  is complete (`NIZK.Correct`); **`anonymityNC_complete`**: `≤ 2n·εR + 2·(φ₀ + φ₁) + 2εprf`.
- **`anonymityNC_vinegarRO`**: averaged over the Anchors' vinegar tables, for signers that fail only
  if all 256 vinegars at the target are bad, `≤ 2n·εR + 2·(δ₀²⁵⁶ + δ₁²⁵⁶) + 2εprf`.
  `Audit/Nonvacuous.lean` instantiates it with pqov's signer model.
The zero-knowledge hypothesis is the per-proof one above, for the redemption relation only.

**Remarks.**
- The base note's 4(b) needed no Keccak assumption, because the bound nullifiers are uniform seed
  outputs. Here, linking two redemptions in different contexts is exactly distinguishing
  `Derive(k, c), Derive(k, c')` from independent values, so a PRF assumption is unavoidable (UF2).
- `t` and the PRF key share one secret: the commitment hides `k` only computationally, and the
  colluding Anchor sees `t`. That is why the assumption is stated with `t` leaked. With the
  generic estimate of §3.2, `Adv^prf-t_2 ≲ 4·(q + 1)·2^{−128}`, the same 128-bit margin as base
  `Adv^hide_Com` (base F4).
- `ctx_red` is no longer hidden from the Anchor by the issuance proof: it does not exist at
  issuance. The Anchor learns nothing about where the token will be used.

---

## 7. Sharing Anchor keys between the two variants

An Anchor that runs both `issue_response` and `unbound_issue_response` with one key signs raw
targets after verifying the matching issuance proof. Thm U1 (cross-variant step) and the remark
after it show that neither variant's tokens can be redeemed in the other, and each variant's
redemptions are bounded by its own issuances, under joint binding of `Com ∪ UCom`. Privacy is
unaffected: the Anchor sees which variant a Client requested, which is inherent in the API (the
request lengths differ: `45 + 7272` against `45 + 6864` bytes). Mixing variants within one
deployment partitions Clients by variant, as any visible option does (base §7, F5).

Base F1 is unchanged: PomFRIT's `issue_response` signs arbitrary targets without a proof, so a key
shared with PomFRIT lets anyone obtain a signature on a `UCom` image of their choice (UF3).

---

## 8. Quantum adversaries

As base §8. The new assumptions have the usual quadratic Grover loss: `Adv^prf-t` and `Adv^ow-kr`
have 64-bit quantum margins (128-bit keys), `Adv^spr-k` about `2^{96}` for the 192-bit match, joint
binding `≈ 2^{120}` (BHT on 360 bits). Harvest-now-decrypt-later privacy (Thm U5) therefore rests on
the 128-bit key `k` as well as on `r` and the proof system, with the same 64-bit quantum margin as
the base protocol.

---

## 9. Findings

- **UF1 — squatting fixed.** §5.2. The draft's NOTE (issue 45, "`nf = PRF(K, ctx_red)`
  in-circuit") is what PR #63 implements, and it removes base F2.
- **UF2 — non-colluding privacy is computational.** §6, remark.
- **UF3 — cross-protocol key reuse.** §7; base F1 applies to unbound tokens.
- **UF4 — client-side bookkeeping.** `UnboundToken` does not record the contexts it was redeemed
  in. A second redemption in the same `ctx_red` is rejected and links the attempts. A Client that
  wants unlinkability must keep the record itself, or the API could offer a consuming variant per
  context.
- **UF5 — DST versioning.** §0. A distinct protocol identifier (e.g. `"mouu"`) or purpose letter
  would keep the version byte for versions.
- **UF6 — one opening, many proofs.** §3.1. With dedicated label rows (`+256` bytes per proof) the
  `Pred_R` term disappears altogether, as for PomFRIT on `main`.

---

## 10. Open gaps

1. The PRF-with-commitment, key-recovery and key-second-preimage assumptions on Keccak-p[800,12]
   are new and are supported only by generic estimates; structural cryptanalysis of 12-round
   Keccak-p[800] with 128-bit keys and 192-bit truncation is outside this note.
2. Extraction for the unbound relations is mechanized to the same extent as for the base
   relations (§2): executable verifier and prover checked against the KATs, bridge, completeness,
   and the random-oracle and ideal-cipher bounds (fixed and adaptive statements, PRF and
   permutation views, spec relations, simultaneous extraction from the proofs of one run) for the
   executable statements. What remains is what remains
   for the base relations (`lean/README.md`, Gaps).
3. Thm U5(a) and (b) are mechanized on the executable spec with adaptive redemption queries
   (`Privacy/MoussakaUnboundAd.lean`, `anonymityAd`; `Privacy/MoussakaUnboundNC.lean`,
   `anonymityNC`, `anonymityNC_complete`, `anonymityNC_vinegarRO`). They rest on two hypotheses
   that stay hypotheses: per-proof zero knowledge (item 5) and the PRF advantage of the explicit
   reductions (item 1). The proof of (b) needed a correction (UF7). Two modelling restrictions
   remain: the number `n` of redemption queries is fixed in advance, and in (b) every queried
   Anchor Set must contain both issuers' keys (as for base 4(b) with `find_issuer`). Further honest
   sessions around the challenge, as in base `Privacy/MoussakaAdaptive.lean`, are not modelled.
4. Thm U1 is mechanized (§4 Status). It rests on the base note's assumptions, stated as
   advantages of explicit adversaries: joint binding of `Com ∪ UCom` (`AdvBind`, a
   standard-model assumption) and CT-UF^open over `D ∪ D_u`. CT-UF^open reduces to OMPR only
   through the modelling hypothesis `hmodel` (Lemma U with `Com` a random function, no inverse
   queries; the permutation version is paper). The bound issuance extraction is charged separately
   from the unbound pair. Cor U2, Prop U3 and Thm U4 have Lean cores only (`nf_determined`,
   `squat_cases`); their games are not mechanized.
5. The mechanized Thm U5 takes **per-proof** zero knowledge (`ZeroKnowledge` for `IssueRelW` and
   `RedeemRelW`, against distinguishers that know the witness). That hypothesis holds with
   dedicated label rows (`lean/docs/zk.md`). On `main` the CRT masks come from the witness, the
   label term is joint over the `H₅` queries (§3.1), and no per-proof simulator exists; the joint
   (PU) hop that replaces it is on paper, as for the base protocol. The theorems do not take the
   joint hypothesis.

---

## Appendix B: Lean

All in `lean/VoleMole/`; no `sorry`, no axioms beyond the standard three.

- `Arith/MoussakaUnbound.lean`: the `UCom` and `Derive` inputs (`encodeUnboundComState`,
  `encodeDeriveState`), their injectivity in the secret fields and disjointness from each other and
  from the bound `Com`; the two constraint generators and their completeness and soundness
  (§2).
- `Protocols/MoussakaUnbound.lean`: the deterministic and finite cores of §4–§6:
  `t_injOn_of_derive`, `exists_unsigned_per_context`, `count_le_per_variant` (Thm U1),
  `nf_determined` (Cor U2), `squat_cases` (Prop U3), `swap_invariant` (Thm U5 step 4) and
  `anonymity_unbound` (Thm U5 from the hop hypotheses).
- `Spec/MoussakaUnbound.lean`: the executable byte-level spec (seed expansion, `ucom`, `derive`,
  both witness encodings, and the protocol steps with `find_issuer`: `findIssuer_some`,
  `findIssuer_isSome`), built on the Arith encodings, with `ucom_getD` and `derive_getD` tying it
  to the Arith model. `lake exe spec_kats` checks it against every field of
  `tests/ihat/unbound_ihat_kat.txt` that does not depend on the VOLEitH internals.
- `EndToEnd/MoussakaUnbound.lean`: degree bounds and the end-to-end extraction theorems for both
  unbound relations (§2).
- `Privacy/MoussakaUnbound.lean`: Theorem U5(a) on the executable spec with queries fixed after
  issuance (`anonymity`), with `close_pi` (`n` independent hops), `simGame_iff`, `prf_hop` and
  `idealGame_eq` (§6).
- `Privacy/MoussakaUnboundAd.lean`: Theorem U5(a) with adaptive redemption queries
  (`anonymityAd`, `4εI + 2n·εR + 2εprf`). Generic pieces: `interact` (an adaptive interaction with
  `n` oracles and a refusal rule), `interact_close` (the `n`-step hybrid over independent oracle
  tapes), `interact_congr_of`, `firstFlag_of_prefix`, `run_swapF` and `pr_run_swap` (step 4 for
  adaptive queries: a table-dependent involution of the uniform table) (§6).
- `Privacy/MoussakaUnboundNC.lean`: Theorem U5(b) with adaptive redemption queries, corrected
  (`anonymityNC`, `2n·εR + 2·(ψ₀ + ψ₁) + 2εprf`; `psi_le`, `kappa_eq_zero`, `anonymityNC_complete`;
  `anonymityNC_vinegarRO`, `2n·εR + 2·(δ₀²⁵⁶ + δ₁²⁵⁶) + 2εprf`), with the honest Anchor's
  `issueResponse` (§6).
- `Audit/Nonvacuous.lean`, section `Unbound`: `anonymityAd` for a constant-guess adversary
  (`εprf = 0`) and `anonymityNC_vinegarRO` with pqov's signer, a Moderator whose sets contain both
  issuers, and a complete issuance proof system.
- `Protocols/DomainSeparation.lean`: the unbound rows (`mousU`).
- `Verifier/Relations.lean`: the verifier statements `moussakaUnboundIssue`,
  `moussakaUnboundRedeem`; `Verifier/UovEval.lean`: `moussakaUnboundRedeemValues` (UOV terms over
  arrays) `= uRedeemValues` (`moussakaUnboundRedeemValues_eq`). `lake exe verifier_vectors`
  (`Verifier/Kats.lean`, `moussakaUnbound`) verifies every proof of `unbound_ihat_kat.txt` and
  rejects mutations; `lake exe prover_vectors` (`Verifier/ProverKats.lean`) reproduces them byte
  for byte, plus random statements of both relations.
- `Verifier/Bridge/Relations.lean`: `moussakaUnboundIssue_values`, `moussakaUnboundRedeem_values`,
  `moussakaUnboundIssue_accept`, `moussakaUnboundRedeem_accept`;
  `Verifier/Bridge/ChainRelations.lean`: `moussakaUnboundIssue_extract_chain`,
  `moussakaUnboundRedeem_extract_chain`; `Verifier/Bridge/Prover.lean`, `Bridge/Complete.lean`:
  `moussakaUnbound*_complete`, `*_complete_tables`, `*_complete_shake`;
  `EndToEnd/MoussakaUnbound.lean`: `moussaka_unbound_redeem_comb_bad_gf128`.
- `Prob/MoussakaUnbound.lean`: the statement properties `Unbound.IssueStmt`, `Unbound.RedeemStmt`
  (C++ parameters, DSTs, combination, the Arith systems as evaluator), the link to the executable
  statements (`Unbound.moussakaUnboundIssue_stmt`, `moussakaUnboundRedeem_stmt`), the per-chain
  extraction for any such statement (`Unbound.issue_extract_chain`, `redeem_extract_chain`), and
  one chain with uniform challenges (`Prob.moussakaUnboundIssue_chain_prob`:
  `≤ 2⁻¹⁵⁰ + ε_QS(3816)`, `moussakaUnboundRedeem_chain_prob`: `≤ 2⁻¹⁵⁰ + ε_QS(7929) + 2⁻¹²⁸`).
- `ROM/MoussakaUnbound.lean`: against the random oracle (`moussakaUnboundIssue_accept_le`,
  `moussakaUnboundRedeem_accept_le`), in the joint random-oracle and ideal-cipher model with
  binding explicit (`IC.*_accept_le_ic`) and every term explicit (`IC.*_accept_le_full`), with AES
  as random permutations and inverse queries (`IC.*_accept_le_perm`); `combOk_moussakaUnbound*`.
- `ROM/MoussakaUnboundAdapt.lean`: adaptively chosen statements (`IC.*_accept_le_adaptive`,
  `IC.*_accept_le_adaptive_perm`), plus `stmtBindEps q`.
- `EndToEnd/MoussakaUnboundSpec.lean`: arithmetized → spec (`SpecRel.uIssueRel_of_wit`,
  `uRedeemRel_of_wit`), and `hinj` for the C++ instance encodings (`hinj_unboundIssue`,
  `hinj_unboundRedeem`; at the executable statements `hinj_moussakaUnboundIssue`,
  `hinj_moussakaUnboundRedeem`).
- `ROM/MoussakaUnboundSpec.lean`: the eight headline bounds for `Spec.MoussakaUnbound.IssueRel`,
  `RedeemRel` (`IC.*_spec`).
- `ROM/MoussakaUnboundSim.lean`: simultaneous extraction (§3.1) per relation
  (`IC.moussakaUnboundIssue_sim_spec`, `IC.moussakaUnboundRedeem_sim_spec`) and for both
  relations together (`IC.moussakaUnbound_sim_joint_spec`); `Audit/SimExtract.lean` instantiates
  the joint one at the executable statements.
- `Audit/UnboundROM.lean`: non-vacuity of the headline bounds at the executable statements
  (trivial prover; families with more than one instance).
- `ROM/MoussakaUnboundOMUF.lean`: Theorem U1 (§4 Status): the game OMUF-U (`anchorU`, `uanchorIC`,
  `uanchorIC_eq_spec`, `umoderatorIC`, `game`, `Win`), the three provers (`PBI`, `PUI`, `PUR`),
  the extracted inputs of `Com ∪ UCom` (`XOp`, `comX`, `WFX`, `Coll`, `Forge`), the per-table core
  `win_imp`, the union bound over three families (`prEvent_bind_le_sum5_of_table`), `omufU_le`,
  `omufU_le_num` (`epsUI`, `epsUR`), liveness (`upfLenI_eq`, `upfLenR_eq`).
- `ROM/MoussakaUnboundOMUFSim.lean`: Theorem U1 with simultaneous extraction (`omufU_le_sim`,
  `prEvent_simBI_le`, `prEvent_simU_le`, `epsUsim`, `omufU_le_num_sim`).
- `Assumptions/UnboundLinks.lean`: the CT-UF^open forger over `D ∪ D_u` (`ctufForgerU`,
  `win_imp_openU`), `omufU_le_open`, `omufU_le_num_open`, `omufU_le_num_ompr` and their `_sim`
  versions.
- `Protocols/MoussakaUnbound.lean`: `collision_or_forgery_unbound` (Thm U1, steps 3–4).
- `Audit/UnboundOMUF.lean`: every Thm U1 corollary instantiated (two honest Anchors, an adversary
  with one bound and one unbound Issue query, the toy ideal forger for `hmodel`).
