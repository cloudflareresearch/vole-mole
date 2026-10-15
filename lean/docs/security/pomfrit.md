# Security of vole-mole's PomFRIT implementation

This note states and proves the security properties of PomFRIT, as implemented in:
- `src/pomfrit/pomfrit.cpp`
- `src/pomfrit/redeem.hpp`
- `src/pomfrit/seeded.hpp`
- `include/vole_mole/pomfrit.hpp`

PomFRIT is Algorithm 2 ("Optimized BS") of Baum, Beckmann, Beullens, Mukherjee and Rechberger,
*Concretely Efficient Blind Signatures Based on VOLE-in-the-Head Proofs and the MAYO Trapdoor*
(ePrint 2026/109, USENIX Security 2026). Here "the paper" means the USENIX prepublication version,
whose numbering is: Defs. 2.4 (blindness), 2.5 (one-more unforgeability), 3.1 (one-more preimage
resistance), 4.2 (NIZK) and 4.3 (knowledge soundness); Algorithm 2; Theorem 6.1; Appendix B.3.

The note builds on these proof-system results:
- the classical straight-line proof of knowledge `ε_ext` (`lean/docs/extraction/README.md`, main theorem and
  §Assembly);
- strong simulation-extractability (`lean/docs/extraction/L8-simulation-extractability.md`);
- arithmetization soundness, i.e. that the constraints force `P(s) = h + r` (`lean/docs/extraction/L7-uov.md`);
- zero knowledge (`lean/docs/zk.md`) and its fix on branch `voleith-label-rows`;
- the QROM proof of knowledge (`lean/docs/extraction/Q2-qrom-fiat-shamir.md`).

The combinatorial core of the new lemma (Lemma P) is checked in Lean, in
`lean/VoleMole/Protocols/PomFRIT.lean`.

Line references are to the working tree at commit `6d7113e`.

## 0. Verdict

| Property | On `main` | With the label-row fix | Section |
|---|---|---|---|
| One-more unforgeability (paper Def. 2.5), classical ROM + ideal cipher | **Holds.** Tight under a τ-shift variant of UOV one-more preimage resistance (Thm U2). Under the paper's standard assumption (Def. 3.1) the reduction loses an extra `(Q₃+ℓ+1)·2^{−71}` (Thm U1) | Same (ZK is not used) | §5–§6 |
| One-more unforgeability, QROM | **Open.** The reduction needs a first-phase extractor *during* the run; Q2 extracts only after the run | Same | §7 |
| Blindness against a malicious Issuer (paper Def. 2.4: malicious key, selective-failure form) | **Fails.** An honest-but-curious Issuer links with advantage ≈ 1 using about 310 SHAKE calls per (signature, session) pair (`lean/docs/zk.md` §4) | **Holds** (Thm B), with advantage `≤ ε_ZK^fix(Q_P = 2) + 2Q_X·2^{−256}`; [Lean] from G1, with (ZK-fix) as a hypothesis (`Privacy/PomFRIT.lean`), and with (ZK-fix) derived for the executable Lean prover with label rows down to its tape hypothesis (`Privacy/PomFRITLean.lean`, `blindness_lean`); in the ROM and ideal-cipher model with the Issuer seeing the tables, for the Lean prover, `≤ 4·εRO(q₃, q₅ + 1248, q_E + 18428) + δ(A) + δ(A.swap)` (`Privacy/PomFRITRO.lean`, `blindnessRO_lean`; the collision terms `δ` explicit, bounded on paper) | §8 |
| No selective failure via `finalize_issue`'s check (`pomfrit.cpp:207`) | Holds: the abort event is a function of the Issuer's own view | Holds | §8.3 |
| Message binding; no re-targeting of a signature | Holds (part of unforgeability; L8 §7) | Holds | §9.1 |
| Third parties cannot maul a signature (strong SE) | Holds against parties who never saw the request `t` | Holds against everyone, the Issuer included | §9.2 |
| One signature per (issuance, message) | **No.** The signature's owner can make any number of distinct valid signatures on the same message from one issuance, by using a non-minimal grinding counter. Demonstrated | Same | §9.3 |
| Replay | Not prevented, by design. Applications must deduplicate on the message (or on a nullifier inside it), **never** on signature bytes | Same | §9.4 |
| `detail::issue_request_with_seed` with a reused seed | Breaks blindness, and leaks `(r, s)`, if the Issuer answers twice with different preimages | Same | §9.5 |

**Main findings.**
- **F1 (paper gap, repaired here).** The paper's unforgeability reduction (proof of Theorem 6.1)
  programs `h := t_j − r` using a first-phase extractor `E₁` that recovers `r` from π₁ alone. For
  multi-tree VOLEitH, π₁ does not determine `r` uniquely. Up to τ = 17 fully-known trees can carry
  different prefixes, and the prover picks which one becomes the witness *after* it sees `h`.
  - Lemma P below gives a rigorous `E₁`: take the prefix of the group of trees with the largest
    total challenge width. It is wrong only with probability `2^{−71}` per H₂³ query.
  - This loss is a reduction artifact, not an attack (§6.3).
- **F2 (blindness, `main`).** Confirmed. The fix is necessary and, with this note's proof,
  sufficient. [Lean] `ZK/Relations.lean`: in every honest run the Issuer's `t ⊕ h(σ)` is `r`
  (`issuerGuess_eq`), its sibling-label query hits on every tape and the attack test accepts every
  real proof (`pomfrit_issuer_hits`, `pomfrit_attack_test`; `lean/docs/zk.md` §4.1).
- **F3 (owner malleability).** `verify` does not check that `ctr` is minimal
  (`faest_sig.hpp:126-135`), so a Client can re-randomize its own signature. Demonstrated in
  `scratchpad/demo/ctr_malleability.cpp`: two distinct signatures on one message, from one Issuer
  response, both verify. This is harmless under the paper's notion (distinct messages), but it
  defeats any deduplication keyed on σ.
- **F4 (essential binding, present).** The prefix correction `d[0..M)` must be hashed into `h`, and
  it is (`pomfrit.cpp:107`). Without it, anyone can forge without the Issuer (§2.2).
- **F5 (deployment).** The Issuer key must be used only for PomFRIT. `derive_preimage` is a raw
  preimage oracle (`uov.hpp` WARNING), so it signs arbitrary UOV messages. Every other use of `sk`
  counts toward ℓ in Thms U1/U2.

## 1. Model and notation

- **Oracles.**
  - Every SHAKE-based hash is a random oracle. This covers the proof system's hashes
    (H₁, H₂⁰…H₂⁴, H₃, H₄, H₅, the combination hash) and PomFRIT's application hashes:
    - `H_T` = `hash_to_target` (`pomfrit.cpp:96-111`);
    - `H_ref` = `commit_to_refresher` (`:76-84`);
    - `XOF_seed` (`:150-161`).
  - AES-128 is an ideal cipher (as in `lean/docs/extraction/README.md`).
- **Lemma DS (assumed; `lean/docs/security/domain-separation.md`, in progress).** The application hashes
  are DST-prefixed (`dst.hpp:41-45`, 7-byte DSTs). The proof-system hashes are tagged at the end.
  The lemma says the input sets of the two families are disjoint, so they are independent random
  oracles. This note cites it and does not reprove it. Where it is used, `ε_DS` denotes its error
  (0 if the families are exactly disjoint).
- **Encodings.** All earlier fields of `H_T`'s input are fixed-length, so the input
  `DST ‖ dig(pk) ‖ chal1 ‖ ũ ‖ d[0..M) ‖ msg` parses uniquely.
  - Lengths: the DST is 7 bytes; `dig(pk)` is the SHAKE256 key digest; `chal1` is
    `CHALLENGE_BYTES` of VOLE_CHECK, at least 5λ+64 = 704 bits; `ũ` is 4λ bits; `d[0..M)` is
    M = 45 bytes; `msg` comes last.
  - `H_ref`'s input is `DST ‖ refresher` (32 bytes). `XOF_seed`'s input is
    `DST ‖ seed ‖ dig(pk) ‖ msg`, squeezed into `rho ‖ refresher ‖ r`.
- **Parameters.** UOV with N = 119 and M = 45 over GF(256) (`uov.hpp:17-18`). The proof system is
  FAEST-EM-128f VOLEitH:
  - λ = 128, τ = 17, w_grind = 8;
  - BAVC with one tree of 2⁸ leaves and sixteen of 2⁷, so `n_Δ = 8 + 16·7 = 120`;
  - QuickSilver degree d = 2;
  - witness `w = r ‖ s`, 164 bytes, with `WIT_OFF_R = 0` and `WITNESS_PREFIX_BYTES = M`
    (`redeem.hpp:42-44, 103`).
- **Relation.** R_PomFRIT((pk, h), (r, s)) ⇔ `P_pk(s) = h ⊕ r` (addition in GF(256)^M is XOR).
  L7 shows that the bit constraints plus the combined output constraint (`redeem.hpp:113-143`)
  force exactly this relation, given L4's dichotomy.
- **Counts.**
  - `Q_T`: H_T queries by the adversary.
  - `q₁`, `q₂`, `Q₃`: H₂¹, H₂², H₂³ queries, grinding included.
  - `N`: all queries.
  - `ℓ`: Issuer (`issue_response`) queries.
  - `Q_X`: XOF_seed queries.
  - `Q₅`: H₅ queries.
  - `Q_V`: verifications the adversary triggers.
  - `ε_ext(N; q₁, q₂, Q)`: the README's PoK bound with per-oracle counts (L8 §4, §9.2), for d = 2:

        ε_ext = 2Q·2^{−128} + q₁·ε_KOS + q₂·(ε_QS + 2^{−128}) + q_c·2^{−448} + ε_bind + ε_dead + (N²+N)·2^{−256}.

    By L8 §9.1, one union bound covers any number of outputs simultaneously.

## 2. Algorithm 2 versus the code

### 2.1 Line by line

| Paper, Algorithm 2 | Code | Match? |
|---|---|---|
| 1–2 `KG`: MAYO.KG | `uov::SecretKey` (pqov UOV, N = 119, M = 45) | UOV instead of MAYO (D7) |
| 3 `Sig1(pk, µ)` | `issue_request` → `detail::issue_request_with_seed` (`pomfrit.cpp:140-185`) | |
| 4 `(π₁, r, st) ← P₁(C)`, with `r` the u-values of ℓ dedicated VOLEs (App. B.2 step 2) | `(rho, refresher, r) ← XOF_seed(seed ‖ dig(pk) ‖ msg)` (`:150-161`); `refresher_com ← H_ref(refresher)` (`:165-166`); `voleith_vole_gen(…, nullptr, r, rho, refresher_com)` (`:167`), which writes `d[0..M) = u[0..M) ⊕ r` (`voleith.hpp:228-233`) | **Deviation D1**: the Client samples `r`, and π₁ carries its correction |
| 5 `h ← H(µ, π₁)` | `h ← H_T(dig(pk), chal1, ũ, d[0..M), msg)` (`:96-111, 170`) | D1/D2: π₁ is represented by `chal1` (which hashes `mu_null`, `com`, corrections, `c_mult`, `iv_pre`, `refresher_com`), `ũ`, and the prefix correction. `pk` is added |
| 6 `t ← h + r` | `:173-176` | ✓ |
| 7 output `ρ₁ = t` | `IssueRequestResult{pending, t}` | ✓ |
| 8–10 `Sig2`: `s ← SPre(sk, t)` | `sk.derive_preimage(t)` (`:188-190`); deterministic: vinegar = H(t ‖ sk_seed ‖ DST ‖ ctr) (pqov `ov.c:226-239`) | ✓ (a deterministic SPre) |
| 12 `if T*(s) ≠ t output ⊥` | `if (pk.eval(response) != impl->t) return nullopt` (`:207`) | ✓ |
| 13–14 `π₂ ← P₂(C_{h,pk}, s, st)` | `voleith_prove_commit(…, {&pk, h}, s, pending, refresher)` (`:213-214`); delayed instance: `mu(pk, h)` enters H₂² (`voleith.hpp:267-273`) | ✓ (D3, D4) |
| 15 `sig = (π₁, π₂)` | `sig = proof ‖ refresher_com ‖ refresher` (`:44-50`) | ✓ |
| 16–19 `Verify` | check `refresher_com = H_ref(refresher)` (`:224-228`), reconstruct with binder `refresher_com` (`:229`), recompute `h` (`:234`), `voleith_verify_commit` with binder `refresher` (`:236`) | ✓ (App. B.3's `com_rand` check included) |

### 2.2 Deviations and their effect

- **D1: the Client samples `r` and corrects for it** (`pomfrit.cpp:86-95`, TODO(cjpatton)). In the
  paper, `r` *is* the VOLE `u` of dedicated rows. Here `r` is a witness prefix committed through
  `d[0..M) = u[0..M) ⊕ r`, where `u` is committed in `com`, which `chal1` hashes.
  - **Unforgeability is preserved, provided `d[0..M)` is hashed into `h`, which it is (`:107`).**
    Then `r` is a function of the `H_T` input and of committed data, fixed before `h` is sampled.
    This is exactly the property the paper gets from borrowing.
  - Without `:107`, there is a trivial universal forgery (finding **F4**):
    1. Run step 1 honestly and compute `h` without `d[0..M)`.
    2. Pick any `s` and set `r := P(s) ⊕ h`.
    3. Write `d[0..M) := u[0..M) ⊕ r` and finish the proof.

    No Issuer is needed.
  - D1 does not remove the paper's multi-tree ambiguity (F1). In both designs, `r` is
    `u^{(i)}[prefix] (⊕ d)` for whichever tree turns out to be free. Lemma P handles both.
  - For ZK, `r` is an ordinary witness prefix (`lean/docs/zk.md` §1). On `main` it is also the free-XOR label
    offset (`lean/docs/zk.md` §4); that is the blindness failure. The fix moves the labels to dedicated rows.
  - Cost: M more correction bytes. No security cost.
- **D2: `h` also binds `dig(pk)` and `ũ`.** Binding `pk` makes a signature for `pk` an independent
  object from one for `pk'`, barring a SHAKE256 digest collision. Binding `ũ` is harmless.
  `chal1` stands in for the rest of π₁. A collision in H₂¹ (≥ 704-bit output) is in `ε_ext`.
- **D3: delayed instance.** `mu_null = H₂⁴(DST)` enters H₂¹, and `mu(pk, h)` enters H₂². L8 §7
  shows that re-targeting a π₁ to a new instance (a new `msg`, hence a new `h`) is not a
  malleability attack.
- **D4: binders.** `b₁ = refresher_com` goes into H₂¹, and `b₂ = refresher` into H₂². `verify`
  checks `refresher_com = H_ref(refresher)`. This matches App. B.3, which needs it so the ZK
  simulator can program chall₂.
  - The repo's simulator (`lean/docs/zk.md` §5) programs only H₂³. So it does not need the refresher. It is
    harmless and costs 64 bytes.
  - It has no effect on unforgeability: no such proof uses `b₁`/`b₂` beyond hashing them.
- **D5: one XOF for `rho`, `refresher` and `r`, also absorbing `pk` and `msg`.** In the ROM, with a
  fresh 256-bit seed, the three squeezes are independent and uniform (cost `Q_X·2^{−256}` per
  session). Absorbing `(pk, msg)` stops a reused seed from reusing the VOLE across messages or keys
  (`:144-146`). The case of a reused seed with the same `(pk, msg)` is §9.5.
- **D6: grinding (FAEST v3).** This is not in the paper's VOLEitH. The verifier checks only the
  zero top bits, not minimality, which gives owner malleability (§9.3).
- **D7: UOV with a raw preimage API.** It is covered by the paper's Def. 3.1 instantiated with
  UOV's `(TrapGen, SPre) = (keygen, derive_preimage)`.
  - `derive_preimage` is deterministic in `t`, so repeated Issuer queries on the same target return
    nothing new. In fact the same preimage also protects §9.5's honest case.
- **D8: the output constraint is a random GF(2¹²⁸)-combination of the M equations**
  (`redeem.hpp:113-143`). L4 accounts for the combination, and L7 for soundness.

## 3. Security notions

**One-more unforgeability (paper Def. 2.5).**
- Setup: `(sk, pk) ← KG`. The adversary gets `pk`, all oracles, and an Issuer oracle
  `issue_response(sk, ·)` on **arbitrary** targets, at most ℓ times.
- Win condition: it outputs `ℓ+1` pairs `(msg_i, σ_i)` with pairwise distinct `msg_i`, all
  accepted by `verify(pk, ·, ·)`.

We also consider a stronger variant, *one-more strong unforgeability* (distinct pairs
`(msg_i, σ_i)`). It fails (§9.3).

**Blindness (paper Def. 2.4).** This is the standard round-optimal game:
- **Malicious key**: `A₁` outputs `pk`.
- `A₂` gets `ρ₁` for `µ_b` and for `µ_{1−b}`, and returns two responses.
- `A₃` gets `(sig^0, sig^1)`, the signatures on `µ_0` and `µ_1`, or `(⊥, ⊥)` if either session
  fails. This is the selective-failure form.

We prove a slightly stronger form, in which `A` also learns *which* session failed, and may
trigger verifications and query all oracles.

**Assumptions** (all explicit; numbering used below):
- **(A-OMPR)** Paper Def. 3.1 for UOV.
  - `Adv^{ompr}_{UOV}(B; n, q)`: given `pk` and `n` uniform targets `t_1..t_n ∈ GF(256)^{45}`,
    with ≤ q calls to `derive_preimage(sk, ·)` on arbitrary targets, output q+1 pairs `(s_i, I_i)`
    with distinct `I_i` and `P(s_i) = t_{I_i}`.
  - The Whipped-MQ / UF-CMA assumption for UOV is the case `(1, 0)`. Note the API's
    derandomization: SPre is a deterministic function of `(sk, t)`.
- **(A-OMPR⊕τ)** τ-shift one-more preimage resistance. This is the same game, except targets are
  requested adaptively.
  - On the k-th target request, B submits a list of shifts `δ_{k,1..m_k}` with `m_k ≤ τ`, and
    receives a uniform `h_k`.
  - B wins with q+1 triples `(k_i, a_i, s_i)` with distinct `k_i` and
    `P(s_i) = h_{k_i} ⊕ δ_{k_i, a_i}`.
  - The case τ = 1 is A-OMPR. We know no reduction between the two with loss better than
    `τ^{q+1}` (guessing), and no attack that uses the choice of shift (§6.3).
- **(PoK)** The README's classical extraction theorem, with simultaneous extraction (L8 §9.1), and
  L7 for the relation.
- **(ZK-fix)** `lean/docs/zk.md`'s theorem with the label-row fix, as standard adaptive two-phase NIZK
  (the distinguisher may know the whole witness):

      ε_ZK^fix(Q_P) = ε_rho + ε_prog + 2ε_hide + ε_lab + ε_iv,   ε_lab = (Q₅ + n_mult·Q_V + Q_P)·2^{−128},

  with the other terms as in `lean/docs/zk.md` §3, and `n_mult ∈ [305, 312]`.
  - Assumed here; the fix is in progress on `voleith-label-rows`.
  - Requirements: `rho` uniform and secret, and an honest prover on a satisfying witness.
  - Multiple sessions may interleave their phases. `lean/docs/zk.md`'s hybrids are per proof and
    order-independent.
- **(DS)** Lemma DS.

## 4. Why the proof needs more than `ε_ext`

The paper's proof (Theorem 6.1) programs `H(µ, π₁) := t_j − r`, with `r = E₁(π₁, queries)`
extracted when `H` is queried. The repo's extractor `E` (README) runs at the end, on a complete
proof. It outputs `w^{(i)} = u_i ⊕ c_i ⊕ d` for the *first* known tree `i` whose candidate
satisfies R. Which tree that is depends on `d[M..)`, which is chosen after `h`.

**The ambiguity is real.** Suppose a prover commits trees with two different prefixes `r_A`
(trees in `G_A`) and `r_B` (trees in `G_B`). After seeing `h`, it may complete either one. If it
completes with `r_B`, then by Claim 4 (Lean `free_tree_holds_witness`) every tree of `G_A` is
*fixed* on the accepting set. That costs a factor `2^{Σ_{G_A} k_i}` in grinding, but for a small
`G_A` that cost is tiny (`2⁷` for one tree). So "extract `r` from π₁" is not a well-defined
operation. App. B.3's justification ("for the majority of VCs all indices must potentially be
extractable") is informal. Lemma P makes the majority idea precise.

## 5. Lemma P: a first-phase extractor `E₁`

**Definition of `E₁`.** On an `H_T` query `x = (dig, chal1, ũ, d_pre, msg)`:
1. Find the first H₂¹ query with output `chal1`. If there is none, output `⊥`.
2. Recover the committed data as in L1: `com`, then `h_i`, then the leaf commitments.
3. Call a tree *alive* if all its leaves are alive in L1's sense, relative to queries before that
   H₂¹ query. `E₁` checks the second cipher block itself.
4. For each alive tree, run ConvertToVOLE and set `r^{(i)} := (u_i ⊕ c_i)[0..M) ⊕ d_pre`, with
   `c₀ = 0`.
5. Partition the alive trees into groups `G_ρ = {i : r^{(i)} = ρ}`. Let `g*` be the group of
   largest width `Σ_{i∈G} k_i`, where `k_i ∈ {8, 7}` is the challenge width of tree `i`. Break ties
   by least index.
6. Output `E₁(x) := ρ_{g*}`, or `⊥` if no tree is alive.

`g*` depends only on `(chal1, d_pre)`, and not on `msg`.

**Lemma P.** Fix any classical adversary. Except with the failure events of `ε_ext` and the
event `Shift` below, every accepted output whose `H_T` input is `x` has an extracted witness
`(r, s)` with `r = E₁(x)`, `P(s) = H_T(x) ⊕ r`, and `s` the suffix of an alive tree in `g*`. And

    Pr[Shift] ≤ (Q₃ + n_out)·2^{−71} + Q_T·q₁·2^{−704}.

*Proof.* Take an accepted output and its chain: its H₂¹ query, then H₂², then H₂³ input `y`.
Discard the README's events L1–L4 for all chains; this costs `ε_ext`, minus its H₂³ term, which
is reused below.
1. If `chal1` was queried to `H_T` before any H₂¹ query output it, a later H₂¹ output must hit a
   value already named in an `H_T` query. The cost is `≤ Q_T·q₁·2^{−704}`.
2. Otherwise L1 fixes the committed data at the H₂¹ query, before the `H_T` query. "Known at the
   end" equals "alive" (README L2), so the extractor's candidates are exactly `E₁`'s trees, and
   their prefixes are the `r^{(i)}`.
3. Apply L6 (`extraction_cases`) to the chain. Either `|A| ≤ max(d,1) = 2`, which is accepted
   with probability `≤ 2·2^{−128}` per H₂³ query (already in `ε_ext`), or `u*` is a bit vector
   and some free tree holds `u*`.
4. In the second case, let `G(u*)` be the alive trees whose prefix equals `u*`'s. By
   `fixed_outside_prefixGroup` [Lean], every tree outside `G(u*)` is fixed on `A`. So by
   `card_le_prod_of_fixed` [Lean], `|A| ≤ 2^{Σ_{G(u*)} k_i}`.
5. If `G(u*) = g*`, the free tree is in `g*`. Its candidate satisfies every uncombined
   constraint, hence R by L7, and its prefix is `ρ_{g*}`.
6. Otherwise, define `Shift` as `G(u*) ≠ g*`. The two groups are disjoint, and `g*` is at least
   as wide. By `minority_weight_le` [Lean], with the widths `(8, 7, …, 7)`,
   `Σ_{G(u*)} k_i ≤ 57`. So `|A| ≤ 2^{57}` (`minority_card_le` [Lean]).
7. `A`, `u*` and `g*` are fixed by the chain before the H₂³ answer at `y`, and that answer is
   uniform over `2^{128}` values. So `Pr[Δ ∈ A] ≤ 2^{57−128} = 2^{−71}` (`per_query_bound`
   [Lean]).
8. A union over the H₂³ queries of the adversary and of the verifier on the outputs gives
   `(Q₃ + n_out)·2^{−71}`. ∎

**Tightness of 2^{−71}.** Take seven 7-bit trees plus the 8-bit tree (width 57) against nine
7-bit trees (width 63). Completing with the minority prefix costs about `2^{71}/Pr[open]` H₂³
calls. So the term is tight up to the opening-success factor.

## 6. One-more unforgeability (classical)

### 6.1 Theorem U1 (standard assumption, paper Def. 3.1)

For every classical adversary `A` against Def. 2.5 with the counts of §1, there is a `B` with
about `A`'s running time, plus `(Q_T + ℓ + 1)` runs of `E₁`, i.e. ≤ 17 ConvertToVOLE calls each,
such that

    Adv^{omuf}_{PomFRIT}(A) ≤ Adv^{ompr}_{UOV}(B; Q_T + ℓ + 1, ℓ)
                             + ε_ext(N; q₁, q₂, Q₃ + ℓ + 1)
                             + (Q₃ + ℓ + 1)·2^{−71} + Q_T·q₁·2^{−704} + ε_DS.

*Proof.* `B` gets `pk` and targets `t_1, t_2, …`, and simulates every oracle for `A` by lazy
sampling, with the ideal cipher included.
- **`H_T`.** On a fresh query `x` under `dig(pk)`, `B` takes the next unused target `t_j` and sets
  `H_T(x) := t_j ⊕ E₁(x)`, reading `⊥` as `0`. Queries under other key digests get fresh uniform
  answers.
  - `E₁(x)` is a function of the log, independent of `t_j`, so `H_T(x)` is uniform.
  - `B`'s own cipher evaluations inside `E₁` are lazily sampled entries that `A` does not see. So
    the simulation is perfect, by (DS) for the independence of `H_T` from the proof oracles.
- **Issuer.** `B` forwards each Issuer query to its `derive_preimage` oracle: ≤ ℓ calls.
- **Output.** `A` outputs `(msg_i, σ_i)` for `i ≤ ℓ+1`, with distinct messages, all accepted.
  - The verifier's `H_T` input `x_i` contains `msg_i`, so the `x_i` are distinct and map to
    distinct indices `j_i`.
  - By Lemma P with `n_out = ℓ+1`, except with the stated errors, each `σ_i` yields `s_i` with
    `P(s_i) = H_T(x_i) ⊕ E₁(x_i) = t_{j_i}`.
  - `B` outputs `(s_i, j_i)`: ℓ+1 preimages of distinct targets, after ℓ oracle calls. ∎

The Issuer oracle is a raw preimage oracle on arbitrary targets, exactly SPre in Def. 3.1. Any
other use of the same `sk` (UOV signing, another protocol) counts toward ℓ (finding F5).

### 6.2 Theorem U2 (tight, τ-shift assumption)

    Adv^{omuf}_{PomFRIT}(A) ≤ Adv^{ompr⊕17}_{UOV}(B'; Q_T + ℓ + 1, ℓ) + ε_ext(N; q₁, q₂, Q₃ + ℓ + 1)
                             + Q_T·q₁·2^{−704} + ε_DS.

*Proof.* This is the same as U1, with one change. On `H_T(x)`, `B'` submits the full list of
alive-tree prefixes `{r^{(i)}}` (≤ 17 shifts) and answers with the returned `h`. In Lemma P,
every alive tree's prefix is now a shift, so the `Shift` event disappears. The free tree's prefix
is among the shifts whenever L6's second case holds. ∎

### 6.3 Numbers and interpretation

For d = 2 at the README's operating point:
- `ε_ext ≈ (2Q₃ + 2q₂)·2^{−128}`, which is `2^{−62}` at `2^{64}` queries.
- U1's extra term, `Q₃·2^{−71}`:
  - `2^{−21}` at `Q₃ = 2^{50}`;
  - `2^{−7}` at `Q₃ = 2^{64}` (Lean `loss_at_2_50`, `loss_at_2_64`).

So, *proved from the standard assumption*, PomFRIT's unforgeability has a 71-bit margin in H₂³
work. From A-OMPR⊕17 it has the full extraction margin.

We believe the 2^{−71} is an artifact. Choosing among ≤ 17 targets `{h ⊕ δ_a}` (whose
differences are fixed before `h`) after seeing `h` does not yield an extra preimage. Each forgery
still needs a preimage of a fresh, uniformly translated target, and `derive_preimage` answers each
target once, deterministically. But no proof of A-OMPR ⇒ A-OMPR⊕17 without the `τ^{ℓ+1}` loss is
known to us. The paper implicitly assumes the `E₁` that Lemma P supplies with this loss.

What Theorems U1/U2 do **not** need:
- ZK or simulated proofs. The Issuer returns only preimages. So unforgeability holds **on `main`**,
  regardless of `lean/docs/zk.md`'s finding.
- Strong SE. Plain simultaneous straight-line extraction suffices (L8 §8 table).

## 7. One-more unforgeability in the QROM

Q2 (Theorem 7.1) gives a straight-line extractor for a quantum prover's *final* proof:

    Pr[accept ∧ E fails] ≤ Σ² + ε_multi + ε_rec (+ ε_Sim).

What changes, and why the result does not lift:
1. **`E₁` is needed mid-run.** Both U1 (programming `H_T(x) := t_j ⊕ E₁(x)`) and U2 (submitting
   the shift set at query time) evaluate `E₁` *when `H_T` is queried*. Quantum `H_T` queries are in
   superposition, and Q2 explicitly "extracts nothing mid-run". Answering a superposition query
   with `t_{j(x)} ⊕ E₁(x)` would need two things:
   - a coherent evaluation of `E₁` on the compressed-oracle database;
   - a small-range or `2q`-wise-independent assignment `x ↦ j(x)` that avoids index collisions
     among the ℓ+1 forgeries.

   Neither is available. **QROM one-more unforgeability from A-OMPR is open.**
2. **What can be stated.** Formulate the τ-shift assumption *in the QROM*: the adversary itself
   has quantum access to `H_T`, and the shifts are the oracle-defined prefixes `r^{(i)}(x)`. Then
   Q2's post-run extractor, applied to each of the ℓ+1 outputs, gives

       Adv^{omuf} ≤ Adv^{A-OMPR⊕τ, QROM} + (ℓ+1)·(Σ² + ε_multi + ε_rec + ε_Sim).

   This assumption is close to restating the theorem for the UOV part, and should be read as a
   reduction of the VOLEitH part only.
   - The factor `(ℓ+1)` is a plain union.
   - Q2 does not show that the τ·(ℓ+1) post-run extraction measurements almost commute, so
     simultaneous extraction in the QROM is itself an open item.
3. **Q2's caps carry over.**
   - Meaningful only for `q_E ≲ 2^{37}` cipher queries (`ε_multi`) and `q ≲ 2^{55}` hash queries
     (the `200q²·2^{−128}` term is vacuous at `2^{64}`, inherently, by Grover on the grinding
     counter).
   - `ε_Sim`, an efficient extractor, is pending (Q4).

## 8. Blindness against a malicious Issuer

### 8.1 On `main`: fails (concrete)

`lean/docs/zk.md` §4. In the Def. 2.4 game, `A₁` uses an honest key, `A₂` answers both sessions honestly,
and `A₃` receives `(sig^0, sig^1)`. Then `A₃` does the following:
1. Compute `h_0 = H_T(dig(pk), chal1(sig^0), ũ(sig^0), d_pre(sig^0), µ_0)`. This is public
   (`pomfrit.cpp:96-111, 234`).
2. Set the guess `g := (t_first ⊕ h_0)[0..16)`. If `sig^0` came from the first session, then
   `g = r[0..16)` (`:173-176`).
3. Run Prop. 4.1's test on `sig^0` with guess `g`:
   - recompute the forced labels;
   - query `H₅` at the sibling labels `L^{γ_e}_e ⊕ d[0..λ) ⊕ g` for all ≈ 310 AND gates;
   - check that every `c_mult ⊕ h⁰ ⊕ h¹` row lies in `im(F)`.
4. Output `b' = 0` iff the test passes.

The test passes with probability 1 for the right session, and with probability `≤ 2^{−885}` for
the wrong one. The advantage is ≈ 1/2, i.e. `Pr[b' = b] ≈ 1`.
- No malicious behaviour is needed: the Issuer is honest-but-curious.
- The paper's own variant (borrowed `r`) very likely has the same flaw (`lean/docs/zk.md` §4), so the
  paper's blindness proof, which assumes black-box NIZK with uniform `w_r` (Def. 4.2), rests on a
  ZK property that this VOLEitH construction lacks.
- I did not re-run this attack. It is established in `lean/docs/zk.md` with Lean support (`attack_recovers`,
  `sibling_eq`).

### 8.2 Theorem B (with the label-row fix)

For every `A = (A₁, A₂, A₃)` in Def. 2.4, with oracle access and verifications, and with the
abort pattern revealed per session:

    |Pr[b' = b] − 1/2| ≤ ε_ZK^fix(Q_P = 2) + 2·Q_X·2^{−256} + ε_DS.

*Proof.* We use these games.
- **G0.** The real game with bit `b`.
- **G1.** For both sessions, replace `(rho, refresher, r) = XOF_seed(seed ‖ dig(pk) ‖ µ)` by
  independent uniform values.
  - The two games are identical unless `A` queries XOF_seed with a session's 32-byte seed, or the
    two seeds collide. The cost is `≤ 2Q_X·2^{−256}` (DS for independence from the other oracles).
- **G2.** Replace both proofs by simulated ones, `(Sim₁, Sim₂)` of `lean/docs/zk.md` §5 with the fix.
  This is a reduction to (ZK-fix) with `Q_P = 2`.
  - The reduction plays the Clients. At `Sig1` it gets π₁ from the ZK challenger for prefix `r`
    and binder `b₁ = H_ref(refresher)`.
  - It computes `h = H_T(dig(pk), chal1, ũ, d_pre, µ)`, sends `t = h ⊕ r`, and receives `s`.
  - Only if `P_pk(s) = t` (exactly the check at `:207`) does it request π₂ for instance `(pk, h)`,
    witness suffix `s` and binder `b₂ = refresher`. The witness then satisfies the relation, as
    the ZK theorem requires. Otherwise the session outputs ⊥, as in the real code.
  - The fixed proof system is ZK against a distinguisher that knows the whole witness `(r, s)`
    and chooses the instance adaptively after π₁ (`lean/docs/zk.md` §7.5, delayed instance). The secret
    `rho` stays internal to the prover. The cost is `ε_ZK^fix(2)`, whose `ε_lab` is now
    `(Q₅ + n_mult·Q_V + 2)·2^{−128}` instead of `lean/docs/zk.md`'s `Pred_R` term, which was ≈ 1 for
    PomFRIT on `main`.
- **G3: the view is independent of `b`.** In G2, `Sim₁` uses no witness, and `d_pre` is uniform.
  So for each session, `r` appears **only** in `t = h ⊕ r`. Since `r` is uniform and independent
  of everything else, `t` is uniform and independent of `h`, of π₁, and of the session's message.
  The rest of the view is as follows:
  - `(t_first, t_second)` are two independent uniform strings, in either order.
  - `A₂`'s responses are functions of these.
  - The abort pattern is `[P_pk(s_first) ≠ t_first]`, `[P_pk(s_second) ≠ t_second]`. These are
    functions of `A`'s own view (§8.3).
  - `(sig^0, sig^1)` are simulated proofs for `(pk, H_T(…, µ_0))` and `(pk, H_T(…, µ_1))`, plus
    uniform refreshers. They are computed from simulator coins, independent of which position
    each session occupied.

  So the joint distribution does not depend on `b`. ∎

**[Lean] `lean/VoleMole/Privacy/PomFRIT.lean`.** G1 → G3 on `Spec/PomFRIT.lean`'s `issueRequest`
and `finalizeIssue`, with `XOF_seed`'s output drawn uniformly (`issueRequest_eq`), for either proof
layout (`Spec/PomFRITLayout.lean`: `main`'s, and the label-row layout's 5579-byte proofs with `ũ`
and `d` at 3075 and 3139; at `Layout.main` the definitions are the spec's, by `rfl`):
- (ZK-fix) is the hypothesis `ZeroKnowledge P S ε`: a two-phase simulator (`phase1` from the
  binder, `phase2` from the instance `(pk, h)` chosen after phase 1) whose run is `ε`-close to the
  real run for every prefix `r`, binder and continuation picking `(pk, h, s, b₂)` with
  `P(s) = h ⊕ r`. The distinguisher may know `r` and `s`. **This hypothesis is false on `main`**:
  `ZK.issuerGuess_eq`, `ZK.pomfrit_issuer_hits`, `ZK.pomfrit_attack_test` (`lean/docs/zk.md`
  §4.1); it is what the label-row fix provides.
- G1 → G2 per session: `sessionClose_real_sim` (whatever the Issuer answers). G3 exactly, with no
  assumption: `simGame_eq` (the one-time pad `t = h ⊕ r`, then exchanging the two sessions'
  simulator coins and refreshers).
- `blindness`: `|Pr[A accepts | b = 0] − Pr[A accepts | b = 1]| ≤ 4ε`, i.e. `|Pr[b' = b] − 1/2| ≤ 2ε`,
  for every Issuer (key, messages, responses). The signatures are revealed only if both sessions
  complete; the Issuer computes the per-session abort pattern itself. The only other hypothesis is
  that phase 1 outputs a `PROOF_BYTES` buffer (`Correct.voleGen_length`).
- On paper: G0 → G1 (`2Q_X·2^{−256}`, Lemma DS) and, for an abstract prover, (ZK-fix) itself.
- **[Lean] (ZK-fix) for the executable prover** (`lean/VoleMole/Privacy/PomFRITLean.lean`,
  `ZK/TwoPhase.lean`, `lean/docs/zk.md` §10.1). The Lean prover with dedicated label rows, run as
  `issue_request_with_seed` / `finalize_issue` run it (`leanProver`: step 1 with `r` and
  `refresher_com`, step 2 for the instance `(pk, h)` and `s` the Client picks after step 1), is
  two-phase zero-knowledge against the simulator `leanSim` (`lean_zeroKnowledge`), under the
  two-phase tape hypothesis `TapeHyp2` (hybrids H1, H4, H6 and the grinding answers), which is
  derived from one hypothesis per hop (`ZK/TwoPhaseHops.lean`, `HopHyps2`:
  `ε = ε_rho + ε_grind + ε_abort + ε_bavc + ε_lab`; the random-oracle hops are proved for the
  hashed domain as a uniform table, `ZK/HopsROM.lean`); the completeness facts `BAVCComplete`,
  `CrtComplete` are proved for faest-arch-opt's tables (`blindness_lean`; `blindness_lean_shake`
  with the hop hypotheses). Step 1 reveals `c_i`, `c_mult`, `ũ`,
  `d[0..M)` and `chal1`; with label rows these are uniform and independent of `r` (one-time pads),
  so the simulator outputs them before the instance exists. `blindness_lean` is Theorem B (from
  G1) for this prover: `≤ 4ε`. On `main` the statement is false (`ZK/Relations.lean`).
  `pomfritVerify_complete_tables`: the final signature passes `verify`.
- **[Lean] Blindness in the random-oracle and ideal-cipher model** (`lean/VoleMole/Privacy/PomFRITRO.lean`,
  `ZK/TwoPhaseRO.lean`, `ZK/TwoPhaseIC.lean`, `ZK/TwoPhaseReadsRO.lean`; `lean/docs/zk.md` §10.2).
  Both sessions run the Lean prover on the same random tables (`H₂³` on every grinding point,
  `H₅` on every 37-byte input, the cipher of the BAVC and VOLE expansion; each session its own
  `H₃` slice), and the Issuer's guess sees all of them, reading `q₃` keys of each slice, `q₅` of
  `H₅`, `q_E` of the cipher and `H₂³` freely; its key, messages and responses do not read the
  tables; `hash_to_target`, `XOF_seed` (drawn uniformly, G1) and the refresher commitment stay
  SHAKE. The game is the spec's (`realSession` on `Layout.labelRows`).
  - The two-phase zero-knowledge theorem behind it (`zk2_rom_ic_h23_num`): the single-proof bound
    `q₃·2⁻¹²⁸ + 2⁻¹¹⁰ + 221·(4607 + q_E + 4607)·2⁻¹²⁸ + (q₅ + 1)·2⁻¹²⁸` holds for the two-phase run,
    with the simulator programming `H₂³` at the prefix it recomputes for the instance `(pk, h)`
    the Client picks after step 1, the fallback block (no accepted grinding answer) inside
    `Pr[GrindBad]`, and a continuation that may itself read `H₅` and the cipher (the Issuer
    answers after seeing both requests, and the other session's request reads the tables): its
    reads are added to `q₅`, `q_E`.
  - The hybrids: session 0 simulated (`hop0`), then session 1 (`hop1`, plus the collision term
    `δ(A)`: session 1, run for real, reads `H₂³` at a point session 0's simulator programmed);
    a session's step 2 is run only when both responses are valid (the signatures are revealed
    only then), so the simulators program symmetrically and the fully simulated games of the two
    worlds are equal (`G2_swap`: the requests are one-time pads, swapped between the positions).
    World 1 is world 0 for the Issuer with the sessions' roles exchanged (`realGameRO_true`).
  - **`blindnessRO_lean`**: `|Pr[A accepts | b = 0] − Pr[A accepts | b = 1]| ≤
    4·εRO(q₃, q₅ + 1248, q_E + 18428) + δ(A) + δ(A.swap)`, about `2⁻¹⁰³·⁴ +
    4·(q₃ + q₅ + 221·q_E)·2⁻¹²⁸ + δ(A) + δ(A.swap)`. On paper `δ ≲ 2⁻¹²⁸ + 2⁻¹¹⁰` (session 1's
    grinding prefix does not depend on session 0's simulated `ã₀`, the last field of the prefix
    session 0 programs at). Remaining modelling steps: SHAKE as a random oracle, AES as an ideal
    cipher (the cipher's rows are uniform functions: the PRP/PRF switching term is on paper),
    the two slices independent (distinct `r`), G0 → G1.

### 8.3 Selective failure, the response `s`, and the check at `pomfrit.cpp:207`

- **Abort.** `finalize_issue` returns `nullopt` iff `pk.eval(s) ≠ t`. The Issuer knows `pk`, `s`
  and the `t` it received, so it can compute the outcome itself. Revealing per-session aborts, in
  session order, therefore leaks nothing.
  - **Correction (found while mechanizing Theorem B):** an earlier version of this note said that
    Def. 2.4's "both ⊥" rule is then not needed. It is needed. Without it the Issuer answers one
    session correctly and the other with garbage, and the single signature it receives is on
    `µ_b` (it verifies only for its own message, §9.1), which reveals `b`. What leaks nothing is
    the abort pattern in session order; the signatures must be withheld unless both sessions
    complete, as in `Privacy/PomFRIT.lean`'s `outcome`.
  - Other aborts are not influenced by the Issuer, and their probability does not depend on `b`:
    - grinding overflow, `std::runtime_error`, probability `≈ (1−p)^{2^{32}}`, reproduced exactly
      by the simulator (`lean/docs/zk.md` `ε_abort = 0`);
    - `std::invalid_argument` for a different `pk`, which does not occur in the game.
- **Malicious key.** `pk` is arbitrary, and the ZK theorem holds for every statement. With a
  malformed key, `P_pk(s) = t` may be unsatisfiable. Then both sessions abort, which is again a
  function of the Issuer's view.
- **Choice of preimage.** The Issuer may pick any `s` in `P^{−1}(t)`, for example one with a
  planted pattern. With the fix, ZK holds against a distinguisher that knows `s`, so the pattern
  is invisible in σ. On `main`, knowing `s` is not even needed for the attack; `r` suffices.
- **The check is necessary.** Without `:207`, the honest prover would run on a non-satisfying
  witness. `lean/docs/zk.md`'s simulator assumes completeness identities (H3), which fail for false
  witnesses. Then a malicious `s` could make σ leak, for example via QuickSilver's response,
  which then depends on the violation. `:207` restores the precondition.

### 8.4 Refresher commitment and binders

`refresher` is uniform per session (G1). `refresher_com = H_ref(refresher)` is inside π₁, which
the Issuer never sees before σ. Both values are independent of `t` and `b`, and are given to `Sim`
as public binders (`lean/docs/zk.md` §7.5). They do not link.

### 8.5 Blindness in the QROM

`lean/docs/zk-qrom.md` is absent. The classical ZK proof programs H₂³ at points with a fresh 3λ+64-bit
prefix. A QROM version needs adaptive reprogramming (GHHM21) and a quantum treatment of the
lazy-sampled `H₅` siblings. G1 lifts directly (a query to an unknown 256-bit seed costs
`O(Q_X²·2^{−256})`), and G3 is information-theoretic. **Blindness in the QROM is open**, pending
`lean/docs/zk-qrom.md`.

## 9. Other properties

### 9.1 Binding of `msg` and `pk`

`msg` is the last field of `H_T`'s uniquely parsed input. So `σ` determines `h` per message, and
`mu(pk, h)` enters H₂².
- **Re-targeting** an honest σ to `msg' ≠ msg` changes `h`. This is L8 §7's delayed-instance case
  (α): every tree is pinned, so it succeeds with probability `2^{−128}` per H₂³ query.
- **Against the Client** (a holder of `(r, s)`), a valid σ on `msg'` needs a preimage of
  `H_T(…msg') ⊕ r'`. That is a one-more forgery (§6).
- **Cross-key:** `dig(pk)` is in `H_T` and in `mu`.

### 9.2 Malleability by third parties

L8 proves strong SE for the proof with binders, and `verify` checks `refresher_com = H_ref(refresher)`.
So, from honest signatures, no one can produce a *different* valid `(msg', σ')`. Changing a binder,
the counter, or the instance all fail (L8 §7). To use SE against parties who saw honest
signatures, one needs the real-to-simulated hop:
- On `main` this hop is valid for parties without `t` (`Pred = 2^{−128}`), but **not** for the
  Issuer or anyone colluding with it.
- With the fix it is valid for everyone.

### 9.3 Owner malleability: many signatures per issuance and message (finding F3, demonstrated)

The grinding counter `ctr` is an H₂³ input. The verifier accepts any `ctr` whose `Δ` has zero top
8 bits and opens successfully (`faest_sig.hpp:126-135`, `vector_com.inc:896-926`). The honest
prover returns the first such counter (`vector_com.inc:1056-1060`), but minimality is never
checked (`lean/docs/zk.md` §7.3).
- The Client knows every seed, so it can keep grinding and open at a second accepting `Δ`. This
  yields a second, distinct, valid σ on the **same** message, from the same Issuer response.
- Expected cost: about `2^8/Pr[open]` extra hashes per extra signature.
- Demo: `/tmp/claude-1016/-home-claude-scm-vole-mole/93cbb905-f2d6-4f97-8011-866bcdeb7a31/scratchpad/demo/ctr_malleability.cpp`
  (outside the repo). It runs one issuance with one `issue_response`, accepted counters 1398 and
  1740, and prints `verify(sig0)=1 verify(sig1)=1 distinct=1`.

Consequences:
- **Not** a break of Def. 2.5 (messages must be distinct) or of blindness. The extra signatures
  carry the same `π₁` and `h`, hence the same session.
- One-more *strong* unforgeability fails.
- Any application that deduplicates on σ, `H(σ)`, or the proof bytes can be double-spent by the
  token holder. Third parties cannot do this (§9.2).

Fix options:
- **Documentation:** say "deduplicate on msg" explicitly next to README's nullifier advice
  (`README.md:122-128`).
- **Code:** have `verify` reject a non-minimal counter. That costs the verifier up to `ctr`
  re-hashes and re-opening checks. It closes this route, but does not by itself give strong
  unforgeability against the owner.

### 9.4 Replay and one signature per message

`verify` is stateless. The same `(msg, σ)` verifies forever, and §9.3 gives more `σ` per `msg`.
The only sound single-use rule is the README's: put a nullifier in `msg` and store
**`msg` (or its nullifier)**. Unforgeability (§6) then bounds the number of distinct messages by
the number of issuances, plus one with negligible probability.

### 9.5 `detail::issue_request_with_seed` with a reused seed (`seeded.hpp:22`, `lean/docs/zk.md` §7.2)

Calling it twice with the same `(seed, pk, msg)` reproduces `(rho, refresher, r)`, hence the same
π₁ and the same `t`.
- **Honest Issuer.** `derive_preimage` is deterministic in `t`, so both runs yield the same `s`
  and an identical σ. This is harmless.
- **Malicious Issuer.** It returns two different preimages `s ≠ s'` (it holds `sk` and can sample
  many). The Client then completes one VOLE commitment twice:
  - `d[M..)` reveals `s ⊕ s'`;
  - the two openings at different `Δ, Δ'` reveal every hidden leaf whose `Δ_i ≠ Δ'_i`, which is
    almost all trees;
  - so `u`, hence `r` and `s`, are recovered;
  - so the Issuer links the signature to the session (via `t = h ⊕ r`), and ZK is void.

  Unforgeability is unaffected; this concerns the Client only.
- **Mitigations already present.** The public API draws a fresh 32-byte seed (`:183-185`), and
  `finalize_issue() &&` consumes the pending state.
- **Recommendation.** Restrict the hook to tests, or document "never reuse a seed".

### 9.6 Key separation (finding F5)

`derive_preimage` signs any target (`uov.hpp` WARNING). An Issuer key that is also used for UOV
signatures (`ov_sign`) or another protocol gives the adversary extra preimages, which count in ℓ.
A PomFRIT Issuer is also a universal UOV signing oracle for that key. So the Issuer key must be
dedicated to PomFRIT.

## 10. Assumptions, collected

1. **ROM and ideal cipher.** SHAKE as random oracles (proof and application hashes), and AES-128
   as an ideal cipher (for PoK) or a PRP (for ZK hiding, `lean/docs/zk.md` §8.1).
2. **Lemma DS.** The proof and application hash families are disjoint (in progress).
3. **UOV.** A-OMPR (paper Def. 3.1) for U1, or A-OMPR⊕17 for the tight U2. The Issuer key is used
   only for PomFRIT.
4. **PoK.** README theorem, L1–L7, simultaneous extraction (L8 §9.1), and the Lean lemmas
   `free_tree_holds_witness` and `extraction_cases`.
5. **ZK.** `lean/docs/zk.md` with the label-row fix (blindness only). `rho` comes from a fresh OS seed.
6. **Seed.** The OS RNG gives 32 fresh uniform bytes per `issue_request` (`random.hpp`).

## 11. What holds where

| | `main` | label-row fix |
|---|---|---|
| U1, U2 (classical one-more unforgeability) | ✓ | ✓ |
| QROM one-more unforgeability | open | open |
| Blindness, honest-but-curious Issuer | ✗ (practical linking) | ✓ (Thm B) |
| Blindness, malicious Issuer, malicious key, selective failure | ✗ | ✓ (Thm B, §8.3) |
| Blindness in the ROM + ideal cipher, Issuer seeing the tables (Lean prover) | ✗ | ✓ (`blindnessRO_lean`, collision terms on paper) |
| Blindness in the QROM | ✗ | open (`lean/docs/zk-qrom.md`) |
| Strong SE / no third-party mauling | ✓ against parties without `t` | ✓ against all |
| Owner re-randomization (§9.3) | present | present |

## 12. Gaps and open items

- **G1.** Is A-OMPR ⇒ A-OMPR⊕τ without the `τ^{ℓ+1}` loss? If so, U1 loses its `Q₃·2^{−71}`
  term. A protocol change that pins `r` to π₁ would also remove it, but none was explored here.
- **G2.** QROM unforgeability (§7) needs mid-run extraction, or a different reduction. QROM
  simultaneous extraction from ℓ+1 proofs is not covered by Q2.
- **G3.** Blindness depends on the label-row fix being implemented as described (dedicated rows,
  `Θ` uniform and witness-independent) and on `lean/docs/zk.md`'s theorem being re-checked for it. The
  paper's App. B.3 ZK argument should not be relied on (§8.1).
- **G4.** Lemma DS is assumed.
- **G5.** The probabilistic steps of Lemma P (the "fixed before the answer" argument and the
  union) are on paper. The deterministic steps are in Lean.
- **G6.** The 2^{−71} uses the FAEST-EM-128f tree shapes. For other parameter sets, recompute it
  as `2^{−(λ − max_{S,T disjoint, Σ_S ≤ Σ_T} Σ_S)}`.

## 13. Lean

`lean/VoleMole/Protocols/PomFRIT.lean` has no `sorry` and no `axiom`. Check it with
`cd lean && lake env lean VoleMole/Protocols/PomFRIT.lean`.

| Statement | Lean |
|---|---|
| Coordinates outside `G` fixed ⇒ `|A| ≤ ∏_{i∈G} |B_i|` | `card_le_prod_of_fixed` |
| A tree differing from `u*` on any row is fixed (Claim 4) | `fixed_of_prefix_ne` |
| Trees outside `u*`'s prefix group are fixed; `|A|` bound | `fixed_outside_prefixGroup`, `card_le_prod_prefix_group` |
| Widths (8, 7×16) sum to 120 | `width_total` |
| Disjoint `S, T` with `Σ_S ≤ Σ_T` ⇒ `Σ_S ≤ 57` | `minority_weight_le` |
| Minority prefix group ⇒ `|A| ≤ 2^{57}` | `minority_card_le` |
| `2^{57}/2^{128} ≤ 2^{−71}`; loss at `2^{50}`, `2^{64}` | `per_query_bound`, `loss_at_2_50`, `loss_at_2_64` |
| Blindness (Thm B, from G1) under (ZK-fix) as a two-phase hypothesis: `≤ 4ε` between the worlds, for either proof layout (`lean/VoleMole/Privacy/PomFRIT.lean`) | `blindness` |
| (ZK-fix) for the executable Lean prover with label rows, from the two-phase tape hypothesis; blindness with that prover; completeness of `verify` on the final signature (`lean/VoleMole/Privacy/PomFRITLean.lean`) | `lean_zeroKnowledge`, `blindness_lean`, `pomfritVerify_complete` |
| G1 → G2 for one session; G3 exactly (one-time pad, then a swap of the sessions' simulator coins) | `sessionClose_real_sim`, `simGame_eq` |
| Two-phase zero knowledge in the ROM and ideal-cipher model with `H₂³` visible, the continuation reading the tables (`lean/VoleMole/ZK/TwoPhaseRO.lean`, `ZK/TwoPhaseIC.lean`, `ZK/TwoPhaseReadsRO.lean`) | `zk2_rom_ic_h23`, `zk2_rom_ic_h23_num`, `zk2_ro`, `lean_zeroKnowledgeROS2` |
| Blindness in the ROM and ideal-cipher model, both sessions on shared tables, the Issuer's guess seeing them (`lean/VoleMole/Privacy/PomFRITRO.lean`) | `blindnessRO`, `blindnessRO_lean`, `hop0`, `hop1`, `G2_swap`, `realGameRO_iff` |
