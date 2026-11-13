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

**Which code.** "`main`" in this note is the code before `64fd1a4` (`6d7113e`), on which the
Issuer's attack works. Since `64fd1a4` `main` gives PomFRIT the dedicated label rows (+256 bytes per
signature): the column "With the label-row fix" below is current `main`, blindness holds there,
and the attack column describes the earlier code (`ZK.pomfrit_issuer_hits` is a theorem about
that layout, `Spec/PomFRITLayout.lean`'s `Layout.main`).

The note builds on these proof-system results:
- the classical straight-line proof of knowledge `ε_ext` (`lean/docs/extraction/README.md`, main theorem and
  §Assembly);
- strong simulation-extractability (`lean/docs/extraction/L8-simulation-extractability.md`);
- arithmetization soundness, i.e. that the constraints force `P(s) = h + r` (`lean/docs/extraction/L7-uov.md`);
- zero knowledge (`lean/docs/zk.md`) and its fix (dedicated label rows, on `main` for PomFRIT since
  `64fd1a4`);
- the QROM proof of knowledge (`lean/docs/extraction/Q2-qrom-fiat-shamir.md`).

The combinatorial core of the new lemma (Lemma P) is checked in Lean, in
`lean/VoleMole/Protocols/PomFRIT.lean`, and so are its per-chain step and its extraction bound in
the random-oracle and ideal-cipher model, with the `Shift` term (`lean/VoleMole/ROM/LemmaPDet.lean`,
`ROM/LemmaP.lean`, §5). The reductions of Theorems U1 and U2 (the game, the programming of
`hash_to_target`, the one-more preimage experiments) are checked in Lean, in
`lean/VoleMole/ROM/OneMore.lean` (generic) and `lean/VoleMole/ROM/OneMorePomfrit.lean`, with
Lemma P's failure probability as an explicit term (§6.4). For Theorem U1 that term is bounded in
Lean too, every term explicit (`ROM/OneMoreLemmaPBound.lean`, `prEvent_pfail_le`,
`pomfrit_U1_explicit`, §6.4), and with simultaneous extraction, each query of the forger's run
charged once (`ROM/OneMoreLemmaPSim.lean`, `pomfrit_U1_sim`). For Theorem U2 it is bounded the
same way, without Lemma P's `2⁻⁷¹` term (`ROM/OneMoreShiftBound.lean`, `pomfrit_U2_explicit`;
`ROM/OneMoreShiftSim.lean`, `pomfrit_U2_sim`; §6.4 item 10).

Line references are to the working tree at commit `6d7113e`.

## 0. Verdict

| Property | On `main` | With the label-row fix | Section |
|---|---|---|---|
| One-more unforgeability (paper Def. 2.5), classical ROM + ideal cipher | **Holds.** Tight under a τ-shift variant of UOV one-more preimage resistance (Thm U2). Under the paper's standard assumption (Def. 3.1) the reduction loses an extra `(Q₃+ℓ+1)·2^{−71}` (Thm U1). [Lean] the game, the programming of `hash_to_target` and the reductions to Def. 3.1 and to A-OMPR⊕τ, with Lemma P's failure probability as an explicit term (`ROM/OneMorePomfrit.lean`, `pomfrit_U1_bound`, `pomfrit_U2_bound`; §6.4). For U1 that term is bounded too, with simultaneous extraction: `Pr[PomWin] ≤ Adv^{ompr} + pfailSimEps` with every term explicit, the forger's queries charged once (`pomfrit_U1_sim`, `pomfrit_U1_ompr_sim`; the union over forgeries, `(ℓ+1)·pfailEps`, is `pomfrit_U1_explicit`); for U2 likewise, with no `2^{−71}` term: `Pr[PomWin] ≤ Adv^{ompr⊕17} + sfailSimEps`, `2⁻⁶²` at `2⁶⁴` queries and `ℓ = 2³⁰` (`pomfrit_U2_sim`, `pomfrit_U2_omprShift_sim`; union: `pomfrit_U2_explicit`) | Same (ZK is not used) | §5–§6 |
| One-more unforgeability, QROM | **On paper, under new quantum-oracle assumptions** (U1-Q, U2-Q of `lean/docs/extraction/Q7-qrom-multi-extraction.md` §4: database-controlled programming replaces the mid-run extractor). From the paper's A-OMPR with the classical reduction: open, since Q2 extracts only after the run | Same | §7 |
| Blindness against a malicious Issuer (paper Def. 2.4: malicious key, selective-failure form) | **Fails.** An honest-but-curious Issuer links with advantage ≈ 1 using about 310 SHAKE calls per (signature, session) pair (`lean/docs/zk.md` §4) | **Holds** (Thm B), with advantage `≤ ε_ZK^fix(Q_P = 2) + 2Q_X·2^{−256}`. [Lean] from G1 with (ZK-fix) as a hypothesis (`Privacy/PomFRIT.lean`, `blindness`), and with (ZK-fix) derived for the executable Lean prover with label rows down to its tape hypothesis (`Privacy/PomFRITLean.lean`, `blindness_lean`). In the ROM and ideal-cipher model, for the Lean prover with the Issuer seeing the tables and every term explicit: `≈ 2⁻¹⁰³·⁴` plus budget terms (`blindnessRO_lean_num`), `≈ 2⁻¹⁰³·²` with the Issuer's key, messages and responses reading the tables except `H₂³` (`blindnessRA_lean_num`), `≈ 2⁻¹⁰²·³` with them reading `H₂³` too (joint budget, `blindnessRAH_lean_num`); each also with AES as random permutations (`_perm`), with one shared `H₃` and no `2⁻³⁶⁰` term (`blindnessSh_num`, `blindnessRASh_num`, `blindnessRAHSh_num`), and from the real Clients' OS seeds and `XOF_seed` (G0), `+ 2·(2Q_X + 1)·2⁻²⁵⁶` (`blindness*_seed`). With many sessions (`lean/docs/zk.md` §10.8), each plus budget terms: `n` sessions in one concurrent schedule `≤ n·2⁻¹⁰³` (`blindnessN_lean_le`; `2⁻⁸³` at `2²⁰`, `2⁻⁷¹` at `2³²`), adaptively scheduled `≤ n·2⁻¹⁰²` (`blindnessAd_lean_le_pfx`, the collision term counting `H₂³` prefixes; `2⁻⁸²` at `2²⁰`, `2⁻⁷⁰` at `2³²`; `n·2⁻⁹²` counting keys, `blindnessAd_lean_le`), interleaved, the Issuer starting further sessions and answering them in any order, `≤ (n + 2)·2⁻¹⁰²` for `n` further sessions (`blindnessIL_lean_le`; the same numbers), also with a scheduler that reads the tables and places the challenge itself, `+ 52·L·(a₃ + a₂ + a₅ + 221·a_E)·2⁻¹²⁸` for `L` steps of at most `a` queries each (`blindnessILO_lean_le`), `N` challenge pairs `≤ N·(2N·2⁻¹⁰³ + …)` (`blindnessP_lean_le`) and, with `H₄` a random-oracle table, `≤ N·2⁻¹⁰³ + 32·N²·2⁻¹²⁸` (`blindnessPH_lean_le`; `2⁻⁸³` at `2²⁰` sessions, `2⁻⁶⁰` at `2³²`). Formulas: §8.2; theorem names: §13 | §8 |
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
  - D1 does not remove the paper's multi-tree ambiguity (F1); D2's binding of `ũ` does, up to an
    efficient extractor (`pomfrit-lemmap-tight.md`). In both designs, `r` is
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
    `τ^{q+1}` (guessing), and no attack that uses the choice of shift and gains at τ = 17 (§6.3; collinear shifts,
    `ompr-shift-algebra.md` §4.1: at most `τ = 2^4.1`, below break-even in the reference model).
    Attacks that use the `D` oracle are in `ompr-cryptanalysis.md`: none beats the direct forgery
    attack, for either assumption.
- **(PoK)** The README's classical extraction theorem, with simultaneous extraction (L8 §9.1), and
  L7 for the relation. [Lean] for one proof, classical, in the random-oracle and ideal-cipher
  model, for any family of signatures and messages: the decoded `(r, s)` satisfy `P(s) = h ⊕ r` on
  bytes for the target `h` at the verifier's `chal1` except with the bounds of
  `lean/VoleMole/ROM/SpecSound.lean` (`pomfritRedeem_accept_le_full_spec`,
  `pomfritRedeem_accept_le_adaptive_spec`, …).
- **(ZK-fix)** `lean/docs/zk.md`'s theorem with the label-row fix, as standard adaptive two-phase NIZK
  (the distinguisher may know the whole witness):

      ε_ZK^fix(Q_P) = ε_rho + ε_prog + 2ε_hide + ε_lab + ε_iv,   ε_lab = (Q₅ + n_mult·Q_V + Q_P)·2^{−128},

  with the other terms as in `lean/docs/zk.md` §3, and `n_mult ∈ [305, 312]`.
  - Assumed here; it holds on `main` since `64fd1a4`, which gives PomFRIT the dedicated label rows.
  - Requirements: `rho` uniform and secret, and an honest prover on a satisfying witness.
  - Multiple sessions may interleave their phases. `lean/docs/zk.md`'s hybrids are per proof and
    order-independent; in Lean, interleaved further sessions are covered by
    `blindnessIL_lean_le`, and with a table-reading scheduler that also places the challenge
    (its start and the step at which its answers are taken) by `blindnessILO_lean_le`
    (`lean/docs/zk.md` §10.8).
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

**In Lean** (`ROM/LemmaPDet.lean`, `ROM/LemmaP.lean`; §6.4 for the one-more game).
- Steps 3–7 per chain: `extract_or_major` (generic), `pomfritT_extract_major_chain` (the
  executable verifier's chains). If every tree outside a set `S` is fixed on the accepting set, some
  tree of `S` in the widest prefix group of `S` (`majP`, ties by least index) has a candidate in the
  relation, or at most `2⁵⁷` admissible `chal3` are accepted.
- Steps 1–8 for one adaptively chosen statement: `pomfritT_accept_le_major`. The prover outputs a
  proof and the index of its statement `pomfritRedeemT pk (hF s) (b₁F s) (b₂F s)`, whose target is
  any function `hF s` of `chal1` (for the one-more game, the answer of `H_T`). The verifier accepts
  and no fully alive tree (`aliveR`: no committed dead leaf at the first `H₂¹` preimage of `chal1`
  in the prover's log) of the widest group has a candidate `(r, σ)` with `P(σ) = h(chal1) ⊕ r`
  (`MajorExtracted`) with probability at most the bound of `pomfritRedeem_accept_le_adaptive`
  with the `H₂³` term `(Q₃+1)·2⁵⁷·2⁻¹²⁸ = (Q₃+1)·2⁻⁷¹` in place of `(Q₃+1)·2·2⁻¹²⁸`. This is
  Lemma P with `E₁` evaluated at the end of the run.
- The ordering step for the one-more game (`ROM/OneMoreLemmaPOrder.lean`, `e1P_eq_major`): `E₁`
  computed at `x`'s first `H_T` query (`e1P`) is the widest group's prefix of the alive trees at the
  end, with the extractor's candidates, if the verifier's `H₂¹` input was queried before `x`;
  otherwise the `H₂¹` answer at that input hits the `chal1` field of the reduction's earlier marker
  query `H₃(x)` (an order hit, `≤ 2⁻¹⁰⁸⁸` per pair of queries), §6.4.

**Tightness of 2^{−71}.** Take seven 7-bit trees plus the 8-bit tree (width 57) against nine
7-bit trees (width 63). Completing with the minority prefix costs about `2^{71}/Pr[open]` H₂³
calls. So the term is tight up to the opening-success factor.

**Can it be tightened?** `pomfrit-lemmap-tight.md`. In short: the term is tight for `E₁` and for
every extractor that does not read `ũ` (there: A1, A2). But `hash_to_target` binds `ũ` (D2), and
`ũ` determines the prefix group up to `2⁻¹³⁴` per `H₂¹` query (Theorem D, Lean
`Seed/KOSUnique.lean`, `witness_determined`). For first messages whose trees agree on the label
rows an efficient extractor has no `Shift` at all (Theorem L). For the others the group hides in
a slice of the challenge space. There (§6 of that note): any two challenges of one slice with the
same check value certify the witness (Lean `slice_collision_sound`).

**Lemma P^cls (`pomfrit-lemmap-tight.md` §6A; paper, with a mechanized per-chain core).** `E₁`'s
default is the wrong one. An accepting set lies in a slice of one *class* (alive trees with the
same witness and label rows), or it has at most `2^{⌊w/2⌋}` points for the width `w` of its prefix
group. The extractor `E₁^cls` outputs the prefix of the widest class; if a second class of width
`≥ 51` has another prefix (then at most one tree is left over), it first runs a decoder
`Dec^cls` (fewer than `2¹⁵` linear systems of 512 equations in at most 64 unknowns) and outputs
that class's prefix if the decoder finds two challenges of one of its slices with the same check
value. Lemma P holds for `E₁^cls` with

    Pr[Shift^cls] ≤ q₁·2^{−134} + (Q₃ + n_out)·2^{−78} + Q_T·q₁·2^{−704},

with no conjecture and no property of `H₅` (`2⁻⁷⁹` for `2²²` systems, `2⁻⁸⁵` for `2³⁶`). In Lean:
the per-chain step `class_or_small_dec`, `extract_or_class` (`ROM/LemmaPClass.lean`,
`Seed/SliceDecode.lean`), with the structure of the CRT masks on slices as hypotheses (read off
the code; proved for a gate model). Not in Lean: these hypotheses for the executable verifier, and
the one-more game with `E₁^cls`. So **the mechanized Lemma P and U1 below keep `2⁻⁷¹`**; the
`2⁻⁷⁸` is Theorem U1^cls of that note, a paper theorem.

## 6. One-more unforgeability (classical)

*Status.* The reductions below are mechanized (§6.4): the game, the programming of `H_T`, the
counting and the union over the `ℓ+1` forgeries, with the advantage against Def. 3.1 (or
A-OMPR⊕τ) and Lemma P's failure probability as explicit terms. Lemma P's extraction and `Shift`
bound is in Lean for one adaptively chosen statement with any target function (§5), and joined to
the one-more game for Theorem U1, so U1 is in Lean with every term explicit (§6.4,
`pomfrit_U1_explicit`), also with simultaneous extraction (`pomfrit_U1_sim`). Theorem U2 is in
Lean with every term explicit too, from Lemma P without `Shift` (§6.4 item 10, `pomfrit_U2_explicit`,
`pomfrit_U2_sim`).

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
work. From A-OMPR⊕17 it has the full extraction margin. With the class extractor
(`pomfrit-lemmap-tight.md` §6A, Theorem U1^cls; paper, the per-chain step in Lean) the term is
`(Q₃ + ℓ + 1)·2^{−78} + q₁·2^{−134}`: `2^{−28}` at `Q₃ = 2^{50}`, `2^{−14}` at `2^{64}` (Lean
`loss_cls_at_2_50`, `loss_cls_at_2_64`), for a reduction that solves fewer than `2¹⁵` small
linear systems per `H_T` query.

We believe the 2^{−71} is an artifact. Choosing among ≤ 17 targets `{h ⊕ δ_a}` (whose
differences are fixed before `h`) after seeing `h` does not yield an extra preimage. Each forgery
still needs a preimage of a fresh, uniformly translated target, and `derive_preimage` answers each
target once, deterministically. But no proof of A-OMPR ⇒ A-OMPR⊕17 without the `τ^{ℓ+1}` loss is
known to us. The paper implicitly assumes the `E₁` that Lemma P supplies with this loss.
`pomfrit-lemmap-tight.md` §4 makes "artifact" precise for the code: after its `H_T` query the
forger has no choice of prefix left; the loss is the reduction's cost of not finding it.

What Theorems U1/U2 do **not** need:
- ZK or simulated proofs. The Issuer returns only preimages. So unforgeability holds **on `main`**,
  regardless of `lean/docs/zk.md`'s finding.
- Strong SE. Plain simultaneous straight-line extraction suffices (L8 §8 table).

### 6.4 In Lean

`lean/VoleMole/ROM/OneMore.lean` (generic, protocol-independent) and
`lean/VoleMole/ROM/OneMorePomfrit.lean` (PomFRIT), classical random-oracle and ideal-cipher model
(the cipher a random function per key, the PRF view of `ROM/CipherGame.lean`).

**The game** (`game`). A key from any key generation and any Issuer function `pre sk`; the honest
Issuer is `honestPre` (`derive_preimage` on the target's 45 bytes). The forger (`Forger`) gets the
public key and queries the proof system's hashes and the cipher, `H_T` and the Issuer. Then each of
its `ℓ+1` forgeries `(msg, sig)` is verified as `pomfritVerify` does, with `H_T` in place of
`hash_to_target` (`verOne`: the refresher check, the verifier up to `chal1`, `H_T` at
`hash_to_target`'s input `tgtIn`, then `verifyQ` at the statement whose target is `H_T`'s answer,
`pomfritRedeemT`; with SHAKE128 for `H_T` this is `pomfritRedeem`, `pomfritRedeem_eq_T`,
`pomfritTarget_eq_tgtIn`). The forger wins (`PomWin`) if all `ℓ+1` verify, the messages are
pairwise distinct, and it made at most `ℓ` Issuer queries.

**Modelling choices.**
- `H_T` is a lazy random oracle whose fresh answers are drawn from a list of `n` uniform targets,
  in order. For a forger with at most `Q_T` `H_T` queries and `n = Q_T + ℓ + 1` (the paper's `n`),
  the list never runs out (`acomp_bound`, `noFall_of_bound`), so it is a random oracle.
- Def. 3.1 is stated with *labelled* targets requested one at a time (`omExp`, `goodPre`): each
  request names a label `x` and receives the next of `n` uniform targets; the win is `ℓ+1`
  preimages of targets with distinct labels after at most `ℓ` preimage queries. An adversary of
  Def. 3.1 as written (`t_1 … t_n` up front) simulates the request oracle by taking the targets in
  order, with the same win. A-OMPR⊕τ is the same experiment with the shift list sent with each
  request (`goodShift τ`).
- The reduction's coins (including the cipher table) and the random oracle it simulates for the
  forger are part of the experiment adversary (a uniform sample and random-oracle access that no
  one else uses). Running times are not modelled.

**The reduction** (`red`). The forger, wrapped so that every `H_T` query carries a *hint* computed
from the forger's query log so far (`wrapImpl`: U1 the first-phase value `E₁(x)`, U2 the list of
at most `τ` shifts), and its verifications, are run with the world and the Issuer forwarded; a
fresh `H_T` query `x` with hint `e` requests the next target `t` for label `x` and answers
`t − E₁(x)` (U1) or `t` (U2). The forger never sees a hint. Programming is perfect
(`real_eqd_comb`: by induction over the computation, the bijection `t = u + e` at each fresh
query). If the forger wins and every forgery's claim (the first extracted candidate `s` that is a
preimage of the programmed target) is good, the reduction wins (`omuf_good_le`). Accepted
forgeries on distinct messages have distinct `H_T` inputs, because the fields before `msg` have
fixed lengths once the proof has the right length (`tgtIn_inj`, `acomp_support`): the paper's
"the `x_i` contain `msg_i`, so they are distinct" needs the format check.

**The theorems** (`pomfrit_U1_bound`, `pomfrit_U2_bound`; without the query bound, with the list's
exhaustion folded into the last term, `pomfrit_U1`, `pomfrit_U2`):

    Pr[PomWin] ≤ Adv^{ompr}_{UOV}(B; Q_T + ℓ + 1, ℓ) + Pr[∃ i ≤ ℓ, PFail_i],
    Pr[PomWin] ≤ Adv^{ompr⊕τ}_{UOV}(B'; Q_T + ℓ + 1, ℓ) + Pr[∃ i ≤ ℓ, ShiftFail_i],

for every first-phase rule `E₁` (a parameter, `e1`) and every shift rule (`sh`, truncated to `τ`).
The first term is the standalone OMPR game of `Assumptions/UOV.lean` (`advOMPR`, labelled targets
on demand; `pomfrit_U1_ompr`, `pomfrit_U2_omprShift` restate the theorems with it), and it is at
most Def. 3.1's advantage, targets given up front, of an explicit adversary that pops them
(`advOMPR_le_ompr31`).
`PFail_i`: forgery `i` verifies, but its claim is not a preimage of `H_T(x_i) + E₁(x_i)`, with
`H_T(x_i)` the oracle's value and `E₁(x_i)` the value at `x_i`'s *first* `H_T` query (the one the
reduction programmed). The claim is the first candidate of the straight-line extractor's known
trees that is a preimage of the target computed from the answer the verification received (`pick`);
that answer is the oracle's value, so `PFail_i` says that no extracted candidate is such a preimage
(this consistency is by construction of the lazy oracle and is not a separate Lean lemma).
`ShiftFail_i`: the same with "a preimage of `H_T(x_i) + δ` for one of the shifts `δ`".

**The converse, and the two assumptions** (`lean/VoleMole/Assumptions/Blind.lean`,
`Assumptions/Shift.lean`; `uov-assumptions.md` §5.6, §6).

The converse of U1 is mechanized as a generic core (`ompr_le_blind`). In the same one-more game
(`omuf`, targets `H_T(x) + r`), the blinding forger of any client with distinct session labels
satisfies `Adv^{ompr}(B; n, ℓ) ≤ Pr[Forges] + Pr[CompFail]`. `CompFail` is a completeness failure
of the client's finishing phase. With U1 this is the equivalence PomFRIT ⇔ OMPR, up to Lemma P's
term and the completeness term.

**The PomFRIT instance** (`lean/VoleMole/Assumptions/BlindPomfrit.lean`). It is stated in
PomFRIT's real one-more forgery game, for a forger with coins:

- *The game* (`gameB`) is `game` for a forger with a `ProbComp` layer of coins and its own random
  oracle (`ForgerB`); the verification is `verAll`, unchanged. For a forger without coins it is
  `game` (`gameB_liftF`, the same `Pr[PomWin]`).
- *The client* (`PomClient`) is any PomFRIT client given as oracle computations over the hashes
  and the cipher: step 1 of session `k` for the message `msgOf k` (step-1 signature bytes,
  `chal1`, a state) and the final signature from the state, the `H_T` answer and the Issuer's
  response. Session `k`'s label is `tgtIn` for its message; distinct sessions have distinct labels
  (`label_ne`, from `tgtIn_inj`), so `ompr_le_blind`'s hypothesis is a theorem.
- *The forger* (`blindForger`) runs `B`, answers `B`'s `k`-th target request by step 1 of session
  `k` and the `H_T` answer at its label, forwards `B`'s preimage queries to the Issuer, and outputs
  the claimed sessions' signatures. Its blinding is `0`: the forger is an adversary and need not
  blind, and the relation `P(s) = H_T(x) ⊕ r` holds with `r = 0`. It makes at most as many `H_T`
  queries as `B` makes target requests (`blindForger_bound`).

Then (`pomfrit_T6`), for every OMPR adversary `B` and every client,

    Adv^{ompr}(B; n, ℓ) ≤ Pr[PomWin(blindForger)] + compFail,

`PomWin` in `gameB` with the programmed target equal to the `H_T` answer (`addHint`, hint `0`),
and `compFail` the probability that `B`'s claims are `ℓ + 1` preimages of distinct sessions'
targets within `ℓ` Issuer queries but the client's signatures do not all pass `pomfritVerify`
(with `H_T` the oracle). For `B` with at most `Q` target requests the game has `Q + ℓ + 1`
targets, U1's convention (`pomfrit_T6_bound`, with `advOMPR_pad`: unused targets do not matter).
The proof: `ompr_le_blind` for the client as a `Blind.Client` (`toClient`: coins are the cipher
table and the client's coins; its state carried across sessions is the game wrapper's log, so
that `start` also makes the reduction's own logged queries at each label, `auxSpec`, exactly as the
wrapper does; `post` finishes the claimed sessions and runs PomFRIT's verification at the final
log), and the blind game and `gameB` have the same key, flag and final state (`projF_eqd`), since
the two composed adversaries have the same flag as oracle computations (`star`). `Blind.Client`
has a carried state for this reason: `auxSpec` reads the log of all sessions so far.

**The Lean client** (G9, closed). The client is the Lean prover run as `issue_request` /
`finalize_issue` with witness prefix `0` (`leanClient`, `lean/VoleMole/Assumptions/PomClientLean.lean`),
with its hashes and cipher evaluations as queries (`ROM/ProverIC.lean`: `step1Q`, `proveCommitQ`).
Per table it is the executable prover (`eval_start`, `eval_finish`: `Prover.voleGen`,
`Prover.proveCommit` with the hashes of the table and the ideal-cipher PRG). Then
`compFail ≤ (ℓ+1)·2^{−113}` (`compFail_le`), so (`pomfrit_T6_lean`,
`Assumptions/BlindPomfritT6Lean.lean`)

    Adv^{ompr}(B; n, ℓ) ≤ Pr[PomWin(blindForger (leanClient …) n B)] + (ℓ+1)·2^{−113},

and `pomfrit_T6_lean_bound` with `B`'s target budget `Q` and `Q + ℓ + 1` targets. The proof
(`Assumptions/BlindPomfritComplete.lean`): for fixed key, coins and target stream the game is the
lazy random oracle's run of one computation; at every table, if `B` wins and the flag is `false`,
then the `H₂³` answers at the grinding prefix of one of the `ℓ+1` claimed sessions are `GrindBad`
(`fail_table`: `B`'s phase keeps each session's answer cached at its label with hint `0` and its
state the client's step 1, `InvH`; the finishing phase does not change cached entries, so the
claims' targets are the sessions' answers; outside `GrindBad` each signature verifies, `verOne_ok`,
from `pom_complete`, `chal1Pre_honest`, `tgtIn_final`). Each claimed session's prefix is computed
without `H₂³` queries (`allQ_pfxB`), so its `2³²` grinding answers are fresh and bad with
probability `≤ 2^{−113}` (`prEvent_grindBad_le`, `Assumptions/BlindPomfritGrind.lean`). Assumed of
`B` besides `pomfrit_T6`'s: its random oracle has finite nonempty answer types. The Issuer's
`derive_preimage` abort does not enter: `compFail` is conditioned on `B`'s claims being preimages.

U2's assumption relates to U1's in both directions:
- A-OMPR⊕τ implies A-OMPR tightly (`advOMPR_le_shift`).
- A-OMPR implies A-OMPR⊕τ with loss `τ^{ℓ+1}` (`advOMPRShift_le_guess`, guessing the shift of each
  request).

**Lemma P's term** (`ROM/LemmaP.lean`, `ROM/OneMoreLemmaP.lean`; G8). The target is
`Pr[∃ i, PFail_i] ≤ ε_ext(N; q₁, q₂, Q₃ + ℓ + 1) + (Q₃ + ℓ + 1)·2^{−71} + Q_T·q₁·2^{−704}` (for U2
without the `2^{−71}` term). Mechanized first as a union over the `ℓ + 1` forgeries (items 1–8),
then with simultaneous extraction (item 9), and for U2 (item 10). Mechanized:
- *(1) The extraction bound for a family of target functions* (`pomfritT_accept_le_major`, §5):
  the adaptive bound of `ROM/AdaptPomfrit.lean` for `pomfritRedeemT` with any target function,
  with Lemma P's goal (the widest group of the alive trees extracts) and `Shift` (`2⁵⁷` accepted
  `chal3` per `H₂³` query when the free tree is in a minority group). The bound reads the target
  only through the `H₂⁰` preimage of the delayed `μ` (`target_eq_of_muInD_T`).
- *(2) The game as a lazy random oracle and the derived provers, table by table*
  (`ROM/OneMoreLemmaP.lean`). For a fixed key, cipher table and target stream, the game's run is
  the lazy random oracle's run of one hash computation (`realImpl_run_eq`). The forger with the
  cipher as queries gives, table by table, the game's forgeries, log and target answers
  (`eval_forger`, `eval_forgerP`; the answers do not depend on the hints, `tStep_sameT`). A failed
  forgery (`PFail_i`) is, at the same tables, an accepted proof of the derived prover `proverI … i`
  (the forger and the reduction's verifications up to forgery `i`) from which no extracted
  candidate decodes to a preimage of the programmed target (`pfail_table`). Lemma P's goal, with
  every alive tree known and the hint equal to the widest group's prefix, contradicts that
  (`not_noPick`). The random-oracle consistency the earlier text asked for is by construction: the
  answer a query receives is the table's entry, which later steps keep (`eval_htW_persist`).
- *(3) `E₁`*: `e1P` is Lemma P's `E₁` as a function of the log at the target query: the first
  `H₂¹` preimage `x₁` of the input's `chal1`, the data committed at `x₁` (`preCore`), the alive
  trees and the widest group's prefix of their candidates `u ⊕ d`. It needs `iv` at query time:
  the reduction now makes its own hidden queries at each target query (`auxSpec`: `mu₁`, `iv`, and a
  marker `H₃(x)` that records `x` in the hash log), as the paper's `B` may.

- *(4) A derived prover that reads the cipher only by queries* (`ROM/OneMoreLemmaPIC.lean`,
  `proverP … i`): the forger with a void hint (the target answers do not depend on the hints), the
  earlier forgeries' verifications up to their target queries and forgery `i`'s, with `chal1`
  through cipher queries (`chal1PreIC`, as `verifyIC`). It outputs forgery `i`'s proof, its
  statement index and, as auxiliary output, its `H_T` input `x` and the *ghost log* of `x` (the log
  at `x`'s first target query, with the reduction's queries). Per table it outputs `proverI`'s proof
  and statement, and the hint the game stored at `x` is `E₁` at the ghost log (`eval_proverP`);
  its joint log is the forger's log `L` followed by the verification queries `V` (`log_proverP`),
  and every ghost log is a prefix of `L` followed by the reduction's queries, or `L` itself followed
  by them (`aux_proverP`). `V` has no `H₂²` and no `H₂³` query (`not_mem_hashLog_contP`).
- *(5) The extraction from `L` is the derived game's* (`ROM/OneMoreLemmaPIdent.lean`): without
  chain hits the verifier's `H₂¹`, `H₂²`, `H₂³` inputs are queried in this order, so if the `H₂³`
  input is in `L` so is the `H₂¹` input (`mem_x_of_mem_z`); then, without Post (`KeysPre`), every
  commitment the extractor looks up is committed at that input and its key is found before it, and
  the extractor finds the same key in `L` as in `L ++ V` (`keysOf_knownOf_prefix`). The alive trees
  are known (`aliveR_subset_known`, L2(c)).
- *(6) Lemma P's ordering step* (`ROM/OneMoreLemmaPOrder.lean`, `e1P_eq_major`): if the ghost log
  before the reduction's queries holds the verifier's `H₂¹` input, `E₁(x)` is the widest group's
  prefix of the alive trees at the end, with the extractor's candidates. It reads `iv` and `mu₁` off
  the reduction's own queries (`ivX_tableOfLog`), `chal1` and `d[0..45)` off `x` for a 32-byte key
  digest (`xChal1_tgtIn`, `xDpre_tgtIn`), the corrections off the `H₂¹` input; the committed keys
  are the extractor's (as in `sameChain_core`), and a candidate's prefix reads only its first 360
  bits (`preB_congr`).
- *(7) The per-table implication* (`ROM/OneMoreLemmaPFail.lean`, `pfail_events`): if forgery `i`
  fails (`PFail_i`), then in the adaptive game of `proverP … i` at the same tables one of these
  holds: the verifier accepts and Lemma P's extraction fails (`MajorExtracted`); Post; the verifier
  accepts and its `H₂³` input is not in the prover's log; a query of the game's log is a chain hit
  or an **order hit** (`orderHitL`: an `H₂¹` answer equal to the `chal1` field of an earlier marker
  query `H₃(x)`; this is the case where the forger asked `H_T(x)` before the `H₂¹` query whose
  answer is `x`'s `chal1`).
- *(8) The bound* (`ROM/OneMoreLemmaPBound.lean`). Each event is bounded in the derived prover's
  adaptive game, joint over the uniform cipher table: Lemma P's extraction by
  `pomfritT_accept_le_major` (`majEps`); Post by `prEvent_joint_postOut_le_A`
  (`1024·q_E·q₁·2⁻²⁵⁶`); the unqueried `H₂³` input by `prEvent_zUnqueried_le_A` (`2⁻¹²⁸`); chain
  hits and order hits by a union bound over the game's queries (`prEvent_hitOrder_le`, through a
  computation that returns its own log, `withLogQ`; an order hit costs `n₃/2¹⁰⁸⁸` per `H₂¹`
  query). The derived provers' budgets come from the forger's (`ForgerBound`: `qA` hash queries per
  kind, `n_A` in all, `q_E` cipher, `Q_T` target queries; `proverP_bounds`). Then
  (`prEvent_pfail_le`), for a key generation with 32-byte key digests and any number of targets,

      Pr[∃ i ≤ ℓ, PFail_i] ≤ (ℓ + 1)·pfailEps(q', q_E', n'),
      pfailEps(q, q_E, n) = majEps(q, q_E, n) + 1024·q_E·q₁·2⁻²⁵⁶ + 2⁻¹²⁸
                            + Σ_{k ∈ {H₁, H₂¹, H₂², H₂³}} n''_k·(hitEps(n'')_k + orderEps(n'')_k),

  with `q' = qA + Q_T·(H₃, H₂⁴, H₄) + (ℓ+1)·vQueries` (`qP`), `q_E' = q_E + (ℓ+1)·verifyCellBound`
  (`eP`), `n' = n_A + 3·Q_T + 26·(ℓ+1)` (`nP`), and `n'' = q' + extractorQueries + verifierQueries`
  (the derived game's queries per kind). `majEps` is `pomfritT_accept_le_major`'s bound: the
  `2⁻¹⁵⁰` per `H₂¹` query (KOS), `ε_QS + 2⁻¹²⁸` per `H₂²` query, `(q₂₃+1)·2⁻⁷¹` (Lemma P's
  `Shift`), the cipher terms `2q_E²·2⁻²⁵⁶`, `openHashEps`, Post, and the chain-hit and
  statement-binding terms. So **Theorem U1 holds with every term explicit**
  (`pomfrit_U1_explicit`; against the standalone OMPR game, `pomfrit_U1_ompr_explicit`):

      Pr[PomWin] ≤ Adv^{ompr}(red …; Q_T + ℓ + 1, ℓ) + (ℓ + 1)·pfailEps(q', q_E', n').

- *(9) Simultaneous extraction* (`ROM/OneMoreLemmaPPrefix.lean`, `ROM/OneMoreLemmaPSim.lean`;
  `lean/docs/probabilistic-plan.md` §2m, §2n). The bound of (8) charges every query of the forger's
  run once per forgery. The pieces for `ROM/SimUnion.lean`'s shared-run union bound
  (`prEvent_le_shared_suffix`):
  - *Prefix runs.* `verPreIC` (an earlier forgery's verification up to its target query) skips a
    forgery whose refresher check fails, `verLastIC` (the last one's) does not; otherwise they make
    the same queries, from any state (`log_verPreIC_eq_last`, `log_verPreAll_state`). A failed
    forgery passed the game's verification (`pfail_refresh`), so at a table where `PFail_i` holds the
    joint and hash logs of `proverP … i` are prefixes of those of `proverP … ℓ`
    (`prefix_of_pfail`). The reference run is `proverP … ℓ`.
  - *The per-query bad event, its bound and its deterministic step as lemmas.* `ROM/LemmaP.lean` now
    exposes Lemma P's bad event (`pomBad`: a bad query of the statement committed there, a chain hit,
    a statement hit), its per-query charge in cache form (`pomEps`, `prEvent_pomBad_le`) and the
    deterministic step (`pomBad_trace`); `prEvent_accept_le_adaptive_pomfritT_E` uses them, its
    statement unchanged. With the order hit, `simBadP`; it reads the logs before the query only
    (`simBadP_prefix_congr`); per query `≤ simEps` (`prEvent_simBadP_le`: `2⁻¹⁵⁰` at `H₂¹`,
    `ε_QS + 2⁻¹²⁸ + ntot·2⁻⁴⁴⁸` at `H₂²`, `2⁵⁷·2⁻¹²⁸` at `H₂³`, the hits, statement hits and order
    hits).
  - *The trace.* If `PFail_i`, then by `pfail_events` and `pomBad_trace` the `i`-th derived game has
    a failure (`failP`: binding, an opened dead leaf, Post, the verifier's `H₂³` input unqueried) or
    a bad query in its log. A bad query of `proverP … i`'s run is one of `proverP … ℓ`'s run, charged
    once; a bad query of its extraction and verification is charged per forgery.

  The result (`prEvent_pfailZ_sim_le_E` per cipher table, `prEvent_pfailZ_sim_le`,
  `prEvent_pfail_sim_le`): **Theorem U1 with simultaneous extraction** (`pomfrit_U1_sim`; against
  the standalone OMPR game, `pomfrit_U1_ompr_sim`), for the same hypotheses as
  `pomfrit_U1_explicit`:

      Pr[PomWin] ≤ Adv^{ompr}(red …; Q_T + ℓ + 1, ℓ) + pfailSimEps(q', q_E', n', ℓ),
      pfailSimEps = Σ_{k ∈ {H₁, H₂¹, H₂², H₂³, H₂⁰}} (q'_k + (ℓ+1)·r_k)·simEps_k
                    + (ℓ + 1)·(failEps(q', q_E') + 2⁻¹²⁸),

  `r` the queries of one extraction and verification (`extractorQueries + verifierQueries`),
  `failEps` the binding, opened-dead-leaf and Post terms (`ROM/SimExtract.lean`). Written out
  (`pfailSimEps_eq`), the chain charges are `(q'₂₁ + ℓ + 1)·2⁻¹⁵⁰ + (q'₂₂ + ℓ + 1)·(ε_QS + 2⁻¹²⁸ +
  (n' + 339)·2⁻⁴⁴⁸) + (q'₂₃ + ℓ + 1)·2⁻⁷¹`: the paper's `(Q₃ + ℓ + 1)·2^{−71}`. It is never worse than the
  union bound: `pfailSimEps ≤ (ℓ + 1)·pfailEps` (`pfailSimEps_le`).

  Numbers (`q` queries of each hash kind, `n_A = q_E = Q_T = q`):

  | `q` | `ℓ` | union `(ℓ+1)·pfailEps` | simultaneous `pfailSimEps` |
  |---|---|---|---|
  | `2⁶⁴` | `2³⁰` | `2²³` (vacuous) | `2⁻⁷·⁰` |
  | `2⁶⁴` | `2²⁰` | `2¹³` (vacuous) | `2⁻⁷·⁰` |
  | `2⁴⁸` | `2³⁰` | `2⁷` (vacuous) | `2⁻²³·⁰` |
  | `2⁴⁰` | `2³⁰` | `2⁻¹·⁰` | `2⁻³¹·⁰` |

  The dominant term is Lemma P's `(q'₂₃ + ℓ + 1)·2⁻⁷¹`; the per-forgery terms
  (`(ℓ+1)·(r·simEps + failEps + 2⁻¹²⁸)`) are about `2⁻⁴¹` at `ℓ = 2³⁰`.

Compared with the paper's term `ε_ext + (Q₃ + ℓ + 1)·2^{−71} + Q_T·q₁·2^{−704}`:
- `pomfrit_U1_sim` charges each query of the forger's run once, as the paper does (L8 §9.1). What
  stays per forgery: its extraction's and verification's own queries, and its failure terms
  (binding, an opened dead leaf, Post, the unqueried `H₂³` input, `2⁻¹²⁸` each at most), as for
  Moussaka and Ratatouille (`probabilistic-plan.md` §2m). `pomfrit_U1_explicit`, the union over the
  forgeries, charges the run `ℓ + 1` times, and Post and the chain hits twice (inside `majEps` and
  again for the identification).
- The ordering term is `n''₂₁·n''₃·2⁻¹⁰⁸⁸` per forgery: the reduction's marker queries `H₃(x)` are
  the `Q_T` target inputs, and the 136-byte `chal1` of this implementation gives `2⁻¹⁰⁸⁸` (the
  paper's `2^{−704}` is the minimum over parameter sets).
- One case the paper puts into `ε_ext` without comment is explicit here: the forger never queried
  the verifier's `H₂¹` input. Then, without hits, it queried neither the `H₂²` nor the `H₂³` input,
  and acceptance is one fresh guess of `Δ` (`2⁻¹²⁸`).
- The key generation must give 32-byte key digests (pqov's `SHAKE256(cpk)` does): the reduction
  reads `chal1` and `d[0..45)` off `hash_to_target`'s input at fixed offsets.

- *(10) Theorem U2* (`ROM/LemmaPSome.lean`, `ROM/OneMoreShiftTable.lean`,
  `ROM/OneMoreShiftFail.lean`, `ROM/OneMoreShiftBound.lean`, `ROM/OneMoreShiftSim.lean`,
  `Assumptions/PomfritShift.lean`, `Assumptions/PomfritShiftSim.lean`; `Pr[∃ i, ShiftFail_i]`
  bounded). The pieces:
  - *The shift rule* (`shP`, `hintS = hint2 17 shP`): as `e1P`, the alive trees at the first `H₂¹`
    preimage of `x`'s `chal1` in the log at `x`'s first target query, and the list of **all** their
    prefixes `u ⊕ d`, in tree order (at most `17`, so `take 17` cuts nothing, `hintS_eq`).
  - *Lemma P without `Shift`* (`ROM/LemmaPSome.lean`). U2's goal on an output is that some alive
    tree has a candidate in the relation (`GoalS`, `SomeExtracted`; Lemma P's `MajorExtracted` is
    the same with the widest-group condition added). The deterministic step and the union bound of
    `ROM/LemmaP.lean` read the goal only through the per-chain hypothesis; they are restated with
    the goal a parameter (`pomBad_traceG`, `prEvent_accept_le_adaptive_pomfritT_EG`,
    `prEvent_accept_le_adaptive_pomfritTG`). The per-chain step is `extract_or_few` for the target
    family (`pomfritT_extract_some_chain`, `combDetG_pomfritT_some`): some tree outside the fixed
    ones extracts, or at most `2` admissible `chal3` are accepted. So `pomfritT_accept_le_some`
    is `pomfritT_accept_le_major` with the `H₂³` term `(Q₃ + 1)·2·2⁻¹²⁸` in place of
    `(Q₃ + 1)·2⁻⁷¹`.
  - *The game with any hint type, table by table* (`ROM/OneMoreShiftTable.lean`). The derived
    prover `proverP … i` of item 4 reads neither the hint rule nor the target rule, so U2 uses it
    unchanged. What was specific to U1 is the relation between the game and it. `InvG` (`InvH` for
    any hint type `Hn` and programming `φ`): the game's state and the void-hint state have the same
    answers, stream and Issuer count, and the hint stored at each answered input is the hint rule at
    that input's ghost log. The game's forger keeps it (`eval_forgerG`), and so do the verifications
    (`eval_verOneG`, `eval_verAll_splitG`, `eval_verPreAllG`). `ver_tableG`: an accepted forgery
    `i` with claim `(x, σ)` passed the refresher check; `proverP … i` outputs `x` and a ghost log
    `Lx`; the game's table holds at `x` the derived prover's answer `a` and the hint rule at `Lx`;
    the verifier accepts at the derived prover's statement; and `σ` is the first candidate
    extracted from the forger's log that is a preimage of one of `tgts (a, hint Lx x)`.
  - *The ordering step* (`shP_eq_alive`): the proof of `e1P_eq_major` with the list of all prefixes
    in place of the widest group's. *The per-table implication* (`shiftFail_events`): `ShiftFail_i`
    gives, in the game of `proverP … i`, the verifier accepting with no alive tree extracting, Post,
    the verifier's `H₂³` input unqueried, a chain hit or an order hit; otherwise the extracting
    tree is known (`aliveR_subset_known`), its prefix is a shift (`shP_eq_alive`), and its decoded
    `σ` is a preimage of `a + δ` for that shift `δ`, so the claim is good (`rel_pick`).
  - *The bounds*, as items 8 and 9 with `N = 2`: `prEvent_shiftFail_le`, `pomfrit_U2_explicit`,
    `pomfrit_U2_omprShift_explicit` (union over forgeries, `(ℓ + 1)·sfailEps`, `sfailEps` =
    `pfailEps` with `someEps` for `majEps`); with simultaneous extraction `prefix_of_shiftFail`,
    `simBadS` (`pomBad` with `N = 2`, or an order hit), `prEvent_shiftFail_sim_le`,
    `pomfrit_U2_sim`, `pomfrit_U2_omprShift_sim`:

        Pr[PomWin] ≤ Adv^{ompr⊕17}(red noHint …; Q_T + ℓ + 1, ℓ) + sfailSimEps(q', q_E', n', ℓ),
        sfailSimEps = (q'₂₁ + ℓ + 1)·2⁻¹⁵⁰ + (q'₂₂ + ℓ + 1)·(ε_QS + 2⁻¹²⁸ + (n' + 339)·2⁻⁴⁴⁸)
                      + (q'₂₃ + ℓ + 1)·2·2⁻¹²⁸ + hits + (ℓ + 1)·(failEps(q', q_E') + 2⁻¹²⁸)

    (`sfailSimEps_eq`), never worse than the union (`sfailSimEps_le`). Hypotheses as for U1:
    32-byte key digests and the forger's budget (`Audit/PomfritLemmaP.lean`).

  Numbers (`q` queries of each hash kind, `n_A = q_E = Q_T = q`), U1's for comparison:

  | `q` | `ℓ` | U1 union | U1 simultaneous | U2 union `(ℓ+1)·sfailEps` | U2 simultaneous `sfailSimEps` |
  |---|---|---|---|---|---|
  | `2⁶⁴` | `2³⁰` | `2²³` | `2⁻⁷·⁰` | `2⁻³²·⁰` | `2⁻⁶²·⁰` |
  | `2⁶⁴` | `2²⁰` | `2¹³` | `2⁻⁷·⁰` | `2⁻⁴²·⁰` | `2⁻⁶²·⁰` |
  | `2⁴⁸` | `2³⁰` | `2⁷` | `2⁻²³·⁰` | `2⁻⁴⁸·⁰` | `2⁻⁷⁸·⁰` |
  | `2⁴⁰` | `2³⁰` | `2⁻¹·⁰` | `2⁻³¹·⁰` | `2⁻⁵⁶·⁰` | `2⁻⁸⁶·⁰` |

  At `2⁶⁴` and `ℓ = 2³⁰` the U2 bound is dominated by the `H₂²` and `H₂³` charges, `≈ 2⁻⁶³` each
  (`q'₂₂·(ε_QS + 2⁻¹²⁸)` and `q'₂₃·2·2⁻¹²⁸`): the paper's `ε_ext ≈ (2Q₃ + 2q₂)·2⁻¹²⁸ = 2⁻⁶²`
  (§6.3). The per-forgery terms are about `2⁻⁸⁸`. So Theorem U2 is tight in Lean as in §6.2: the
  forger's advantage is the reduction's A-OMPR⊕17 advantage up to `2⁻⁶²`. Nothing in the paper's
  argument for U2 was found wrong; the mechanized term adds, as for U1, the order hits and the
  per-forgery failure terms (binding, an opened dead leaf, Post, the unqueried `H₂³` input).

## 7. One-more unforgeability in the QROM

*Status.* This section explains why the classical reduction does not lift with Q2 alone. The
QROM theorems were later written in `lean/docs/extraction/Q7-qrom-multi-extraction.md` §4 (U1-Q,
U2-Q, paper): database-controlled programming of `H_T` (Q7 Lemma S) replaces the mid-run `E₁`,
Theorem M gives simultaneous extraction from the ℓ+1 outputs, and the UOV assumptions become
their quantum-random-oracle forms A-OMPR-RO and A-OMPR⊕τ-RO, which are new. What follows is the
analysis with Q2 only.

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
  - The collision is not charged. It is harmless here: for `µ₀ ≠ µ₁` the two inputs differ even
    for equal seeds, and for `µ₀ = µ₁` the two worlds are equal. **[Lean]** (`lean/docs/zk.md`
    §10.6): `(2Q_X + 1)·2^{−256}` per world, the `2^{−256}` from a model keyed by the seed alone.
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
- G0 → G1 is **[Lean]** for the games below (`lean/docs/zk.md` §10.6, `Privacy/SeedXOF.lean`,
  `Privacy/SeedXOFGames.lean`): with `XOF_seed` a uniform table (a column of answers per seed,
  over a finite type of contexts `dig(pk) ‖ msg`), uniform seeds, and an Issuer `A g` at table `g`
  that reads at most `Q_X = q_k + q_g` columns, each theorem gains `2·(2Q_X + 1)·2^{−256}` in the
  left/right difference (`blindness*_seed`). The note's `2Q_X·2^{−256}` names the seed collision
  but does not charge it. In the full random-oracle model it is still right, since `µ₀ ≠ µ₁` keeps
  the two inputs apart and `µ₀ = µ₁` makes the worlds equal; the Lean model keys the table by the
  seed alone and pays `2^{−256}`. Lemma DS (c) (the seed XOF's independence from the
  proof-system oracles, F-DS2) is mechanized on one SHAKE oracle read by every party
  (`Privacy/SeedXOFDS.lean`, `seedXofDS_two_le`: `(2Q + 1)·2^{−256}`, `Q` counting every
  evaluation at a string of the seed XOF's shape, proof-system ones included); its composition with
  the games' separate tables is on paper (`lean/docs/zk.md` §10.6). On paper also, for an abstract
  prover, (ZK-fix) itself.
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
  tables (lifted below, except for `H₂³`); `hash_to_target`, `XOF_seed` (drawn uniformly, G1) and
  the refresher commitment stay SHAKE. The game is the spec's (`realSession` on
  `Layout.labelRows`).
  - The two-phase zero-knowledge theorem behind it (`zk2_rom_ic_h23_num`): the single-proof bound
    `q₃·2⁻¹²⁸ + 2⁻¹¹³ + 221·(4607 + q_E + 4607)·2⁻¹²⁸ + (q₅ + 1)·2⁻¹²⁸` holds for the two-phase run,
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
    4·(q₃ + q₅ + 221·q_E)·2⁻¹²⁸ + δ(A) + δ(A.swap)`. In Lean (`Privacy/PomFRITDelta.lean`,
    `deltaRO_le`) `δ(A) ≤ noHitProb + 2⁻¹²⁸`: session 1's grinding prefix does not depend on
    session 0's simulated `ã₀` (`16` bytes, the last field of the prefix session 0 programs at),
    and if session 1 continues then so does session 0 (`bothOK` is symmetric). So
    **`blindnessRO_lean_num`**: `≤ 4·εRO(q₃, q₅ + 1248, q_E + 18428) + 2·noHitProb + 2·2⁻¹²⁸`.
    Remaining modelling steps: SHAKE as a random oracle, AES as an ideal
    cipher (with the cipher's rows uniform functions; with uniform permutations read forward and
    inverse, the PRP/PRF switching term included, the same bound with `εROPm` for `εRO`,
    `blindnessRO_lean_num_perm`, and `blindnessRA_lean_num_perm` for the table-reading Issuer below,
    `lean/docs/zk.md` §10.4), and the composition of Lemma DS (c) for `XOF_seed` (mechanized on
    the single SHAKE oracle, `seedXofDS_le`) with the games' tables; G0 → G1 is mechanized
    (`blindnessRO_lean_num_seed`, `blindnessRA_lean_num_seed`, `blindnessRAH_lean_num_seed`,
    `blindnessSh_num_seed`, `blindnessRASh_num_seed`, the `OC` versions and `_perm`;
    `+ 2·(2Q_X + 1)·2^{−256}`, `lean/docs/zk.md` §10.6). The two sessions' slices need not be independent: with one
    shared `H₃(r ‖ μ ‖ ρ ‖ 3)`, each session reading its column of the shared tables at its prefix
    (equal for sessions with equal `r` and refresher commitment), **`blindnessSh_num`**:
    `≤ 4·εRO(q_E + 18428, q₅ + 1248, q_E + 18428) + 2·noHitProb + 2·2⁻¹²⁸`, no `2⁻³⁶⁰` term (hop 0
    uses the adaptive two-phase theorem, since session `0`'s continuation runs session `1`'s step 1,
    which reads session `0`'s column when the prefixes coincide); with the table-reading Issuer
    below, **`blindnessRASh_num`** (`4·εRO(q_E + 4i_E + 23035, q₅ + 4i₅ + 1872, q_E + 4i_E + 23035)
    + 2·noHitProb + 2·2⁻¹²⁸`), `blindnessOCSh_num`, `_perm` (`lean/docs/zk.md` §10.5); with the
    Issuer that also reads `H₂³` (below), **`blindnessRAHSh_num`**, `blindnessOCHSh_num`, `_perm`
    (`Privacy/SharedH3PomFRITRAH.lean`), and with the seeds `blindnessRAHSh_num_seed`,
    `blindnessOCHSh_num_seed`.
- **[Lean] Blindness with an Issuer whose key, messages and responses read the tables**
  (`lean/VoleMole/ZK/TwoPhaseAd.lean`, `Privacy/PomFRITRA.lean`, `Privacy/PomFRITRAGame.lean`;
  `lean/docs/zk.md` §10.3). The Issuer (`AdversaryRA`) picks its key and both messages as functions
  of the two slices and the shared tables, and its two responses as functions of both requests,
  the slices and the tables (`AdversaryRA.at`: the Issuer at fixed tables is an `AdversaryRO`; the
  real game `realGameRA` is `realGameRO` at the game's tables). Its interaction's budget
  (`IBudget i₃ i₅ i_E`): the key-and-messages stage and the response stage at every pair of
  requests are consistent table readers (`SReads`) of each slice and the shared tables, at most
  `i₃` slice keys, `i₅` `H₅` keys, `i_E` cipher keys and **no `H₂³` key**; the guess as before.
  For an Issuer whose stages are VCVio oracle computations over the tables (`AdversaryOC`,
  `lean/VoleMole/ROM/PrivacyReads.lean`), consistency is a theorem and the budget is the
  syntactic query bound (`QBudget`): `blindnessOC_lean_num`, `blindnessOC_lean_num_perm`, the
  same bounds with no consistency hypothesis on the interaction (the guess keeps its semantic
  read budget).
  `hash_to_target`, `XOF_seed` and the refresher commitment stay SHAKE, outside the tables.
  - The zero-knowledge theorem (`zk2_adaptive`, `zk2_rom_ic_h23A_num`): the continuation (the
    Issuer's response to the request computed from the session's step-1 output) reads the
    session's slice, `H₅` and the cipher at keys that depend on that output; the H1, H6 and H4
    hops pay for its reads at the output's step 1, every other hop holds for every value of the
    tables. Error `εRO(q₃ + q_k3, q₅ + q_k5, q_E + q_kE)`.
  - The hybrids are those of `blindnessRO` at the Issuer at the original tables (the simulators
    program only `H₂³`, which the interaction does not read). The reductions read the Issuer only
    at its key and at its responses to the two requests they compute (`D0_fix`, `D1_fix`), so
    the interaction is counted twice per hop (as the continuation's reads and as the reduction's),
    and the step-1 reads of the other session once more.
  - **`blindnessRA_lean_num`**: `|Pr[A accepts | b = 0] − Pr[A accepts | b = 1]| ≤
    4·εRO(q₃ + 4i₃, q₅ + 4i₅ + 1872, q_E + 4i_E + 23035) + 2·noHitProb + 2·2⁻¹²⁸`, about `2⁻¹⁰³·²`
    plus `4·(q₃ + 4i₃ + q₅ + 4i₅ + 221·(q_E + 4i_E))·2⁻¹²⁸` (`2⁻¹⁰³·⁴` table-oblivious).
  - Why the interaction may not read `H₂³` there: the hybrids run the Issuer at the original
    tables, which is the Issuer at the programmed ones only if it ignores `H₂³`. Otherwise the
    two-phase simulator's programming at the zero-prefix block when its continuation stops
    (`simTab2` at `outPre2 = ∅`), the programming hop (exact only for points independent of
    `H₂³`) and the reductions (which see only programmed tables) would each need a change or a
    collision term.
- **An Issuer that also reads `H₂³`** (`lean/VoleMole/Privacy/PomFRITRAH.lean`,
  `lean/VoleMole/ZK/CollideAd2.lean`; `lean/docs/zk.md` §10.3). The budget is joint
  (`IBudgetH i₃ i₂ i₅ i_E`): the key stage and the response stage at every pair of requests are
  consistent readers of both slices and the shared tables together, at most `i₃` keys of each
  slice, `i₂` `H₂³` keys, `i₅` `H₅` keys, `i_E` cipher keys. The hybrids and the simulator are
  unchanged: the interaction's `H₂³` reads are removed before them.
  - *Lazy sampling of `H₂³`* (`pr_resampleC`, `pr_G0RA_resample`): with everything else fixed
    the interaction reads `H₂³` at `≤ 2i₂` keys, consistently, so the game is the game in which it
    reads an independent table `Γ` and the sessions and the guess see `H₂³` patched with `Γ` at
    those keys.
  - *The substituted Issuer* (`AdversaryRA.subst`): reads `Γ` in place of `H₂³`, its guess
    patches `H₂³` at the interaction's read set (recomputed from the requests: `2i₃`, `2i₅`, `2i_E`
    more guess reads). `blindnessRA_lean_numG` applies to it for every `Γ`. Its game differs from
    the patched one only if a real session's grinding block meets the interaction's `H₂³` reads.
  - *The collision term* (`ZK.Sim.pr_tail2A`, `pr_bad0H`, `pr_bad1H`): outside `GrindBad`
    (`2⁻¹¹³`) the block is recomputed from the proof; by a second application of two-phase zero
    knowledge it meets the reads with the simulated proof's probability, and the simulated block's
    tail is the simulator's uniform 16-byte `ã`, which the reads (computed from step 1) do not
    see: `2⁻¹¹³ + εRO(6i₃, 6i₅ + 2184, 6i_E + 18428) + 2i₂·2⁻¹²⁸` per session and world.
  - **`blindnessRAH_lean_num`**: `|Pr[A accepts | b = 0] − Pr[A accepts | b = 1]| ≤
    4·εRO(q₃ + 6i₃, q₅ + 6i₅ + 1872, q_E + 6i_E + 23035) + 2·noHitProb + 2·2⁻¹²⁸ +
    [i₂ > 0]·4·(2⁻¹¹³ + εRO(6i₃, 6i₅ + 2184, 6i_E + 18428) + 2i₂·2⁻¹²⁸)`, about `2⁻¹⁰²·³` plus the
    budget terms; `blindnessRAH_lean_num_perm` with `εROPm`; for an Issuer written as oracle
    computations, `blindnessOCH_lean_num` (`_perm`), the budget from `QBudget` (`sReadsP_runT`).
  - *Counting prefixes* (`lean/VoleMole/Privacy/PomFRITRAHPfx.lean`): the grinding block is all
    `2³²` keys of one prefix, so the collision term depends on the reads only through their
    prefixes (`ZK.Sim.pr_tail2A_pfx`). With `IBudgetHB i₃ b₂ i₅ i_E` (the `H₂³` read sets of at
    most `b₂` prefixes each; `IBudgetH.toB` gives it with `b₂ = i₂`), **`blindnessRAH_lean_num_pfx`**
    (`_numG_pfx`, `_num_perm_pfx`) is the bound above with `2b₂·2⁻¹²⁸` in place of `2i₂·2⁻¹²⁸`
    (`pr_bad0H_pfx`, `pr_bad1H_pfx`).
  - *With one shared `H₃`* (`Privacy/SharedH3PomFRITRAH.lean`, `ZK/SharedH3Tail.lean`; the Issuer
    reads `H₃` through the rows and no slot slice): the same proof on the shared tables, the
    collision term by `ZK.Sim.pr_tail2Sh` (the session's column re-sampled, then `pr_tail2A`).
    **`blindnessRAHSh_num`**: `≤ 4·εRO(q_E + 6i_E + 23035, q₅ + 6i₅ + 1872, q_E + 6i_E + 23035) +
    2·noHitProb + 2·2⁻¹²⁸ + [i₂ > 0]·4·(2⁻¹¹³ + εRO(6i_E + 13824, 6i₅ + 2184, 6i_E + 18431) +
    2i₂·2⁻¹²⁸)`, also about `2⁻¹⁰²·³`; `_perm`, `blindnessOCHSh_num` (`_perm`), and with the seed
    XOF `+ 2·(2Q_X + 1)·2⁻²⁵⁶` (`*_seed`).
  - Not covered: `H₂³` reads under the per-slice budget `IBudget` (the substituted Issuer's guess
    must recompute the reads jointly); a two-phase zero-knowledge theorem whose continuation reads
    `H₂³` (not needed for the game).

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
      by the simulator (`lean/docs/zk.md` §3, `ε_abort = 0`; the Lean two-phase tape hypothesis
      charges `noHitProb ≤ 2^{−2¹⁵}` for the fallback block instead, `ε_abort`);
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

The classical ZK proof programs H₂³ at points with a fresh 3λ+64-bit prefix. A QROM version needs
adaptive reprogramming (GHHM21) and a quantum treatment of the lazy-sampled `H₅` siblings.
`lean/docs/zk-qrom.md` gives it on paper, including the delayed-instance setting of PomFRIT's
issuance (`Exp^{dly-G}`, its §10: proof-level unlinkability against a quantum Issuer costs about
`2⁻¹⁹` at `2³⁰` queries). G1 lifts directly (a query to an unknown 256-bit seed costs
`O(Q_X²·2^{−256})`), and G3 is information-theoretic. Theorem B itself is not restated with the
quantum ZK bound (zk-qrom.md leaves `hash_to_target` and the refresher outside), so **blindness in
the QROM is not written out**; nothing of it is mechanized.

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
- Demo: `scratchpad/demo/ctr_malleability.cpp` (outside the repo). It runs one issuance with one
  `issue_response`, accepted counters 1398 and
  1740, and prints `verify(sig0)=1 verify(sig1)=1 distinct=1`.

Consequences:
- **Not** a break of Def. 2.5 (messages must be distinct) or of blindness. The extra signatures
  carry the same `π₁` and `h`, hence the same session.
- One-more *strong* unforgeability fails.
- Any application that deduplicates on σ, `H(σ)`, or the proof bytes can be double-spent by the
  token holder. Third parties cannot do this (§9.2).

Fix options:
- **Documentation:** say "deduplicate on msg" explicitly next to README's nullifier advice
  (`README.md:115-120`). The current text says the verifier should use a nullifier in the message,
  which points the right way, but it does not warn against deduplicating on σ.
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
2. **Lemma DS.** The proof and application hash families are disjoint (`lean/docs/security/domain-separation.md`
   §7): the refresher commitment by part (a), the seed XOF by part (c) (up to `n_seed·Q·2⁻²⁵⁶`;
   in Lean on one random oracle up to `(n_seed·Q + n_seed²)·2⁻²⁵⁶`, `Privacy/SeedXOFDS.lean`),
   and `hash_to_target` only in the restricted form (d), at a cost `ε_MC` per hop, because its
   domain overlaps four proof-system domains (finding F-DS1; a final domain byte would remove it).
3. **UOV.** A-OMPR (paper Def. 3.1) for U1, or A-OMPR⊕17 for the tight U2. The Issuer key is used
   only for PomFRIT.
4. **PoK.** README theorem, L1–L7, simultaneous extraction (L8 §9.1), and the Lean lemmas
   `free_tree_holds_witness` and `extraction_cases`.
5. **ZK.** `lean/docs/zk.md` with the label-row fix (blindness only). `rho` comes from a fresh OS seed.
6. **Seed.** The OS RNG gives 32 fresh uniform bytes per `issue_request` (`random.hpp`).

## 11. What holds where

| | `main` | label-row fix |
|---|---|---|
| U1, U2 (classical one-more unforgeability) | ✓ (reductions in Lean; U1 and U2 with every term explicit, the extraction term bounded with simultaneous extraction, U2 without the `2⁻⁷¹` term, §6.4) | ✓ |
| T6 (OMPR ≤ one-more unforgeability) | ✓ (in Lean, for the Lean client: `pomfrit_T6_lean`, §6.4, G9) | ✓ |
| QROM one-more unforgeability | paper, new quantum UOV assumptions (Q7 §4) | same |
| Blindness, honest-but-curious Issuer | ✗ (practical linking) | ✓ (Thm B) |
| Blindness, malicious Issuer, malicious key, selective failure | ✗ | ✓ (Thm B, §8.3) |
| Blindness in the ROM + ideal cipher, Issuer seeing the tables (Lean prover) | ✗ | ✓ (`blindnessRO_lean_num`, every term explicit; `blindnessRA_lean_num` with the key, messages and responses reading the tables except `H₂³`; `blindnessRAH_lean_num` with them reading `H₂³` too; `_perm` with AES as random permutations; `blindnessSh_num`, `blindnessRASh_num`, `blindnessRAHSh_num` with one shared `H₃`; `blindness*_seed` from the OS seeds and `XOF_seed`; many sessions, `N` pairs, adaptive and interleaved schedules: `blindnessN_lean_num`, `blindnessP_lean_num`, `blindnessPH_lean`, `blindnessAd_lean_num`, `blindnessAd_lean_num_pfx`, `blindnessIL_lean_num`, `blindnessILO_lean_num` with a table-reading scheduler and a free challenge) |
| Blindness in the QROM | ✗ | proof-system ZK on paper (`lean/docs/zk-qrom.md`); Theorem B not restated (§8.5) |
| Strong SE / no third-party mauling | ✓ against parties without `t` | ✓ against all |
| Owner re-randomization (§9.3) | present | present |

## 12. Gaps and open items

- **G1.** Is A-OMPR ⇒ A-OMPR⊕τ without the `τ^{ℓ+1}` loss? (With the loss it is Lean
  `advOMPRShift_le_guess`; the converse, A-OMPR⊕τ ⇒ A-OMPR, is tight, `advOMPR_le_shift`.) If so, U1 loses its `Q₃·2^{−71}`
  term. A protocol change that pins `r` to π₁ would also remove it, but none was explored here.
  `pomfrit-lemmap-tight.md`: `ũ` in `hash_to_target` already pins `r` information-theoretically
  (§4 there); for first messages whose trees disagree on the label rows, extraction is reduced to
  finding a slice (§6 there); the class extractor finds it whenever more than `2⁵⁰` challenges
  accept, which gives `2⁻⁷⁸` per `H₂³` query on paper, unconditionally (§6A there; per-chain step
  in Lean, the one-more game with it not mechanized); protocol options are in §8 there.
- **G2.** QROM unforgeability (§7) needs mid-run extraction, or a different reduction. Q7 §4
  supplies one (database-controlled programming, simultaneous extraction from ℓ+1 proofs by
  Theorem M), on paper and under the new assumptions A-OMPR-RO and A-OMPR⊕τ-RO; from the
  classical A-OMPR it remains open.
- **G3.** Blindness depends on the label-row fix being implemented as described (dedicated rows,
  `Θ` uniform and witness-independent) and on `lean/docs/zk.md`'s theorem being re-checked for it. The
  paper's App. B.3 ZK argument should not be relied on (§8.1).
- **G4.** Lemma DS is proved on paper (`lean/docs/security/domain-separation.md`), but covers
  `hash_to_target` only in a restricted form (F-DS1), with the extra term `ε_MC`. Part (c), for
  `XOF_seed` (F-DS2), is mechanized in the random-oracle model on one SHAKE oracle
  (`Privacy/SeedXOFDS.lean`, `seedXofDS_le`, `(n·Q + n²)·2⁻²⁵⁶`); part (d) is not.
- **G5.** Lemma P's "fixed before the answer" argument and the union over `H₂³` queries are in
  Lean for one adaptively chosen statement (`pomfritT_accept_le_major`, §5), and its ordering step
  (`E₁` at query time) in the one-more game (`e1P_eq_major`, `pfail_events`, §6.4).
- **G6.** The 2^{−71} uses the FAEST-EM-128f tree shapes. For other parameter sets, recompute it
  as `2^{−(λ − max_{S,T disjoint, Σ_S ≤ Σ_T} Σ_S)}`.
- **G7.** Blindness in Lean (§8.2, §13) leaves:
  - the modelling steps: SHAKE as a random oracle and AES as an ideal cipher;
  - for Lemma DS (c) for `XOF_seed` (mechanized on the single SHAKE oracle, `seedXofDS_le`), its
    composition with the games' separate tables (routing an Issuer's query at a seed-XOF input
    that is also a proof-system input to that domain's table), and contexts beyond the length
    bound of the finite context type of the seed-XOF model;
  - the consistency of an Issuer given as a bare function of the tables (a theorem for one
    written as oracle computations);
  - `H₂³` reads under the per-slice budget `IBudget` (covered under the joint budget `IBudgetH`,
    with per-session slices and with one shared `H₃`);
  - for many sessions (`lean/docs/zk.md` §10.8; mechanized: any number of further honest sessions
    in one concurrent schedule, `≤ n·2⁻¹⁰³`, adaptive schedules, `≤ n·2⁻¹⁰²` (`n·2⁻⁹²` with the
    `H₂³` reads counted in keys), interleaved schedules, also with a table-reading scheduler that
    places the challenge, `≤ (n + 2)·2⁻¹⁰²` (plus the scheduler's reads), and `N` challenge
    pairs, `≤ N·(2N·2⁻¹⁰³ + …)`, or `≤ N·2⁻¹⁰³ + 32·N²·2⁻¹²⁸` with `H₄` a random-oracle table,
    each plus budget terms): a bound linear in `N` without the `iv` birthday term and with the
    budget terms charged once (the quadratic terms are artifacts of the proofs, not attacks); the
    `H₄`-table games with AES as random permutations; further sessions in the shared-`H₃` and
    seed-XOF games.

- **G8 (closed).** U1/U2's extraction term in Lean (§6.4). **Closed for U1**: `Pr[∃ i ≤ ℓ, PFail_i] ≤
  (ℓ + 1)·pfailEps(q', q_E', n')` with every term explicit (`prEvent_pfail_le`), so
  `Pr[PomWin] ≤ Adv^{ompr} + (ℓ + 1)·pfailEps` (`pomfrit_U1_explicit`, `pomfrit_U1_ompr_explicit`;
  `ROM/OneMoreLemmaPIC.lean` … `ROM/OneMoreLemmaPBound.lean`). The pieces: a derived prover that
  reaches the cipher only by queries (`proverP`), the extraction from the forger's log equal to the
  derived game's outside hits and Post (`keysOf_knownOf_prefix`), Lemma P's ordering step
  (`e1P_eq_major`, with the order hit as its failure event), the per-table implication
  (`pfail_events`) and the probability assembly with the derived provers' query bounds. Hypotheses:
  32-byte key digests and the forger's query budget (`ForgerBound`); both hold for real objects
  (`Audit/PomfritLemmaP.lean`). **With simultaneous extraction** (the paper's `ε_ext` once, L8
  §9.1): `Pr[PomWin] ≤ Adv^{ompr} + pfailSimEps(q', q_E', n', ℓ)` (`pomfrit_U1_sim`,
  `pomfrit_U1_ompr_sim`, `prEvent_pfail_sim_le`; `ROM/OneMoreLemmaPPrefix.lean`,
  `ROM/OneMoreLemmaPSim.lean`), each query of the forger's run charged once and each forgery's
  extraction, verification and failure terms once per forgery; `pfailSimEps ≤ (ℓ + 1)·pfailEps`
  (`pfailSimEps_le`). At `2⁶⁴` queries and `ℓ = 2³⁰` the union bound is `2²³` (vacuous), the
  simultaneous one `2⁻⁷`, dominated by Lemma P's `(q'₂₃ + ℓ + 1)·2⁻⁷¹` (§6.4 item 9). The pieces, as
  for the other protocols (`adaptBad`, `adaptBad_trace`): the derived provers' runs as prefixes of the
  last one's where a forgery fails (`prefix_of_pfail`; `verPreIC` and `verLastIC` differ only when
  the refresher check fails, which a failed forgery passed), and Lemma P's per-query bad event with
  its per-query bound and deterministic step as lemmas (`pomBad`, `prEvent_pomBad_le`,
  `pomBad_trace` in `ROM/LemmaP.lean`; with the order hit, `simBadP`, `prEvent_simBadP_le`,
  `simBadP_prefix_congr`). **Closed for U2** (§6.4 item 10): `Pr[PomWin] ≤ Adv^{ompr⊕17} +
  sfailSimEps(q', q_E', n', ℓ)` (`pomfrit_U2_sim`, `pomfrit_U2_omprShift_sim`; union
  `(ℓ + 1)·sfailEps`, `pomfrit_U2_explicit`, `pomfrit_U2_omprShift_explicit`), with U2's shift
  rule `hintS` (all alive trees' prefixes) and no `2⁻⁷¹` term: `2⁻⁶²` at `2⁶⁴` queries and
  `ℓ = 2³⁰`. The pieces: Lemma P without `Shift`, `N = 2` per chain (`pomfritT_accept_le_some`,
  `ROM/LemmaPSome.lean`); the game with any hint type related to the same derived prover
  (`InvG`, `ver_tableG`, `ROM/OneMoreShiftTable.lean`); the ordering step for the list of shifts
  (`shP_eq_alive`) and the per-table implication (`shiftFail_events`). Found on the way: the
  game's `chal1Pre` used the AES PRG instead of the ideal cipher's, so the target oracle's input
  was not at the verifier's `chal1` (fixed earlier).
- **G8-cls (open).** Theorem U1^cls in Lean (`pomfrit-lemmap-tight.md` §6A): U1 with the class
  extractor and `(Q₃ + ℓ + 1)·2⁻⁷⁸ + q₁·2⁻¹³⁴` for Lemma P's `(Q₃ + ℓ + 1)·2⁻⁷¹`. In Lean: the
  per-chain step (`class_or_small_dec`, `extract_or_class`) with the decoder as a function of the
  check value and its evaluation count. Missing: the label rows' tree form and the affine and
  two-label structure of `Verifier`'s CRT masks on slices; `KOSPar` as a bad event at `H₂¹`;
  `E₁^cls` on the query log with its `H₅` evaluations as the reduction's queries (the goal of
  `ROM/LemmaP.lean` reads only the candidates and the alive trees).
- **G9 (closed).** Theorem 6 (OMPR ≤ PomFRIT, `uov-assumptions.md` §5.6) is in Lean for the Lean
  client with the completeness term bounded: `compFail ≤ (ℓ+1)·2^{−113}` (`compFail_le`) and
  `Adv^{ompr}(B; n, ℓ) ≤ Pr[PomWin] + (ℓ+1)·2^{−113}` (`pomfrit_T6_lean`, `pomfrit_T6_lean_bound`;
  §6.4). The client's steps are the Lean prover's as oracle computations (`ROM/ProverIC.lean`,
  `Assumptions/PomClientLean.lean`), equal per table to `Prover.voleGen` and `Prover.proveCommit`
  (the PRG calls are recorded with cipher queries and replayed, `voleGenAt_congrA`, `memoF_map`).
  The per-session bound is the grinding term only; the union is over the `ℓ+1` claims, not the
  `n` sessions, because a claimed session's prefix is computed without `H₂³` queries.
  Composing T6 with U1 into an equivalence also needs that `Pr[PomWin]` does not depend on the
  hint rule (U1 uses Lemma P's `E₁`, T6 the hint `0`; the forger never sees hints), which is not
  stated in Lean.

## 13. Lean

`lean/VoleMole/Protocols/PomFRIT.lean`, `lean/VoleMole/ROM/OneMore.lean`,
`lean/VoleMole/ROM/OneMorePomfrit.lean`, `ROM/LemmaPDet.lean`, `ROM/LemmaP.lean` and
`ROM/OneMoreLemmaP.lean`, `ROM/OneMoreLemmaPIC.lean`, `ROM/OneMoreLemmaPIdent.lean`,
`ROM/OneMoreLemmaPOrder.lean`, `ROM/OneMoreLemmaPQueries.lean`, `ROM/OneMoreLemmaPFail.lean`,
`ROM/OneMoreLemmaPBound.lean`, `Assumptions/PomfritLemmaP.lean`, `ROM/OneMoreLemmaPPrefix.lean`,
`ROM/OneMoreLemmaPSim.lean`, `Assumptions/PomfritLemmaPSim.lean`, `ROM/LemmaPSome.lean`,
`ROM/OneMoreShiftTable.lean`, `ROM/OneMoreShiftFail.lean`, `ROM/OneMoreShiftBound.lean`,
`ROM/OneMoreShiftSim.lean`, `Assumptions/PomfritShift.lean` and `Assumptions/PomfritShiftSim.lean`
have no `sorry` and no `axiom`. Check them with
`cd lean && lake env lean VoleMole/Protocols/PomFRIT.lean` (and `lake build
VoleMole.ROM.OneMorePomfrit`).

| Statement | Lean |
|---|---|
| Coordinates outside `G` fixed ⇒ `|A| ≤ ∏_{i∈G} |B_i|` | `card_le_prod_of_fixed` |
| A tree differing from `u*` on any row is fixed (Claim 4) | `fixed_of_prefix_ne` |
| Trees outside `u*`'s prefix group are fixed; `|A|` bound | `fixed_outside_prefixGroup`, `card_le_prod_prefix_group` |
| Widths (8, 7×16) sum to 120 | `width_total` |
| Disjoint `S, T` with `Σ_S ≤ Σ_T` ⇒ `Σ_S ≤ 57` | `minority_weight_le` |
| Minority prefix group ⇒ `|A| ≤ 2^{57}` | `minority_card_le` |
| `2^{57}/2^{128} ≤ 2^{−71}`; loss at `2^{50}`, `2^{64}` | `per_query_bound`, `loss_at_2_50`, `loss_at_2_64` |
| Lemma P per chain: the widest prefix group (`majP`, ties by least index) extracts, or `≤ 2⁵⁷` accepted `chal3` (`lean/VoleMole/ROM/LemmaPDet.lean`) | `grpW`, `majP`, `majP_spec`, `majP_congr`, `extract_or_major`, `pomfritT_extract_major_chain` |
| Lemma P for one adaptively chosen statement with any target function: the deterministic step with a general goal, the alive trees of an output, the bound with `(Q₃+1)·2⁻⁷¹` (`lean/VoleMole/ROM/LemmaP.lean`) | `pomfritRedeemT`, `pomfritRedeemT_values`, `combBad_of_acceptG`, `CombDetG`, `combBad_trace_icDG`, `aliveR`, `dead_of_not_mem_aliveR`, `GoalP`, `MajorExtracted`, `prEvent_accept_le_adaptive_pomfritT_E`, `prEvent_accept_le_adaptive_pomfritT`, `combDetG_pomfritT`, `pomfritT_accept_le_major` |
| Lemma P with the class extractor, per chain (generic; `lean/VoleMole/ROM/LemmaPClass.lean`, `lean/VoleMole/Seed/SliceDecode.lean`; `pomfrit-lemmap-tight.md` §6A): `2⁵⁰` in place of `2⁵⁷`, the decoder and its evaluation count. Not joined to the one-more game | `clsExt`, `class_or_small`, `class_or_small_dec`, `extract_or_class`, `dec`, `dec_sound`, `dec_cert_sound`, `dec_cert_complete`, `card_decQ_le`, `dec_congr`, `basePts_cover`, `twoLabel_gate`, `per_query_bound_cls`, `loss_cls_at_2_64` |
| The one-more game against Lemma P (`lean/VoleMole/ROM/OneMoreLemmaP.lean`): the game as a lazy random oracle; `E₁`; the forger with the cipher as queries; verification and a failed forgery table by table; Lemma P's goal gives the claim | `realImpl_run_eq`, `htW`, `tStep`, `e1P`, `wrapIC`, `eval_forger`, `log_forger`, `wrapP`, `tStep_sameT`, `eval_forgerP`, `eval_verOne`, `eval_verAll_split`, `eval_htW_persist`, `proverI`, `pfail_table`, `not_noPick` |
| A derived prover with the cipher as queries (`lean/VoleMole/ROM/OneMoreLemmaPIC.lean`): `chal1` by cipher queries; the forger with a void hint and the hints as ghost logs; the derived prover, its output, log and ghost logs per table | `chal1PreIC`, `evalWithAnswerFn_chal1PreIC`, `InvH`, `eval_wrapIC_hint`, `verPreIC`, `verPreAll`, `verLastIC`, `proverP`, `eval_proverP`, `contP`, `log_proverP`, `GhostI`, `GhostV`, `aux_proverP` |
| The extraction from a prefix of the prover's log (`lean/VoleMole/ROM/OneMoreLemmaPIdent.lean`): the verifier's chain in the prefix; same keys and known trees outside hits and Post; the alive trees are known | `extractKey_sandwich`, `mem_x_of_mem_z`, `keysOf_knownOf_prefix`, `aliveR_eq_filter`, `aliveR_subset_known` |
| Lemma P's ordering step (`lean/VoleMole/ROM/OneMoreLemmaPOrder.lean`): `hash_to_target`'s input layout; a candidate's prefix reads its first 360 bits; `E₁` at query time is the widest group's prefix at the end | `xChal1_tgtIn`, `xDpre_tgtIn`, `preB_congr`, `tableOfLog_eq`, `ivX_tableOfLog`, `corrBit_pcd`, `e1P_eq_major` |
| The derived prover's queries (`lean/VoleMole/ROM/OneMoreLemmaPQueries.lean`): the forger's budget; the wrapped forger's and the verifications' queries; no `H₂³` query after the forger | `ForgerBound`, `kinds_wrapIC`, `left_wrapIC`, `right_wrapIC`, `vBound_contP`, `not_mem_hashLog_contP`, `qP`, `nP`, `eP`, `proverP_bounds` |
| A failed forgery is a bad event of the derived game, table by table (`lean/VoleMole/ROM/OneMoreLemmaPFail.lean`): extraction failure, Post, unqueried `H₂³` input, chain hit or order hit | `orderHitL`, `chal1Pre_of_accept`, `pfail_events` |
| Lemma P's term bounded; Theorem U1 with every term explicit (`lean/VoleMole/ROM/OneMoreLemmaPBound.lean`, `lean/VoleMole/Assumptions/PomfritLemmaP.lean`; non-vacuity in `Audit/PomfritLemmaP.lean`) | `withLogQ`, `HitOut`, `orderEps`, `prEvent_hitOrder_le`, `majEps`, `pfailEps`, `prEvent_pfailZ_le`, `prEvent_pfail_le`, `pomfrit_U1_explicit`, `pomfrit_U1_ompr_explicit` |
| Lemma P's per-query bad event, its bound and its deterministic step as lemmas (`lean/VoleMole/ROM/LemmaP.lean`) | `pomBad`, `pomEps`, `pomBad_trace`, `prEvent_pomBad_le` |
| The derived provers' runs are prefixes of the last one's where a forgery fails (`lean/VoleMole/ROM/OneMoreLemmaPPrefix.lean`) | `RefreshOk`, `log_verPreIC_state`, `log_verPreIC_eq_last`, `log_verPreAll_state`, `log_verPreAll_append`, `log_contP`, `log_contP_prefix`, `jOf_proverP_prefix`, `runE_proverP_prefix`, `pfail_refresh`, `prefix_of_pfail` |
| Theorem U1 with simultaneous extraction: each query of the forger's run charged once; never worse than the union over forgeries (`lean/VoleMole/ROM/OneMoreLemmaPSim.lean`, `lean/VoleMole/Assumptions/PomfritLemmaPSim.lean`; non-vacuity in `Audit/PomfritLemmaP.lean`) | `simBadP`, `simBadP_prefix_congr`, `cellEps`, `simEps`, `prEvent_simBadP_le`, `failP`, `prEvent_pfailZ_sim_le_E`, `prEvent_avg_le_sum4`, `pfailSimEps`, `pfailSimEps_eq`, `sum_simEps_eq`, `pfailSimEps_le`, `prEvent_pfailZ_sim_le`, `prEvent_pfail_sim_le`, `pomfrit_U1_sim`, `pomfrit_U1_ompr_sim` |
| Lemma P without `Shift` (for U2): some alive tree extracts, `N = 2` per chain, the `H₂³` term `(Q₃+1)·2·2⁻¹²⁸`; the deterministic step and union bound with any goal (`lean/VoleMole/ROM/LemmaPSome.lean`) | `GoalT`, `GoalS`, `GoalOut`, `SomeExtracted`, `someExtracted_of_major`, `pomBad_traceG`, `prEvent_accept_le_adaptive_pomfritT_EG`, `prEvent_accept_le_adaptive_pomfritTG`, `pomfritT_extract_some_chain`, `combDetG_pomfritT_some`, `pomfritT_accept_le_some` |
| The one-more game with any hint type, table by table, against the derived prover `proverP` (`lean/VoleMole/ROM/OneMoreShiftTable.lean`) | `HTSG`, `hs0G`, `SameG`, `tStep_sameG`, `InvG`, `InvG.step`, `eval_forgerG`, `eval_verOneG`, `eval_verAll_splitG`, `eval_htW_persistG`, `eval_verPreAllG`, `runG`, `ver_tableG` |
| U2's shift rule, its ordering step, a failed forgery of U2 as a bad event of the derived game (`lean/VoleMole/ROM/OneMoreShiftFail.lean`) | `shP`, `hintS`, `hintS_eq`, `shP_eq_alive`, `extractIC_keys_known`, `rel_pick`, `ShiftFailZ`, `shiftFail_events` |
| Theorem U2 with every term explicit, union over forgeries (`lean/VoleMole/ROM/OneMoreShiftBound.lean`, `lean/VoleMole/Assumptions/PomfritShift.lean`; non-vacuity in `Audit/PomfritLemmaP.lean`) | `someEps`, `sfailEps`, `evJS`, `prEvent_shiftFailZ_le`, `prEvent_shiftFail_le`, `pomfrit_U2_explicit`, `pomfrit_U2_omprShift_explicit` |
| Theorem U2 with simultaneous extraction (`lean/VoleMole/ROM/OneMoreShiftSim.lean`, `lean/VoleMole/Assumptions/PomfritShiftSim.lean`; non-vacuity in `Audit/PomfritLemmaP.lean`) | `simBadS`, `simBadS_prefix_congr`, `cellEpsS`, `simEpsS`, `prEvent_simBadS_le`, `prefix_of_shiftFail`, `prEvent_shiftFailZ_sim_le_E`, `sfailSimEps`, `sfailSimEps_eq`, `sum_simEpsS_eq`, `sfailSimEps_le`, `prEvent_shiftFailZ_sim_le`, `prEvent_shiftFail_sim_le`, `pomfrit_U2_sim`, `pomfrit_U2_omprShift_sim` |
| The generic one-more reduction (`lean/VoleMole/ROM/OneMore.lean`): the real game with a programmable target oracle fed by `n` uniform targets, the labelled one-more preimage experiment (Def. 3.1, A-OMPR⊕τ), the reduction; programming is perfect; forger's win `≤` reduction's advantage `+ Pr[∃` claim accepted and not good`]`; with at most `n` target queries the target list never runs out | `omuf`, `omExp`, `red`, `realImpl`, `chImpl`, `redImpl`, `collapse`, `real_eqd_comb`, `omuf_good_le`, `omuf_le_ex`, `omuf_le`, `goodPre`, `goodShift`, `TgInv`, `tgInv_preserved`, `NoFall`, `noFall_of_bound`, `omuf_le_of_bound` |
| PomFRIT's one-more forgery game with `hash_to_target` a random oracle and the verifier as `pomfritVerify` (`lean/VoleMole/ROM/OneMorePomfrit.lean`); distinct messages give distinct `H_T` inputs; at most `Q_T + ℓ + 1` target queries | `game`, `PomWin`, `Forger`, `wrapImpl`, `verOne`, `tgtIn`, `pomfritRedeemT`, `pomfritRedeem_eq_T`, `pomfritTarget_eq_tgtIn`, `honestPre`, `relP`, `tgtIn_inj`, `acomp_support`, `pomWin_forges`, `acomp_bound` |
| Theorems U1 and U2 (§6.4): `Pr[PomWin] ≤ Adv^{ompr}(B; Q_T+ℓ+1, ℓ) + Pr[∃ i, PFail_i]`, and with A-OMPR⊕τ and `ShiftFail_i`; non-vacuity with the honest Issuer (`Audit/Nonvacuous.lean`) | `pomfrit_U1_bound`, `pomfrit_U2_bound`, `pomfrit_U1`, `pomfrit_U2`, `PFail`, `ShiftFail` |
| A-OMPR⊕τ ⇒ A-OMPR, tight; A-OMPR ⇒ A-OMPR⊕τ with loss `τ^{ℓ+1}` (guessing) (`lean/VoleMole/Assumptions/Shift.lean`) | `advOMPR_le_shift`, `advOMPRShift_mono`, `advOMPRShift_le_guess`, `guessRed` |
| Theorem 6, generic core: OMPR ≤ one-more forgery + completeness failure, for the blinding forger of any client with distinct labels (`lean/VoleMole/Assumptions/Blind.lean`); audited at PomFRIT's trapdoor (`Audit/OMPRShift.lean`) | `ompr_le_blind`, `blindAdv`, `Client`, `Distinct`, `bcomb_eqd`, `win_mid`, `post_pres` |
| Theorem 6 at PomFRIT (§6.4): `Adv^{ompr}(B; n, ℓ) ≤ Pr[PomWin(blindForger)] + compFail` in PomFRIT's real one-more forgery game for a forger with coins, for any client as oracle computations; with `B`'s target budget `Q` and `Q + ℓ + 1` targets; the game for a forger with coins is `game` for one without; for the Lean client `compFail ≤ (ℓ+1)·2^{−113}` (G9) (`lean/VoleMole/Assumptions/BlindPomfrit.lean`, `PomClientLean.lean`, `BlindPomfritGrind.lean`, `BlindPomfritComplete.lean`, `BlindPomfritT6Lean.lean`, `ROM/ProverIC.lean`; audited in `Audit/T6Pomfrit.lean`) | `pomfrit_T6`, `pomfrit_T6_bound`, `compFail`, `gameB`, `ForgerB`, `PomWinB`, `gameB_liftF`, `PomClient`, `label_ne`, `toClient`, `distinct_toClient`, `blindForger`, `blindForger_bound`, `star`, `projF_eqd`, `advOMPR_pad`, `compFail_le`, `pomfrit_T6_lean`, `pomfrit_T6_lean_bound`, `leanClient`, `eval_start`, `eval_finish`, `pom_complete`, `fail_table`, `prEvent_grindBad_le`, `step1Q`, `proveCommitQ` |
| Blindness (Thm B, from G1) under (ZK-fix) as a two-phase hypothesis: `≤ 4ε` between the worlds, for either proof layout (`lean/VoleMole/Privacy/PomFRIT.lean`) | `blindness` |
| (ZK-fix) for the executable Lean prover with label rows, from the two-phase tape hypothesis; blindness with that prover; completeness of `verify` on the final signature (`lean/VoleMole/Privacy/PomFRITLean.lean`) | `lean_zeroKnowledge`, `blindness_lean`, `blindness_lean_shake`, `pomfritVerify_complete`, `pomfritVerify_complete_tables` |
| G1 → G2 for one session; G3 exactly (one-time pad, then a swap of the sessions' simulator coins) | `sessionClose_real_sim`, `simGame_eq` |
| Two-phase zero knowledge in the ROM and ideal-cipher model with `H₂³` visible, the continuation reading the tables (`lean/VoleMole/ZK/TwoPhaseRO.lean`, `ZK/TwoPhaseIC.lean`, `ZK/TwoPhaseReadsRO.lean`) | `zk2_rom_ic_h23`, `zk2_rom_ic_h23_num`, `zk2_ro`, `lean_zeroKnowledgeROS2` |
| Blindness in the ROM and ideal-cipher model, both sessions on shared tables, the Issuer's guess seeing them (`lean/VoleMole/Privacy/PomFRITRO.lean`) | `blindnessRO`, `blindnessRO_lean`, `hop0`, `hop1`, `G2_swap`, `realGameRO_iff`; the collision term: `deltaRO_le`, `blindnessRO_lean_num` (`Privacy/PomFRITDelta.lean`) |
| Liveness (`lean/VoleMole/Audit/Liveness.lean`): an Issuer with a trapdoor key (`keyI`, a key of pqov's key generation with `O = 0` whose signer never fails) makes both sessions finalize on every tape, so the guess sees both signatures in message order; every PomFRIT game uses the label-row layout of the Lean prover, so no length check rejects an honest session (not shown: that the revealed signature passes `pomfritVerify`) | `realGame_liveP`, `realGameRO_liveP`, `session_live` |
| Two-phase zero knowledge with a continuation that reads the slice, `H₅` and the cipher after step 1 (`lean/VoleMole/ZK/TwoPhaseAd.lean`) | `zk2_rom_ic_h23A`, `zk2_rom_ic_h23A_num`, `zk2_adaptive`, `Hyp2RA` |
| Blindness with the Issuer's key, messages and responses reading the tables except `H₂³` (`lean/VoleMole/Privacy/PomFRITRA.lean`, `Privacy/PomFRITRAGame.lean`) | `AdversaryRA`, `IBudget`, `hyp2RA_R`, `hyp2RA_S`, `budget_D0A`, `budget_D1A`, `hop0RA`, `hop1RA`, `G2RA_swap`, `deltaRA_le`, `blindnessRA`, `blindnessRA_lean_num`; for an Issuer written as oracle computations over the tables (no consistency hypothesis, `ROM/PrivacyReads.lean`): `AdversaryOC`, `blindnessOC_lean_num`, `blindnessOC_lean_num_perm` |
| Blindness with the Issuer's interaction reading `H₂³` too (`lean/VoleMole/Privacy/PomFRITRAH.lean`, `ZK/CollideAd2.lean`) | `SReadsP`, `IBudgetH`, `AdversaryRA.subst`, `pr_resampleC`, `pr_G0RA_resample`, `G0_at_iff_subst`, `K1R`, `hyp2RA_R1`, `pr_tail2A`, `pr_bad0H`, `pr_bad1H`, `G0RA_subst_close`, `blindnessRAH_lean_numG`, `blindnessRAH_lean_num`; `blindnessRAH_lean_num_perm` (`Privacy/PermRA.lean`); `blindnessOCH_lean_num`, `blindnessOCH_lean_num_perm` (`ROM/PrivacyReads.lean`); counting prefixes: `pr_tail2A_pfx`, `IBudgetHB`, `IBudgetH.toB`, `pr_bad0H_pfx`, `pr_bad1H_pfx`, `G0RA_subst_close_pfx`, `blindnessRAH_lean_numG_pfx`, `blindnessRAH_lean_num_pfx`, `blindnessRAH_lean_num_perm_pfx` (`Privacy/PomFRITRAHPfx.lean`) |
| Blindness with AES as random permutations (`lean/VoleMole/Privacy/PermRO.lean`, `Privacy/PermRA.lean`, `ZK/TwoPhasePerm.lean`; `lean/docs/zk.md` §10.4) | `zk2_rom_ic_h23_num_perm`, `zk2_adaptive_perm`, `blindnessRO_lean_num_perm`, `blindnessRA_lean_num_perm` |
| Blindness with one shared `H₃` (`lean/VoleMole/ZK/SharedH3Two.lean`, `Privacy/SharedH3PomFRIT.lean`, `Privacy/SharedH3PomFRITRA.lean`, `Privacy/SharedH3PomFRITRAH.lean`, `ZK/SharedH3Tail.lean`, `ROM/SharedH3Reads.lean`; `lean/docs/zk.md` §10.5) | `zk2_sharedA`, `zk2_shared`, `deltaRO_sh`, `deltaSh_le`, `blindnessSh_num`, `blindnessRASh_num`, `blindnessOCSh_num`, `pr_tail2Sh`, `pr_G0RASh_resample`, `pr_bad0HSh`, `pr_bad1HSh`, `blindnessRAHSh_num`, `blindnessOCHSh_num`, with `_perm` |
| G0 → G1, the seed-XOF hop (`lean/VoleMole/Privacy/SeedXOF.lean`, `Privacy/SeedXOFGames.lean`, `ROM/SeedXOFReads.lean`; `lean/docs/zk.md` §10.6) | `abs_pr_seed_le`, `abs_pr_seedGame_sub_le`, `blindnessRO_lean_num_seed`, `blindnessRA_lean_num_seed`, `blindnessRAH_lean_num_seed`, `blindnessSh_num_seed`, `blindnessRASh_num_seed`, `blindnessOC_lean_num_seed`, `blindnessOCH_lean_num_seed`, `blindnessOCSh_num_seed`, `blindnessRAHSh_num_seed`, `blindnessOCHSh_num_seed`, with `_perm_seed` |
| Blindness with many sessions: further honest sessions on the same tables, concurrently with the challenge pair, as a reduction to the table-reading game (the further sessions consistent table readers); `N` challenge pairs by a hybrid over the pairs (`lean/VoleMole/Privacy/PomFRITMany.lean`, `ZK/ReadsMany.lean`; `lean/docs/zk.md` §10.8) | `AdversaryN`, `realGameN`, `realGameN_iff`, `s1R_sreads`, `step1_cons`, `red_iBudget`, `red_gBudget`, `blindnessN_lean_numG`, `blindnessN_lean_num`, `blindnessN_lean_num_perm`, `blindnessN_lean_le`, `blindnessN_lean_2pow20`, `blindnessN_lean_2pow32`; `AdversaryP`, `realGameP`, `realGameP_iff`, `abs_sub_le_mul_of_steps`, `blindnessP_lean_numG`, `blindnessP_lean_num`, `blindnessP_lean_num_perm`, `blindnessP_lean_le`, `blindnessP_lean_2pow20`, `blindnessP_lean_2pow32` |
| Blindness with many sessions and `H₄` a random-oracle table, with no per-session charge: step 1 reads the cipher only at its tree's nodes on the CTR blocks of its own `iv`, so the further sessions are moved to private tables by lazy sampling, up to the event that a challenge session reads one of their points (equal `iv`s, or a common node with equal second `iv` lanes, `≤ 4·2⁻¹²⁸` per pair of sessions) (`lean/VoleMole/Privacy/PomFRITLin.lean`, `ZK/ReadsPoint.lean`; `lean/docs/zk.md` §10.8) | `hb4`, `step1Iv_hb4`, `step1_consP`, `rdX_cons`, `QX_cons`, `AdversaryN.redP`, `redP_iBudget`, `redP_gBudget`, `red_close_redP`, `red_step`, `Bp_cases`, `pr_treeNode_eq_le`, `pr_Bp_le`, `pr_badQ_le`, `realGameNH`, `blindnessNH_lean`, `blindnessNH_lean_le`, `blindnessNH_lean_2pow20`, `blindnessNH_lean_2pow32`, `realGamePH`, `blindnessPH_lean`, `blindnessPH_lean_le`, `blindnessPH_lean_2pow20`, `blindnessPH_lean_2pow32` |
| Blindness with an adaptive schedule: further sessions run one after the other before, during and after the challenge, each chosen from the earlier sessions' outcomes; the reduction runs them inside its `H₂³`-reading interaction (`RAH`), a whole session (step 2 included) a consistent table reader (`lean/VoleMole/Privacy/PomFRITAdaptive.lean`; `lean/docs/zk.md` §10.8) | `fullX`, `fullX_sreads`, `sigR_h23`, `preX_cons`, `sigR_tables`, `runSeq`, `runSeq_sreads`, `SReadsP.of_shared`, `AdversaryAd`, `realGameAd`, `realGameAd_iff`, `red_iBudgetH`, `red_gBudget`, `blindnessAd_lean_numG`, `blindnessAd_lean_num`, `blindnessAd_lean_num_perm`, `blindnessAd_lean_le`, `blindnessAd_lean_2pow20`, `blindnessAd_lean_2pow32`; counting prefixes (`Privacy/PomFRITAdaptivePfx.lean`, `≤ n·2⁻¹⁰²`): `SReadsB`, `fullX_sreadsB`, `runSeq_sreadsB`, `red_iBudgetHB`, `blindnessAd_lean_numG_pfx`, `blindnessAd_lean_num_pfx`, `blindnessAd_lean_num_perm_pfx`, `blindnessAd_lean_le_pfx`, `blindnessAd_lean_2pow20_pfx`, `blindnessAd_lean_2pow32_pfx` |
| Blindness with an interleaved schedule: the Issuer an interactive machine that starts further sessions and delivers responses to pending ones in any order; the whole interleaved run is a consistent table reader with `n` times a session's reads, because a session's read set (step 1's keys, then `fullKeys`) depends only on its tape and its messages and grows with them (the interleaving lemma, `lean/VoleMole/ZK/ReadsInterleave.lean`; `lean/VoleMole/Privacy/PomFRITInterleave.lean`; `lean/docs/zk.md` §10.8, `≤ (n + 2)·2⁻¹⁰²`) | `Act`, `Ev`, `runT`, `SessReads`, `Good`, `Good.step`, `Good.run`, `Good.sreads`, `card_RQl`, `fullX_cons`, `outIL`, `QIL`, `sessReads_IL`, `Good.sreadsB_IL`, `AdversaryIL`, `realGameIL`, `realGameIL_iff`, `red_iBudgetHB`, `red_gBudget`, `blindnessIL_lean_numG`, `blindnessIL_lean_num`, `blindnessIL_lean_num_perm`, `blindnessIL_lean_le`, `blindnessIL_lean_2pow20`, `blindnessIL_lean_2pow32` |
| Blindness with an interleaved schedule whose scheduler reads the tables (each step a VCVio oracle computation over both challenge slices and the shared tables, within a per-step query bound) and places the challenge (it starts when `go` holds, its answers are taken when `done` holds); the interleaving lemma with the scheduler's query logs added to the union, consistent by construction (`lean/VoleMole/ZK/ReadsInterleaveOC.lean`; `lean/VoleMole/Privacy/PomFRITInterleaveOC.lean`; `lean/docs/zk.md` §10.8, `≤ (n + 2)·2⁻¹⁰² + 52·L·(a₃ + a₂ + a₅ + 221·a_E)·2⁻¹²⁸` plus budget terms) | `stepO`, `runO`, `logO`, `GoodO`, `GoodO.run`, `GoodO.sreads`, `countP_logO_qb`, `runO_pure`, `GoodO.sreadsPB_IL`, `AdversaryILO`, `realGameILO`, `realGameILO_iff`, `realGameILO_toO`, `blindnessILO_lean_numG`, `blindnessILO_lean_num`, `blindnessILO_lean_num_perm`, `blindnessILO_lean_le`, `blindnessILO_lean_2pow20`, `blindnessILO_lean_2pow32` |
