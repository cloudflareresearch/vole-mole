# UOV assumptions behind vole-mole's unforgeability proofs

This note relates the protocol-specific UOV assumptions used in
- `lean/docs/security/pomfrit.md` (A-OMPR, i.e. Def. 3.1 of ePrint 2026/109, and its τ-shift variant A-OMPR⊕17),
- `lean/docs/security/moussaka.md` (CT-UF and its Lemma U),
- `lean/docs/security/ratatouille.md` (A-OMPI, UF-Tag, the Lean theorem's UF-Tag with a signability
  probe, recommendation R1),

to each other and to the standard UOV assumptions: the UOV problem, and EUF-CMA of the specified
(salted) scheme. Where a reduction is not available, the note says exactly why.

The counting cores are checked in Lean, in `lean/VoleMole/Protocols/UOVAssumptions.lean`
(no `sorry`, no `axiom`; check it with
`cd lean && lake env lean VoleMole/Protocols/UOVAssumptions.lean`).

Line references are to the working tree at commit `6d7113e`. pqov references are to the patched
checkout `subprojects/pqov` (revision `fac2ec1`, UOV round-3 code, with
`subprojects/packagefiles/pqov-patches/0001`).

## 0. Summary

**Definitions** (§3). Besides the six assumptions in the task, the note needs:
- **OW**: one-wayness of `P` on `P(s)` for uniform `s`;
- **GPI(q)** (*good-preimage indistinguishability*): given `pk`, `q` uniform points of
  `F^119` are hard to tell from `q` uniform *good* points, i.e. points whose vinegar gives an
  invertible oil system;
- **CT-UF^open**: CT-UF in which the adversary must also open every target it had signed (plain
  CT-UF is false for UOV, row O);
- **det-FDH**: EUF-CMA of deterministic hash-and-sign UOV, `σ = D_sk(H(m))`.
- **UF-Tag+probe**: UF-Tag with an extra oracle that reveals only whether `D` succeeds on
  `Tag(c, x)`. This is the game of the Lean balance theorem.

**Results.**

| # | Statement | Loss | Where |
|---|---|---|---|
| L-D | `derive_preimage` (ROM) is the *ideal deterministic sampler*: `D(y)` uniform on the good preimages of `y`, independently per `y` | `q_v·2^{−256} + ℓ·E[δ^{256}]` | §2 |
| L-C | Real preimages are never "bad"; uniform ones are bad w.p. `δ ≈ 2^{−7.994}`. q samples: TV `1 − (1−δ)^q` exactly. Every public-key-only simulator is off by at least its mass on bad points | exact | §2, §4 |
| T1 | A-OMPI ≡ det-FDH EUF-CMA (ROM); `Adv^{euf}_{spec} ≤ Adv^{ompi} ≤ Adv^{suf}_{spec}`; `Adv^{ompi} ≤ Adv^{ompr}`. [Lean] (a) and (c); (c) needs `q_T + Q` targets and costs `(q_T + Q)·ρ` with a sampler that may fail (corrected) | tight; (c) tight up to the sampler-failure term `(q_T + Q)·E[δ^{255}]` (SUF step: `q_H` signing queries) | §5.1 |
| T2 | A-OMPI ⇐ GPI + OW, or ⇐ GPI + UOV problem | `q_T` | §5.2 |
| T3 | EUF-CMA of the **specified** salted UOV ⇐ GPI + UOV problem. (The spec's own proof is for salt-UOV, a different signer.) | `q_H + 1` on UOV, none on GPI | §5.3 |
| T4 | **Lemma U is incorrect as stated**: CT-UF with an arbitrary-target signing oracle does not follow from OMPR; it is in fact false (row O). CT-UF^open ⇐ OMPR, tight up to the sampler-failure term `n·E[δ^{255}]`, `n = q_f + 2q_S + 1` ([Lean] with `Com` a random function: `advCTUFIdeal1_le_ompr`; the paper's timing term is unnecessary; `K` keys by guessing, `advCTUFIdeal_le_ompr`); CT-UF^open ⇐ GPI + OW | tight up to `n·E[δ^{255}]`, ×K / `q_π` | §5.4 |
| T5 | With R1, Ratatouille balance ⇐ EUF-CMA of salted UOV with `H = Tag`, which ⇐ GPI + UOV (or ⇐ UOV alone with salt-UOV signing) | `q_K + 1` | §5.5 |
| T6 | **PomFRIT ⇔ OMPR**: an OMPR breaker *is* a PomFRIT one-more forger. So OMPR ≤ PomFRIT ≤ OMPR⊕17. [Lean] generic core for any client with distinct session labels, plus a completeness term (`ompr_le_blind`); in PomFRIT's real game for any client as oracle computations (`pomfrit_T6`); the completeness term for the Lean client is paper (`pomfrit.md` G9) | tight, plus completeness failures | §5.6 |
| P7 | OMPR does not reduce to the UOV problem, OW or any EUF/SUF-CMA notion by a key-preserving black-box reduction (theorems A1–A3 of `uov-open-structure.md`; §5.7 has the original sketch). Determinism makes a separation easier, not harder (A2) | `k + 1` (runs of the adversary) | §5.7, `uov-open-structure.md` Part A |
| O | **Follow-up (`uov-open-reductions.md`).** CT-UF as defined is **false**: `P(λs) = λ²P(s)`, so one query on `μ·Com(x*)` forges. Its repair up to scalars equals "OMPR with free non-challenge calls", which no relativizing reduction derives from OMPR. For OMPR ⇒ OMPR⊕τ, every relativizing reduction, with rewinding, loses `≥ τ^{q+1}/2` | — | `uov-open-reductions.md` |
| P8 | OMPR⊕τ ⇐ OMPR loses `τ^{q+1}`. Every *simple-embedding* reduction loses that much against some adversary. In a generic model the two assumptions have the same bound. For PomFRIT's tree shapes, U1's additive `Q₃·2^{−71}` (≈ `2^{−7}` at `2^{64}` queries) is unavoidable for simple-embedding reductions, and (row O) for every relativizing reduction up to a factor 2. [Lean] (a) `advOMPRShift_le_guess`; the converse OMPR⊕τ ⇒ OMPR, tight, `advOMPR_le_shift` | — | §6 |
| P9 | UF-Tag+probe ≡ UF-Tag up to the aborts of `D` on signed or probed pairs; so UF-Tag+probe ⇐ A-OMPI ⇐ OMPR with no extra oracle calls. The probe and the paper's abort event `E4` cost the same in Ratatouille's balance; R1 does not change this, the F5 fix removes the probe. [Lean] (a) `ufTagAdv_le_noProbe`, `balance_le_noProbe` | `(q_S + q_P)·E[δ^{255}] + q_v·2^{−256}` (≈ `N·2^{−295.8}`) | §5.8 |

**Follow-up.** `uov-open-structure.md` treats two of the open items of §9: the meta-reduction
(Part A) and the cryptanalysis of GPI (Part B: reliable badness tests are key-recovery attacks;
conjectured security of GPI ≈ key recovery, `≈ 2^{201}` bit operations for uov-Ip; estimates under
  semi-regularity, literature cited from memory).

**Cryptanalysis of OMPR.** `ompr-cryptanalysis.md` studies attacks that use the oracle of OMPR
and OMPR⊕τ (key recovery from the answers, one more preimage, shifts). It finds none below the
oracle-free attacks: direct forgery `≈ 2^{140}` multiplications, key recovery `≈ 2^{194}`.
`ompr-cryptanalysis-2.md` is a second pass. It lowers the forgery figure: `P(s) ∈ F·t` is 44
homogeneous quadrics, and a solution scales to a preimage of `t` (known: Ostuzzi, ePrint
2026/2247). In the cost model of the UOV round-3 specification this is `≈ 2^{135.1}`
multiplications, `2^{142.2}` bit operations, against `2^{146.8}` without it and NIST level 1's
`2^{143}` (its §8). This is an attack on the UOV problem, without calls. It also bounds statistics
of the answers of every degree, gives quantum estimates (Grover-hybrid forgery `≈ 2^{120}`
gates, above AES-128 key search at every depth limit), and finds no multi-target gain.

**Assessment** (§7).
- State all three protocols under **one** assumption: **A-OMPR**, i.e. Def. 3.1 instantiated with
  uov-Ip and `derive_preimage`, per key. It is *necessary* for PomFRIT (T6) and suffices tightly, up to
  the sampler-failure term `n·E[δ^{255}] ≈ n·2^{−295.8}`, for Moussaka (via CT-UF^open) and
  Ratatouille (via A-OMPI).
- In Lean, Moussaka and Ratatouille end at OMPR (`omuf_le_num_ompr`, `balance_le_ompr`), each under
  one named modelling hypothesis that idealizes `Com` (`hmodel`) or `Tag` (`TagIdeal`) in the
  standalone game only. For Moussaka (both variants) the hypothesis can instead be taken with
  `Com` a random permutation with inverse queries (`hmodelP`; `omuf_le_num_ompr_perm`,
  `omufU_le_num_ompr_perm`), the permutation terms explicit (§5.4), and also with AES as random
  permutations (`omuf_le_num_ompr_simP`, `omufU_le_num_ompr_simP`). For Ratatouille the
  hypothesis can be taken with `Tag` a random permutation with inverse queries (`TagIdealP`;
  `balance_le_ompr_perm`, `balance_le_ompr_sim_perm`, §5.8), also with AES as random
  permutations (`balance_le_ompr_simP`, `balance_le_ompr_sim_permP`). PomFRIT's U1 and U2 are stated with OMPR and OMPR⊕τ
  (`pomfrit_U1_ompr`, `pomfrit_U2_omprShift`).
- Secondary statements: Moussaka and Ratatouille also follow, with loss `q`, from GPI plus the UOV
  problem (or OW). Ratatouille also follows from SUF-CMA of the specified scheme.

**Recommendations** (§8).
- Documentation:
  - fix Moussaka's Lemma U by using CT-UF^open (B₂ already has the openings) — done in
    `moussaka.md` §3.3;
  - qualify Ratatouille §2.3: the 1/255 gap also affects the *specified* salted UOV, and only
    salt-UOV signing avoids it.
- R1 (Ratatouille salt) is cheap, and moves the assumption to salted-UOV EUF-CMA.
- Hash-then-sign the request in Moussaka and PomFRIT, with a salted, domain-separated KP800 tag.
  This would put all three protocols on salted-UOV EUF-CMA. It also removes PomFRIT's
  OMPR/17-shift issue, and the cross-protocol raw-preimage hazard. The cost is one KP800 in the
  proved circuit (≈ +3.7 KB per proof).
- Do not randomize preimages.
- Do not adopt salt-UOV retry signing unless its retry count is hidden.

---

## 1. Model and notation

- `F = GF(256)`. `(N, M, V) = (119, 45, 74)` (`uov.hpp:17-18`, pqov `_OV256_119_45`, `_OV_PKC`,
  i.e. uov-Ip-pkc). `KeyGen` is pqov's `generate_keypair_pkc` on a 32-byte `sk_seed`
  (`uov.cpp:62-70`, `ov_keypair.c:170-208`): `pk_seed ‖ O ← SHAKE256(sk_seed)`, and `P1, P2` are
  expanded from `pk_seed`.
- The public map `P : F^N → F^M` vanishes on the oil space `𝒪 = {(O·x, x) : x ∈ F^M}`.
  - Write `ι(x) = (O·x, x)`, and for `s ∈ F^N` let `vin(s) = s[0..V) − O·s[V..N)`. Then
    `s = (vin(s), 0) + ι(x)` is a bijection `F^N ≅ F^V × F^M`.
  - For `v ∈ F^V`, `P((v,0) + ι(x)) = P(v,0) + L_v·x`, with `L_v` an `M × M` matrix that depends
    on `v` and `sk` but **not** on the target. This holds because `P` is quadratic and its polar
    form vanishes on `𝒪 × 𝒪`.
- **Good and bad.** `G_sk = {v : L_v invertible}`, `δ = δ(sk) = 1 − |G_sk|/256^V`.
  - `Good = {s : vin(s) ∈ G_sk}` and `Bad = F^N ∖ Good`, so `|Bad|/|F^N| = δ`.
  - `S^G_y = {s ∈ Good : P(s) = y}`.
  - Intrinsically, `s` is bad iff `𝒪 ∩ ker(DP_s) ≠ {0}`, where `DP_s = P'(s, ·)` is the
    differential.
- **Heuristic value of δ.** If `L_v` behaves like a uniform matrix, then
  `δ = 1 − ∏_{i=1}^{45}(1 − 2^{−8i}) = 0.0039215… = 2^{−7.994}`.
  - Lean `singular_prob_bounds_256` proves `δ_unif ∈ [2^{−8}, 1/255]` from Mathlib's
    `card_GL_field`.
  - The proofs below carry `δ(sk)` as a parameter.
  - **Only on average over the key.** For a fixed key `L_v = vᵀS` is linear in `v`, so it ranges
    over a subspace of dimension `≤ 74` of the `45 × 45` matrices and its law is not uniform (a
    key with `S = 0` has `δ = 1`). With `S = (P1 + P1ᵀ)O + P2` uniform (uniform `P2`), `L_v` is
    uniform for `v ≠ 0`, so `E[δ] ≤ δ_unif + 256^{−74}`, and `m ≤ 74` linearly independent
    vinegars give independent uniform systems, so `E[δ^m] ≤ δ_unif^m + 256^m/(255·256^{74})`
    (`E[δ^{255}] ≤ 255^{−37} + 1/(255·256^{37}) ≈ 2^{−295.8}`). Lean: `pr_singular_avg`,
    `pr_singular_all`, `pr_dependent_le` (`Privacy/PqovDelta.lean`), and for pqov's key
    generation with **any** oil matrix `O` and `P1` (fixed) and `P2` uniform
    `avg_delta255_pqovKey` (`Privacy/PqovKeys.lean`; `avg_delta255_keyO0` is `O = 0`). `S` is read
    from the key layout (`sysCoef_pqovKey`). The modelling step is `P2` uniform given `(O, P1)`:
    AES-128-CTR of `pk_seed` as a random function, `O` independent of `pk_seed` (SHAKE256 a random
    oracle); it is not derived.
- **The UOV identities, in Lean** (`Spec/PqovKey.lean`, on the expanded key in
  `for_each_monomial`'s layout, blocks `P1`, `P2`, `P3` at pqov's `idx_of_trimat` offsets):
  - For every key, `B(e_i, (O_j, e_j))_k = ((P1 + P1ᵀ)·O + P2)_{k,ij}` (`sysCoef_eq_pqovS`: the
    system the signer model builds from the polar form is pqov's `ov_calc_l1_mat`, `vᵀS`), and
    `P(v, 0) = P₁(v)` (`qmap_vinVec_eq`).
  - `P(Oy, y) = Σ_{a ≤ b} (P3 − UT(M + Mᵀ))_{ab} y_a y_b` with `M = Oᵀ(P1·O + P2)`
    (`qmap_oil_eq`), so `P` vanishes on `𝒪` **iff** `P3 = UT(M + Mᵀ)`, pqov's `calculate_F2_P3`
    (`oilSpace_iff_P3Pqov`). `pqovKey O P1 P2` (the key with that `P3`) satisfies it for all `O`,
    `P1`, `P2` (`oilSpace_pqovKey`), so `Spec.Pqov.signer` is correct for pqov's keys.
  - `lake exe spec_kats` runs the model (`Spec/PqovSignerExec.lean`) on the test key with pqov's
    vinegars: it reproduces the C++ `derive_preimage` on six KAT targets byte for byte.
- **Oracles.** SHAKE256 is a random oracle. That covers pqov's key expansion and vinegar hash, and
  vole-mole's key digest; these have distinct input lengths (32, 98 and 46591 bytes), so they are
  disjoint.
  - Where a protocol hash or commitment is idealised, it is said explicitly.
  - Keccak-p[800,12] (Com, Tag) is idealised **only inside standalone games**, never inside the
    protocol proofs, as `moussaka.md` F3 requires.
- **Advantages** are written `Adv^{x}(A; params)`. A "loss" `L` means `Adv_target ≤ L·Adv_base + …`.

## 2. What `derive_preimage` does, exactly

`SecretKey::derive_preimage` (`uov.cpp:104-110`) calls `ov_derive_preimage`, which comes from
patch 0001 (`ov.c:226-239` after patching):

```
D_sk(y):                                  // y ∈ F^45, used as is (no hashing, no salt)
  for ctr = 0, 1, …, 255:
    v ← SHAKE256(y ‖ sk_seed ‖ "pqov-derive-preimage" ‖ ctr)[0..74)      // ctr: one byte
    if L_v is invertible:                 // gf256mat_gaussian_elim; l1_succ is declassified
      x ← L_v^{-1}·(y − P(v,0))
      return (v + O·x, x)                 // = (v,0) + ι(x)
  fail                                    // C++: throws std::runtime_error
```

- **Deterministic** in `(sk_seed, y)`. The whole secret key is a function of `sk_seed`.
- **Vinegar** is derived from the target and the secret seed by SHAKE256, with a DST that separates
  it from `ov_sign`'s `H(m‖salt‖sk_seed‖ctr)` (patch comment, `ov.c:217-224`). vole-mole never
  calls `ov_sign`.
- **Retries** happen on a singular `L_v`. pqov draws at most 256 vinegars but **uses only 255**:
  `ov_preimage_core` increments `n_attempt` before each attempt and, after the loop, returns `-1`
  if `MAX_ATTEMPT_VINEGAR <= n_attempt` (`subprojects/pqov/src/ov.c:166`), which also holds after a
  success at `ctr = 255`. So `D_sk` fails iff the first 255 vinegars are bad, and the abort
  probability is `δ^{255}` (not `δ^{256}`; read `E[δ^{256}]` below as `E[δ^{255}]`, a negligible
  difference). Since `L_v` does not depend on `y`, this holds at every target. Lean:
  `Spec.Pqov.signer` (`tries = 255`), `signer_fail`, `signer_correct`.
- **Timing** reveals the number of rejected vinegars. These are independent of the output, so this
  reveals nothing about the returned preimage.
- **The same function** serves PomFRIT (`pomfrit.cpp:189`), Moussaka (`moussaka.cpp:135`) and
  Ratatouille (`ratatouille.cpp:180, 282`). There is no per-protocol separation, so key separation
  is the caller's job (`uov.hpp:64-68`).

**Lemma C (counting; Lean `card_good_fiber`, `good_coords_bijective`).**
- For every `y`, `|S^G_y| = |G_sk|`. The map `v ↦ (v,0) + ι(L_v^{-1}(y − P(v,0)))` is a bijection
  `G_sk → S^G_y`.
- `(v, y) ↦ (v, x)` is a bijection `G_sk × F^M → G_sk × F^M`. So a uniform `y` and a uniform
  `v ∈ G_sk` give a uniform point of `Good`.

**Lemma D (ideal deterministic sampler).**
- Let `D*` be the random function that assigns to each `y`, independently, a uniform element of
  `S^G_y`.
- Consider any `A` with `q_v` SHAKE256 queries and `ℓ` queries to `D_sk` (and `pk`). Then

      | Pr[A^{D_sk}(pk) = 1] − Pr[A^{D*}(pk) = 1] | ≤ q_v·2^{−256} + ℓ·E_sk[δ(sk)^{256}].

*Proof.*
1. `pk` and `O` are RO outputs on `sk_seed`, so `A`'s view is independent of `sk_seed` until `A`
   queries an input containing it.
2. Each query contains at most one candidate seed: the 32-byte input itself, or bytes 45..77 of a
   98-byte input. So such a hit has probability `≤ 2^{−256}` per query.
3. Without a hit, the vinegars `v_{y,0..255}` are i.i.d. uniform on `F^V`, and independent across
   distinct `y`.
4. The first good one is uniform on `G_sk`, except when all 256 are bad (probability `δ^{256}`).
5. By Lemma C, its completion is uniform on `S^G_y`. ∎

**Corollary.** For uniform `y`, the pair `(y, D*(y))` is `s ← U(Good)` with `y := P(s)`.
- The naive simulation instead samples `s ← U(F^N)`.
- By Lean `tv_unif_good` and `tv_unif_good_pow`:

      TV(U(Good), U(F^N)) = δ,        TV(U(Good)^q, U(F^N)^q) = 1 − (1 − δ)^q.

- For uov-Ip this is `0.63` at `q = 256`, `0.98` at `q = 1024`, and `1 − 2^{−5944}` at
  `q = 2^{20}`.
- So the gap is **information-theoretically** detectable, for an unbounded distinguisher, after a
  few hundred samples. A computational argument is unavoidable (§4).

## 3. The assumptions

All games are for one key `(sk, pk) ← KeyGen` unless `K` is given. `D = D_sk` throughout.

1. **UOV problem** (UOV spec v3, App. A, Def. 2, for the uov-Ip-pkc key distribution).
   `Adv^{uov}(A) = Pr[P(A(pk, t)) = t]`, with `t ← U(F^M)`.
   - The **n-target** version ("find a preimage of any one of `t_1..t_n`") is at most
     `n·Adv^{uov}`, by guessing.
   - *MQ on random targets* (spec Def. 1, a random quadratic map) is a different, presumably
     harder, problem. Nothing below reduces to it.
2. **OW**: `Adv^{ow}(A) = Pr[P(A(pk, P(s))) = P(s)]`, with `s ← U(F^N)`.
   - `P_*(U(Good)) = U(F^M)` by Lemma C. So `|Adv^{ow} − Adv^{uov}| ≤ δ` statistically, but no tight
     reduction is known in either direction.
3. **GPI(q)** (new; decisional):

       Adv^{gpi}(A; q) = | Pr[A(pk, s_1..s_q) = 1 : s_i ← U(F^N)] − Pr[A(pk, s_1..s_q) = 1 : s_i ← U(Good_sk)] |.

   - The challenger needs `sk` to sample `U(Good)`, so the assumption is falsifiable.
   - It is statistically false for `q ≳ 2^8` (Corollary). It asks that no *efficient* algorithm
     detects badness.
   - Deciding badness of `s` means deciding whether `𝒪` meets the public 74-dimensional space
     `ker DP_s` nontrivially. We know no way to do that without `𝒪`. This is a structural
     property of `𝒪`, of the kind the intersection attack exploits [Beu21], so GPI needs
     cryptanalysis like any new assumption. A first analysis is in `uov-open-structure.md`
     Part B.
4. **EUF-CMA / SUF-CMA of the specified scheme** (UOV spec §3.2; pqov `ov_sign`), ROM.
   - `σ = (s, salt)`, with `salt ← {0,1}^{128}`, `y = SHAKE256(m‖salt)|_{45}`, and `s` from the
     loop above with vinegar `SHAKE256(m‖salt‖sk_seed‖ctr)`.
   - EUF: forge on an unqueried `m`. SUF: forge a pair `(m, σ)` not returned by the oracle.
5. **EUF-CMA of salt-UOV** (spec App. A, Fig. 4 [SSH11]). The vinegar is fixed per signature. The
   *salt* is retried until the system is solvable, and a uniform solution is taken.
6. **det-FDH**: EUF-CMA of `Sign(m) = D(H(m))`, with `H` a random oracle into `F^M`.
7. **OMPR(n, q)** (paper Def. 3.1, `pomfrit.md` A-OMPR), with `(TrapGen, SPre) = (KeyGen, D)`.
   - `A` gets `pk` and `t_1..t_n ← U(F^M)`, and makes ≤ `q` calls to `D` on arbitrary targets.
   - It wins with `q+1` pairs `(s_i, I_i)` with distinct `I_i` and `P(s_i) = t_{I_i}`.
   - With targets requested on demand, the notion is the same (reveal pre-sampled targets lazily).
   - Since `D` is a function, repeated calls are useless. So "≤ q calls" is "≤ q distinct targets"
     without loss of generality.
8. **OMPR⊕τ(N, q)** (`pomfrit.md` A-OMPR⊕τ).
   - On its `k`-th request, `A` submits shifts `δ_{k,1..m_k}` (`m_k ≤ τ`) and receives
     `h_k ← U(F^M)`.
   - It wins with `q+1` triples `(k_i, a_i, s_i)` with distinct `k_i` and
     `P(s_i) = h_{k_i} ⊕ δ_{k_i,a_i}`, after ≤ `q` calls to `D`.
9. **A-OMPI(q_T, Q)** (`ratatouille.md` §2.3). Targets `y_1, y_2, …` come on demand. The oracle is
   `i ↦ D(y_i)` (**indices only**, ≤ `Q` calls). `A` wins with `(i*, s*)`, where `i*` was never
   queried and `P(s*) = y_{i*}`.
10. **CT-UF_K** (`moussaka.md` §3.3). `A` gets `P_1..P_K` and `Sign_k = D_{sk_k}` on **arbitrary**
    targets. It wins with `(k, x*, s*)`, where `x* ∈ D_Com`, `P_k(s*) = Com(x*)`, and `Com(x*)`
    was never queried to any `Sign_j`.
    - **False as stated** (`uov-open-reductions.md` Theorem B1): `P` is homogeneous of degree 2, so
      the answer to `Sign_k(μ·Com(x*))`, `μ ∉ {0,1}`, rescaled, is a forgery. Use CT-UF^open
      (item 11), which is not affected.
11. **CT-UF^open_K** (new). This is CT-UF_K, except that `A` must also output, for every target `t`
    it queried to `Sign_k`, an opening `x_t ∈ D_Com` with `Com(x_t) = t`. Otherwise it loses.
12. **UF-Tag** (`ratatouille.md` §2.3). The oracle takes `(c, x)` and returns `D(Tag(c, x))`.
13. **UF-Tag+probe** (new; Lean `TagForger`, `UFWin`, `ufTagAdv`). UF-Tag plus a probe oracle
    `(c, x) ↦ [D(Tag(c, x)) ≠ ⊥]`. `A` wins with a valid `(c*, x*, s*)` if no signing query on
    `(c*, x*)` was answered: an unsigned, a probed-only, or a failed pair counts. Equivalent to
    UF-Tag up to `(q_S + q_P)·E[δ^{255}] + q_v·2^{−256}` (§5.8).

**Lean.** Every item except 4 and 5 is a game in `lean/VoleMole/Assumptions/UOV.lean`, generic in
`KeyGen`, the preimage relation of `P` and `D` (`Trapdoor`): `advUOV`, `advUOVn` (1), `advOW` (2),
`advGPI` (3), `advFDH` (6), `advOMPR` and `advOMPR31` (7), `advOMPRShift` (8), `advOMPI` (9),
`advCTUF` (10), `advCTUFOpen` (11), `advUFTag` and `advUFTagProbe` (12). The protocol theorems'
terms are advantages in them (`Assumptions/UOVLinks.lean`). T1(a) and T1(c) are proved between
them (`Assumptions/IdealTag.lean`), and Ratatouille's balance is stated with `advOMPR`
(`Assumptions/RatatouilleOMPR.lean`). With `Tag` a random function, item 12 with the strict win is
item 6 with `H = Tag`. See §10.

## 4. The 1/255 obstacle, and what can fix it

Every reduction to the UOV problem or OW must answer signing or preimage queries without `sk`.

**Proposition 4.1 (no statistical fix).**
- Let `μ` be the output distribution of any sampler for preimages of programmed targets, i.e. it
  outputs `s` and programs `y := P(s)`.
- By Lean `tv_ge_mass_off`, `TV(μ, U(Good)) ≥ μ(Bad)`.
- So a simulator beats the naive one (`μ = U(F^N)`, `μ(Bad) = δ`) by `ε` per sample only if it
  lands in `Bad` with probability `≤ δ − ε`.
- That means a public-key-only algorithm that *avoids* a hidden `δ`-dense set defined by `𝒪`.
- This is not known to reduce to anything standard. Avoiding `Bad` with advantage `ε` is exactly a
  GPI(1) distinguisher with advantage `ε`, for a distinguisher that knows `μ`.

So the gap is not removable by a cleverer simulator that works statistically. There are three
honest ways around it:
1. **Assume GPI** (computational, tight). This route is used in T2–T5.
2. **Change the signer** so that honest preimages are exactly uniform. That is salt-UOV: fixed
   vinegar, salt retry, and a uniform solution in the singular case.
   - *Proof.* For fixed `v`, `(y, o) ↦ o` hits each `o ∈ F^M` with probability
     `q^{−(M−k)}·q^{−k} = q^{−M}`, where `k = M − rank L_v`.
   - The simulation is then perfect, up to salt collisions. This is the spec's App. A theorem
     [SSH11].
   - **Caveat.** The number of salt retries is geometric with parameter `256^{−k}`, so timing
     reveals whether the *published* `s` is bad. That is information about `𝒪`, which the ROM
     proof does not model.
   - Contrast `D`: its rejected vinegars are never published.
3. **Bake the sampler into the assumption**: OMPR, A-OMPI, CT-UF, as the protocol notes do.

Randomizing the vinegar (fresh randomness instead of the target hash) does **not** help. The output
is still `U(S^G_y)` per call. It only gives the adversary several preimages per target, so it
strengthens the oracle.

## 5. Reductions

### 5.1 Theorem 1: A-OMPI, det-FDH, and the specified scheme

All in the ROM, with `D` replaced by `D*` (Lemma D, error `ε_D`) on both sides.

**(a) det-FDH ≤ A-OMPI, tightly:** `Adv^{euf}_{det}(A; q_H, q_S) ≤ Adv^{ompi}(B; q_H + 1, q_S)`.
- `B` answers each fresh `H(m)` with a fresh target `y_i`, and `Sign(m)` with the index oracle.
- A forgery on an unsigned `m*` is a preimage of an unqueried index. ∎

**(b) A-OMPI ≤ det-FDH, tightly:** `Adv^{ompi}(B; q_T, Q) ≤ Adv^{euf}_{det}(A; q_H = q_T, q_S = Q)`.
- `A` maps "new target" to `H(m_i)` for fresh messages `m_i`, and index queries to `Sign(m_i)`.
- The oracle answers are identical functions. ∎

**So A-OMPI *is* EUF-CMA of deterministic UOV-FDH in the ROM**, which is the standard EUF-CMA
notion for an unsalted hash-and-sign variant of UOV.

**(c) A-OMPI ≤ OMPR, tightly (for `D*`; with the real sampler, up to `(q_T + Q)·E[δ^{255}]` and with
`q_T + Q` targets, see the correction below):** `Adv^{ompi}(q_T, Q) ≤ Adv^{ompr}(q_T, Q)`.
- Forward the index queries as `D(t_i)`.
- The `Q` answers plus the forgery are `Q+1` preimages of distinct indices. ∎

*Correction to (c)* (found in the Lean proof). Two details of the one-line proof do not hold as
written:
- OMPR's win needs **exactly** `Q + 1` claims after at most `Q` preimage queries. An A-OMPI
  adversary may make fewer than `Q` index queries, or repeat an index. The reduction must cache
  repeated indices and **pad**: it requests `Q − (answered indices)` further targets and their
  preimages. So it uses `q_T + Q` targets, not `q_T`.
- With the real sampler `D`, an answer may be `⊥` (an abort). A failed index query costs the
  reduction one preimage query and yields no claim; a failed padding query likewise. So (c) holds
  up to the event that `D` errs on one of the challenger's `q_T + Q` targets:

      Adv^{ompi}(A; q_T, Q) ≤ Adv^{ompr}(B; q_T + Q, Q) + (q_T + Q)·ρ,    ρ = Pr_{y}[D(y) = ⊥]

  (`ρ = δ(sk)^{255}` for `derive_preimage`, §2; on average `E[δ^{255}] ≤ 2^{−295.8}`). For `D*`
  (Lemma D), which never aborts, `ρ = 0`; the aborts are the `ℓ·E[δ^{256}]` part of `ε_D`.

**Lean** (`lean/VoleMole/Assumptions/IdealTag.lean`; no `sorry`, no `axiom`). Generic in the
trapdoor, the messages and the world:
- **(a)** `advFDH_le_ompi`: for a det-FDH forger with at most `k` hash and signing queries on every
  path, `Adv^{euf}_{det}(A; q_H, q_S) ≤ Adv^{ompi}(fdhRed A; k + 1, q_S)`. The reduction `fdhRed`
  programs each fresh `H(m)` with a fresh challenge target (`fdh_step`: the programming is perfect
  per query, through the projection `fdhProj`; `fdh_inv`: the invariant). The lazy A-OMPI
  challenger (`ompiLazy`) is the stream one (`ompi_lazy_eqd`, `advOMPI_eq_lazy`). The paper's
  `q_H + 1` is `k + 1` here because Lean counts signing queries separately from hash queries.
- **(c)** `advOMPI_le_ompr`: `Adv^{ompi}(A; q_T, Q) ≤ Adv^{ompr}(ompiRed A; q_T + Q, Q) +
  badTargets(q_T + Q)`, `badTargets(n)` the probability that `D` errs on one of `n` uniform targets;
  `advOMPI_le_ompr_rate` with `≤ (q_T + Q)·ρ` (`failRate`, `badTargets_le`). The reduction caches
  (`ompiRedImpl`), caps the targets at `q_T`, and pads (`padC`, `pad_spec`); `ompi_step`,
  `ompi_inv`, `ompiWin_imp`. Holds for every trapdoor and adversary.
- **(a) then (c)**: `advFDH_le_ompr`, `advFDH_le_ompr_rate`.
- Generic tools: `simulateQ_proj_eqd`, `simulateQ_inv_bound` (a simulation through a state
  projection, with a per-query budget), `prEvent_unifList_exists_le₀`, `prEvent_le_bind` (all in
  `Assumptions/LazyIdeal.lean`, shared with T4 and the shift reductions),
  `prEvent_keyed_unifList_exists_le` (union bound over uniform targets), `unifList_add`.
- **(b)** (A-OMPI ≤ det-FDH), (d), (e) are not mechanized.

**(d) spec-EUF ≤ det-FDH:**
`Adv^{euf}_{spec}(A; q_H, q_S) ≤ Adv^{euf}_{det}(B; q_H + q_S + 1, q_S) + (q_H+q_S+1)²·2^{−361} + ε_D`.
- `B` sets `H_spec(m‖salt) := H_det(m‖salt)`. It answers `Sign(m)` by picking a salt and calling
  `Sign_det(m‖salt)`.
- Both samplers are `U(S^G_y)`. They differ only when two distinct inputs share a target, because
  `D*` is a function of `y`.
- `m*‖salt*` parses uniquely, since the salt is the last 16 bytes. So a fresh `m*` gives an
  unsigned det-FDH message. ∎

**(e) det-FDH ≤ spec-SUF:**
`Adv^{euf}_{det}(A; q_H, q_S) ≤ Adv^{suf}_{spec}(B; q_H, q_H) + 2^{−591} + q_v·q_H·2^{−128} + ε_D`.
- On the first use of `H_det(m)`, `B` asks its signing oracle for `(s_m, salt_m)` on `m`. It sets
  `H_det(m) := H_spec(m‖salt_m)`, and later answers `Sign_det(m)` with `s_m`.
- Consider a forgery `(m*, s*)`, with `m*` unsigned by `A`:
  - if `s* ≠ s_{m*}`, then `(m*, (s*, salt_{m*}))` is a fresh pair, i.e. a strong forgery;
  - `A` never saw `s_{m*}`, which is uniform on `|G| ≥ 2^{591.9}` good preimages given `A`'s
    view, so `s* = s_{m*}` has probability `≤ 2^{−591}`.
- The `q_v·q_H` term covers `A` querying SHAKE256 at a hidden `m‖salt_m`. ∎

**Consequence.** A-OMPI, and hence Ratatouille's UF-Tag via Lemma 2.1 of `ratatouille.md`, is
sandwiched (with `Tag` a random function, UF-Tag with the strict win *is* det-FDH with `H = Tag`,
so (a) is Lemma 2.1 in that model, with no loss):

    spec-EUF-CMA  ⇐  A-OMPI (= det-FDH)  ⇐  spec-SUF-CMA (with q_T signing queries),

with A-OMPI ⇐ OMPR as well. EUF-CMA *alone* is not known to suffice. The gap is the hidden salt:
the deterministic scheme fixes one preimage per message, and a second preimage of that target is
only an SUF forgery.

**What OMPR adds over all of these** is the *chosen-target* oracle: preimages of arbitrary `t`, not
only of hash outputs. No EUF-CMA or SUF-CMA oracle can answer such queries. So OMPR is not known to
follow from either. PomFRIT genuinely needs it (§5.6).

### 5.2 Theorem 2: A-OMPI (det-FDH) from GPI and OW, or from GPI and the UOV problem

For every `A` against A-OMPI with `q_T` targets and `Q` index queries:

    Adv^{ompi}(A) ≤ Adv^{gpi}(B₁; q_T) + q_T·Adv^{ow}(B₂) + q_T²·2^{−359} + ε_D,
    Adv^{ompi}(A) ≤ q_T·( Adv^{uov}(B₃) + Adv^{gpi}(B₄; q_T − 1) ) + q_T²·2^{−359} + ε_D.

*Proof (first bound).*
- **Game 1.** Lemma D gives `D*`. Pairs `(y_i, D*(y_i))` are `U(Good)` pairs. Sampling them
  independently (`s_i ← U(Good)`, `y_i := P(s_i)`) differs only on a target collision, which costs
  `q_T²·2^{−361}`.
- **Game 2.** `s_i ← U(F^N)`. This is a GPI(q_T) hop: `B₁` uses its samples, runs `A`, and outputs
  the win bit.
  - Game 2 is symmetric in the indices.
  - `B₂` takes the OW instance `z = P(s*)`, picks `j*` uniformly, and sets `y_{j*} := z`. The view
    is identical, so `Pr[i* = j*] = Pr[win]/q_T`.
  - When `i* = j*`, `j*` was never queried, so `B₂` never needs `s_{j*}`. ∎

*Second bound.* Guess `j*` in Game 1, where the view is independent of `j*`. Hop the other
`q_T − 1` samples to uniform, and embed the uniform UOV target at `j*`, which is already uniform.
So `Adv/q_T ≤ Adv^{uov} + Adv^{gpi}(q_T − 1)`. ∎

**Why `q_T` and not `Q`.**
- The adversary decides *after* seeing all targets which indices to open. So the reduction cannot
  reserve the challenge for an index it will not be asked about.
- Without GPI the hop costs `1 − (1−δ)^{q_T}`, which is vacuous. That is the exact form of
  `ratatouille.md`'s "not statistical".

### 5.3 Theorem 3: the specified salted UOV from GPI and the UOV problem

    Adv^{euf}_{spec}(A; q_H, q_S) ≤ Adv^{gpi}(B₁; q_S) + (q_H + 1)·Adv^{uov}(B₂) + q_S(q_H + q_S)·2^{−128} + ε_D.

*Proof.*
1. Program each signing point `m‖salt` (fresh salt) as `P(s_i)`, with `s_i ← U(Good)`. This is
   exact, unless the salt point was already queried (`q_S(q_H+q_S)·2^{−128}`).
2. GPI(q_S) hop to `s_i ← U(F^N)`.
3. The non-signing `H` answers are uniform. So the UOV target can be embedded at a uniformly
   guessed one among `A`'s `q_H` queries plus the forgery check. The forgery's point is
   non-signing, because `m*` is unsigned. ∎

Remarks:
- Unlike T2, GPI is not multiplied. The salt makes every signing point fresh, so the reduction
  knows in advance which points will be opened. This is the concrete proof benefit of a salt.
- **The spec does not prove the specified scheme's EUF-CMA.** App. A ("salt-UOV and its EUF-CMA
  security") proves salt-UOV:

      ε′ ≥ ε·(1 − (q_h+q_s)·q_s·2^{−salt_len})/(q_s+q_h+1)    [SSH11]

  and argues that the attacks on the two variants coincide. T3 closes the gap modulo GPI. We are
  not aware of a proof of the *vinegar-retry* signer from the UOV problem alone. Its signatures
  are `δ`-far from uniform per query (Corollary §2).
- Kosuge and Xagawa [KX24] study probabilistic hash-and-sign *with retry* in the (Q)ROM. We could
  not retrieve the paper in this session, so we neither use nor restate its bounds.

### 5.4 Theorem 4: CT-UF, the gap in Lemma U, and the repaired statement

**The gap.** `moussaka.md` Lemma U claims
`Adv^{ct-uf}_{UOV,Com,1} ≤ Adv^{om-uov}(Q = q_P^fwd, ℓ ≤ q_Sign) + …`. Its last step says "together
with the ℓ oracle answers, [the forgery] gives ℓ+1 solutions". That holds only if every `Sign`
query was on a *challenge* target, i.e. on a programmed Com output.
- CT-UF's oracle accepts **arbitrary** targets. Take an adversary that makes one query `Sign(0)`
  (not a Com output) and later forges.
- The reduction must spend an OMPR call on `0`. It then holds `h + 1` challenge preimages after
  `h + w` calls, where `w ≥ 1` counts the non-challenge calls.
- That is not a one-more win (Lean `wasted_calls`: `h+1 ≥ h+w+1 ⇔ w = 0`).
- There is no other way to answer `Sign(0)` without `sk`. So **CT-UF as defined is not shown to
  follow from OMPR**.
- What Lemma U actually needs is an OMPR variant in which calls on non-challenge targets are free.
  That is a different assumption.
- **Follow-up (`uov-open-reductions.md` §2–§3).** CT-UF as defined is in fact false (one query on
  a scalar multiple of the target). With freshness up to scalars it is equivalent to that
  free-call variant, which no relativizing reduction derives from OMPR. The repair below is not
  affected.

**The repair: CT-UF^open.** Model `Com = KP800(·)|_{360}` on the structured domain `D_Com` (576 free
input bits, 224 fixed), with `KP800` a random permutation with inverse access, **in the standalone
game only**. Let `q_f` and `q_i` be `A`'s forward and inverse queries, and `q_S` its `Sign` queries.
Then

    Adv^{ct-uf-open}_{UOV,Com,1}(A) ≤ Adv^{ompr}(B; q_f + q_S + 1, q_S)
                                     + q_i·2^{−223.9} + q_S·(q_f + q_S + 1)·2^{−359.9} + (q_f + q_S + 1)²·2^{−800},

and `Adv^{ct-uf-open}_K ≤ K·Adv^{ct-uf-open}_1`, since the reduction generates the other `K−1` keys
itself.

*Proof.* `B` simulates `KP800` lazily.
- A fresh forward query on a `D_Com`-structured input gets `y_j ‖ z`, with `y_j` the next OMPR
  target and `z ← {0,1}^{440}`. Resample `z` on a range collision; this is the last term.
- Every other query gets a fresh uniform value.
- An inverse query that returns a `D_Com`-structured input is a bad event, with probability at most
  `2^{576}/(2^{800} − q) ≤ 2^{−223.9}` per query.
- `Sign(t)`: `B` forwards `t` to its OMPR oracle (≤ `q_S` calls).
- At the end, `B` evaluates `Com` on the forgery `x*` and on every opening `x_t`. That is
  `≤ q_S + 1` more forward evaluations, which may allocate targets.
- Now suppose `A` wins.
  - Consider a signed `t` whose opening input was first evaluated *after* `Sign(t)`. Its output is
    fresh, and its prefix equals the already-fixed `t` with probability `≤ 2^{−359.9}`. The
    middle term is the union over `(t, evaluation)` pairs.
  - Otherwise, at the time of `Sign(t)`, `t` was already a programmed challenge `y_j`. So every
    call hit a challenge target.
  - The forgery's `Com(x*)` is a challenge value never signed. Its index is therefore distinct from
    the `q_S` signed indices (Lean `one_more_count`).
  - `B` outputs the `q_S` oracle answers and `s*`: `q_S + 1` preimages of distinct indices, after
    `q_S` calls.
- Runs in which some call missed are runs in which `A` loses (outside the bad events). `B` does not
  need to win those. ∎

**Corrections (found while mechanizing; the Lean statement is below).**
- *The middle term is not needed.* OMPR does not ask that a call be made after its target was
  issued, or on a target at all: the win only counts calls and checks the claimed preimages. If a
  signed `t` is only later the `Com` value of its opening, `B` still holds a preimage of that
  challenge (the oracle's answer on `t`). So `q_S·(q_f + q_S + 1)·2^{−359.9}` can be dropped. The
  same holds in the permutation model.
- *The sampler may fail.* `D = derive_preimage` returns `⊥` after 255 vinegar attempts. A claim
  from a failed answer is not a preimage, so `B` loses. Add `n·failPr`, the probability that some
  of the `n` targets is a failure point of `D` (`failPr = E[δ^{255}]`, about `2^{−295.8}` for
  pqov's key generation, `Privacy/PqovKeys.lean` `avg_delta255_pqovKey`).
- *Repeated queries and padding.* Def. 3.1 wins with exactly `ℓ + 1` claims on distinct targets
  after at most `ℓ` calls. `B` must cache repeated `Sign` queries (else it pays twice for one
  claim), and, if `A` signed `d < q_S` distinct targets, pad with `q_S − d` fresh targets and
  their preimages. With `B` evaluating `Com` on every opening (at most `q_S`) and then padding,
  `B` uses up to `q_f + 2q_S + 1` targets. (The note's `q_f + q_S + 1` holds when `A` signs
  exactly `q_S` distinct targets, or with a `B` that pads with targets of unused openings.)

**Lean (random-function version).** `lean/VoleMole/Assumptions/CTUFOpenOMPR.lean`, with `Com` a
lazy random function `D_Com → F^{45}` (no inverse queries; the permutation with inverse access is
not mechanized). The ideal game is `advCTUFIdeal1` / `advCTUFIdeal` / `advCTUFIdealAt`
(`Assumptions/UOV.lean`: the forger is an oracle computation with the world, the signers and
`Com`; the challenger evaluates `Com` at `x*` and at every opening; the win `CIWin` reads `Com`'s
table). For a forger with at most `q_f` `Com` and `q_S` signing queries and `q_S` openings
(`CIBudget`), `n = q_f + 2q_S + 1` and `failPr = preFailPr`:

    Adv^{ct-uf-open}_1(F) ≤ Adv^{ompr}(ompRed q_S F; n, q_S) + n·failPr          (advCTUFIdeal1_le_ompr)
    Adv^{ct-uf-open}_K(F) ≤ Σ_j Adv^{ct-uf-open}_1(guessKey j F)                   (advCTUFIdeal_le_sum)
                         ≤ Σ_j Adv^{ompr}(B_j; n, q_S) + K·n·failPr                (advCTUFIdeal_le_ompr)

`Adv^{ompr}` is the on-demand game `advOMPR`, at most Def. 3.1's advantage of `popAdv`
(`advOMPR_le_ompr31`). The `K`-key step is also stated at fixed keys (`advCTUFIdealAt_le_sum`,
`advCTUFIdealAt_le_ompr`, with the OMPR game at a fixed key, `Trapdoor.atKey`), the form the
Moussaka theorem needs. The proof:
- `B` (`ompRed`, a `QueryImpl` `rImpl` plus `claimsQ`) answers a fresh `Com(x)` with a fresh
  challenge target labelled `x`, forwards a new `Sign(t)` to the preimage oracle and caches it,
  claims `(x*, s*)` and each signed target's answer under the label of the first opening with
  that `Com` value (`baseCl`), and pads with fresh labels `inr i` (`padQ`).
- Pre-sampling (`LazyIdeal.rfStream_presample`): with at most `k ≤ m` queries, a lazy random
  function equals one fed from `m` uniform values.
- `B` against the OMPR challenger, projected, is the ideal challenger fed from the targets
  (`combC_run_proj`, step by step under the invariant `InvC`); the stream is long enough
  (`combC_budget`, from VCVio's cost lemma).
- On every such run where the forger wins, `B` wins or some target is a failure point of `D`
  (`win_imp`; the counting is `one_more_count`'s, with the padding `padQ_run`). Union bound over
  the targets: `LazyIdeal.prEvent_unifList_exists_le`.
- `K` keys: the guessing forger `guessKey j F` generates `K` keys, puts the challenge key at
  `j`, and answers the other keys' signing queries itself (`guessImpl`); seen from key `j`, the
  `K`-key run is its one-key run (`guess_run`), and re-embedding a fresh key keeps the keys iid
  (`LazyIdeal.iidVec_update`).

**Lean (permutation version).** `lean/VoleMole/Assumptions/LazyPerm.lean`,
`Assumptions/CTUFPerm.lean`, `Assumptions/PermLinks.lean`. `KP800` is a lazily sampled random
permutation `π` of the blocks `T × Z` with forward and inverse queries (`LazyPerm.rpImpl`: a fresh
answer is uniform on the unused outputs, resp. inputs); `Com(x)` is the first component of
`π(emb x)` for an injective encoding `emb` of the openings. The game is `advCTUFPermAt` (the
challenger evaluates `π` forward at `x*` and at every opening; the win `CPWin` is `CIWin` read off
the permutation's table). For a forger with at most `q_f` forward, `q_i` inverse and `q_S` signing
queries and `q_S` openings (`CPBudget`):

    Adv^{perm}_K(F) ≤ Σ_j (Adv^{ompr}_{key j}(B_j; n, q_S) + n·failPr_{key j})
                      + (q_f + q_i + q_S + 1)²/|T × Z| + q_i·|X|/|T × Z|        (advCTUFPermAt_le_ompr)

with `n = (q_f + q_S + 1) + 2q_S + 1`. The proof:
- *The switch* (`LazyPerm.prEvent_rp_le_rf`, shared with `Assumptions/FDHPerm.lean`): the
  permutation and a two-sided lazy random function differ by at most `q·(n₀ + q)/|B|` for `q`
  queries that read it (forward, inverse, or the challenger's), by identical-until-a-flag on one
  uniform draw per fresh answer (`freshRP`, `freshRF`), proved in the project
  (`prEvent_le_add_flag`, `prEvent_bad_le`), since VCVio's total-variation lemmas are not in the
  built package set.
- *Inverse hits* (`prEvent_invHit_le`): an inverse answer is a structured input with probability
  `≤ q_i·|X|/|B|`.
- *The reduction* (`permRed`, `simC`): the function-model forger simulates `π`: a fresh forward
  query at `emb x` is answered `(Com(x), z)`, every other fresh answer is a coin, and coins are
  values of the world's random oracle at fresh indices (`ARc`). Against the function-model
  challenger its run, projected, is the random-function hybrid (`combP_step`, under the invariant
  `InvP`, `combP_inv`); without an inverse hit, `Com` read off the table is the function's value
  (`comP_tab`), and the final evaluations only extend `Com`'s table (`ciWin_ciFinal`). So
  `Adv^{perm}(F) ≤ Adv^{ideal}(permRed F) + permEps` (`advCTUFPermAt_le_ideal`), and T4 applies.
- Compared with the paper's statement: the inverse-hit term is the same
  (`q_i·2^{576}/2^{800} = q_i·2^{−224}`); the switching term counts inverse queries too (an
  inverse answer of a permutation is not uniform either), so it is `(q_f + q_i + q_S + 1)²·2^{−800}`
  rather than `(q_f + q_S + 1)²·2^{−800}`; and the reduction reuses the function-model one, which
  budgets the final evaluations twice, so `n` has `q_S + 1` more targets than the corrected
  `q_f + 2q_S + 1` (the term `n·failPr` changes accordingly). The lazily sampled permutation is
  the eagerly drawn uniform one (`Assumptions/EagerPerm.lean`, `rp_eqd_eager`,
  `prEvent_rp_eq_eager`): for every oracle computation, without a query bound, a run against
  `rpImpl` from the empty table has the joint distribution of output, table and other state of
  `π ← $ᵗ Equiv.Perm B` and a run answered from `π` (`epImpl π`, the table a log of the points
  determined; `rp_eqd_eager0`: the same without the table, `epImpl0 π`). So every bound on
  `advCTUFPermAt` holds for the game with `π` drawn up front. Corollaries restating the headline
  theorems with the eager game are not written.
- The Moussaka corollaries take the modelling hypothesis in this form (`hmodelP`: concrete
  CT-UF^open of `B₂` ≤ `advCTUFPermAt` of some forger within budget):
  `omuf_le_num_ompr_perm`, `omufU_le_num_ompr_perm`. Non-vacuity: `Audit/PermOMPR.lean` (a toy
  forger wins the permutation-model game with probability one and meets `hmodelP`).
- *AES as random permutations too* (`Assumptions/PermSimLinks.lean`). Moussaka's Theorem 1 with AES
  as random permutations and an adversary with inverse cipher queries (`omuf_le_num_simP`,
  `ROM/MoussakaOMUFSimPerm.lean`) has its forgery term as the CT-UF^open advantage of the forger
  `ctufForgerP`, whose common randomness is the permutation table (`omuf_le_open_simP`,
  `omuf_le_num_open_simP`). Its `reads` property (it uses its signers only on its signing log)
  needs the logs of the jointly normalized provers: they are a function of the permutation-model
  game's log (`tableQueryLog_normJ`, `tableQueryLog_liftP`), which reads the signers only at the
  accepted Issue queries (`gameP_congr`). With `hmodelP` for `ctufForgerP`:

      Pr[Win] ≤ εIR^simP(q', q'_E, n', qI, qR) + Pr[Coll]
                + Σ_j (Adv^{ompr}_{key j}(B_j; n, q_S) + n·failPr_{key j})
                + (q_f + q_i + q_S + 1)²/|T × Z| + q_i·|Xc|/|T × Z|       (omuf_le_num_ompr_simP)

  Non-vacuity: `Audit/PermSim.lean`. Unbound Moussaka the same way
  (`Assumptions/UnboundPermSimLinks.lean`): its permutation-model game
  (`ROM/MoussakaUnboundOMUFSimPerm.lean`, `omufU_le_num_simP`), the forger `ctufForgerUP` over
  `Com ∪ UCom` (`gameUP_congr`; the bound issuance provers are normalized by `normP`, whose log
  is `tableQueryLog_normP`), `omufU_le_num_open_simP`, and with `hmodelP`
  `omufU_le_num_ompr_simP`:

      Pr[Win] ≤ εI^simP + εU^simP + Pr[Coll]
                + Σ_j (Adv^{ompr}_{key j}(B_j; n, q_S) + n·failPr_{key j})
                + (q_f + q_i + q_S + 1)²/|T × Z| + q_i·|Xc|/|T × Z|.

**How the concrete game relates.** The CT-UF^open game of `advCTUFOpenAt` (Moussaka's
`Com = KP800(·)|_{360}`, read by the forger as a function) is not reduced to the ideal one: that
replacement is the modelling step of this section, and is a hypothesis (`hmodel`) of the Moussaka
corollary `Links.omuf_le_num_ompr`. It is sound only in the standalone game, which contains no
proof about `Com`'s circuit.

**CT-UF^open from GPI and OW.**

    Adv^{ct-uf-open}_{UOV,Com,1} ≤ Adv^{gpi}(q_f + q_S + 1) + (q_f + q_S + 1)·Adv^{ow} + (the same three terms).

- As in T2: program `y_j := P(s_j)` from GPI samples, and embed the OW instance at a guessed index.
- Answer `Sign(y_j)` with `s_j`. **Abort** on `Sign(y_{j*})`, and on a non-table `t`.
- A non-table `t` can be opened later only in the bad event already counted.

**Effect on Moussaka.** Theorem 1's `B₂` already extracts an opening `x_q` of every accepted
issuance target (`moussaka.md` §4, proof step 2). So it can output the openings of the targets it
had signed under the embedded key. **Theorem 1 holds verbatim with CT-UF^open in place of CT-UF**,
and then Lemma U holds as repaired.
- CT-UF^open requires a fresh `Com` value, which is slightly stronger than Moussaka needs: a forgery
  that only re-randomizes `r` for a signed `(nf, ctx_iss, ctx_red)` does not win Moussaka's game.
- Inverse access is harmless only because of the 224 fixed input bits.

### 5.5 Theorem 5: Ratatouille with R1 (an Issuer salt in Tag)

R1: `Tag(c, x, σ) = KP800("rata"‖0‖"t0" ‖ σ ‖ 0⁹ ‖ c ‖ ⟨x⟩₈ ‖ 0²⁸)[0..45)`.
- The Issuer draws `σ ← {0,1}^{128}` fresh per signature, from the OS RNG, and returns
  `(x', σ, s')` with `s' = D(Tag(c', x', σ))`.
- `σ` goes into the spend witness.

**Reduction to EUF-CMA.** This is exactly the specified UOV's signing structure (fresh public salt,
deterministic vinegar from target and seed), for messages `(c, x)` and with hash `Tag` instead of
SHAKE256. So

    Adv^{bal} ≤ ε_ext + Adv^{euf}_{UOV[Tag]}(B; q_K, N_I + N_S) + ε_bind^K + q_K·(2^{−287} + 2^{−351})
              + (N_I + N_S)·E[δ^{255}] + q_v·2^{−256}.

The last term is the Issuer's aborts (`E4`), which R1 does not remove (§5.8).

*Proof.* This is `ratatouille.md` Theorem 1, with `S` the set of signed `(c, x)` pairs, and with
(E3) replaced by "some spend's parent `(c_j, x_j)` was never signed".
- Then the extracted `(c_j, x_j, σ_j, s_j)` is an EUF-CMA forgery on a fresh message.
- A parent signed under a different salt is not a forgery, but it is harmless: the balance
  accounting uses `(c, x)` only, and binding and nullifiers are unchanged.
- The Tag domain now has 352 fixed bits, so an inverse query lands in it with probability at most
  `2^{−351}`. ∎

**Reduction of `UOV[Tag]` to the UOV problem.** In the standalone game, idealise KP800 and argue as
in T3:

    Adv^{euf}_{UOV[Tag]} ≤ Adv^{gpi}(N_I + N_S) + (q_K + 1)·Adv^{uov} + (N_I + N_S)·q_K·2^{−128} + q_K·2^{−351} + q_K²·2^{−799} + ε_D.

If the Issuer instead signs as salt-UOV (§4, item 2), the GPI term disappears and balance rests on
**the UOV problem alone**, classically.

**Answer to the task's question.**
- With R1, balance reduces to *salted UOV EUF-CMA with `H = Tag`*. That is a ROM-level claim of the
  same form as the specified scheme's, with KP800 in place of SHAKE256.
- It is **not** a reduction to the plain UOV problem. That further step needs GPI, or salt-UOV
  signing.
- `ratatouille.md` §2.3's sentence "the salted UOV EUF-CMA proofs avoid this by resampling the
  salt" is right only for salt-UOV. Resampling the salt *with a fixed vinegar* is what removes the
  `δ` gap. The specified signer, like `D`, resamples the vinegar and keeps the gap.

What R1 buys over A-OMPI:
- EUF instead of SUF (T1(e) is no longer needed);
- an un-multiplied GPI term (T3 versus T2);
- with salt-UOV signing, the UOV problem alone;
- the salted structure that QROM proofs of hash-and-sign-with-retry assume.

### 5.6 Theorem 6: PomFRIT is equivalent to OMPR

For every `B` against OMPR(n, ℓ), there is a PomFRIT one-more forger `F` that makes `n` honest
`issue_request` computations and `ℓ` Issuer queries, with

    Adv^{omuf}_{PomFRIT}(F) ≥ Adv^{ompr}(B; n, ℓ).

*Proof.*
1. `F` runs `issue_request` on `n` distinct messages, with fresh seeds. Each request is
   `t_i = h_i ⊕ r_i`, where `h_i = H_T(…)` is a fresh RO value independent of `r_i`. So
   `t_1..t_n` are i.i.d. uniform, and they are all `B` sees.
2. `F` runs `B(pk, t_1..t_n)`, and answers `B`'s `SPre` calls with the Issuer (`issue_response` is
   `derive_preimage`, `pomfrit.cpp:188-190`).
3. `B` returns `ℓ+1` preimages of distinct `t_{I_i}`. `F` finalizes those sessions: the check
   `P(s) = t` passes, and honest proving is complete. This gives `ℓ+1` valid signatures on
   distinct messages. ∎

With `pomfrit.md` U1 and U2:

    Adv^{ompr}(n, ℓ)  ≤  Adv^{omuf}_{PomFRIT}  ≤  Adv^{ompr⊕17}(…) + ε_ext + …   (U2)
                                               ≤  Adv^{ompr}(…) + ε_ext + (Q₃+ℓ+1)·2^{−71} + …   (U1).

**Lean** (`lean/VoleMole/Assumptions/Blind.lean`, `ompr_le_blind`). The forger and its proof
are mechanized for an abstract client, in the one-more game of U1 (`OneMore.omuf`, programmed
targets `H_T(x) + r`). The client has coins, a first phase `start` (label `x`, blinding `r`, state,
over its own oracle), a state carried across sessions (`init`; PomFRIT's instance carries the
game's query log), and a finishing phase `post` (over its oracle and `H_T`, no Issuer) that
returns one acceptance flag. The forger `blindAdv cl n B` answers `B`'s `k`-th request with
session `k`'s blinded request and forwards `B`'s preimage queries to the Issuer. If the sessions'
labels are pairwise distinct (`Distinct`, on the supports, for all carried states), then

    Adv^{ompr}(B; n, ℓ) ≤ Pr[Forges] + Pr[CompFail].

`CompFail` is a completeness failure: the forger's `ℓ+1` claims are preimages of their programmed
targets, on distinct labels, within `ℓ` Issuer queries, but `post` rejects. The proof uses
OneMore's perfect programming (`real_eqd_comb`): against the challenger, `B` receives
`(t − r) + r = t`, as in `omExp` (`bcomb_eqd`). The client's runs are integrated out, because they
read only the client's oracle, which is separate from `B`'s. Then `B`'s win is the forger's
(`win_mid`). The finishing phase keeps the programmed targets and the Issuer count (`post_pres`).
The audit instantiates this at PomFRIT's trapdoor with a client whose `CompFail` term is 0
(`Audit/OMPRShift.lean`).

**Lean, the PomFRIT instance** (`lean/VoleMole/Assumptions/BlindPomfrit.lean`, `pomfrit_T6`,
`pomfrit_T6_bound`; `pomfrit.md` §6.4). The game is PomFRIT's real one-more forgery game
(`ROM/OneMorePomfrit.lean`: the forger wrapped, then `verAll`, i.e. `pomfritVerify` with `H_T` the
oracle) for a forger with coins and its own random oracle (`gameB`); for a forger without coins it
is `game` (`gameB_liftF`). The client is any PomFRIT client given as oracle computations over the
hashes and the cipher (`PomClient`: step 1 of session `k` for the message `msgOf k`, and the final
signature from the state, the `H_T` answer and the Issuer's response). Session labels are
`hash_to_target`'s inputs; distinct messages give distinct labels (`label_ne`, from `tgtIn_inj`),
so `Distinct` is a theorem. The forger `blindForger cl n B` blinds with `r = 0`: it is an
adversary, so it need not blind, and step 1 of the proof then reads `t_i = h_i`, a fresh RO value;
PomFRIT's relation `P(s) = h ⊕ r` holds with `r = 0`. For every `B` and every client,

    Adv^{ompr}(B; n, ℓ) ≤ Pr[PomWin(blindForger cl n B)] + compFail,

`compFail` the probability that `B`'s claims are `ℓ+1` preimages of distinct sessions' targets
within `ℓ` Issuer queries but the client's signatures do not all verify. With at most `Q` target
requests by `B`, the game has `Q + ℓ + 1` targets and the forger makes at most `Q` `H_T` queries
(`pomfrit_T6_bound`, `advOMPR_pad`, `blindForger_bound`). The proof is `ompr_le_blind` for the
client as a `Blind.Client` (`toClient`, carrying the game wrapper's log so that it also makes
the reduction's logged queries `auxSpec` at each label), and the observation that the blind game and `gameB` agree
on the key, the forger's flag and the final state (`projF_eqd`, `star`).

*The Lean client* (`pomfrit.md` §6.4, G9). The Lean prover's `voleGen` and `proveCommit` as a
`PomClient` (`leanClient`, with hashes and cipher calls as queries, `ROM/ProverIC.lean`), equal per
table to the executable prover (`eval_start`, `eval_finish`), has `compFail ≤ (ℓ+1)·2^{−113}`
(`compFail_le`): outside `GrindBad` of a claimed session's grinding answers its signature verifies,
and each claimed session's prefix is computed without `H₂³` queries, so its answers are fresh.
Hence `Adv^{ompr}(B; n, ℓ) ≤ Pr[PomWin] + (ℓ+1)·2^{−113}` (`pomfrit_T6_lean`,
`Assumptions/BlindPomfritT6Lean.lean`).

Step 1's uniformity is the programming step above; the distinct messages are `Distinct`.

**PomFRIT's unforgeability cannot rest on anything weaker than OMPR**, in particular not on
EUF-CMA. The Issuer *is* a chosen-target preimage oracle, which blindness requires. This mirrors
Chaum blind signatures and the one-more-RSA problem [BNPS03].

### 5.7 Proposition 7: OMPR and the UOV problem; what determinism does and doesn't give

**Determinism gives three things.**
1. Lemma D: the oracle is a fixed random function with known output law.
2. Call counting equals distinct-target counting.
3. Restricted to hash-output targets, the equivalence T1(a, b) with det-FDH.

**Determinism does not make OMPR equivalent to a standard assumption.**
- *Chosen targets* (§5.1): no EUF-CMA oracle answers them.
- *Multicollisions.* The paper's App. A argument still applies: compute a `k`-multicollision for
  `t`, then ask `D(t)`. That gives a `(k+1)`-multicollision, which the UOV problem doesn't provide.
  Determinism allows one such query per target, but one is enough.
- *Meta-reduction (sketch, following [BMV08]).*
  - Let `R` be a key-preserving reduction that solves the UOV problem by running an OMPR(n, q)
    adversary once (`q ≥ 1`, `n ≥ q+1`), without rewinding it.
  - Let `A` be the unbounded adversary that queries a random `q`-subset of `t_1..t_{q+1}` and then
    outputs preimages of all `q+1`.
  - A meta-reduction `M` can rewind `R` to the point where it hands out the targets. It can then
    play `A` with two different subsets, which together cover all `q+1` targets. `R` must answer
    every query in each run, or `A` aborts there.
  - `M` then completes one run with a preimage of the missing target taken from the other run.
  - If `R`'s success doesn't depend on *which* valid preimage of the unqueried target `A` returns,
    `M` solves UOV without help.
  - Caveats: the preimage-obliviousness proviso is real for UOV, because preimages are not unique,
    unlike DL. And reductions that rewind `A`, or change the key, are not covered.

  So this is evidence, not a theorem. OMPR should be treated as an independent assumption, as the
  paper does ("a new hardness assumption is indeed necessary").

  **Update.** `uov-open-structure.md` Part A has the theorems. In short:
  - the sketch above, with queries on listed targets only, cannot separate OMPR from UOV: for such
    adversaries OMPR follows from GPI and the UOV problem with loss `n`, as in T2. Made precise,
    it is a tightness bound (A3: loss `≥ q_T`, with the preimage-obliviousness proviso as the
    term `Δ_R`);
  - the separation comes from *off-list* queries: a key-preserving reduction that answers one
    query on a random target has solved UOV (A1; no proviso, rewinding allowed);
  - determinism gives a second separation for fully black-box reductions, since `D`'s answers
    are unique given `pk` and unpredictable (A2).

### 5.8 Proposition 9: UF-Tag with a signability probe

**Why the probe exists.** `spend_response` signs before the caller's nullifier check
(`ratatouille.md` F5). On the duplicate-nullifier path the Issuer computes `D(Tag(c', x'))` and
withholds it, but its answer still shows whether `D` succeeded (an exception against a rejection).
The Lean balance theorem therefore bounds the forgery term by a UF-Tag game with a probe
(`ROM/RatatouilleBalance.lean`, `TagForger`, `UFWin`, `ufTagAdv`, `balance_le_ufTag`):

- **UF-Tag+probe** (§3, item 13). The forger has `Sign(c, x) = D(Tag(c, x))`, which may return `⊥`,
  and `Probe(c, x) = [D(Tag(c, x)) ≠ ⊥]` (`q_S` and `q_P` queries). It wins with `(c*, x*, s*)`,
  `P(s*) = Tag(c*, x*)`, if no `Sign` query on `(c*, x*)` was answered. So a forgery on a probed
  pair, or on a pair whose signing failed, counts.
- This differs from UF-Tag (item 12) in two ways: the probe, and the win on a failed signing query.

**What the probe reveals.** The probe does *not* reveal whether `Tag(c, x)` is "good". Goodness is a
property of preimages, not targets: every target has exactly `|G_sk|` good preimages (Lemma C).
The only target-dependent event is the abort of `D`, which happens iff the first 255 vinegars at
the target are bad (§2). With SHAKE256 a random oracle and no query at `sk_seed`, this has
probability `δ(sk)^{255}` at every fresh target, independently of the target, of `A`'s view and of
the other targets. On average over the key `E[δ^{255}] ≤ 2^{−295.8}` (§1). So the probe answer is
"yes" except with probability about `2^{−296}` per pair. (The per-target abort probability is
`δ^{255}`, not `δ ≈ 2^{−7.994}`: `δ` is the probability that one *vinegar* is bad.)

**Proposition 9.** Let `A` be a UF-Tag+probe forger with `q_S` signing, `q_P` probe, `q_v` SHAKE256
and `q_K` KP800 queries, and let

    φ = (q_S + q_P)·E_sk[δ(sk)^{255}] + q_v·2^{−256}.

(a) **Probe elimination.** Let `A⁰` be `A` with every probe answered "yes" (no oracle call). Then

    Adv^{uf-tag+probe}(A) ≤ Adv^{uf-tag}(A⁰) + φ,      Adv^{uf-tag}(A⁰) ≤ Adv^{uf-tag+probe}(A⁰).

So the two notions are equivalent up to `φ`, statistically.

(b) **From A-OMPI and A-OMPR.** With `q_T ≤ q_K` Tag inputs,

    Adv^{uf-tag+probe}(A) ≤ Adv^{ompi}(B; q_T, q_S) + φ + q_K·2^{−479} + q_K²·2^{−799}
                          ≤ Adv^{ompr}(B; q_T, q_S) + φ + q_K·2^{−479} + q_K²·2^{−799}.

Probes cost no one-more budget: `B` makes only `A`'s `q_S` signing queries.

*Proof of (a).*
1. Let `Fail` be the event that `D` returns `⊥` on `Tag(q)` for some pair `q` that `A` signed or
   probed. Outside `Fail`, every probe answer is "yes", so the runs of `A` and `A⁰` are identical.
   A win of `A` outside `Fail` is on a pair with no answered signing query. Since no signing query
   failed, the pair was never signed, so it is a UF-Tag win of `A⁰`. The second inequality is
   trivial.
2. **The failure event is read off a run that cannot fail** (Lean `failOut_iff_patch`). Let
   `τ` be any total signer that agrees with `D` wherever `D` succeeds. A forger reads the signer
   only through its signing answers and probe bits (`TagForger.reads`). So `Fail` holds in the run
   against `D` iff `D` fails on a pair logged by the run against `τ`. Both directions follow by
   applying `reads` to the run that has no failing logged pair.
3. **The law of `D`** (Lemma D). Given no query at `sk_seed` (`q_v·2^{−256}`), `D(y)` is `⊥` with
   probability `δ^{255}`, and otherwise uniform on `S^G_y`, independently across `y`. This is the law
   of `withFail(f, τ)`: `⊥` if `f(y) = 1`, else `τ(y)`. Here `f(y)` is an independent
   Bernoulli(`δ^{255}`) bit and `τ(y) ← U(S^G_y)` is independent of `f`.
4. **Union bound.** The run against `τ`, and so its logged pairs, does not depend on `f`. So
   `Pr[Fail | sk] ≤ (q_S + q_P)·δ(sk)^{255}` (Lean `pr_failOut_le`, per table). Average over `sk`. ∎

*Proof of (b).* `B` runs Lemma 2.1's simulation of KP800 for `A⁰`, forwards its signing queries to
the index oracle, and answers each probe "yes" itself. A forgery of `A⁰` on a pair never signed is a
preimage of an unqueried index. Then apply (a) and T1(c). ∎

**The other two ways of answering probes.**
- *Spend an oracle call per probe.* The simulation is then exact, but it fails exactly where it
  matters:
  - the budget becomes `q_S + q_P`;
  - a probed index counts as queried, so a forgery on a probed pair is no one-more win.
  
  In Ratatouille, the probed pairs are exactly the duplicate-path states whose later spend the
  balance reduction must catch (F5). This is `wasted_calls` again: `h + 1 ≥ h + w + 1` forces
  `w = 0`.
- *Guess "yes".* That is (b). It loses `q_P·E[δ^{255}]`, not `q_P·δ`.
- *A separation.* No separation beyond `φ` is possible. The probe oracle is simulated within `φ`
  for every adversary with `q_v` SHAKE256 queries, whatever its running time.
- *Weak keys.* For a fixed key the term is `(q_S + q_P)·δ(sk)^{255}`, which is 1 for a key with
  `δ(sk) = 1` (`S = 0`, §1). On such a key the probe is informative, but it still reveals only
  `D`'s abort, which the forger can use only as a signing failure. Only the key average is small.

**Is the probe avoidable in the balance proof?** Yes, at no cost in the bound.
- *With the probe* (Lean). `B` logs at most one pair per Issuer call (`forger_logs_le`), so
  `q_S + q_P ≤ N_I + N_S`. By (b):

      Adv^{bal} ≤ ε_ext + Adv^{ompi}(q_T, N_I + N_S) + (N_I + N_S)·E[δ^{255}] + q_v·2^{−256} + ε_bind^K + q_K·2^{−479} + q_K²·2^{−799}.

  Lean `balance_le_noProbe` states the first step: `Adv^{uf-tag+probe}(B) ≤ Adv^{uf-tag}(B.noProbe τ)
  + failAdv(B)`, with a probe-free forger and the failure term.
- *With `E4`* (paper, `ratatouille.md` §4). `B'` checks the store first. It forwards only
  fresh-nullifier signing calls, and answers duplicate-path calls "success" itself. It discards
  `E4`, "`D` aborts on a target the Issuer evaluates". `E4` must include aborts on *forwarded*
  calls: a spend of a state whose signing failed is no UF-Tag forgery, since its pair was queried.
  `Pr[E4] ≤ (N_I + N_S)·E[δ^{255}] + q_v·2^{−256}`, the same term.
- **Final statement under A-OMPR.** Both routes give

      Adv^{bal} ≤ ε_ext + Adv^{ompr}(q_T, N_I + N_S) + (N_I + N_S)·E[δ^{255}] + q_v·2^{−256} + ε_bind^K + q_K·2^{−479} + q_K²·2^{−799}.

  - State it in this probe-free form, with UF-Tag (item 12) as the intermediate notion. The probe
    game is the Lean proof's interface, and `balance_le_noProbe` converts it.
  - The abort term is about `N·2^{−295.8}`. `ratatouille.md` Theorem 1 omitted it ("negligible");
    it is now explicit.
  - **[Lean]** `balance_le_ompr`, `balance_le_ompr_rate` (`Assumptions/RatatouilleOMPR.lean`):

        Pr[win] ≤ N·ε_iss + N·ε_spend + Adv^{ompr}(B'; k + 1 + N, N) + (k + 1 + N)·ρ(σ) + failAdv(B) + Adv^{coll}(C),

    at the Issuer's key (`ratTrap pk σ`, the per-key OMPR game), `B' = ompiRed (fdhRed A')`. The
    steps: `ufTagAdv_le_strict` (`Adv^{uf-tag+probe}(B) ≤ Adv^{uf-tag}_{strict}(B.noProbe τ) +
    failAdv(B)`, where the strict win is item 12's "never signed"; a win on a failed signing is a
    failure); then the **modelling hypothesis** `TagIdeal`: the strict UF-Tag advantage of
    `B.noProbe τ` against the concrete KP800 is at most the det-FDH advantage of an ideal-model
    forger `A'` (`Tag` a random function) with at most `k` hash and signing queries and `q_S = N`;
    then (a) and (c) (§5.1). `TagIdeal` is the step "`Tag` is ideal in the standalone game only":
    `Tag` is evaluated inside the protocol game and its proofs, so it cannot be an oracle there,
    and no Lean statement can turn the concrete forger into an ideal-model one. It is an explicit
    hypothesis of the theorem, not proved.
  - Compared with the paper's statement: the Lean bound has `N` for `N_I + N_S` (one call each),
    `q_T = k + 1` with the padding's `N` more targets, the term `(k + 1 + N)·ρ` from (c)'s
    correction, `failAdv(B)` for `(N_I + N_S)·E[δ^{255}] + q_v·2^{−256}` (bounded per table by
    `pr_failOut_le`), and **no** `q_K·2^{−479} + q_K²·2^{−799}`: those come from KP800 as a
    permutation with inverse queries (K1, and the permutation/function switch), and the Lean model
    of `Tag` in `TagIdeal` is a random function.
  - **[Lean] `Tag` a random permutation with inverse queries** (`Assumptions/FDHPerm.lean`,
    `Assumptions/RatatouillePerm.lean`). `KP800` is a lazily sampled random permutation `π` of the
    blocks `T × Z` with forward and inverse queries; `Tag(m)` is the first component of
    `π(emb m)` for an injective encoding `emb` of the pairs `m = (c, x)`; the signer evaluates `π`
    itself. The game is `advFDHPerm` (the challenger evaluates `π(emb m*)`; the win `FPWin`: `m*`
    never signed and `s*` a preimage of `Tag(m*)`). For a forger with at most `q_f` forward, `q_i`
    inverse and `q_S` signing queries:

        Adv^{perm}(A) ≤ Adv^{euf}_{det}(fdhPermRed A; q_f + 1 + q_S, q_S)
                        + (q_f + q_i + q_S + 1)²/|T × Z| + q_i·|M|/|T × Z|        (advFDHPerm_le_fdh)
                      ≤ Adv^{ompr}(B'; k + 1 + q_S, q_S) + Pr[D errs on one of k + 1 + q_S targets]
                        + (the same two terms),   k = q_f + 1 + 2q_S             (advFDHPerm_le_ompr)

    The proof:
    - *Two hybrids* (`advFDHPerm_le_hyb`): the permutation becomes the two-sided random function
      (`LazyPerm.prEvent_rp_le_rf`; `q = q_f + q_i + q_S + 1` queries read it), and fresh inverse
      answers are drawn outside the structured inputs (`LazyPerm.prEvent_rf_le_avoid`,
      `q_i·|M|/|B|`). Unlike CT-UF^open, the signer reads the permutation, so an inverse record at
      a structured input would change what the signer answers; the hybrid excludes it.
    - *The reduction* (`simCF`, `fdhPermRed`): a det-FDH forger with `H` a random function
      simulates the hybrid's permutation: a fresh forward query at `emb m` gets `(H(m), z)`, every
      other fresh forward answer is a coin, a fresh inverse answer a coin outside the structured
      inputs, the coins values of the world's random oracle at fresh indices; `Sign(m)` evaluates
      `π(emb m)` first, then asks the signing oracle. Against the det-FDH challenger its run,
      projected, is the hybrid (`combF_step`, under the invariant `InvF`: coins unused from the
      counter on, `H` defined only at recorded structured inputs, a forward record at `emb m`
      carries `H(m)`, no inverse record at a structured input). So `Tag(m*)` read off the table is
      `H(m*)` (`h_of_fwdFind`), and a hybrid win is a det-FDH win (`hyb_le_fdh`); the reduction
      makes at most `q_f + 1 + q_S` hash and `q_S` signing queries (`simA_budget`, counted in the
      challenger's state, `fdhImpl_hq`, `fdhImpl_signed`).
    - Ratatouille (`balance_le_ompr_perm`, `balance_le_ompr_rate_perm`, and with simultaneous
      extraction `balance_le_ompr_sim_perm`, `balance_le_ompr_rate_sim_perm`) takes the modelling
      hypothesis in this form, `TagIdealP`: the strict UF-Tag advantage of `B.noProbe τ` is at most
      `advFDHPerm` of some forger `A'` within `(q_f, q_i, q_S)`. For KP800, `|T × Z| = 2^{800}`
      and `|M| = 2^{320}` (32-byte commitment, 8-byte credits), so the terms are
      `(q_f + q_i + q_S + 1)²·2^{−800} + q_i·2^{−480}`: the paper's `q_K²·2^{−799} + q_K·2^{−479}`,
      with the inverse queries in the switching term as in §5.4. The OMPR target count is
      `k + 1 + q_S` with `k = q_f + 1 + 2q_S` (the reduction's hash and signing queries; the
      signer's forward evaluations are hash queries of the reduction). Non-vacuity:
      `Audit/PermFDH.lean` (a toy forger wins `advFDHPerm` with probability one; the balance
      corollaries instantiated for `balA0`, with `TagIdealP` an argument,
      `tagIdealP_of_eq_zero`).
    - The lazily sampled permutation is the eager uniform one, as in §5.4 (`rp_eqd_eager`).
    - With AES as random permutations (`ROM/RatatouilleBalanceSimPerm.lean`,
      `Assumptions/RatatouillePermSim.lean`) the balance theorem's forgery term `forgeAdvP` is at
      most the UF-Tag advantage of `forgerP : TagForger PTable` (`TagForger` is generic in the
      table that is its common randomness; `forgeAdvP_le_ufTag`). Its `reads` property
      (`bOut_readsP`) is `bOut_reads_of` with `games_congrP`. The modelling hypothesis is then
      taken for `(forgerP …).noProbe τ`: `balance_le_ompr_simP` (`TagIdeal`),
      `balance_le_ompr_sim_permP` (`TagIdealP`). Non-vacuity: `Audit/PermSim.lean`.

**Does R1 remove the issue?** No. R1 is orthogonal to it.
- The probe comes from the API order (F5), not from Tag's input. With R1, `spend_response` still
  signs `Tag(c', x', salt)` before the store check, so its answer still reveals whether `D`
  succeeded. Now the salt is fresh and hidden, so the abort bit at that target is
  Bernoulli(`δ^{255}`) whatever `A` does.
- The T5 reduction to EUF-CMA of `UOV[Tag]` must still answer that bit without signing. Signing
  `(c', x')` would make it a signed message, so a later spend of that state would be no EUF
  forgery: the same obstacle as above.
- So T5 also carries `(N_I + N_S)·E[δ^{255}] + q_v·2^{−256}`. The specified signer, like `D`,
  aborts after 255 bad vinegars, and an EUF-CMA forgery on a message whose signing aborted does
  not count.
- What removes the term:
  - **The F5 fix** (check the store inside `spend_response`, before signing) removes the probe.
    The aborts on signing calls remain, so the term stays as `(N_I + N_S)·E[δ^{255}]`, now over
    signing calls only.
  - **A signer that cannot abort** (salt-UOV with unbounded salt retry, §4 item 2) makes the probe
    constant and the term zero. C4 advises against it for other reasons.
  - Neither is needed: the term is about `2^{−232}` at `N = 2^{64}`.

**Lean** (`ROM/RatatouilleProbe.lean`; no `sorry`, no `axiom`):
- `patch`, `FailOut`, `failAdv`;
- `run_patch_of_not_fail`, `failOut_iff_patch` (step 2);
- `TagForger.noProbe`, `noProbe_probeFree`, `ufWin_noProbe`, **`ufTagAdv_le_noProbe`** ((a) for
  any signer, with the failure term `failAdv`);
- `withFail`, **`pr_failOut_le`** (step 4: per table, over the failure bits, at most the number of
  logged pairs times `Pr[bad]`);
- `signRec_probeRec_le`, `logs_length_le`, `forger_logs_le` (at most `N` logged pairs);
- **`balance_le_noProbe`** (Theorem 1 with the probe-free forger and `failAdv`).

Two steps stay on paper:
- that pqov's `derive_preimage` in the vinegar ROM has the law `withFail(f, τ)` (step 3, Lemma D);
- moving `pr_failOut_le` from one table to the average over the lazy oracle and the cipher in
  `failAdv`. This is a Fubini step: the failure bits are independent of both.

The module is separate from `Protocols/UOVAssumptions.lean`, which imports only Mathlib and is
imported by `Privacy/PqovDelta.lean`.

## 6. Proposition 8: OMPR versus 17-shift OMPR

**(a) Guessing.** `Adv^{ompr⊕τ}(N, q) ≤ τ^{q+1}·Adv^{ompr}(N, q)`.
- On request `k`, guess `a_k ← [m_k]` and answer `h_k := t_k ⊕ δ_{k,a_k}`. This is uniform, and
  the view doesn't depend on the guesses.
- The output is usable iff all `q+1` forgeries used the guessed shift.
- For `q = 0` the loss is just `τ`, so OMPR⊕τ(N, 0) ≤ `τN·Adv^{uov}`. For τ = 17, the loss is
  `≥ 2^{4(q+1)}` (Lean `guess_loss`).

**Lean** (`lean/VoleMole/Assumptions/Shift.lean`, `advOMPRShift_le_guess`), for `τ ≥ 1`:
`Adv^{ompr⊕τ}(B; n, ℓ) ≤ τ^{ℓ+1}·Adv^{ompr}(R; n, ℓ)`. `R = guessRed n τ B` draws a uniform guess
vector `g : [n] → [τ]` up front. It answers request `k` with shift list `δs` by `t − δs[g k]` for a
fresh challenge `t`, at the fresh label `(x, k)`, so the guess is uniform in `[τ]`, not in
`[m_k]`. `R` is OneMore's `red addHint` of an adapter. The proof has three parts:
- perfect programming (`omuf_good_le`);
- an exact simulation of the adapter by the shift game (`adReal_eqd`, `recCh_eqd`);
- with the guesses drawn after the run, a count: a winning run's at most `ℓ+1` claimed requests
  are hit with probability `≥ τ^{−(ℓ+1)}` (`guess_count`, `pr_guess_ge`).

The converse direction, A1 of `uov-open-reductions.md` (`advOMPR_le_shift`, tight), is in the same
file.

**(b) Simple-embedding reductions lose `τ^{q+1}`.**
- Call `R` *simple-embedding* if it runs `A` once without rewinding, forwards each of `A`'s preimage
  queries to its own oracle, and answers request `k` with `h_k = t_{j(k)} ⊕ c_k`, where `c_k` is
  any function of its view.
- A forgery `(k, a, s)` gives a challenge preimage only if `c_k = δ_{k,a}`. Otherwise
  `P(s) = t_{j(k)} ⊕ (c_k ⊕ δ_{k,a})` equals another challenge target only with probability
  `≤ n²·2^{−360}`. Aligning two shifts at once needs `t_j ⊕ t_i = δ_{k,1} ⊕ δ_{k,2}`, which is
  just as unlikely.
- `A`'s queries come before its outputs, so each costs `R` one call. Hence `R` needs all `q+1`
  forgeries usable.
- Against the (unbounded) adversary that picks each `a_k` uniformly, independently of `h_k`, `R`
  succeeds with probability `≤ τ^{−(q+1)} + n²·2^{−360}`.

**(c) Generic model: no gap beyond counting.**
- Replace `P` by a random function `F : F^N → F^M`, with a forward oracle (`W` queries) and a
  deterministic inversion oracle returning a uniform preimage (`q` queries; lazily: a fresh point
  `x` with `F(x) := y`). Then

      Adv^{ompr⊕τ}(N, q) ≤ ((W + q + 1)·Nτ + N²τ²/2)·2^{−360},    Adv^{ompr}(n, q) ≤ ((W + q + 1)·n + n²/2)·2^{−360}.

- *Proof.*
  - Two requests share a shifted target only if the later `h` hits one of `τ²` values; this is the
    `N²τ²` term.
  - Otherwise, `q` inversions cover at most `q` requests, so some winning request `k` was never
    inverted on.
  - Its `s` is not an inversion answer for a value of `k`'s family. So its `F`-value was fresh at a
    forward query or final check, and it hit one of at most `Nτ` shifted targets.
- So, generically, OMPR⊕τ with `N` requests is OMPR with `Nτ` targets. Both are far below the UOV
  margins at `N, W ≤ 2^{128}`.
- This is evidence of the same kind as the paper's App. A. It ignores UOV's algebraic structure,
  which is the only place a separation could come from.
  - We found no structural use of the shifts. Turning a preimage of `h ⊕ δ₁` into one of `h ⊕ δ₂`
    means solving `P(s + e) − P(s) = δ₂ − δ₁`. That is the UOV problem for the translated map
    `e ↦ P(s + e) − P(s)`, which has the same oil space.

**(d) PomFRIT: U1's additive loss is optimal among simple-embedding reductions.**
- In PomFRIT the "shift" is the prefix of whichever alive-tree group the prover completes. That
  choice is forced by `Δ`, not free.
- Completing with a group of width `w` succeeds with probability `≤ 2^{w−128}` per H₂³ query
  (`pomfrit.md` Lemma P, step 4).
- Lean `group_gap`: for complementary groups with widths `8b + 7a`, the narrower one is ≥ 6 bits
  narrower. The gap 6 is attained by widths 57 and 63 (`group_gap_attained`).
- So the 57/63 adversary of `pomfrit.md` §5 ("Tightness") completes with the minority prefix in a
  fraction `≈ 2^{−71}/(2^{−65} + 2^{−71}) ≈ 2^{−6}` of its accepted outputs, at about
  `2^{65}/Pr[open]` H₂³ calls each.
- A simple-embedding reduction fixes `c` when `H_T` is queried, before `Δ` exists.
  - If it embeds the majority prefix (U1's `E₁`), it fails with probability `≈ Q₃·2^{−71}` (times
    `Pr[open]`).
  - If it embeds the minority prefix, it fails on the far likelier majority completions.
- Hence **the additive `Q₃·2^{−71}` of U1 is necessary for this class.** At `Q₃ = 2^{64}`, that is
  the `≈ 2^{−7}` margin loss (`pomfrit.md` §6.3).
- A non-simple reduction would have to rewind past the `H_T` answer. In a one-more game that spends
  fresh oracle calls on the replayed queries, unless they repeat exactly. Determinism of `D` helps
  only in that case.

**Verdict on G1.**
- OMPR ⇒ OMPR⊕17 is **open**. No tight black-box proof exists in the natural class (b, d).
  `uov-open-reductions.md` §4 extends (b) to all reductions that are black-box in `(P, D)`, with
  rewinding (loss `≥ τ^{q+1}/2`), and notes that (b) must allow embeddings `μ·t_j ⊕ c_k`.
- There is no separation either, and the generic bound (c) is the same.
- `ompr-shift-algebra.md` treats reductions that use the algebra of `P`. A reduction that is
  black-box in the adversary still loses `τ^{q+1}/4`, unless it breaks OMPR^free
  (`uov-open-reductions.md` §3.1). The only structural use of the shifts found is a list on one
  line `F·c`, which removes one of the 45 equations: no gain at τ = 17, `≈ 2^{3.7}` at `τ ≥ 256`.
- `ompr-cryptanalysis.md` adds the attacks that use the oracle: none separates the two games,
  and none beats the direct forgery attack.
- Keep U1, which is proved and loses at most `2^{−7}` at `2^{64}` queries, as the main statement.
  Cite U2 under the explicitly stronger OMPR⊕17.
- The cleanest way out is a protocol change, §8 C2. It makes the 17-shift question moot.

## 7. Assessment: one common assumption?

Yes: **A-OMPR, i.e. OMPR(n, q) of Def. 3.1 for uov-Ip with `SPre = derive_preimage`, per key.**

| Protocol | From A-OMPR | Loss | Best alternative without OMPR |
|---|---|---|---|
| PomFRIT | U1 (`pomfrit.md`); **and necessary** (T6). [Lean] U1/U2 with OMPR / OMPR⊕τ (`pomfrit_U1_ompr`, `pomfrit_U2_omprShift`), Lemma P's term explicit; T6 generic core (`ompr_le_blind`) and in PomFRIT's game up to the Lean client's completeness term (`pomfrit_T6`) | `(Q₃+ℓ+1)·2^{−71}`; optimal for relativizing reductions (P8, row O) | none: equivalent to OMPR; U2 needs OMPR⊕17 |
| Moussaka | CT-UF^open ⇐ OMPR (T4), in Thm 1. [Lean] `omuf_le_num_ompr`, with `Com` idealized in the standalone game (`hmodel`) | tight up to `n·E[δ^{255}]`, ×K | GPI + OW, loss `q_π`, ×K (T4) |
| Ratatouille | A-OMPI ≤ OMPR (T1c), in Lemma 2.1 and Thm 1; the Lean theorem's UF-Tag+probe ≤ A-OMPI + abort term (P9). [Lean] `balance_le_ompr`, with `Tag` idealized in the standalone game (`TagIdeal`) | tight up to `(q_T + Q)·E[δ^{255}]`, plus `(N_I + N_S)·E[δ^{255}] + q_v·2^{−256}` for Issuer aborts (`E4`, or the probe) | spec-SUF-CMA (T1e); GPI + OW (T2), loss `q_T`; both plus the same abort term |

Reasons:
1. PomFRIT forces it (T6).
2. It covers the other two tightly, up to the sampler-failure term `n·E[δ^{255}] ≈ n·2^{−295.8}`.
3. It is the paper's published assumption (Def. 3.1) instantiated with the actual sampler.
4. A single assumption makes the key-separation rule uniform. Each key's oracle answers count in
   that key's one-more budget, so **no key may serve two protocols**. That is `pomfrit.md` F5 and
   `ratatouille.md` F1. A PomFRIT key signs arbitrary targets, Ratatouille's and Moussaka's
   included.

Each protocol note should state its UOV hypothesis as "A-OMPR (`uov-assumptions.md` §3, item 7)".
- For Moussaka, replace CT-UF by CT-UF^open, with the repaired Lemma U (done, `moussaka.md` §3.3;
  plain CT-UF is false, row O of §0).
- For Ratatouille, keep A-OMPI as the immediate hypothesis, with the chain
  OMPR ⇒ A-OMPI ⇔ det-FDH.

In the QROM, none of these reductions is available as written. All of them program an idealised
Com, Tag or `H_T`, and `pomfrit.md` §7 and `ratatouille.md` §10 already flag the missing tools. The
salted, hash-then-sign variants in §8 are the ones with a known QROM proof strategy (salted
hash-and-sign with retry [KX24]).

## 8. Recommendations (not implemented)

**C0 (documentation only).**
- `moussaka.md` §3.3: replace CT-UF by CT-UF^open, and Lemma U by T4. `B₂` outputs the openings.
- `ratatouille.md` §2.3: qualify "salted proofs avoid this". Note that A-OMPI ⇔ det-FDH, and
  ⇐ spec-SUF.
- `pomfrit.md` G1: add §6's optimality result.
- All three notes: cite one A-OMPR.

**C1 (Ratatouille, cheap): R1.** Put a 16-byte Issuer salt in Tag's zero slot.
- Effect: balance ⇐ EUF-CMA of salted UOV[Tag] (T5).
- Wire format:
  - the issuance response and spend response each grow by 16 bytes;
  - the token grows by 16 bytes;
  - the spend witness grows by 16 bytes, i.e. `16·17 = 272` bytes more proof. At these parameters
    the proof grows by 17 bytes per witness byte: Moussaka's redeem witness is 87 bytes longer
    than its issue witness, and its proof is `8751 − 7272 = 1479 = 17·87` bytes longer
    (`moussaka.hpp:30-32`).
  - No extra Keccak call.
- Margins: Tag's fixed bits drop from 480 to 352, so the inverse-landing term goes from `2^{−479}`
  to `2^{−351}`.
- Privacy:
  - `σ` is witness-only and never revealed at spend, so an Issuer-chosen `σ` cannot link sessions,
    given ZK.
  - On `main`, do not place `σ` among the leading witness bytes that `lean/docs/zk.md` §4 uses as the
    free-XOR label offset (the bytes whose unpredictability its `Pred_R` term needs), because the
    Issuer knows `σ`. This is irrelevant after the label-row fix.
- `σ` must be fresh and uniform. A `σ` derived from the request turns the scheme back into det-FDH.

**C2 (Moussaka and PomFRIT, costly): hash-then-sign the request.**
- Have the Anchor/Issuer sign `Tag_P(t, σ) = KP800(DST_P ‖ σ ‖ t ‖ 0…)[0..45)` instead of the raw
  `t`, and return `σ`. The client proves `P(s) = Tag_P(t, σ)` with `σ` in the witness.
- Effect:
  - The oracle becomes salted-UOV signing of the message `t`, so OMPR, CT-UF and openings are no
    longer needed.
  - Moussaka: distinct `(ctx_red, nf)` plus binding give distinct `t`, and pigeonhole yields an
    EUF-CMA forgery.
  - PomFRIT: forgeries need distinct `t_i = h_i ⊕ r_i`. `r_i` ranges over ≤ 17 alive prefixes
    fixed before `h_i`, so a collision has probability `≤ 17²·Q_T²·2^{−360}`. **No `H_T`
    programming and no `E₁`** are needed, so the Shift term and the 17-shift question disappear.
  - A key used only through domain-separated tags (with `derive_preimage` not exposed for it) also
    defuses the cross-protocol hazard F1/F5.
- Cost:
  - one KP800 evaluation inside `RedeemRelation` (Moussaka), or inside the redeem circuit
    (PomFRIT, which currently proves no hash). With two committed 100-byte intermediate states
    plus `σ`, that is 216 witness bytes, i.e. ≈ +3.7 KB per proof at 17 bytes per witness byte
    (C1);
  - +16 bytes in the response.
- PomFRIT departs from the paper's raw-trapdoor design. Blindness is unchanged in kind, since `t`
  and `σ` stay hidden at redemption.

**C3: keep `derive_preimage` deterministic.**
- Randomized vinegar has the same per-call law (§4), but gives several preimages per target. That
  is a stronger oracle.
- It would also void `pomfrit.md` §9.5's honest-Issuer protection.

**C4: do not switch to salt-UOV retry signing unless the retry count is hidden.**
- It would make the C1/C2 reductions rest on the UOV problem alone.
- But the geometric retry count reveals the badness of the published preimage (§4), which is
  information about `𝒪`.
- GPI is the recommended route to a UOV-problem-based statement.

**C5: enforce key separation by type.**
- For example, a distinct secret-key type per protocol, or a protocol label bound into the signed
  hash (C2).
- A per-protocol vinegar DST alone does not help. Distinct targets already get independent
  preimages (Lemma D), and the hazard is the raw oracle itself.

## 9. Open items

- **GPI** is new. It needs cryptanalysis: is badness of `s` decidable from `pk`, or with a few
  samples? First analysis: `uov-open-structure.md` Part B. Reliable (certifying) badness tests
  give key recovery; no cheaper test is known; weak two-sided distinguishers remain open.
- **OMPR ⇒ OMPR⊕17** (§6). Partly answered in `uov-open-reductions.md` §4: OMPR⊕τ ⇒ OMPR is
  tight (Lean `advOMPR_le_shift`), and the `τ^{q+1}` guessing bound is Lean
  `advOMPRShift_le_guess`; the converse has no relativizing proof with loss below `τ^{q+1}/2`,
  even with rewinding; the shift cannot be absorbed into the key. `ompr-shift-algebra.md`: a proof
  that uses the algebra of `P` but the adversary as a black box would break OMPR^free (Theorem R
  there); no attack at τ = 17. A proof that is not black-box in the adversary, and a separation,
  remain open. `ompr-cryptanalysis.md`: the two games have the same oracle, and no attack that
  uses it beats the oracle-free ones; a separation can only be on the forgery side.
- **OMPR itself** has no proof from the UOV problem (P7) and no outside cryptanalysis. First
  analysis: `ompr-cryptanalysis.md`. The answers are uniform good fibre points; they give the oil
  space only by a vinegar collision (`2^{292.5}` calls) or by statistics of goodness (`2^{600}`
  answers for linear ones). Open: statistics of higher degree (chosen-target GPI), quantum
  attacks.
- **CT-UF with arbitrary targets** versus OMPR. Answered in `uov-open-reductions.md` §2–§3: CT-UF
  as defined is false (scaling); up to scalars it *is* the "free non-challenge calls" variant,
  which is not implied by OMPR for relativizing reductions, and is implied when the free calls do
  not depend on the targets. Whether UOV satisfies the variant is open.
- ~~Turn the **meta-reduction** (§5.7) into a theorem, with a precise proviso.~~ Done for
  key-preserving reductions: `uov-open-structure.md` Part A. Open: reductions that change the key.
- **QROM** versions of T2–T5. This needs quantum programming of an invertible permutation for
  Com/Tag. The salted variants are the promising ones.
- `δ(sk)` for a fixed key is not bounded: `L_v = vᵀS` ranges over a subspace of dimension `≤ 74`,
  so it is not distributed like a uniform matrix. On average over the key (uniform `P2`, any
  `O`, `P1`) `E[δ^m] ≤ δ_unif^m + 256^m/(255·256^{74})` is proved (§1, `Privacy/PqovKeys.lean`);
  the uniformity of `P2` (AES-CTR output) is the modelling step. The proofs use `δ(sk)`
  symbolically, and `E[δ^{256}]` only in Lemma D.

## 10. Lean

`lean/VoleMole/Protocols/UOVAssumptions.lean`:

| Statement | Lean |
|---|---|
| `|S^G_y| = |G|` for every target (Lemma C) | `card_good_fiber` |
| `(v, x) ↦ (v, f_v(x))` bijective on `G × X` | `good_coords_bijective` |
| One-sided TV is symmetric for equal masses | `tv_symm` |
| `TV(U(G), U(α)) = 1 − |G|/|α|` | `tv_unif_good` |
| `TV(U(G)^q, U(β)^q) = 1 − (|G|/|β|)^q` | `tv_unif_good_pow` |
| `TV(μ, U(G)) ≥ μ(α ∖ G)` (Prop. 4.1) | `tv_ge_mass_off` |
| `∏(1 − a_i) ≥ 1 − Σ a_i` | `one_sub_sum_le_prod` |
| `Pr[invertible] = ∏ (1 − q^i/q^n)` (from `Matrix.card_GL_field`) | `prob_invertible_eq` |
| `Pr[singular] ∈ [1/q, 1/(q−1)]`; `[2^{−8}, 1/255]` for `45 × 45` over a 256-element field | `singular_prob_bounds`, `singular_prob_bounds_256` |
| Complementary group widths differ by ≥ 6; attained at 57/63 | `group_gap`, `group_gap_attained` |
| `17^{−k} ≤ 16^{−k}` | `guess_loss` |
| One-more counting; wasted calls | `one_more_count`, `wasted_calls` |
| UF-Tag+probe ≤ UF-Tag of the probe-free forger + failures (P9(a)); failure event read off the total signer; union bound per table; `B` logs ≤ `N` pairs; Theorem 1 with a probe-free forger | `ufTagAdv_le_noProbe`, `failOut_iff_patch`, `pr_failOut_le`, `forger_logs_le`, `balance_le_noProbe` (in `ROM/RatatouilleProbe.lean`) |
| T1(a) det-FDH ≤ A-OMPI; T1(c) A-OMPI ≤ OMPR (corrected: `q_T + Q` targets, `+ (q_T + Q)·ρ`); both | `advFDH_le_ompi`, `advOMPI_le_ompr`, `advOMPI_le_ompr_rate`, `advFDH_le_ompr_rate` (in `Assumptions/IdealTag.lean`) |
| P9(b) with `Tag` a random function, and the final statement under A-OMPR (with the modelling hypothesis `TagIdeal`) | `ufTagAdv_le_strict`, `balance_le_ompr`, `balance_le_ompr_rate` (in `Assumptions/RatatouilleOMPR.lean`) |
| T4 with `Com` a random permutation with inverse queries; the switch permutation/function; Moussaka and unbound Moussaka down to OMPR with it | `advCTUFPermAt_le_ompr`, `advCTUFPermAt_le_ideal` (`Assumptions/CTUFPerm.lean`), `prEvent_rp_le_rf`, `prEvent_invHit_le`, `prEvent_rf_le_avoid` (`Assumptions/LazyPerm.lean`), `omuf_le_num_ompr_perm`, `omufU_le_num_ompr_perm` (`Assumptions/PermLinks.lean`) |
| det-FDH with `Tag` a random permutation: the game, the hybrids, the reduction to det-FDH and to OMPR; Ratatouille balance under OMPR with it | `advFDHPerm`, `advFDHPerm_le_hyb`, `combF_step`, `combF_inv`, `hyb_le_fdh`, `advFDHPerm_le_fdh`, `advFDHPerm_le_ompr` (`Assumptions/FDHPerm.lean`), `balance_le_ompr_perm`, `balance_le_ompr_sim_perm` (`Assumptions/RatatouillePerm.lean`) |
| Moussaka with AES and `Com` both random permutations with inverse queries, down to OMPR | `ctufForgerP`, `gameP_congr`, `tableQueryLog_normJ`, `omuf_le_open_simP`, `omuf_le_num_ompr_simP` (`Assumptions/PermSimLinks.lean`) |
| Unbound Moussaka with AES and `Com ∪ UCom` both random permutations, down to OMPR | `omufU_le_num_simP` (`ROM/MoussakaUnboundOMUFSimPerm.lean`), `ctufForgerUP`, `gameUP_congr`, `tableQueryLog_normP`, `omufU_le_num_open_simP`, `omufU_le_num_ompr_simP` (`Assumptions/UnboundPermSimLinks.lean`) |
| Ratatouille with AES as random permutations, down to OMPR (`Tag` a random function or permutation) | `forgerP`, `bOut_readsP`, `forgeAdvP_le_ufTag`, `balance_le_ufTag_simP`, `balance_le_ompr_simP`, `balance_le_ompr_sim_permP` (`Assumptions/RatatouillePermSim.lean`) |
| Cores of `uov-open-reductions.md`: combiner forest, lottery accounting, the rewinding supermartingale inequality | `combiner_count`, `lottery_count`, `four_mul_le_pow`, `rewind_supermartingale` |
| Scaling symmetry of `P` and the one-query CT-UF attack (`Spec/PqovScale.lean`) | `qmap_smul`, `sq_pow_128`, `scaled_preimage`, `ctuf_scaling_attack` |

The probabilistic steps (Lemma D, the hybrid games, the ideal-permutation bookkeeping) are on paper,
except T1(a), T1(c), the chain of P9(b), and T4 with `Com` a random function (below).

**The assumptions as games** (`lean/VoleMole/Assumptions/UOV.lean`, `UOVLinks.lean`; no `sorry`,
no `axiom`). A *trapdoor* (`Trapdoor`) is a key generator, the preimage relation `IsPre pk s t`
("`P(s) = t`") and the sampler `D`; every game is generic in it.

| §3 item | Game | Notes |
|---|---|---|
| 1 | `advUOV`, `advUOVn` | `advUOVn_le_sum`: n-target ≤ Σᵢ single-target, by embedding at `i` (`embedAt`) |
| 2, 3 | `advOW`, `advGPI` | GPI's good sampler `U(Good_sk)` is a parameter |
| 6 | `advFDH` | lazy random oracle `H`, signer `D(H(m))`, budgets `q_H`, `q_S` |
| 7 | `advOMPR` (= `OneMore.omExp` with `goodPre`: labelled targets on demand), `advOMPR31` (Def. 3.1 literally: all targets up front) | `advOMPR_le_ompr31`: on-demand ≤ Def. 3.1, for the popping adversary `popAdv` (a simulation, `comb31_eqd`) |
| 8 | `advOMPRShift` (`omExp` with `goodShift τ`) | |
| 9 | `advOMPI` | targets from a stream of `q_T`, index oracle, budget `Q` |
| 10 | `advCTUF`, `advCTUFAt` | **false for UOV**: `ctuf_pqov_broken` (the rescaling forger `scaleForger` wins with probability 1, from `ctuf_scaling_attack`) |
| — | `advCTUFXAt` (CT-UF^×, freshness up to a class; `uovCls`: nonzero scalars) | `advCTUFXAt_le`; the rescaling forger loses it (`not_ctxWin_scale`) |
| 11 | `advCTUFOpen`, `advCTUFOpenAt` | `advCTUFOpenAt_le`: ≤ CT-UF |
| 11, ideal `Com` | `advCTUFIdeal`, `advCTUFIdeal1`, `advCTUFIdealAt` (`Com` a lazy random function, `CIWin`) | `advCTUFIdeal1_le_ompr` (T4), `advCTUFIdeal_le_sum` (`K` keys); §5.4 |
| 12 | `advUFTag`, `advUFTagProbe` (and `…At`) | `advUFTagAt_eq_probe`: a forger without probe is a probe forger |

CT-UF and UF-Tag are *semantic-oracle* games (`SemForger`, the form of Ratatouille's
`TagForger`): the forger gets the signer as a function, with a proof (`reads`) that its output
depends on it only at the points it logs (and, for the probe, only on success there). Every
oracle forger is one (`ofOracle`, same advantage); the converse is not proved. The
trivial attacks lose each game (`not_wins_of_iq`, `not_ompiWin_of_opened`, `not_fdhWin_of_signed`,
`not_ctWin_of_signed`, `not_ufWin_of_answered`). pqov's trapdoor (keys of
`Privacy/PqovKeys.lean`, the reference `derive_preimage`) is correct (`Audit.pqovTrap_correct`).

The protocol terms:
- **Moussaka** (repairs Lemma U as §5.4 says): `omuf_le_num_open` is `omuf_le_num` with
  `Adv^{ct-uf-open}_K` of the explicit forger `ctufForger` in place of `Pr[Forge]`. The forger runs
  the OMUF game and all extractions with the signers as its oracle (it reads them only at the
  accepted Issue queries, `game_congr`), outputs `Forge`'s forgery and an extracted opening of
  every signed target. The openings may be missing only if an accepted issuance proof was not
  extracted, which is already the term `BadI` (`win_imp_open`), so no term is added.
- **Ratatouille**: `ufTagAdv` is the UF-Tag-with-probe advantage (`ufTagAdv_eq`);
  `balance_le_ufTagProbe`. Under OMPR (`Assumptions/RatatouilleOMPR.lean`): `balance_le_ompr`,
  with the UOV term `Adv^{ompr}` of the explicit reduction `ompiRed (fdhRed A')`, the error term
  `badTargets` (`≤ (k + 1 + N)·ρ`), `failAdv(B)` and `Adv^{coll}(C)`, under the modelling
  hypothesis `TagIdeal` (§5.8). Instantiated in `Audit/IdealTag.lean` (every hypothesis but
  `TagIdeal`, which holds e.g. when the strict UF-Tag advantage is `0`, `tagIdeal_of_eq_zero`).
- **PomFRIT**: U1's and U2's experiment terms are `advOMPR` and `advOMPRShift τ` of
  `pomTrap KG pre` by definition (`pomfrit_U1_ompr`, `pomfrit_U2_omprShift`), and U1's is at most
  Def. 3.1's advantage of `popAdv` (`advOMPR_le_ompr31`; instantiated in `Audit/Nonvacuous.lean`).

- **Moussaka down to OMPR** (`Links.omuf_le_num_ompr`): `omuf_le_num_open` with the CT-UF^open
  term bounded, under the modelling hypothesis `hmodel` (concrete `Com` ≤ ideal `Com` for some
  forger `F` within the budget), by `Σ_j (Adv^{ompr}_{key j}(B_j; q_f + 2q_S + 1, q_S) +
  (q_f + 2q_S + 1)·failPr_{key j})` (T4 and the `K`-key step, §5.4). Its hypotheses, `hmodel`
  included, are met by a toy forger in `Audit/Nonvacuous.lean` (`toyF_wins`: the ideal game is
  winnable).

**Reductions** (`Assumptions/CTUFOpenOMPR.lean`, generic lemmas in `Assumptions/LazyIdeal.lean`):
T4 with `Com` a random function, `advCTUFIdeal1_le_ompr`; the `K`-key step,
`advCTUFIdeal_le_sum`, `advCTUFIdealAt_le_sum`; together, `advCTUFIdeal_le_ompr`,
`advCTUFIdealAt_le_ompr` (§5.4). Generic: lazy random function = pre-sampled stream
(`rfStream_presample`, `rfStream_rest_le`), union bound over a uniform stream
(`prEvent_unifList_exists_le`), embedding a key among iid keys (`iidVec_update`).

The reductions between the games (`lean/VoleMole/Assumptions/Shift.lean`, `Blind.lean`,
`BlindPomfrit.lean`; audits in `Audit/OMPRShift.lean` at PomFRIT's trapdoor, `τ = 17`, and
`Audit/T6Pomfrit.lean`):

| Statement | Lean |
|---|---|
| A1 (`uov-open-reductions.md` §4.1): `Adv^{ompr}(B) ≤ Adv^{ompr⊕τ}(shiftZero B)`, `τ ≥ 1`, tight; `Adv^{ompr⊕τ}` grows with `τ` | `advOMPR_le_shift`, `advOMPRShift_mono` |
| P8(a): `Adv^{ompr⊕τ}(B) ≤ τ^{ℓ+1}·Adv^{ompr}(guessRed n τ B)` | `advOMPRShift_le_guess`, `guess_count`, `pr_guess_ge`, `adReal_eqd`, `recCh_eqd` |
| T6, generic core (§5.6): `Adv^{ompr}(B) ≤ Pr[Forges] + Pr[CompFail]` for the blinding forger of any client with distinct session labels | `ompr_le_blind`, `blindAdv`, `Client`, `bcomb_eqd`, `win_mid`, `post_pres` |
| T6 at PomFRIT (§5.6): `Adv^{ompr}(B; n, ℓ) ≤ Pr[PomWin(blindForger)] + compFail` in PomFRIT's one-more forgery game for a forger with coins (`= game` without coins), any client as oracle computations; with `B`'s budget `Q`, `Q + ℓ + 1` targets; unused targets do not change `Adv^{ompr}` (`Assumptions/BlindPomfrit.lean`, `Audit/T6Pomfrit.lean`) | `pomfrit_T6`, `pomfrit_T6_bound`, `compFail`, `gameB`, `gameB_liftF`, `PomClient`, `toClient`, `distinct_toClient`, `blindForger`, `blindForger_bound`, `star`, `projF_eqd`, `advOMPR_pad` |
| A simulation along a projection (shared, `Assumptions/LazyIdeal.lean`) | `simulateQ_proj_eqd_inv` |

Not mechanized:
- T1(b, d, e), T2, T3, T5 and P8(b)–(d) (T1(a) and T1(c) are in `Assumptions/IdealTag.lean`, §5.1;
  T4 with `Com` a random function in `Assumptions/CTUFOpenOMPR.lean`, §5.4);
- the completeness term of T6 at PomFRIT for the Lean client, which needs the Lean prover as
  oracle computations and its completeness in the lazy random-oracle model (§5.6);
- the converse of `advOMPR_le_ompr31`. In Def. 3.1 the adversary's coins may depend on the
  targets, and an on-demand adversary (`omExp`) draws its coins before it sees them. The converse
  holds for coins-first adversaries, but is not stated;
- OMPR^free, and items 4 and 5.

pqov's `derive_preimage` and its keys (§1–2): `Spec/PqovSigner.lean` (`signer_correct`,
`signer_fail`, 255 attempts), `Spec/PqovKey.lean` (`sysCoef_eq_pqovS`, `qmap_vinVec_eq`,
`qmap_oil_eq`, `oilSpace_iff_P3Pqov`, `pqovKey`, `oilSpace_pqovKey`, `sysCoef_pqovKey`),
`Privacy/PqovDelta.lean` (`pr_singular_avg`, `pr_singular_all`, `pr_dependent_le`) and
`Privacy/PqovKeys.lean` (`avg_delta_pqovKey`, `avg_delta_pow_pqovKey`, `avg_delta255_pqovKey`).
`lake exe spec_kats` checks the model against the C++ `derive_preimage` (`Spec/PqovSignerExec.lean`).

## References

- [UOV-R3] W. Beullens et al., *UOV: Unbalanced Oil and Vinegar, Algorithm Specifications and
  Supporting Documentation*, v3.0, 30 Aug 2026. §3.2 (signing), App. A (salt-UOV, Def. 2, Thm 1).
  https://csrc.nist.gov/csrc/media/Projects/pqc-dig-sig/documents/UOV_Specification_R3.pdf
- [SSH11] K. Sakumoto, T. Shirai, H. Hiwatari, *On provable security of UOV and HFE signature
  schemes against chosen-message attack*, PQCrypto 2011 (= [84] in [UOV-R3]).
- [BBBMR26] C. Baum, J. Beckmann, W. Beullens, S. Mukherjee, C. Rechberger, *Concretely efficient
  blind signatures based on VOLE-in-the-head proofs and the MAYO trapdoor*, ePrint 2026/109, USENIX
  Security 2026. Def. 3.1, App. A.
- [BNPS03] M. Bellare, C. Namprempre, D. Pointcheval, M. Semanko, *The one-more-RSA-inversion
  problems and the security of Chaum's blind signature scheme*, J. Cryptology 16(3), 2003.
- [BMV08] E. Bresson, J. Monnerat, D. Vergnaud, *Separation results on the "one-more" computational
  problems*, CT-RSA 2008.
- [Beu21] W. Beullens, *Improved cryptanalysis of UOV and Rainbow*, EUROCRYPT 2021.
- [KX24] H. Kosuge, K. Xagawa, *Probabilistic hash-and-sign with retry in the quantum random oracle
  model*, PKC 2024 (ePrint 2022/1359). Not retrieved in this session; cited only as the relevant
  line of work.
- [GPV08] C. Gentry, C. Peikert, V. Vaikuntanathan, *Trapdoors for hard lattices and new
  cryptographic constructions*, STOC 2008 (preimage-sampleable functions; the uniform-preimage
  property that UOV's vinegar-retry signer lacks).
