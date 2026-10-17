# UOV assumptions behind vole-mole's unforgeability proofs

This note relates the protocol-specific UOV assumptions used in
- `lean/docs/security/pomfrit.md` (A-OMPR, i.e. Def. 3.1 of ePrint 2026/109, and its τ-shift variant A-OMPR⊕17),
- `lean/docs/security/moussaka.md` (CT-UF and its Lemma U),
- `lean/docs/security/ratatouille.md` (A-OMPI, UF-Tag, recommendation R1),

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
- **CT-UF^open**: CT-UF in which the adversary must also open every target it had signed;
- **det-FDH**: EUF-CMA of deterministic hash-and-sign UOV, `σ = D_sk(H(m))`.

**Results.**

| # | Statement | Loss | Where |
|---|---|---|---|
| L-D | `derive_preimage` (ROM) is the *ideal deterministic sampler*: `D(y)` uniform on the good preimages of `y`, independently per `y` | `q_v·2^{−256} + ℓ·E[δ^{256}]` | §2 |
| L-C | Real preimages are never "bad"; uniform ones are bad w.p. `δ ≈ 2^{−7.994}`. q samples: TV `1 − (1−δ)^q` exactly. Every public-key-only simulator is off by at least its mass on bad points | exact | §2, §4 |
| T1 | A-OMPI ≡ det-FDH EUF-CMA (ROM); `Adv^{euf}_{spec} ≤ Adv^{ompi} ≤ Adv^{suf}_{spec}`; `Adv^{ompi} ≤ Adv^{ompr}` | tight (SUF step: `q_H` signing queries) | §5.1 |
| T2 | A-OMPI ⇐ GPI + OW, or ⇐ GPI + UOV problem | `q_T` | §5.2 |
| T3 | EUF-CMA of the **specified** salted UOV ⇐ GPI + UOV problem. (The spec's own proof is for salt-UOV, a different signer.) | `q_H + 1` on UOV, none on GPI | §5.3 |
| T4 | **Lemma U is incorrect as stated**: CT-UF with an arbitrary-target signing oracle is not shown to follow from OMPR. CT-UF^open ⇐ OMPR, tightly; CT-UF^open ⇐ GPI + OW | tight / `q_π` | §5.4 |
| T5 | With R1, Ratatouille balance ⇐ EUF-CMA of salted UOV with `H = Tag`, which ⇐ GPI + UOV (or ⇐ UOV alone with salt-UOV signing) | `q_K + 1` | §5.5 |
| T6 | **PomFRIT ⇔ OMPR**: an OMPR breaker *is* a PomFRIT one-more forger. So OMPR ≤ PomFRIT ≤ OMPR⊕17 | tight | §5.6 |
| P7 | OMPR is not expected to reduce to the UOV problem (meta-reduction sketch); determinism doesn't change that | — | §5.7 |
| P8 | OMPR⊕τ ⇐ OMPR loses `τ^{q+1}`. Every *simple-embedding* reduction loses that much against some adversary. In a generic model the two assumptions have the same bound. For PomFRIT's tree shapes, U1's additive `Q₃·2^{−71}` (≈ `2^{−7}` at `2^{64}` queries) is unavoidable for simple-embedding reductions | — | §6 |

**Assessment** (§7).
- State all three protocols under **one** assumption: **A-OMPR**, i.e. Def. 3.1 instantiated with
  uov-Ip and `derive_preimage`, per key. It is *necessary* for PomFRIT (T6) and suffices tightly
  for Moussaka (via CT-UF^open) and Ratatouille (via A-OMPI).
- Secondary statements: Moussaka and Ratatouille also follow, with loss `q`, from GPI plus the UOV
  problem (or OW). Ratatouille also follows from SUF-CMA of the specified scheme.

**Recommendations** (§8).
- Documentation:
  - fix Moussaka's Lemma U by using CT-UF^open (B₂ already has the openings);
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
     cryptanalysis like any new assumption.
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
11. **CT-UF^open_K** (new). This is CT-UF_K, except that `A` must also output, for every target `t`
    it queried to `Sign_k`, an opening `x_t ∈ D_Com` with `Com(x_t) = t`. Otherwise it loses.
12. **UF-Tag** (`ratatouille.md` §2.3). The oracle takes `(c, x)` and returns `D(Tag(c, x))`.

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

**(c) A-OMPI ≤ OMPR, tightly:** `Adv^{ompi}(q_T, Q) ≤ Adv^{ompr}(q_T, Q)`.
- Forward the index queries as `D(t_i)`.
- The `Q` answers plus the forgery are `Q+1` preimages of distinct indices. ∎

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
sandwiched:

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
  That is a different, unstudied assumption.

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

    Adv^{bal} ≤ ε_ext + Adv^{euf}_{UOV[Tag]}(B; q_K, N_I + N_S) + ε_bind^K + q_K·(2^{−287} + 2^{−351}).

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

## 6. Proposition 8: OMPR versus 17-shift OMPR

**(a) Guessing.** `Adv^{ompr⊕τ}(N, q) ≤ τ^{q+1}·Adv^{ompr}(N, q)`.
- On request `k`, guess `a_k ← [m_k]` and answer `h_k := t_k ⊕ δ_{k,a_k}`. This is uniform, and
  the view doesn't depend on the guesses.
- The output is usable iff all `q+1` forgeries used the guessed shift.
- For `q = 0` the loss is just `τ`, so OMPR⊕τ(N, 0) ≤ `τN·Adv^{uov}`. For τ = 17, the loss is
  `≥ 2^{4(q+1)}` (Lean `guess_loss`).

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
- There is no separation either, and the generic bound (c) is the same.
- Keep U1, which is proved and loses at most `2^{−7}` at `2^{64}` queries, as the main statement.
  Cite U2 under the explicitly stronger OMPR⊕17.
- The cleanest way out is a protocol change, §8 C2. It makes the 17-shift question moot.

## 7. Assessment: one common assumption?

Yes: **A-OMPR, i.e. OMPR(n, q) of Def. 3.1 for uov-Ip with `SPre = derive_preimage`, per key.**

| Protocol | From A-OMPR | Loss | Best alternative without OMPR |
|---|---|---|---|
| PomFRIT | U1 (`pomfrit.md`); **and necessary** (T6) | `(Q₃+ℓ+1)·2^{−71}` | none: equivalent to OMPR; U2 needs OMPR⊕17 |
| Moussaka | CT-UF^open ⇐ OMPR (T4), in Thm 1 | tight, ×K | GPI + OW, loss `q_π`, ×K (T4) |
| Ratatouille | A-OMPI ≤ OMPR (T1c), in Lemma 2.1 and Thm 1 | tight | spec-SUF-CMA (T1e); GPI + OW (T2), loss `q_T` |

Reasons:
1. PomFRIT forces it (T6).
2. It covers the other two tightly.
3. It is the paper's published assumption (Def. 3.1) instantiated with the actual sampler.
4. A single assumption makes the key-separation rule uniform. Each key's oracle answers count in
   that key's one-more budget, so **no key may serve two protocols**. That is `pomfrit.md` F5 and
   `ratatouille.md` F1. A PomFRIT key signs arbitrary targets, Ratatouille's and Moussaka's
   included.

Each protocol note should state its UOV hypothesis as "A-OMPR (`uov-assumptions.md` §3, item 7)".
- For Moussaka, replace CT-UF by CT-UF^open, with the repaired Lemma U.
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
  samples?
- **OMPR ⇒ OMPR⊕17** (§6), in either direction.
- **CT-UF with arbitrary targets** versus OMPR: is the "free non-challenge calls" variant implied?
- Turn the **meta-reduction** (§5.7) into a theorem, with a precise proviso.
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

The probabilistic steps (Lemma D, the hybrid games, the ideal-permutation bookkeeping) are on paper.

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
