# Plan: an executable Lean VOLEitH verifier

Goal (D): a Lean function `verify : Relation → instance → proof → Bool` that accepts the real proofs
the C++ produces (the KAT files `tests/ihat/ihat_kat.txt`, `tests/ratatouille/
act_kat.txt`, PomFRIT's `tests/pomfrit/pomfrit_kat.txt`) and rejects mutated ones. It should
be assembled from pieces that are the executable counterparts of the Lean models the proofs use
(`Seed/Commitments.lean`, `Seed/KOS.lean`, `Seed/QuickSilver.lean`, the `Arith/*` constraint
generators), so that each model can later be connected to the verifier by a theorem.

All `file:line` citations are relative to the repository root. `fao/` stands for
`subprojects/faest-arch-opt/` (v3.0.0 plus patches 0001-0004 of `main`).

## Parameters

Every relation uses FAEST-EM-128f's VOLEitH parameters (e.g. `src/moussaka/issue.hpp:133-136`):
`s128`, τ = 17, AES-CTR PRGs, `leaf_hash::aes_ctr`, `W_GRIND = 8` (so `delta_bits` = 120), one-tree
BAVC with `T_OPEN = 105`, CRT VOLE masks, v3 hash inputs. Derived (`fao/constants.hpp:305-470`):
k₀ = 8, k₁..k₁₆ = 7, L = 2304 leaves, 4607 tree nodes; `VOLE_WIDTH_SHIFT = 3` on both AVX2 and
aarch64; `N_MASK = (QS_DEGREE − 1) + 4`; `N_MULT = 312` (generated table
`build/subprojects/faest-arch-opt/crt_constants_128f.{hpp,json}`).

Proof layout (`fao/faest_sig.hpp:39-66`), e.g. Moussaka issuance (witness 2048 bits, degree 9,
7272 bytes): corrections c₁..c₁₆ (16 × 256) · c_mult (12 × 39) · ũ = VOLEHash (64) · d (256) ·
QuickSilver ã (8 × 16) · opening (17 × 32 + 105 × 16 = 2224) · Δ (16) · iv_pre (16) · ctr (4).

## Pipeline as implemented

`voleith_verify` (`src/voleith.hpp:488-494`) = `voleith_vole_reconstruct` (`:354-409`) then
`voleith_verify_commit` (`:420-481`). Hashes are `hash_state` = SHAKE128 here (`fao/hash.hpp:21-58`);
the domain byte is appended last. The Lean verifier takes them as a record `Hs : Hashes`, one
function per domain (milestone 9).

| # | Step | Code | Lean model of the math | Primitives | Size |
|---|---|---|---|---|---|
| 0 | `check_format`: top 8 bits of Δ zero; c_mult rows zero-padded | `fao/faest_sig.hpp:126-152`, `src/voleith.hpp:363` | — | — | trivial |
| 1 | `mu = H(inst ‖ DST ‖ 8)`; `iv = H(iv_pre ‖ mu ‖ 4)` (16 B) | `src/voleith.hpp:107-123`, `:371-377` | `Protocols/DomainSeparation.lean`, `Seed/Commitments.lean` (domains) | SHAKE128 | 2 hashes |
| 2 | BAVC reconstruction: parse Δ into Δᵢ, place opened seeds (walk `L−2..0`), reject on overflow or nonzero padding, expand the GGM tree (node n's children = `PRG(node, iv, tweak n)`), leaf commitment = `PRG(leaf, iv, tweak i + L − 1)`, 2 blocks | `fao/vector_com.inc:855-979`, tree `:663-727`, positions `:628-641`, leaf hash `:1069-1085` | `Seed/Commitments.lean` (`ctrInput`, role disjointness); L1/L2 of `docs/extraction/` | AES-128, AES-CTR PRG | ≈ 4.6k key schedules, 9.2k blocks |
| 3 | `vole_commit_check = H(H(c_0‖1) ‖ … ‖ H(c_16‖1) ‖ 1)` over the leaf commitments | `fao/vole_commit.inc:28-80` | L1 (binding) | SHAKE128 | 74 KB hashed |
| 4 | ConvertToVOLE per small VOLE i (tweak `2³¹ + i`): `q` columns `= Σ_x x_b · PRG(r_{x⊕Δᵢ})` (Gray-code accumulation), then `q_col += Δ_{i,b} · c_i` on the first `VOLE_CORRECTION_BYTES`; columns of the 8 zero Δ bits cleared | `fao/vole_commit.inc:137-191`, `fao/small_vole.inc:106-260` | `Extraction/*` (label/VOLE correlations), `SeedExtraction.lean` | AES-CTR PRG (`VOLE_COL_BLOCKS` blocks per leaf) | 2304 leaves × ~18 blocks |
| 5 | CRT VOLE: hash G-lifted q prefix per gate (`H(iv ‖ e ‖ L0_e ‖ 5)`, 4-byte outputs), CRT-lift q columns (W_CRT), transpose to rows, `q_mask = W_TREE·r̃(q) + W_GATE·(hashes ⊕ γ∧c_mult)`; `Δ ← crt_lift_delta(Δ)` | `fao/vole_commit.inc:337-432`, `:500-549`, `:614-651`; lifts `fao/crt_vole_helpers.inc:225-345`, `:583-620`; tables `fao/tools/gen_crt_tables.py` | `ZK/Labels.lean`, `ZK/Masking.lean` (labels/masks), `Seed/KOS.lean` (`e` = CRT lift) | SHAKE128 (312 short hashes), GF(2) matrix-vector products, Barrett mod Mᵢ | 312 × 128 and 120 × 128 bit matrices |
| 6 | `chal1 = H(mu ‖ check ‖ c₁..c₁₆ ‖ c_mult ‖ iv_pre ‖ binder₁ ‖ 9)` (8·16+8 B) | `src/voleith.hpp:396-405` | L0 | SHAKE128 | — |
| 7 | KOS / VOLEHash: `h = VOLEHash(q rows, q_mask) + Δ·ũ`, hashed into chal2 (no equality test: the check is implicit via chal2→chal3) | `fao/kos_vole_check.hpp:82-176`, `:204-217`; `fao/universal_hash.hpp:12-150` | `Seed/KOS.lean` (`voleHashP`, `kosValue`) | GF(2¹²⁸) (`Arith/GF.lean`), 64-bit-key hash | 2048 rows × 5 Horner steps |
| 8 | `chal2 = H(chal1 ‖ ũ ‖ h ‖ [mu] ‖ binder₂ ‖ d ‖ 10)` (3·16+8 B); `q_j += d_j·Δ` | `src/voleith.hpp:435-459` | L3/L4 interface | SHAKE128 | — |
| 9 | QuickSilver verifier: evaluate the relation's constraints on MACs `q_j` (degree raising by Δ powers), ZKHash with `chall₂ = (r₀, r₁, s, t)`, mask `q_mask[0] + Σ (ãᵢ + q_mask[i])Δⁱ + ã_{d−1}Δ^{d−1}` → `qs_check` | `fao/quicksilver.hpp:307-378` (helpers), `:420-432`, `:642-659`; `Relation::constraints` (e.g. `src/moussaka/issue.hpp:170-190`) | `Seed/QuickSilver.lean` (`QSExpr`, `zkHash_eq_code`), `Arith/*` generators (`Expr F` evaluated at verifier MACs) | GF(2¹²⁸) | ~10⁴–10⁵ constraints |
| 10 | `chal3 = H(chal2 ‖ qs_check ‖ ã ‖ ctr ‖ 11)`; accept iff chal3 = Δ (this is also the grinding check: Δ's top 8 bits were checked in step 0) | `src/voleith.hpp:470-480`; prover side `fao/vector_com.inc:981-1066` | `ZK/Grinding.lean` | SHAKE128 | — |

Notes.
* **Leaf order.** faest-arch-opt stores the verifier's leaves permuted (`vole_permute_key_index_inv`
  of `j ⊕ Δᵢ`, `fao/vole_key_index_permutation.hpp`, Gray code within chunks of 8) to make step 4
  cheap. The Lean model works in spec order (leaf `j` of vector `i`, hidden leaf zero) and computes
  step 4 as the plain sum; the dumper undoes the permutation before writing.
* **Dedicated label rows (patch 0005, branch `voleith-label-rows` only).** With
  `CRT_DEDICATED_LABEL_ROWS`, `VOLE_CORRECTION_ROWS` grows by 128 (rows `ℓ..ℓ+127` after the
  witness feed the gate labels in step 5 instead of witness rows `0..127`), each correction cᵢ is 16
  bytes longer (+256 B per proof), the mask rows move down by 128, step 7's hashed rows include the
  128 label rows, and step 8 applies `d` only to the `ℓ` witness rows. In Lean this is the one
  switch `Params.labelRows` (derived: `labelRowOffset`, `correctionRows`, `correctionBytes`); the
  relation constructors of `Relations.lean` take `(labelRows := …)`. The KAT files differ between
  the branches (PomFRIT's `pomfrit_kat.txt` exists only on this branch and must be regenerated with
  `gen_pomfrit_kat` in a label-rows build).
* **Spec vs. code risks to watch:** chal1/chal2 binders (empty for all KATs except where the
  protocol passes one), delayed-instance `mu` in chal2 (PomFRIT redemption, `src/voleith.hpp:445-
  448`), the 64-bit-key hashes (`uhasher_gfsecpar_64`), `load_dup` vs `load` of challenges.

## Primitives (status)

| Primitive | Lean | Check |
|---|---|---|
| SHAKE128/256 | `Spec/SHAKE.lean` (shared with the protocol specs) | FIPS 202 `#guard`s; `verifier_vectors`: 17 `hash_state` records (rate boundaries, 200-byte squeezes, an `x4` lane) |
| AES-128, `aes_ctr_prg<s128>` | `Verifier/AES.lean` | FIPS 197 A.1/B/C.1 `#guard`s; `verifier_vectors`: 4 AES (round keys + ct) and 3 PRG records (lane wrap-around of counter and tweak) |
| GF(2¹²⁸) | `Arith/GF.lean` | already cross-checked (`arith_vectors`) |
| One-tree BAVC + `hash_hashed_leaves` | `Verifier/BAVC.lean` | `verifier_vectors`: whole tree, leaves, commitments, check for a fixed seed; reconstruction at Δ; the first Moussaka KAT proof's opening (leaves, commitments, `vole_commit_check`); mutated openings |
| CRT tables (Mᵢ, W_CRT, W_TREE, W_GATE, G) | `Verifier/CrtData.lean` (generated matrices) + `Verifier/CrtGen.lean`, `Verifier/CrtSearch.lean` (port of `vole_mult_tables.py`) | `W_crt`, `M_tree` recomputed from the moduli; bilinear identity checked on all basis pairs; F, G, W_tree, W_gate regenerated exactly; row tables equal the dumped C++ ones |
| Proof layout, `check_format`, `mu`, `iv`, `chal1` | `Verifier/Proof.lean` | `verifier_vectors`, 5 relations |
| VOLE check, QuickSilver, full verifier, relations | `Verifier/KOS.lean`, `QuickSilver.lean`, `Verify.lean`, `Relations.lean`, `Kats.lean` | all 18 KAT proofs accepted, 51 mutations rejected |
| pqov `expand_pk` (AES-128-CTR) | `Verifier/Relations.lean` `UovPk.ofCompressed`, `Verifier/Keygen.lean` `publicInputs` | equals the C++ expanded `test` key |
| pqov key generation (`generate_keypair_pkc`) | `Verifier/Keygen.lean` `compressedPk` | equals all 64 compressed keys of `verifier_keys.txt` |
| ConvertToVOLE, CRT VOLE (gate hashes, row lift, r̃, `q_mask`, lifted Δ) | `Verifier/VOLE.lean` | `verifier_vectors`, 5 relations |

AES also unblocks the protocol specs: with pqov key generation (`Verifier/Keygen.lean`) and
`expand_pk`, `lake exe spec_kats` builds every Moussaka Anchor key from its `anchor_sk` and checks
the redemption requests with `finalizeRedeem`, the abstract verifier instantiated by the Lean
verifier, so the digests of non-issuer Anchors are checked too (and a swap of two is rejected).

## Debug dumps (`tests/voleith/dump_verifier_vectors.cpp` → `lean/vectors/verifier_*.txt`)

Format: as `tests/arith/dump_arith_vectors.cpp` (`record GROUP NAME`, `KEY HEX` lines, `end`); the
dumper's header documents every key. Byte strings are the C++'s memory layout except leaves (spec
order). Currently:
* `verifier_prims.txt` — AES, PRG, SHAKE (see above).
* `verifier_bavc.txt` — `bavc commit` (seed, iv, tree, leaves, hashed_leaves, check) and `bavc open`
  (delta, opening, verifier leaves/commitments, check).
* `verifier_kat.txt` — `crt tables` (Mᵢ, M_TREE, row tables of W_CRT, W_TREE, W_GATE, G), then one
  `kat` record per relation: Moussaka issuance (KAT record 0) and redemption (record 1, three
  anchors), Ratatouille issuance and first spend (record 0), PomFRIT redemption (signature 1;
  delayed instance, binders `refresher_com`/`refresher`). Each has the parameters, `dst`,
  `inst_enc` (the bytes `hash_instance` absorbs; the dumper checks `H(inst_enc ‖ DST ‖ 8)` against
  `hash_mu`), binders, the proof, and every intermediate: `mu`, `mu1`, `iv`, leaves,
  hashed_leaves, `q_columns`, `vole_commit_check`, `gate_hashes`, `r_tilde`, `q_rows`, `q_mask`,
  `delta_lifted`, `chal1`, `chal2`, `qs_check`, `delta_check`, `accept`. The dumper re-runs the
  verifier's steps itself and asserts that `delta_check` = Δ and that the real verifier accepts.

Label-rows vectors (milestone 7): in a worktree at `formal-proofs-wip` with `d5def9c`
cherry-picked (the dumper and `gen_pomfrit_kat` live only on this branch), build
`tests/dump_verifier_vectors` and `tests/gen_pomfrit_kat`, regenerate
`tests/pomfrit/pomfrit_kat.txt` there, dump into a fresh directory (optionally copy
`lean/vectors/uov_keys.txt` next to it for the expanded-key cross-check), and run `lake exe verifier_vectors DIR WORKTREE/tests`; the layout is read off
`correction_rows`. The dumper applies `d` to the `WITNESS_BITS` rows only (as `voleith.hpp` does
on both branches). The relation-specific
`inst_enc` is taken from the dump; building it in Lean from the instance (via the `Spec/*` modules)
is part of milestone 6.

## Milestones

1. **Done:** SHAKE, AES, AES-CTR PRG, one-tree BAVC reconstruction + `vole_commit_check`, matched on
   real KAT proofs. `lake exe verifier_vectors` runs milestones 1-4 on all records in about 5 s.
2. **Done:** chal1 (steps 0, 1, 3, 6): `Verifier/Proof.lean` (parameters, layout, `check_format`,
   `mu`, `iv`, `chal1`); matches all five relations' KAT proofs. Mutation tests: a flipped byte in
   the corrections, `c_mult`, the opening or `iv_pre` changes `chal1` or is rejected; a grinding
   bit of Δ fails `check_format`.
3. **Done:** ConvertToVOLE (step 4): `Verifier/VOLE.lean` `convertToVole`, the spec-order sum (no
   Gray code); matches `q_columns` for all five relations. 110-470 ms per proof (2304 leaves ×
   12-54 AES blocks).
4. **Done:** CRT VOLE (step 5): `Verifier/VOLE.lean` `crtReconstruct` (gate hashes, row lift by
   W_CRT, r̃ mod Mᵢ, W_TREE/W_GATE/γ∧c_mult, lifted Δ); matches `gate_hashes`, `r_tilde`,
   `q_rows`, `q_mask`, `delta_lifted` for all five relations, 30-60 ms per proof. The tables still
   come from the dump.
5. **Done:** KOS + chal2 (steps 7-8): `Verifier/KOS.lean` (`voleHashReceiver`: Horner VOLEHash
   over `Arith/GF.lean`'s `GF128`, `chal2`); matches `chal2` for all five relations, 12-60 ms.
   Stated and proved in milestone 8 (`Bridge/KOS.lean`, `map_voleHashReceiver`).
6. **Done:** QuickSilver + full accept (steps 9-10): `Verifier/QuickSilver.lean` (constraint keys as
   `Δ^d · f_k(q/Δ)`, so the `Arith/*` sharing evaluators run unchanged at `x_j = q_j Δ⁻¹`; ZKHash,
   mask, `chal3`), `Verifier/Verify.lean` (the whole verifier for a `Statement`),
   `Verifier/Relations.lean` (the five relations; instance encodings from `Spec.Moussaka`
   `IssueInstance/RedeemInstance.encode` and `Spec.PomFRIT.hashToTarget`, Ratatouille's written out
   since `Spec/Ratatouille.lean` has none; UOV keys expanded from compressed keys with
   `Verifier/AES.lean`, pqov's `expand_pk`), `Verifier/Kats.lean`. `lake exe verifier_vectors`
   accepts all 18 KAT proofs (6 Moussaka, 9 Ratatouille, 3 PomFRIT) and rejects 51 mutations
   (a byte flipped in each proof field of the first proof of each relation; a changed instance;
   PomFRIT's refresher). Time ≈ 25 s (≈ 5 min before (c) below); Moussaka/Ratatouille issuance
   ≈ 0.12 s, the 64-anchor redemption ≈ 0.8 s.
   CRT tables: `Verifier/CrtData.lean` holds faest-arch-opt's generated matrices
   (`vole_mult_tables.py --preset 128f`); `Verifier/CrtGen.lean` recomputes `W_crt` and `M_tree`
   from the moduli, checks the defining bilinear identity of `F`, `G`, `W_tree`, `W_gate` on all
   `128 · 120` basis pairs, and builds the row tables (equal to the C++'s); the verifier no
   longer reads tables from the dump.
   Done since: (a) pqov key generation (`Verifier/Keygen.lean`: `generate_keypair_pkc` of
   uov-Ip-pkc, `SHAKE256(sk_seed) = pk_seed ‖ O`, `P1 ‖ P2` from the AES-128-CTR public-input PRG,
   `calculate_F2_P3`'s `P3 = UT(M + Mᵀ)` with `M = Oᵀ(P1·O + P2)`, table-driven GF(256) loops on
   `ByteArray`s, ≈ 0.08 s per key, 5 s for the 64 KAT keys); `Verifier/Kats.lean` and
   `Spec/Kats.lean` derive every UOV key from the KATs' compact secret keys, and compare with
   `verifier_keys.txt` (64 of 64 compressed keys equal) and `uov_keys.txt` only when present;
   (b) `Verifier/CrtSearch.lean` ports `vole_mult_tables.py` for `128f` (tree moduli, the cost
   search with the script's tie-breaking, the bilinear algorithms, interpolation by the same
   elimination, `build_tables`, `prune`); its `F`, `G`, `W_tree`, `W_gate` (25 places, 312
   gates) equal `CrtData`'s, checked by `verifier_vectors`. `CrtData` stays the verifier's source
   (the regenerated tables are compared with it, not substituted).
   (c) speed (`verifier_vectors` 5 min 20 s → 26 s, `spec_kats` 3.5 min → 16 s, same results).
   The UOV constraints went through `Expr` trees: per monomial, `combineVec` (45 · 9 products) and
   the 8-product byte loads were recomputed, ≈ 2.3 s per key. `Verifier/UovEval.lean` evaluates
   `qs_eval_combined_public_map`'s loop on values (`publicMapValue`, equal to `Expr.eval` of
   `evalCombinedPublicMap` for any `+ *`), with the coefficient of a monomial read from the table
   `l_k·ι(a)` (`combTab`, 45 lookups) and the 119 loaded bytes computed once per proof and shared
   by all Anchors (≈ 10 ms per key); `moussakaRedeemValues`, `ratatouilleSpendValues`,
   `pomfritRedeemValues` replace only the UOV term and are proved equal to the `Arith/*`
   evaluators (`*_eq`), which `Bridge/Relations.lean`'s `*_values` now go through, so the bridge
   theorems are about what runs. `GF128.mul` is compiled as `mulFast` (`@[csimp]
   mul_eq_mulFast`, `Arith/GF.lean`): the same shift-and-add on four unboxed `UInt64`s with the
   bit read by a mask, proved equal by induction, ≈ 0.3 µs instead of 1.7 µs (KOS 12-60 ms →
   2-11 ms). Outside QuickSilver: AES `encrypt` uses the four round tables (ConvertToVOLE
   110-490 ms → 31-121 ms per proof; checked by the FIPS `#guard`s and the vectors), and
   `CrtGen.dot` (the identity check, run at start-up) XORs 64-bit limbs instead of clearing bits
   one by one (≈ 22 s → 5 s).
7. **Done:** label-rows variant behind `Params.labelRows` (`Proof.lean`: correction rows/bytes and
   label-row offset; `VOLE.lean`: gate labels from rows `o … o + 127` of each column, lifted rows
   and mask rows relative to `correctionRows`; `Relations.lean`: `(labelRows := …)` on every
   constructor, PomFRIT's `hash_to_target` reads `ũ` and `d` at the layout's offsets
   (`pomfritTarget`; `Spec.PomFRIT` hard-codes `main`'s, checked by a `#guard`); `KOS.lean` and
   `QuickSilver.lean` needed no change). On vectors and KATs from a `voleith-label-rows` build: all
   intermediate values of the five dumped proofs match, all 18 KAT proofs are accepted and 51
   mutations rejected, ≈ 26 s. `main`'s checks are unchanged.
8. **Partly done: bridges** (`Verifier/Bridge/*`, proofs, no tests; no `sorry`/`axiom`/
   `native_decide`):
   * `CtrInput.lean`: `lanes (ctrBlock iv c t) = Commitments.ctrInput (lanes iv) c t`;
     `prgExpanded` is the concatenation of the encrypted `ctrBlock iv (c + j) t`; the tweaks of
     `BAVC.children`, `BAVC.leafCom` and `convertToVole` lie in `Commitments.tweaks` of their
     roles, so `ctrBlock_ne_of_roles` (from `role_inputs_ne`) separates them. No assumptions.
   * `Field.lean`: `GFEmbedding F`, an injective map `GF128 → F` into a field preserving `1`, `+`,
     `*`. One exists with `|F| = 2¹²⁸` (`Concrete.lean`, below). For any such `φ`, the executable
     `horner` is `Seed.horner`, `hornerPoly`'s evaluation and the C++ blocked hash
     (`Seed.blockedHash`, so `zkHash_eq_code` applies), `gfPow` is the power, `gfInv` the inverse.
   * `KOS.lean`: `φ` of `voleHashReceiver` is `Seed.kosValue` (challenge parsed from `chal1`, `Q`
     the `ℓ' + d − 1` hashed rows, `D` the four direct masks, `e(Δ) = φ Δ_lifted`), pointwise in Δ.
   * `QuickSilver.lean`: `mac_constraintQS` (the MAC of `constraintQS d e` is `Δ^d·e(m/Δ)`, the
     executable's shortcut), `qsCheck_zkCoeff`, `map_constraintKeys`, `map_qsCheck`
     (`φ(check_V) + z = EndToEnd.qsCheck … + (Seed.maskPoly d a b ã z).eval Δ` when the mask MACs are
     `a_i + b_i Δ`), `hacc_of_qsCheck` (char 2, `z = φ(check_V)`). Hypothesis `hvals`, the
     relation's `GF128` evaluator is `System.values cs` transported along `φ`: proved per relation
     in `Relations.lean` (below).
   * `Accept.lean`: `accept_iff` (the verifier unfolded into its step functions), `map_correctedKeys`
     (the QuickSilver inputs are `EndToEnd.macs`' `Q_j + d_j Δ`, zero beyond `ℓ`, for both layouts),
     `accept_hacc` (acceptance ⇒ `φ Δ_lifted ≠ 0`, `chal3 = Δ`, and `EndToEnd`'s accepting equation
     `qsCheck + R(Δ) = 0` at this transcript, with `R = maskPoly d (φ ∘ q_mask) 0 ã (φ check_V)`).
   * `Concrete.lean`: `gfK : GFEmbedding GF128.K`, `K = GF(2)[X]/(X¹²⁸ + X⁷ + X² + X + 1)`, from
     `Arith/GFField.lean` (kernel-checked: the modulus is irreducible, by Mathlib's degree criterion
     with `X^(2¹²⁸) = X` and an inverse of `X^(2⁶⁴) + X` computed in `GF128`; evaluation at the root
     is multiplicative and bijective, `GF128 ≃+* K`, `Field GF128`). `accept_hacc_K`,
     `map_constraintKeys_K`, `map_gfInv_K`, `map_voleHashReceiver_K` (`T = univ`) restate the
     theorems at `gfK` with `|F| = 2¹²⁸` and characteristic 2 proved.
   * `Relations.lean`: `GF128` is itself a field (`GF128.instField`, `CharP GF128 2`), so
     `gfId : GFEmbedding GF128` and `accept_hacc_GF` (`hvals` an equation over `GF128`). Per
     relation, the statement's evaluator is `System.values` of the `Arith/*` system at
     `β := beta`, `K := GF256` and the verifier's instance data (`*_values`: the `Arith/*`
     `issueValues_eq`/`redeemValues_eq`/`issueSystem_values`/`spendSystem_values`, `betaFast_eq`;
     the cached UOV coefficients `ofArr (combinationOf …)` are the system's `l`), and the degree
     bounds are `EndToEnd/Degree`'s. Hence `moussakaIssue_accept`, `moussakaRedeem_accept`,
     `ratatouilleIssue_accept`, `ratatouilleSpend_accept`, `pomfritRedeem_accept`,
     `pomfritVerify_accept` (also the refresher check): acceptance gives `EndToEnd`'s accepting
     equation for the relation's system over GF(2¹²⁸), no hypotheses. `values_map` gives `hvals`
     at any other `φ` (e.g. `gfK`) with the system mapped by `Expr.map`. The systems' soundness at
     GF(2¹²⁸) and the `*_extract` theorems there are `Arith/ConcreteField.lean` and
     `EndToEnd/Concrete.lean`.
   * Across Δ (`Lift.lean`, `Columns.lean`, `Chain.lean`, `ChainRelations.lean`). Executable
     refactor (checked: all intermediate values of the five dumped proofs, 18 accepted / 51
     rejected): `convertToVoleAt`/`crtReconstructAt` take `Δ` as bits (`BAVC.deltaBit`, `c < 120`)
     and the commitments as arguments; `treeColumns` computes each column as one fold over the
     PRG outputs (`prgOuts`, hidden leaf never read); `xorWords` is a `mapIdx`.
     - `Lift.lean`: `Blocks` (`Δ_i ∈ F₂^{k_i}`), `blocksOf`/`dbitOf`, `sum_range_120` (the 120 bit
       positions are the `p_i + b`); `lift T` (the CRT lift as `Blocks →+ GF128`), `rowMul_lift`
       (`crt_lift_delta` is `lift T (blocksOf dbit)`), `blockLift_lift`; `lift_injective` for any
       tables with `liftInvOk` (an offline left inverse of `W_CRT`, 120 linear forms), and
       `liftInvOk_tables` (`decide +kernel`, ≈ 30 s).
     - `Columns.lean`: `treeColumns_affine` (column `p_i + b` is `V_{i,b} + dI_b · u^{(i)}`,
       `u^{(i)} = c_i + Σ_j R_j` = `smallVoleU`, for any `dI`), `testBit_hiddenIndex`,
       `resp_row` (lifted row `r` is `C_r + Σ_i u^{(i)}_r · e_i(Δ_i)`: `Claim4Hyp.tree_form`);
       `convertToVoleAt_congr_key` and `crtReconstruct_eq_respAt` (a run whose opening
       reconstructs the committed keys off the hidden leaves is the committed response `respAt`).
     - `Chain.lean`: `Chain` (reference proof for `c_i`, `c_mult`, `iv_pre`, `ũ`, `d`, `ã`, `ctr`;
       committed keys; `iv` and the gate hash `h5`; `chal1`, `h_V`, `z`; `chal2` and the constraint
       evaluator `vals` as fields, equal to the verifier's (for hashes `Hs`) by hypotheses of
       `onChain_of_accept`), `OnChain` (the committed responses
       at `Δ'` give `Δ_lifted ≠ 0`, the chain's `h_V` and `z`), `vole_kosValue` (`KOSGood`'s
       `Q`, `D` are the committed hashed rows/masks, `X` = blocks), `chain_kos_affine`,
       `chain_tree_form`, `chain_claim4` (`Claim4Hyp` and the accepting equation on all of `A`
       with one `R = maskPoly d a b ã z`), `onChain_of_accept` (an accepted proof of the chain is
       on the chain at its `Δ`, and `Δ = chal3`).
     - `ChainRelations.lean`: `moussakaIssue_extract_chain`, `moussakaRedeem_extract_chain`,
       `ratatouilleIssue_extract_chain`, `ratatouilleSpend_extract_chain`,
       `pomfritRedeem_extract_chain`.
   Still open (all probabilistic or random-oracle, kept as hypotheses): `KOSGood` for `chal1`
   (L3), `IsFixed` for the dead-leaf trees (L2), `hQS`/`hcomb` for the slope of the witness rows
   on `A` (guarded by `|A| ≥ 2`, where it is L4 §5's canonical slope), `hδ`/`hclaim1` and the
   binding of the leaf commitments (`hbind`, and the chain identification of `chal1`, `h_V`, `z`
   in `onChain_of_accept`) (L1). `pomfritVerify`'s refresher check is not part of the chain
   theorem (its proof part is `pomfritRedeem`). `Prob/` (`docs/probabilistic-plan.md`, phase A)
   discharges `KOSGood`, `hQS`/`hcomb` and `hδ` for uniform independent `chal1`, `chal2`, `l`
   (`*_chain_prob`), and `ROM/` (phase B) runs the verifier against the random oracle
   (milestone 9).
9. **Done: the hash record** (`Verifier/Hashes.lean`). The verifier takes `Hs : Hashes`, one
   function `Hs.hash k` per domain `k : Kind` of `docs/extraction/L0-L2-commitments.md` §2.1 (the
   argument is the whole SHAKE input, domain byte included; `Kind.outLen` the output length);
   `Hashes.shake` is SHAKE128 in every domain. Changed: `mu`, `ivOf`, `chal1`, `chal2`, `chal3`,
   `crtReconstruct` take `Hs`; `BAVC.check`, `gateHashes`, `crtReconstructAt` take the one function
   they use (`H₁`, `H₅`); the hash inputs are definitions of their own (`chal1Input`, `chal2Input`,
   `chal3Input`, `BAVC.leafHashInputs`/`comInput`, `gateInputs`; `crtReconstructWith` takes the
   gate hashes); the UOV combination moved from the statement to the verifier (`Statement.comb =
   some (M, dst)`, `Statement.combBytes`; `values` reads the combination bytes, decoded by
   `combinationOf`); `Transcript.iv`. Hashes outside L0 stay SHAKE: `UovPk`'s digest and
   expansion, PomFRIT's `hash_to_target` and refresher commitment. The runners pass
   `Hashes.shake` and give the same output as before on both layouts (18 accepted, 51 rejected;
   `spec_kats`, `arith_vectors` unchanged). The bridge theorems are generic in `Hs`
   (`accept_iff`, `accept_hacc`, `AcceptEq`, `*_accept`, `crtReconstruct_eq_respAt`,
   `onChain_of_accept`); none mentions SHAKE, so no `Hashes.shake` corollaries are needed.
   `ROM/Verifier.lean` runs the same verifier with every hash a random-oracle query
   (`verifyQ`, equal to `verify (Hashes.ofTable g)` against a complete table).
10. **Done: the prover** (`Verifier/Prover.lean`, `Verifier/ProverKats.lean`,
   `Verifier/Bridge/Prover.lean`; `lake exe prover_vectors`, root `Verifier/ProverMain.lean`).
   An executable Lean model of `voleith_vole_gen` + `voleith_prove_commit`
   (`src/voleith.hpp:146-322`) that reproduces the C++ proofs byte for byte, built from the
   verifier's own step functions:
   * Step 1 (`Prover.voleGen`): `(seed, iv_pre) = H₃(w_prefix ‖ mu₁ ‖ rho ‖ 3)`, `iv`;
     `BAVC.commit`; the prover's VOLE in spec order: `u^{(i)} = Σ_j R_j` (`smallVoleUWords`), the
     tags `v` = the verifier's `convertToVoleAt` at `Δ = 0` (`senderColumns`; the hidden leaf is
     leaf 0, which contributes nothing), `c_i = u^{(0)} ⊕ u^{(i)}` on the `ℓ'` corrected rows; CRT
     sender (`crt_vole_commit`): labels `L0 = G·v` and `L1 = L0 ⊕ u[o..o+128)` (`gateInputsOff`,
     `o` the label-row offset), their `H₅` hashes `h⁰`, `h¹`; lifted tags and `ṽ_mask` = the
     verifier's `crtReconstructWith h⁰` at `Δ = 0`; `u_mask = W_CRT·u_low ⊕ M_tree·u_hi`
     (`u_hi` = `PRG(seed, iv, 2³¹ − 1)`, `uMaskOf`); `c_mult` bit `e` of mask `m` = bit `m` of
     `h⁰_e ⊕ h¹_e` plus `⟨F[e], u_mask[m]⟩` (`cMultOf`); `chal1` as the verifier; `ũ` and `h_V` =
     the verifier's `voleHashReceiver` at `Δ' = 0` on `(u, u_mask)` and `(v, ṽ_mask)`; `d` on the
     prefix.
   * Step 2 (`Prover.proveCommit`): `d`, `chal2` as the verifier; QuickSilver (`qsProve`): the
     verifier's check value `G(Δ')` with `ã = 0` at the prover's keys `v + wΔ'` and masks
     `ṽ_mask + u_mask Δ'` (`qsAt`) is a polynomial of degree `≤ d`; it is evaluated at the `d + 1`
     points `1 … d + 1` and interpolated, `ã_{i−1} = G_i`, `qs_check = G_0`, and the prover refuses
     if `G_d ≠ 0` (witness does not satisfy the constraints). The C++ computes the same
     coefficients with its degree-tracking `quicksilver_state<S, false, d>`; they are unique,
     since acceptance needs the check value to be constant in `Δ'`. No separate coefficient
     decomposition of the `Arith/*` constraints is needed. Grinding (`findFirst`, `grindStep`) and
     the opening (`BAVC.openAt`, `one_tree_bavc::open`).
   * PomFRIT: `voleGen` with `r`, `mu₁ = H₂⁴(DST ‖ 12)`, binder `refresher_com`; the statement
     `pomfritRedeem` is built from step 1's signature (its `ũ`, `d[0..45)` give `h`); `proveCommit`
     with the Signer's `s`, binder `refresher`.
   * Seeds: the KATs carry the protocol seeds and witnesses; `rho` comes from the `Spec/*` seed
     expanders, so no new C++ dumps were needed.
   Checked by `lake exe prover_vectors [TESTS [main|labelrows]]`: all 18 KAT proofs
   (6 Moussaka, 9 Ratatouille, 3 PomFRIT) reproduced byte for byte on `main`, and the 18
   label-rows KAT proofs with `labelrows` (the KAT files of a `voleith-label-rows` build, as in
   milestone 7); every Lean proof accepted by the
   Lean verifier, including random statements of all five relations (seeds, contexts and credits
   from SHAKE of a label; issuers' UOV preimages from a test-only oil-space sampler, `sample`) and
   KAT witnesses with a random `rho`; a flipped witness bit or a wrong Signer response makes the
   prover refuse. For every Lean proof the harness also checks the two correctness facts of the
   completeness theorem (the opening reconstructs the prover's keys and commitments; the
   verifier's rows and masks are `v + u·Δ'`), now proved (below). About 44 s per layout (34 s of proving and verifying, 5 s of
   UOV key generation); a proof takes 0.2–1.1 s, the 64-anchor redemption 6.5 s (10 evaluations
   of its constraints).
   Proved (`Bridge/Prover.lean`, no `sorry`, axioms `propext`, `Classical.choice`, `Quot.sound`):
   the byte/word round trips of the proof format and the field layout of `assemble`; the VOLE
   correlation on columns and lifted rows for every `Δ` (`prover_column`, `prover_row`); the VOLE
   check identity (`voleHash_complete`); QuickSilver completeness for every `Δ' ≠ 0`
   (`qsProve_complete`, via `EndToEnd.sysCheckPoly` and Lagrange uniqueness); and completeness of
   the whole verifier on the prover's output (`verify_proveCommit`, `verify_prove`,
   `moussakaIssue_complete`, `moussakaRedeem_complete`, `ratatouilleIssue_complete`,
   `ratatouilleSpend_complete`, `pomfritRedeem_complete`), assuming `HashesWF` (discharged for
   SHAKE, `hashesWF_shake`), `BAVCComplete` (the tree opening), `CrtComplete` (the CRT masks are a
   VOLE) and `Δ' ≠ 0` (not tested by the C++ either; `Δ' = 0` has probability `Pr[hit]/|A| ≈ 2⁻¹¹⁸·⁷`,
   not `2⁻¹²⁰`: the accepted `Δ` is uniform on the grinding acceptance set `A`, `|A| ≈ 0.40·2¹²⁰`;
   proved `≤ 2⁻¹¹⁴`, `ZK.Sim.pr_hitZero_le_114`). Without these two assumptions, in the
   random-oracle model: `ZK/CompleteRO.lean` (`complete_rom`, below).
   **Both correctness facts are proved** (no `sorry`, same axioms):
   * `Bridge/BAVCComplete.lean`, `bavcComplete`: for every seed, `iv` and `Δ`. The verifier's
     reconstruction and the prover's `openSeeds` share one walk (`BAVC.openNodes`, a fold of
     `markStep`; the top-down derivation is a fold of `deriveStep`; `reconstruct` restructured
     accordingly, same outputs). The tree is `treeNode` (structural recursion on the node index,
     `expandTree_get`); the marks after the walk are `hid` (hidden leaf or ancestor, `walk_spec`),
     so every node off the hidden paths with a parent on one is opened (`mem_openNodes`) and the
     root is on one; the opening's layout (`opening_spec`), the placement and the derivation
     (`placed_spec`, `derive_spec`: by induction over the walk, every known seed is the tree's
     node and every node off the hidden paths becomes known) and the leaves as concatenations of
     fixed-size pieces (`leavesOf_eq`, `extract_pieces`) finish it.
   * `Bridge/CrtComplete.lean`, `crtComplete`: for `CrtGen.tables`, every `Δ` and every statement
     whose label rows are corrected rows (`hlab_of`: witnesses of ≥ 16 bytes; all five relations,
     both layouts). The verifier's gate labels are `L^{γ_e}_e` (`gateInputs_eq`), it reads back
     `c_mult` (`cmult_bit`), `r̃` is bilinear (`polyMod` and `rTildeOf` are folds; `polyMod_xor`,
     `zb_polyMod_rTildeIn`; the mask rows are uncorrected, `prover_column_mask`), so the masks'
     difference is `Σ_c Δ_c L_c(u_mask)` (`crt_core`) with `L_c` of `Bridge/CrtCheck.lean`, where
     `Lc_eq : L_c(a) = a · W_crt[c]` is the tables' bilinear identity, checked on all
     `120 · 128` basis pairs by `decide +kernel` (`crtCheck_eq`: per `c` the 128 values are packed
     into one `2¹⁶³⁸⁴`-bit number as XORs of outer products `w · spread v`; ≈ 1 min, ≈ 4 GB; the
     tables are hex literals in `CrtData`, so the kernel parses no strings).
   * `Bridge/Complete.lean`: `verify_proveCommit_tables`, `verify_prove_tables`,
     `*_complete_tables` (five relations), `*_complete_shake`: completeness at `CrtGen.tables`
     assuming only `HashesWF` (none with SHAKE) and `Δ' ≠ 0`. For PomFRIT also on the final
     signature (`Privacy.PomFRIT.pomfritVerify_complete_tables`).
   * `ZK/CompleteRO.lean`: **probabilistic completeness** with neither the prover's success nor
     `Δ' ≠ 0` assumed: with `H₃`, `H₂³`, `H₅` uniform tables (`recH`) and `ρ` uniform, the
     prover fails or `verify` rejects with probability `≤ Pr[GrindBad] ≤ 2⁻¹¹³` (`complete_rom`,
     `complete_rom_ic`, the five relations `*_complete_rom`, two phases `complete2_rom`). The `ZeroKnowledge` hypotheses
     of `Privacy/Basic.lean` are instantiated with this prover in `Privacy/*Lean.lean`
     (`docs/zk.md` §10.1).
