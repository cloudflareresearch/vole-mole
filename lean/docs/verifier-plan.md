# Plan: an executable Lean VOLEitH verifier

Goal (D): a Lean function `verify : Relation → instance → proof → Bool` that accepts the real proofs
the C++ produces (the KAT files `tests/moussaka/moussaka_kat.txt`, `tests/ratatouille/
ratatouille_kat.txt`, PomFRIT's `tests/pomfrit/pomfrit_kat.txt`) and rejects mutated ones. It should
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
the domain byte is appended last.

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
* **Dedicated label rows (patch 0005, branch `voleith-label-rows` only).** Target `main`'s layout.
  With `CRT_DEDICATED_LABEL_ROWS`, `VOLE_CORRECTION_ROWS` grows by 128 (rows `ℓ..ℓ+127` after the
  witness feed the gate labels in step 5 instead of witness rows `0..127`), each correction cᵢ is 16
  bytes longer (+256 B per proof), step 7's hashed rows include the 128 label rows, and step 8
  applies `d` only to the `ℓ` witness rows. Keep "label row offset" and "corrected rows" as
  parameters of the Lean model so both layouts are one switch apart. The KAT files differ between
  the branches.
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
| CRT tables (Mᵢ, W_CRT, W_TREE, W_GATE, G) | dumped (`record crt tables`), parsed in `Verifier/VectorsMain.lean` | used by the CRT step below, which matches the C++; porting `fao/tools/gen_crt_tables.py` (or reading `crt_constants_128f.json`) is still to do |
| Proof layout, `check_format`, `mu`, `iv`, `chal1` | `Verifier/Proof.lean` | `verifier_vectors`, 5 relations |
| ConvertToVOLE, CRT VOLE (gate hashes, row lift, r̃, `q_mask`, lifted Δ) | `Verifier/VOLE.lean` | `verifier_vectors`, 5 relations |

AES also unblocks the protocol specs: Moussaka's spec cannot yet check the digests of non-issuer
anchor keys, because expanding a compressed UOV public key needs AES-128-CTR (pqov's
`pk_seed` expansion). `Verifier/AES.lean` provides that (pqov's CTR layout still to be matched).

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

Still to add when needed: the VOLEHash `h` (64 B) and the ZKHash state before the mask (milestones
5-6), and records from a `voleith-label-rows` build (milestone 7). The relation-specific
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
5. **KOS + chal2** (steps 7-8): VOLEHash with `Arith/GF.lean`; check `chal2`. State
   `voleHash_eq` against `Seed/KOS.lean`'s `voleHashP`.
6. **QuickSilver** (step 9): verifier MAC semiring (value, degree) over `GF128` with Δ powers; run
   the `Arith/*` generators at it (as `arith_vectors` does with `BitOps.field`); ZKHash; check
   `qs_check`, then `delta_check` and full accept on all KAT proofs; mutation tests (flip a byte in
   each proof field → reject).
7. **Label-rows variant** behind a flag, checked on the `voleith-label-rows` KATs.
8. **Bridges** (proofs, not tests): AES-CTR input = `Commitments.ctrInput`; ZKHash code =
   `Seed/QuickSilver.lean`'s `zkHash_eq_code`; VOLEHash = `Seed/KOS.lean`'s model; accept ⇒ the
   hypotheses of the extraction theorems for the concrete transcript.
