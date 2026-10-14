# Zero knowledge of the VOLE-in-the-Head proofs in vole-mole

This note analyses whether the VOLEitH proof system in `src/voleith.hpp`, as the five relations
in this repository use it, is zero-knowledge. All relations use the FAEST-EM-128f v3 VOLEitH
parameters (λ = 128, τ = 17, w_grind = 8, `one_tree` BAVC with T_open = 105, `aes_ctr` leaf hash,
CRT VOLE masks), with one deliberate change to the VOLE layout: the gate labels of the CRT masks
come from λ **dedicated label rows** (faest-arch-opt patch 0005, flag
`OWF_CONSTANTS::CRT_DEDICATED_LABEL_ROWS`). Their QuickSilver degree is d = 2 (PomFRIT) or d = 9
(Keccak relations). Write ℓ = `WITNESS_BITS`.

**Which code.** The main analysis (§§0–3, 5–10) is of branch `voleith-label-rows` (commit
d5def9c). Citations `src/…:<line>` refer to that branch. Citations `faest/<file>:<line>` refer to
faest-arch-opt v3.0.0 with patches 0001–0005 applied. Patch 0005 inserts lines into
`vole_commit.inc` (after line 338, so later lines move by +34) and `constants.hpp`. The other
faest files cited here (`kos_vole_check.hpp`, `quicksilver.hpp`, `vector_com.inc`,
`small_vole.inc`, `crt_vole_helpers.inc`, `prgs.hpp`) are the same as on `main`. §4 is about the
**unpatched** code (`main`, patches 0001–0004, the layout FAEST itself uses). Its citations are
marked `main:`. "Spec" means the FAEST v3.0 specification (faest.info/faest-spec-v3.0.pdf).

## 0. Verdict

**With patch 0005, the proof system is zero-knowledge in the standard (adaptive, multi-proof)
sense** (§2). The theorem (§3) puts no condition on the witness. The distinguisher may choose the
witness itself, and the bound is statistical in `w`. It relies only on the random-oracle,
AES-PRP/GGM and fresh-`rho` assumptions that FAEST's own ZK proof uses.

**On `main`, it was not** (§4). FAEST v3's CRT masks come from garbling-style gate labels
`L⁰_e`, `L¹_e = L⁰_e ⊕ Θ`, and the verifier learns one label per gate. The other label is what
hides the masks. On `main`, the label offset Θ is the prover's `u` on the first λ witness rows, so
`Θ = d[0..λ) ⊕ w[0..λ)` with `d` public. A verifier that knows `w[0..λ)` therefore knows Θ. It
can compute both labels, unmask `c_mult` and then the masks, and unmask the KOS and QuickSilver
responses. ZK held only under an extra condition, (PU): `w[0..λ)` must be unpredictable to the
verifier. That fails for PomFRIT against the Issuer, which gives a practical attack that links
signatures to issuance sessions (§4).

**The fix.** With `CRT_DEDICATED_LABEL_ROWS`, the labels come from λ extra VOLE rows
`[ℓ, ℓ+λ)` directly after the witness:
- These rows get the cross-tree corrections `c_i = u₀ ⊕ u_i`.
- They are hashed by the KOS check.
- They get no witness correction `d`.

So Θ = `u₀[ℓ, ℓ+λ)`. Θ is padded by the hidden leaf of tree 0, and each `c_i` is padded by the
hidden leaf of tree i, so Θ is uniform given everything the verifier sees (§7.1). The cost is
`(τ−1)·λ/8 = 256` bytes per proof (`include/vole_mole/*.hpp`: every proof size grows by 256), and
proofs are no longer wire compatible with FAEST signatures. FAEST's own parameter sets don't set
the flag and are unchanged.

| Relation | `main` (labels on `w[0..λ)`) | Patched (dedicated label rows) |
|---|---|---|
| PomFRIT redeem (blind signature) | **Fails** against the Issuer, which can compute `r = t ⊕ h` (§4). Blindness is broken. | ZK; blindness no longer fails on this account |
| Moussaka issue | ZK under (PU), computational (one-wayness of the Keccak-p[800] commitment in `r`) | ZK, statistical in `w` |
| Moussaka redeem | ZK under (PU), with margin exactly 2¹²⁸ | ZK, statistical in `w` |
| Ratatouille issue | ZK under (PU), computational | ZK, statistical in `w` |
| Ratatouille spend | ZK under (PU), computational | ZK, statistical in `w` |

The rest of the construction checks out on both code versions (§§5–7):
- The 4 + (d − 1) CRT masks hide the VOLE-check and QuickSilver responses.
- The grinding counter is perfectly simulatable.
- The unopened `aes_ctr` leaves stay hiding.
- Challenge-dependent constraints, binders and delayed instance binding do not affect the
  simulator.
- The prover randomness `rho` is fresh in every caller.

All code claims of the new argument were checked against the branch (§7.1). No mismatch was
found.

## 1. The proof, as implemented

**Prover, step 1** (`voleith_vole_gen`, `src/voleith.hpp:166-256`):

1. `mu ← H₂⁰(instance ‖ DST)`, or `H₂⁴(DST)` in delayed mode (`voleith.hpp:125-140`).
2. `(seed, iv_pre) ← H₃(w_pre ‖ mu ‖ rho)`, where `w_pre = w[0..WITNESS_PREFIX_BYTES)`
   (`voleith.hpp:186-201`). Then `iv ← H₄(iv_pre ‖ mu)` (`voleith.hpp:205-211`).
3. `crt_vole_commit(seed, iv)` (`voleith.hpp:220-221`, `faest/vole_commit.inc:607-646`):
   - BAVC tree and leaves from `seed`. The small VOLEs give `u` (from tree 0) and the columns `V`.
   - Row layout (`faest/constants.hpp:408-414, 417-423, 432-438`): witness rows `[0, ℓ)`, label
     rows `[ℓ, ℓ+λ)` (`CRT_LABEL_ROW_OFFSET = QUICKSILVER_ROWS = ℓ`, `:363-366`), then the
     uncorrected mask rows. `VOLE_CORRECTION_ROWS = ℓ + λ` and `VOLE_ROWS = ℓ + λ + n_mask·k`.
   - Corrections `c_i = u₀ ⊕ u_i` on all `ℓ + λ` correction rows
     (`faest/vole_commit.inc:103-122`). The extra mask rows of trees i ≥ 1 stay secret in
     `u_extra` (`:113-120`).
   - Gate labels from the label rows: `L⁰_e = G[e]·V[ℓ, ℓ+λ)` (`crt_labels`, `:351-372`, called
     at `:403`) and `L¹_e = L⁰_e ⊕ Θ` with `Θ = u[ℓ, ℓ+λ)` (`crt_label_offset`, `:341-348`, loaded
     at `:398`, applied at `:427, 457`). They are hashed as `h^b_e = H₅(iv, e, L^b_e)`
     (`lift_and_hash_vq`, `:373-466`).
   - Masks `ū_m = W_crt·u_low,m ⊕ M_tree·u_hi,m`. Here `u_low` comes from the uncorrected rows
     after `VOLE_CORRECTION_ROWS` (`:194-230`, offset at `:208`) and
     `u_hi = PRG(seed, iv, 2³¹−1)` (`:232-263`).
     `c_mult[m, e] = h⁰_e[m] ⊕ h¹_e[m] ⊕ F[e]·ū_m` (`:497-510`).
     `v̄_m` gets `W_gate·h⁰` (`:485-494`). There are `n_mask = (d−1) + 4` masks
     (`faest/constants.hpp:379-383`).
4. `chal1 ← H₂¹(mu ‖ com ‖ c_1..c_{τ−1} ‖ c_mult ‖ iv_pre ‖ chal1_binder)` (`voleith.hpp:223-233`).
5. KOS VOLE check (`voleith.hpp:237-243`, `faest/kos_vole_check.hpp:83-201`). It hashes the
   `ℓ + λ` corrected rows of `u` (the witness *and* label rows: `n_hash = VOLE_CORRECTION_ROWS`,
   `kos_vole_check.hpp:197`) and the QuickSilver masks `ū_0..ū_{d−2}`, then adds the four masks
   `ū_{d−1}..ū_{d+2}` (`kos_vole_check.hpp:127-129, 51-65`). The response `ũ` (4λ bits) goes in
   the proof. `h_V` goes into the chal2 hasher.
6. `d[0..pre) = u ⊕ w_pre` on witness rows only (`voleith.hpp:245-250`). The proof's `d` field is
   `ℓ/8` bytes (`faest/faest_sig.hpp:46`).

**Prover, step 2** (`voleith_prove_commit`, `voleith.hpp:266-335`):

7. `chal2 ← H₂²(chal1 ‖ ũ ‖ h_V ‖ [mu_inst] ‖ chal2_binder ‖ d)`, with `d` completed for the
   suffix (`voleith.hpp:284-302`).
8. QuickSilver over constraints derived from `(instance, chal2)` (`voleith.hpp:306-312`). It reads
   `v` on the witness rows only. The proof is `ã_1..ã_{d−1}`. `qs_check = ã_0` is hashed but not
   sent (`faest/quicksilver.hpp:568-611`).
9. Grinding: `Δ ← H₂³(chal2 ‖ qs_check ‖ ã ‖ ctr)` for the least `ctr` such that the top
   `w_grind` bits of Δ are zero and the BAVC opening at Δ succeeds (`voleith.hpp:314-333`,
   `faest/vector_com.inc:982-1066`). The opening is written to the proof.

**Verifier** (`voleith_vole_reconstruct` and `voleith_verify_commit`, `voleith.hpp:370-498`):
1. Reconstruct Q from the opening, the corrections and Δ (`faest/vole_commit.inc:650-685`). The
   corrections are applied to all `ℓ + λ` rows inside `vole_reconstruct` (`:173-175`), *before*
   the labels are computed.
2. Recompute the forced labels `L^{γ_e}_e = G[e]·Q[ℓ, ℓ+λ)`, with `γ_e = G[e]·Δ'`
   (`lift_and_hash_vq<P, true>` at `:672`).
3. Compute `q̄_m` from `h^{γ_e}_e ⊕ γ_e·c_mult[·, e]` (`:534-562`).
4. Run KOS on the `ℓ + λ` rows (`voleith.hpp:457-459`).
5. Apply `d` to the witness rows only (`voleith.hpp:469-476`).
6. Recompute `chal2` and `qs_check`, and accept iff `H₂³(…‖ctr)` equals the Δ in the proof.

## 2. Security notion

We work in the programmable random oracle model (H₂⁰..H₂³, H₃, H₄, H₅ and the XOFs, all SHAKE).

**Two-phase adaptive experiment.** This captures delayed instance binding and adaptive instances.
The distinguisher `D` may ask for `Q_P` proofs, interleaved arbitrarily. For each proof:
1. `D` chooses `w_pre` and a `chal1_binder` and gets the first-phase message π₁, which is the
   proof fields written by step 1 plus `chal1`.
2. `D` then chooses `(x, w_suf, chal2_binder)` such that `(x, w_pre ‖ w_suf) ∈ R`, and gets π₂.

In the non-delayed mode, `x` is fixed with `w_pre` instead. Relations other than PomFRIT use
`w_pre = w`. `D` also gets every oracle and may run the verifier (`Q_V` verifications).

**Definition.** The proof system is *zero-knowledge* if there is a simulator `(Sim₁, Sim₂)`, which
may program the RO, such that the real and simulated experiments differ by at most `ε_ZK` for
every `D`:
- `Sim₁` gets only `chal1_binder` and the public parameters, and outputs π₁.
- `Sim₂` gets `(x, chal2_binder)` and outputs π₂.

`D` knows `w`, so this is standard adaptive NIZK (with delayed instances), and it implies witness
indistinguishability. On `main`, only a weaker "(PU)-ZK" held, where `D` must not be able to
predict `w[0..λ)`, and Proposition 4.1 shows that standard NIZK fails there. With patch 0005, no
predictability term remains.

## 3. Main theorem

**Theorem.** Consider the patched code. Assume the following:
- H₂ʲ, H₄ and H₅ are random oracles. H₃ is a random oracle or a PRF keyed by `rho`.
- `rho` is uniform in {0,1}¹²⁸ and secret for every proof.
- AES-128 under a uniform key is a PRP. This is spec Lemma 10.24, including its divergence
  factor for the fixed 128-bit block.
- The witness satisfies the relation.

Then the proof system is zero-knowledge (§2), with

```
ε_ZK ≤ ε_rho + ε_prog + 2·ε_hide + ε_lab + ε_iv + ε_abort,

ε_rho   = Q_P·(Q₃ + Q_P)·2⁻¹²⁸                 (H₃ guessed, or rho collides; §6 H1)
ε_prog  = Q_P·(Q₂,₃ + Q_P)·2^{−(3λ+64)}         (H₂³ programming; H2)
ε_hide  = the multi-hiding bound of spec Lemma 10.24 for Q_P commitments: GGM, root-PRG and
          FAEST-EM leaf-PRG terms, plus the e^{Q·β²/2¹²⁸} divergence factor   (H4, H8)
ε_lab   = (Q₅ + n_mult·Q_V + Q_P)·2^{−λ}        (sibling-label queries and Θ = 0; H6)
ε_iv    = λ·(Q₅ + 2·n_mult·Q_P)·Q_P·2^{−(128+λ)} (iv collisions between proofs; spec eq. (10))
ε_abort = 0                                      (the simulator reproduces the abort exactly)
```

Here `Q_P` is the number of proofs, `Q_x` the number of queries to H_x, `Q_V` the number of
verifications `D` triggers, and `n_mult ∈ [305, 312]` the number of AND gates. `n_mult` is
derived from the 39-byte `c_mult` rows implied by the proof sizes in `docs/perf.md`. Patch 0005
does not change `c_mult`.

None of the terms depends on the witness or on what `D` knows about it. Compared with `main`,
`ε_lab` lost its `Pred_R` factor: on `main` it was `(Q₅ + n_mult·Q_V)·Pred_R + Q_P·2^{−λ}`, which is
tight by Proposition 4.1.

**Per relation.** The theorem applies to all five relations. Each sets the flag in its
`OWF_CONSTANTS`, and its header asserts that the flag is set for its parameters and unset for
FAEST-EM-128f:
- `src/pomfrit/redeem.hpp:66, 93-94`
- `src/moussaka/issue.hpp:127, 152-153`
- `src/moussaka/redeem.hpp:142, 167-168`
- `src/ratatouille/issue.hpp:113, 138-139`
- `src/ratatouille/spend.hpp:281, 306-307`

In particular, PomFRIT's proof is zero-knowledge towards the Issuer, so the linking attack of §4
no longer applies. Moussaka and Ratatouille no longer rely on the one-wayness of their Keccak
commitments for ZK of the proof.

## 4. The unpatched code (`main`): the attack

*This section describes `main` (and FAEST's own layout, flag unset), where the label rows are the
first λ witness rows. It does not apply to the patched code.* There, the labels are computed from
`V[0..λ)` and the offset is `u[0..λ)` (`main:faest/vole_commit.inc:364, 369`). Since
`d = u ⊕ w` on the witness rows (`main:src/voleith.hpp:228-233`),
`Θ = d[0..λ) ⊕ w[0..λ)`.

**Proposition 4.1 (standard NIZK fails on `main`).** Let a distinguisher `D` know `w[0..λ)` (for
example, it chose `w`). Given a proof, `D` does the following:
1. Run the verifier's reconstruction to get `L^{γ_e}_e`, `h^{γ_e}_e` and `d`.
2. Query `H₅(iv, e, L^{γ_e}_e ⊕ d[0..λ) ⊕ w[0..λ))` for every gate `e`.
3. Set `y_m[e] := c_mult[m, e] ⊕ h⁰_e[m] ⊕ h¹_e[m]`.
4. Output 1 iff every `y_m ∈ im(F)`.

On a real proof, `y_m = F·ū_m` always: this is Lean `attack_recovers` and `sibling_eq`. On a
simulated proof, the queried points are not the labels that defined `c_mult`. So `y_m` is uniform,
and lands in `im(F)` (dimension ≤ λ) with probability at most `2^{−(n_mult−λ)·n_mask} ≤ 2⁻⁸⁸⁵`.
The advantage is about 1, using `n_mult` hash calls.

`D` also learns more than one bit. If F has full column rank (which the CRT identity essentially
forces; see `faest/tools/vole_mult_tables.py`, "Model"), `D` learns `ū_m` itself. That unmasks:
- the KOS response, which reveals 4 GF(2¹²⁸) universal hashes of `u` on the witness rows, that
  is, of `d ⊕ w`;
- the QuickSilver coefficients `ã_i`, which are polynomials in `w`.

So knowing `w[0..λ)` leaks about 4λ + (d−1)λ bits of information about the rest of the witness.
Hiding `w[0..λ)` itself does not help: the leak hurts every witness whose first 16 bytes are
predictable. The same test also breaks witness indistinguishability whenever two witnesses differ
in their first 16 bytes.

**PomFRIT linking attack (concrete, `main`).** In PomFRIT:
- `r` is the witness prefix, with `WIT_OFF_R = 0` and `WITNESS_PREFIX_BYTES = uov::M`
  (`main:src/pomfrit/redeem.hpp:42, 103`).
- The Client sends `t = h ⊕ r` (`src/pomfrit/pomfrit.cpp:173-176`).
- `h = H(pk, chal1, ũ, d[0..M), msg)` is recomputable from the final signature
  (`pomfrit.cpp:96-111, 234`).

An Issuer that logs every request `t_j` does this for each redeemed signature σ:

```
h := hash_to_target(pk, σ, chal1(σ), msg)
for each logged t_j:
    g := (t_j ⊕ h)[0..16)
    run Proposition 4.1's test with guess g     // n_mult ≈ 310 SHAKE calls
    if it passes: σ came from session j
```

The test passes for the right session with probability 1, and for a wrong one with probability
at most 2^{−177·5}. This breaks blindness (unlinkability) outright for an honest-but-curious
Issuer, in about 310·N hash calls per signature. The Issuer also knows `s_j`, so it could test the
full witness, but `r` is enough. Reordering the witness would not help, because the Issuer knows
`s` too.

The PomFRIT paper's variant, which borrows `r` from the VOLE rows (`pomfrit.cpp:89-95`), very
likely has the same problem, because there `u[0..λ)` would be `r` directly.

**Why the patch stops it.** On the branch, the label rows `[ℓ, ℓ+λ)` carry no `d`. The test's guess
`L^{γ_e} ⊕ d[0..λ) ⊕ w[0..λ)` is neither label, except with probability 2^{−λ} per gate. The
regression test `Pomfrit.LabelOffsetIsNotDeterminedByCorrectionAndWitness`
(`tests/pomfrit/test_pomfrit.cpp`, branch) checks this, and §6 H6 bounds every other way of
reaching the sibling label.

## 5. The simulator

`Sim` holds the RO tables and can program them.

**Sim₁** (for π₁; needs no instance in delayed mode):
1. Sample `seed* ← {0,1}^λ` and `iv_pre ← {0,1}¹²⁸`. Compute `mu` and `iv` honestly.
2. Run `crt_vole_commit(seed*, iv)` honestly. This yields the tree, `com`, the corrections
   `c_i` (on witness and label rows), `u`, `V`, `ū_m` and `v̄_m`. Then *replace* `c_mult` with a
   uniform value. (`c_mult` computed honestly from `seed*` would also work. The uniform version
   matches the hybrids directly.)
3. Compute `chal1` honestly. Set `ũ` to a uniform value in F^4_{2^λ}.
4. Set `d[0..pre)` to a uniform value. Output `(c_i, c_mult, ũ, d[0..pre), iv_pre)`.

**Sim₂(x, chal2_binder)**:
5. Grinding outcome first. Sample `ctr` geometrically with parameter `p = |A|/2^λ`, `Δ ← A`
   uniformly, and `Δ_c ← Aᶜ` uniformly for each `c < ctr`. Here
   `A = {Δ : top w_grind bits zero ∧ BAVC.Open(Δ) succeeds}`, a set that depends on Δ only. With
   probability `(1−p)^{2³²}`, output ⊥ instead (as the prover does).
6. Open the BAVC at Δ (Sim has the tree). Run the verifier's reconstruction to get Q, the forced
   labels and `q̄_m`.
7. Compute `h_V` *as the verifier does*, from Q on the `ℓ + λ` corrected rows, `q̄`, Δ and `ũ`.
   Set `d[pre..ℓ)` to a uniform value. Compute `chal2` via the RO.
8. Set `ã_1..ã_{d−1}` to uniform values. Evaluate the verifier's QuickSilver on `Q + d·Δ` (witness
   rows) with `Relation::constraints(x, chal2)` and the masks `q̄` to get `qs_check`.
9. Program `H₂³(chal2 ‖ qs_check ‖ ã ‖ c) := Δ_c` for `c < ctr`, and `:= Δ` for `c = ctr`. Abort
   if any of these points is already defined. Output the rest of the proof.

`Sim` never uses `w`, and never queries H₅ at a sibling label.

## 6. Hybrids

Let `H0` be the real experiment. All differences are summed over the `Q_P` proofs. The
`D`-dependent bad events are defined so that the challenger, which knows `w` and the tree, can
check them.

**H1: random seed.** `(seed, iv_pre)` is uniform instead of `H₃(w_pre ‖ mu ‖ rho)`
(`voleith.hpp:186-201`). The experiments are identical unless `D` queries H₃ at `(w_pre, mu, rho)`
(probability ≤ `Q₃·2⁻¹²⁸`, since `rho` is uniform and secret, even though `D` knows `w_pre`), or
two proofs share `rho` and `mu`.

In the second case, if the inputs are also equal, the deterministic prover outputs the same proof,
and H1 replays it. This is the spec's convention (§10.10, G2). For non-delayed relations,
`w_pre = w` and `mu` binds the instance, so equal `(w_pre, mu, rho)` means equal proofs. For
PomFRIT, see §7.2. Cost: `ε_rho`.

**H2: Δ first.** The challenger samples the grinding outputs (step 5) before running the prover,
and programs H₂³ at the end. `grind_and_open` returns the first counter whose output lies in A
(`faest/vector_com.inc:1040-1063`), and membership in A depends only on Δ (`:801-821`, `:1033`).
So the joint law of `(ctr, Δ, failed outputs)` is exactly that of i.i.d. uniform outputs
(Lean: `card_isFirstHit`, `isFirstHit_uniform_on_A`, `card_noHit`, `isFirstHit_unique`).
Programming fails only if `D` queried a point that starts with the fresh `chal2` (3λ+64 bits).
Cost: `ε_prog`.

**H3: verifier-side recomputation.** The prover's `h_V` and `qs_check` are replaced by the
verifier's recomputation from public data and Δ. These are equal by perfect completeness:
- KOS is the identity `h_V(q) = h_V(v) + Δ·ũ`. It holds on the label rows too, because they are
  corrected, so `Q = V + Δ·u` there.
- QuickSilver's identity holds for a satisfying witness.

This is perfect (`kos_vole_check.hpp:161-170`, `quicksilver.hpp:642-660`).

**H4: puncture the hidden paths.** For the τ hidden leaves and their ancestors, all AES outputs
under hidden keys are replaced by uniform values. This covers:
- the GGM children (tweak = node index, `faest/vector_com.inc:688, 714`);
- the hidden leaves' commitments, `com = AES_k(iv ⊞ (0, twk)) ‖ AES_k(iv ⊞ (1, twk))` with
  `twk = vec_index + 2303` (`:754, 1071-1085`);
- the hidden leaves' VOLE PRG outputs on all rows (tweak `2³¹ + i`, `faest/vole_commit.inc:106`);
- the root's `u_hi` block (tweak `2³¹ − 1`, counter 0, `:241-251`).

All inputs under a given key are distinct, because the tweak occupies a separate 32-bit lane:
`iv.add32(set_low_high32(cnt, twk))` (`faest/prgs.hpp:204`), and the tweaks are below
`(τ+1)·2^k < 2³¹`. This is spec Lemma 10.24, with the FAEST-EM leaf variant and
`β_root = 2β + ⌈n_mask·w_grind/128⌉ = 2β + 1`. Cost: `ε_hide`. The challenger knows `w`, so the
bad event stays checkable.

After H4, on every row, `u₀ = known₀ ⊕ r₀` and `u_i = known_i ⊕ r_i`, with every pad `r_i`
uniform. Different rows get independent coordinates of the hidden leaves' PRG outputs. On the mask
rows, `u_low,m` is uniform, and so is `u_hi,m`. So every `ū_m` is uniform and independent of the
opened data and of the witness and label rows.

**H5: decouple d, the corrections and Θ.** Sample `d` and the witness-row parts of
`c_1..c_{τ−1}` uniformly, and *define* `u₀ := d ⊕ w` and `u_i := u₀ ⊕ c_i` on the witness rows.
On the label rows, sample `Θ` and the label-row parts of `c_1..c_{τ−1}` uniformly, and define
`u₀ := Θ` and `u_i := Θ ⊕ c_i`. This is perfect:
- `(u₀, u_i) ↦ (u₀ ⊕ w, u₀ ⊕ u_i)` is a bijection for every `w` (Lean `correctionsEquiv`,
  `corrections_fiberCard`).
- `(u₀, u_i) ↦ (u₀, u₀ ⊕ u_i)` is a bijection (Lean `labelCorrEquiv`, `labelCorr_fiberCard`).

The prover's V is `Q − Δ·u` and is determined by the rest: for every `u` there is exactly one
consistent V (Lean `vole_v_unique`, `vole_u_uniform_given_q`). Q is a function of the opened
seeds, the corrections, `d` and Δ only.

After H5:
- `w` enters the view only through (b) `ũ` and (c) `ã`.
- Θ enters only through (a) `c_mult` together with the H₅ values at the sibling labels, and (b)
  `ũ`, because KOS hashes the label rows.
- The label-row corrections `c_i` are independent of Θ.

**H6: c_mult uniform, siblings unprogrammed.** `c_mult` is sampled uniformly, and H₅ is not
defined (or redefined) at the sibling points `(iv, e, L^{1−γ_e}_e)`.

H5 and H6 are identical until `D` (or a verification `D` triggers) queries H₅ at a sibling point,
before or after the proof. The reason: in H5, `c_mult[·, e] = h^{γ_e} ⊕ h^{1−γ_e} ⊕ F[e]·ū` is a
bijective image of the unqueried value `h^{1−γ_e}` (Lean `cmultEquiv`, `cmult_fiberCard`). By
lazy sampling, that value can be defined only when it is first queried. The verifier's gate
shares `h^{γ_e} ⊕ γ_e·c_mult` are computed from public data in both hybrids. The prover's `v̄_m`
is no longer used after H3.

The sibling label is `L^{γ_e}_e ⊕ Θ` (Lean `label_q_eq`, `sibling_eq_labelRows`), with no witness
term. A single query `(iv, e, X)` hits it iff `X ⊕ L^{γ_e}_e = Θ` for a proof with that `iv`.
Each query names one `iv`, which matches the `iv` of at most `K − 1` proofs except with the spec's
`ε_iv` probability (spec §10.10, abort₅). So each query tests one candidate for one Θ. The event
`L⁰ = L¹`, that is `Θ = 0`, costs `2^{−λ}` per proof (Lean `card_theta_zero`).

We bound the probability of the bad event in H7. There, up to the first hit, the view is
independent of Θ:
- the label-row `c_i` are uniform and independent of Θ (H5);
- `c_mult` is uniform (H6);
- H₅ at the sibling points is unprogrammed;
- `ũ` and `ã` are uniform (H7).

So every query is a function of a view that is independent of the uniform Θ, and hits with
probability exactly `2^{−λ}` (Lean `labelView_theta_card`, `card_query_hits_sibling`, `card_query_hits_sibling_responses`). Pr[bad] is
the same in H6 and H7, because the joint law of the view and Θ is unchanged (Lean
`labelView_responses_theta_card`; see H7). Hence `Pr[bad] ≤ (Q₅ + n_mult·Q_V + Q_P)·2^{−λ}`.
Cost: `ε_lab`.

**No hybrid uses any property of the witness.** On `main` this hop needed (PU), because the
sibling label was `L^{γ_e} ⊕ d ⊕ w[0..λ)` (§4). Proposition 4.1 shows that this was necessary
there.

**H7: uniform responses.** `ũ` and `ã` are replaced by uniform values. This is perfect. After
H4–H6, the masks `ū_0..ū_{d+2}` are uniform, independent of the witness, the label rows and the
opened data, and occur only in the responses. The map
`(ū_0..ū_{d−2}, ū_{d−1}..ū_{d+2}) ↦ (ã, ũ)` is a bijection for every value of everything else:
the witness, Θ, every unmasked QuickSilver coefficient vector, every KOS hash (which takes the
witness rows, the label rows and `ū_0..ū_{d−2}` as input), every `q̄` and every Δ:
- QuickSilver is unit-bidiagonal in its masks (`ã_k = H_k + ū_k + v̄_{k+1}` with
  `v̄ = q̄ − Δ·ū`; `quicksilver.hpp:597-611`). Lean `qsResponse_bijective`.
- KOS is triangular on top of it. Lean `kosQsEquiv`, `kosQs_fiberCard`, `kosQs_indep`.
- The shear lemma (Lean `fiberCard_shear`, `fiberCard_shear_indep`) says that a view of the form
  (public part, bijectively masked part) has a distribution independent of the witness. Applied
  with Θ in the public part, it keeps the joint law of (view, Θ) (Lean
  `labelView_responses_theta_card`).

There are exactly enough masks: `n_mask = (d−1) + 4` (`faest/constants.hpp:379-383`) against
`d−1` QuickSilver elements (`constants.hpp:271-277`) and 4 KOS elements (`:300-309`). The
KOS hash's `n_hash_extra = d−1` matches (`kos_vole_check.hpp:197`). There are 5 masks for
PomFRIT and 12 for the degree-9 relations, both within the 16 or 32 that patch 0002 allows.

**H8 = Sim.** Reverse H4: the tree is generated honestly from a uniform `seed*` (`ε_hide`). Now
every value is produced as in §5, so H8 is the simulated experiment.

## 7. Per-item findings

### 7.1 Gate labels and the dedicated label rows

**Claims the theorem relies on, checked against the branch:**

1. **The labels come from the label rows, for both prover and verifier.** `lift_and_hash_vq`
   computes `L0` with `crt_labels` (`faest/vole_commit.inc:403`). `crt_labels` gathers
   `secpar_bytes` from each of the `delta_bits` columns at byte offset `CRT_LABEL_ROW_OFFSET/8`
   (`:351-372`, gather at `:362-368`) and applies `G_lift_a`. The same code runs on V for the
   prover (`:632`) and on Q for the verifier (`:672`). The prover's offset is
   `crt_label_offset(u)`, which loads `u` at the same byte offset (`:341-348`, used at `:398`).
   `CRT_LABEL_ROW_OFFSET = QUICKSILVER_ROWS = ℓ` (`constants.hpp:413-414, 363-366`).
   `static_assert`s require the label rows to be corrected and byte aligned (`:498-501`).
   Branch tests pin the layout: `tests/pomfrit/test_pomfrit.cpp:224-227` for the flag, and
   `tests/voleith/test_voleith.cpp:69-70` for FAEST with the flag unset.
2. **The verifier computes labels after applying the c_i.** `crt_vole_reconstruct` first calls
   `vole_reconstruct` (`vole_commit.inc:667`). That applies each tree's `VOLE_CORRECTION_BYTES`
   of correction, which now include the label rows (`:173-175`; `small_vole.inc:120-135`). Only
   then does it call `lift_and_hash_vq<P, true>` (`:672`). So on the label rows,
   `Q = V + Δ·u₀ = V + Δ·Θ`, and the verifier's label is `L⁰ + γ_e·Θ` (Lean `label_q_eq`). The CRT
   lift (`crt_lift_q`, `:675`) comes after, as before. `d` is applied later still, and only to
   witness rows (`voleith.hpp:469-476`).
3. **KOS covers the label rows.** Both sides pass the first `VOLE_CORRECTION_ROWS = ℓ + λ` rows
   (`voleith.hpp:240-242, 457-459`; `constants.hpp:432-438`), and `kos_vole_check_both` hashes
   `n_hash = VOLE_CORRECTION_ROWS` rows (`kos_vole_check.hpp:197, 214`). In H7 the KOS hash is
   therefore a function of Θ, and the four direct masks hide it.
4. **Nothing else reads u on the label rows.**
   - `d` is computed over `witness_prefix.size()` and `WITNESS_BYTES` bytes only
     (`voleith.hpp:245-250, 294-300`; `faest_sig.hpp:46`).
   - QuickSilver reads `v` and `w` on the witness rows only (`voleith.hpp:306-307`).
   - `u_extra` and `u_low` start at `VOLE_CORRECTION_BYTES`, past the label rows
     (`vole_commit.inc:113-120, 208`).
   - `compute_r_tilde` starts at `VOLE_CORRECTION_ROWS` (`:295`).
   - No other code in `src/` or `include/` touches `u_bytes()` or `u()` (grep on the branch: only
     `voleith.hpp:240-242, 246, 294`).
5. **Θ is uniform given the view.** Θ = `u₀[ℓ, ℓ+λ)` is padded by tree 0's hidden leaf. Each
   `c_i = Θ ⊕ u_i[ℓ, ℓ+λ)` is padded by tree i's hidden leaf (H4, H5). The verifier's Q on these
   rows, and hence its forced labels, are functions of the opened seeds, the `c_i` and Δ. So
   (opened data, `d`, `c_i`, forced labels) is independent of Θ (Lean `labelView_theta_card`,
   `labelView_theta_indep`). The responses are masked by uniform masks that are independent of Θ
   (claim 6), and `c_mult` is uniform after H6.
6. **The masks are still uniform given everything revealed.** The mask rows moved down by λ, but
   everything that locates them is relative to `VOLE_CORRECTION_ROWS`/`_BYTES`:
   - `extract_u_low` at `:208` and `u_extra` at `:113-120`;
   - `compute_r_tilde` at `:295`;
   - the CRT lift of the corrected rows only, at `:636, 675`;
   - `VOLE_ROWS` at `constants.hpp:417-423`.

   The proof still publishes only the first `VOLE_CORRECTION_BYTES` of each tree's correction
   (`vole_commit.inc:112`). §7.4 therefore applies unchanged: `u_low` comes from uncorrected rows
   of trees with one hidden leaf each, and `u_hi` comes from the never-opened root.

No mismatch between the code and these claims was found. One remark on robustness: the flag is
opt-in per relation. `voleith.hpp` itself does not `static_assert` it, so a new relation that
forgets the flag silently gets the `main` layout and needs (PU) (§9).

**What `w[0..16)` is, and why it no longer matters.** On `main`, ZK needed `w[0..λ)` to be
unpredictable. That failed for PomFRIT, whose `w[0..16) = r[0..16)` is known to the Issuer via
`t = h ⊕ r` (`pomfrit.cpp:147-161, 173-176, 188-190`). It was computational for the Keccak
relations, whose `w[0..16) = r` is the commitment opening (`moussaka/issue.hpp:58, 95`;
`moussaka/redeem.hpp:74-75, 114`; `ratatouille/issue.hpp:55, 89`; `ratatouille/spend.hpp:92,
240`). With dedicated label rows, the witness's first bytes play no special role.

### 7.2 Partial witness binding and `rho`

Every caller derives `rho` from 32 fresh OS bytes through a domain-separated XOF:
- `pomfrit.cpp:147-161, 184`
- `moussaka.cpp:58-85, 124, 230`
- `ratatouille.cpp:70-83, 167, 261`

`ProveSeed` has 128 bits (`voleith.hpp:90-92`). PomFRIT publishes the refresher, which is another
squeeze of the same XOF. Squeezed blocks are independent in the ROM, so this reveals nothing
about `rho`.

**Repeated `rho`.** For the four non-delayed relations, `w_pre` is the whole witness and `mu`
binds the instance, so a repeated `(w, x, rho)` reproduces the identical proof. That is harmless,
as in deterministic FAEST signing.

For PomFRIT, H₃ binds only `r` and the instance-free `mu`. If the same `Seed` were reused for the
same `(pk, msg)` and the Issuer returned a *different* preimage `s'` (UOV preimages are not
unique), the two proofs would share a VOLE with different suffixes. They would then leak
`s ⊕ s'` through `d`, and open different leaves under two values of Δ. This needs a reused seed
through the `detail::` seeded API. The public API draws a fresh seed, and `PendingBlindSignature`
is consumed by `finalize_issue() &&` (`pomfrit.cpp:194-215`).

**Attacker-influenced `rho`.** If an attacker can predict `rho`, then H₃ becomes a deterministic
function of `w_pre`. A distinguisher that knows `w_pre` can then recompute the seed, and with it
the whole VOLE, so standard ZK fails outright. Under a (PU)-style notion, a guess of the full
prefix can be checked, and a predictability term in `w_pre` (not just `w[0..λ)`) appears. Fresh
`rho` is therefore an assumption of the theorem.

### 7.3 Grinding

The counter depends only on Δ and on the opening-size condition. `open` counts hidden nodes from
the Δ bits alone and fails iff `#hidden − 2τ + 1 > T_open` (`vector_com.inc:801-821`). The
top-bits test reads only the hash output (`:1033-1040`). The first success is returned, even
with 4-way batching (`counter − 4 + i`, `:1058`). The verifier checks only the top bits
(`faest_sig.hpp:126-135`), not minimality.

The simulator reproduces the law exactly, including the overflow abort: Lean `card_isFirstHit`
gives the count `|Aᶜ|ⁿ·|Ω|^{N−1−n}`, which is independent of `x ∈ A`, and `card_noHit` gives the
abort count. The probability `(1−p)^{2³²}` with `p ≈ 2⁻⁸·Pr[open succeeds]` is negligible.

### 7.4 CRT masks

- **Low bits.** `u_low,m` takes `k_i` bits from each tree's *uncorrected* extra rows, which now
  start after the label rows (`vole_commit.inc:194-230`, offset `VOLE_CORRECTION_BYTES` at
  `:208`). These are never published: only `VOLE_CORRECTION_BYTES` of each correction are copied
  (`:112-120`). Each tree has one hidden leaf, so they are uniform after H4. They are independent
  of Θ, which uses other coordinates of the same PRG outputs.
- **High bits.** `u_hi,m` is 8 bits of `PRG(seed, iv, 2³¹−1, ctr 0)` (`:232-263`). The root seed
  is never opened, and its tree-expansion inputs use tweak 0. So `u_hi` is uniform after H4.
- **Assembly.** `ū_m = W_crt·u_low ⊕ M_tree·u_hi` is a bijection onto F_{2^λ}, so `ū_m` is uniform.
- **Count.** The number of masks is exactly sufficient (H7, Lean `kosQsEquiv`).
- **Verifier side.** The verifier's `q̄_m` depends on `c_mult` and on `h^{γ_e}` only through public
  data, so it adds nothing beyond H6.

### 7.5 Challenge-dependent constraints, binders, delayed instance

- **Constraints.** `Sim₂` evaluates `Relation::constraints(x, chal2)` on the verifier side only.
  The real response is uniform whatever the coefficients `H_k` are, so deriving constraints from
  `chal2` (for example, random linear combinations of UOV equations) does not matter. It needs
  only that the prover's constraint evaluation has no side output, which holds
  (`voleith.hpp:306-308`).
- **Binders.** These are public inputs to H₂¹ and H₂² (`voleith.hpp:231, 291`) and are given to
  `Sim`.
- **Delayed instance.** π₁ contains no value that depends on Δ, and `h_V` is only absorbed, not
  output. So `Sim₁` needs neither `x` nor Δ, and the instance (PomFRIT's
  `h = H(…, chal1, ũ, d_pre, …)`) may depend adaptively on π₁. The instance enters only `chal2`
  (`voleith.hpp:287-290`). The H6 bound no longer involves the witness, so the adaptive choice of
  `(x, w_suf)` after π₁ is covered by §2's notion. On `main`, this is exactly where PomFRIT failed:
  `t` related `x = h` to `w_pre = r`.

### 7.6 BAVC opening and leaf commitments

For the hidden leaf, `com = AES_k(iv ⊞ (0, twk)) ‖ AES_k(iv ⊞ (1, twk))` is revealed, and
`sd = k` (`vector_com.inc:1071-1085`, line 1082). The VOLE expansion uses the same key `k` with
tweak `2³¹ + i`, a different input lane. So, under the PRP assumption (spec Lemma 10.24, FAEST-EM
leaf variant `PRG_pair_EM`), `com` hides the leaf's VOLE outputs.

The opened seeds (T_open ≤ 105 nodes) together with all τ hidden commitments determine Q exactly,
and the corrections `c_i = u₀ ⊕ u_i` are uniform given them, on the witness rows and on the label
rows (H5, Lean `corrections_fiberCard`, `labelCorrEquiv`). The simulator generates this data
honestly from its own tree, so nothing beyond the simulator's output leaks.

## 8. Assumptions and deviations from the FAEST v3 ZK argument

### 8.1 Assumptions used
1. H₂⁰..H₂³, H₄ and H₅ are random oracles, programmable for H₂³ and lazily sampled for H₅. H₃ is
   a random oracle, or a PRF keyed by `rho` as in the spec.
2. AES-128 is a PRP under uniform keys, for the GGM, root and leaf PRGs, with the spec's
   divergence accounting (spec §10.3.4, Lemma 10.24).
3. `rho` is uniform, secret and fresh. Callers satisfy this (§7.2).
4. The honest prover runs on a satisfying witness (completeness identities in H3).

No assumption on the witness is needed. On `main`, a fifth assumption was needed: (PU), that
`w[0..λ)` is unpredictable to the verifier (§4).

### 8.2 Where the repo deviates from FAEST v3
- **Dedicated label rows (patch 0005).** The gate labels come from λ extra corrected rows instead
  of the first λ witness rows. Corrections grow by λ bits per tree i ≥ 1 (256 bytes per proof),
  `VOLE_ROWS` grows by λ, and the mask rows move down by λ. Proofs are not wire compatible with
  FAEST (`voleith.hpp:23-37`). With the flag unset, the code is FAEST's, so FAEST's parameter
  sets and signatures are unchanged (`tests/voleith/test_voleith.cpp:69-70`).
- **Generic witness instead of a uniform key.** The spec's argument silently uses that the first
  λ witness bits are the uniformly random secret key (§8.3). With patch 0005 that is no longer
  needed.
- **Partial witness binding.** H₃ binds only `w_pre`, not `sk`. This is harmless with fresh
  `rho`, but see the PomFRIT seed-reuse caveat (§7.2).
- **Delayed instance binding.** `mu` has no instance in the seed or `iv`. ZK is unaffected (§7.5).
- **Binders and challenge-dependent constraints.** No effect on ZK (§7.5).
- **QuickSilver degree.** The degree differs (2 or 9 instead of FAEST's), and so does
  `n_mask = d + 3`. The mask counting is generic (Lean `qsResponse_bijective` holds for every
  `n`).
- **Patch 0002.** H₅ output is widened to 32 bits and up to 32 masks are allowed. Each mask uses
  its own output bit of H₅, and SHAKE output is prefix-consistent, so ZK and wire compatibility
  for 16 or fewer masks are unaffected. The patch's motivation (a degree-16 issuance proof) is
  stale: the largest degree is now 9, giving 12 masks.
- **FAEST-EM leaf hash with a generic witness.** Identical to FAEST-EM-128f, so the spec's EM
  hiding bound applies verbatim.

### 8.3 A gap in the spec's own argument
In the proof of Theorem 10.42 (spec §10.10), G6 programs `H₅(iv, e, L^{γ⊕1}) := c_mult ⊕ …` at
points offset by `u[0..λ)`. G9 then replaces `d := w + u` by a uniform `d`, and calls this
"perfectly indistinguishable … because u is uniform since G6".

That is not perfect. After G6, `u[0..λ)` is no longer used only in `d`: it also fixes where H₅
was programmed. A distinguisher who can guess `w[0..λ)` tells G8 from G9 by querying
`L′ ⊕ d ⊕ w[0..λ)`.

For FAEST this costs only `Q₅·Pr[predict sk[0..λ) from pk]`, which is negligible. So the theorem
survives, but the hop silently uses that `w[0..λ)` is the uniform, secret key. That is exactly
the condition (PU) that does not carry over to generic relations.

Patch 0005 removes the gap rather than paying for it. The label offset lives on rows without `d`,
so in our H5 the offset Θ and `d` are sampled independently. The G8→G9-style hop (our H5) then
really is perfect, and the label offset is handled in H6 at cost `(Q₅ + n_mult·Q_V + Q_P)·2^{−λ}`.

## 9. Recommendations

1. **Done: dedicated label rows.** The branch implements the generic fix, which replaces the
   per-relation pad that an earlier version of this note proposed. All five relations set
   `CRT_DEDICATED_LABEL_ROWS` and assert it. The PomFRIT unlinkability argument should still be
   re-read against the new theorem, which now gives standard ZK towards the Issuer.
2. **Make the flag hard to forget.** `voleith.hpp` accepts any relation, and a new relation
   without the flag silently gets the `main` layout, whose ZK needs (PU). Add a `static_assert`
   in `voleith_vole_gen` / `voleith_vole_reconstruct` that `CP::CRT_DEDICATED_LABEL_ROWS` holds,
   unless the relation explicitly opts out (for example, a FAEST-compatibility test relation).
3. **Raise with the FAEST authors.** Raise the spec's G8→G9 hop (§8.3) and the label offset, with
   patch 0005 as the proposed generic-VOLEitH layout. The patch has a TODO to this effect, and see
   also `voleith.hpp:124`.
4. **Moussaka and Ratatouille.** No action is needed for ZK. Their (PU) argument from the Keccak
   commitment's one-wayness (§4, `main`) is no longer used.

## 10. What is formalized in Lean

All files are under `lean/VoleMole/ZK/`. There is no `sorry` and no `axiom`. `#print axioms`
lists only `propext`, `Classical.choice` and `Quot.sound`.

| Statement | Lean | Used in |
|---|---|---|
| A view (public part, bijectively masked part) has a distribution independent of the bijection, and hence of the witness | `fiberCard_shear`, `fiberCard_shear_indep`, `fiberCard_equiv` | H5–H7 |
| The QuickSilver response is a bijection of its `d−1` masks for any coefficients, `q̄` and Δ | `qsResponse_injective`, `qsResponse_bijective` | H7 |
| KOS + QuickSilver responses together are a bijection of all `n + 4` masks; uniform and witness-independent | `kosQsEquiv`, `kosQs_fiberCard`, `kosQs_indep` | H7 |
| `(d, c_i) = (u₀+w, u₀+u_i)` is a bijection for every `w` (witness rows) | `correctionsEquiv`, `corrections_fiberCard` | H5 |
| One `c_mult` column is a bijection of the sibling hash | `cmultEquiv`, `cmult_fiberCard` | H6 |
| Given Δ and Q, each `u` has exactly one consistent V | `vole_v_unique`, `vole_u_uniform_given_q` | H5 |
| Verifier label = `L⁰ + γ_e·u` (either layout) | `label_q_eq` | H6, §4 |
| **Patched layout:** `(Θ, u_i) ↦ (Θ, Θ+u_i)` on the label rows is a bijection | `labelCorrEquiv`, `labelCorr_fiberCard` | H5 |
| **Patched layout:** the view `(d, c_i, forced labels)` is independent of Θ, and Θ is uniform given it | `labelView_theta_card`, `labelView_theta_indep`, `labelView_theta_uniform`, `labelView_indep` | H6, §7.1 |
| **Patched layout:** with the bijectively masked responses added (KOS depends on Θ), the joint law with Θ is unchanged | `labelView_responses_theta_card` | H6, H7 |
| **Patched layout:** sibling = forced + Θ (no witness term); a query that is any function of the view hits with probability exactly `2^{−λ}`; `Θ = 0` likewise | `sibling_eq_labelRows`, `query_hits_sibling_iff_labelRows`, `card_query_hits_sibling`, `card_query_hits_sibling_responses`, `card_theta_zero` | H6 |
| **`main` layout:** sibling = forced + `d` + `w[0..λ)`; one query tests one guess | `sibling_eq`, `query_hits_sibling_iff` | §4 |
| **`main` layout:** the attack recovers `F·ū` exactly | `attack_recovers` | §4 |
| Grinding: first-hit law `|Aᶜ|ⁿ|Ω|^{N−1−n}`, uniform on A, unique; abort law | `card_isFirstHit`, `isFirstHit_uniform_on_A`, `isFirstHit_unique`, `card_noHit` | H2 |

The patched-layout results are in `lean/VoleMole/ZK/LabelRows.lean`. The `main`-layout results
stay in `Labels.lean`, labelled as statements about the unpatched layout.

**Proved only on paper:**
- the random-oracle and lazy-sampling steps (H1, H2 programming, H6 identical-until-bad, and the
  union bound over adaptive H₅ queries, each of which is a function of a Θ-independent view);
- the PRP/GGM hiding (H4/H8, imported from spec Lemma 10.24);
- the completeness identities (H3);
- the identification of the Lean model with the C++ (§7.1, by inspection);
- the claim that `rank F ≤ λ < n_mult` makes the attack's test sound on `main`. `n_mult` is
  inferred from the proof sizes, not computed from the generated tables.
