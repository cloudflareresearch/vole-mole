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
AES-PRP/GGM and fresh-`rho` assumptions that FAEST's own ZK proof uses. For the executable Lean
prover with label rows, the single-proof bound and the privacy theorems of all three protocols are
mechanized in the random-oracle and ideal-cipher model (§10.1–10.6).

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
| PomFRIT redeem (blind signature) | **Fails** against the Issuer, which can compute `r = t ⊕ h` (§4). Blindness is broken. [Lean, §4.1] | ZK; blindness no longer fails on this account |
| Moussaka issue | ZK under (PU), computational (one-wayness of the Keccak-p[800] commitment in `r`). Bad event `≤ q·ε_PU` [Lean, §4.1] | ZK, statistical in `w` |
| Moussaka redeem | ZK under (PU), with margin exactly 2¹²⁸: towards a verifier that has no information on `r` (the Moderator), `ε_PU = 2⁻¹²⁸` exactly, with no assumption [Lean, §4.1]; towards a colluding Anchor (knows `t`), computational as for issue | ZK, statistical in `w` |
| Ratatouille issue | ZK under (PU), computational [Lean, §4.1] | ZK, statistical in `w` |
| Ratatouille spend | ZK under (PU), computational [Lean, §4.1] | ZK, statistical in `w` |

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

### 4.1 ZK on `main` under (PU): what is mechanized

`lean/VoleMole/ZK/Main.lean` and `ZK/Relations.lean` mechanize the (PU) hop on `main`: the
counterpart of H6 for the unpatched layout, where the sibling label is `L^{γ_e} ⊕ d[0..λ) ⊕
w[0..λ)` (`sibling_eq`).

**Model.** As `LabelRows.lean`, but with the label rows equal to the first λ witness rows: the tape
is the tree outputs `(u₀, u_i)` on the witness rows (uniform after H4), the view is `d = u₀ ⊕ w`,
`c_i = u₀ ⊕ u_i` and the forced labels (a function `forcedOf` of public data), and
`Θ = π(u₀)`, with `π` the projection to the first λ rows (`mainView`). For several proofs that
share a secret (a token's issuance and redemption proofs, both with `r` first), `MainLayout`
abstracts a family of such views with a re-parametrisation of the tapes; `MainLayout.prod` puts
proofs side by side.

**Statements (all proved, no hypotheses beyond those listed):**
1. *The view without Θ is witness-independent* (H5, H7 on `main`): `(d, c_i, forced labels)` is
   uniform on consistent values for every `w` (`mainView_card`, `mainView_indep`), also with the
   bijectively masked KOS/QuickSilver responses, which may depend on Θ and `w`
   (`mainView_responses_indep`).
2. *But Θ is determined by the view and `w[0..λ)`*: `Θ = π(d) − π(w)` (`mainView_theta`); the
   joint count with `Θ = θ` is 1 iff `θ = π(d) − π(w)` (`mainView_theta_card`). Compare
   `labelView_theta_card`, where it is 1 for every θ.
3. *The bad event is exactly prediction.* For a query `(j, X − L^{γ})` computed from auxiliary
   information `aux(s)` about the secret, the view, and coins `ω` independent of the secret and
   the tape, `Pr[hit] = Pr[B predicts w_j[0..λ) from aux(s)]`, where `B = MainLayout.predictor Q`
   runs the query on the view of the zero witness (which needs no secret) and outputs
   `Θ' − offset` for its own simulated `Θ'` (`MainLayout.prU_hit_eq`, an equality). For `q`
   queries, `Pr[some query hits] ≤ Σ_k Pr[B_k predicts] ≤ q·ε_PU`
   (`MainLayout.prU_exists_hit_le`), also when the queries see the responses (the predictor
   samples them uniformly; `MainLayout.prU_exists_hit_responses_le`). **(PU) is the explicit
   hypothesis** that each of these `q` predictors (efficient: the adversary plus a simulated view)
   succeeds with probability `≤ ε_PU`.
4. *Statistical case*: if `aux` is constant and each label prefix is uniform, every predictor,
   unbounded, succeeds with probability at most `2^{−λ}` (`prU_guess_le_of_uniform`,
   `MainLayout.prU_exists_hit_le_of_uniform`).
5. *Per relation* (`ZK/Relations.lean`), from the `Arith/` witness layouts: the label prefix is
   `labelOfBytes` of the commitment opening that the constraint systems read, `issueR`
   (`issue.hpp:58, 95`), `redeemR` (`redeem.hpp:74-75, 114`), `bytesAt w 0` for both Ratatouille
   relations (`ratatouille/issue.hpp:55, 89`, `spend.hpp:92, 240`): `moussakaIssue_labelPrefix`,
   `moussakaRedeem_labelPrefix`, `ratatouilleIssue_labelPrefix`, `ratatouilleSpend_labelPrefix`;
   the honest `Spec/Moussaka.lean` encodings start with `r` (`encodeIssueWitness_take`,
   `encodeRedeemWitness_take`). With (PU) stated as predicting the 16 opening bytes
   (`MainLayout.prU_exists_hit_le_opening`): `moussaka_main_zk` and `ratatouille_main_zk` bound the
   bad event of a token's issuance and redemption (spend) proofs jointly by `q·ε_PU`, with the
   responses. `moussakaRedeem_main_zk_uniform` gives `q·2⁻¹²⁸` for a redemption verifier whose
   information does not depend on `r`.
6. *PomFRIT* (`issuerGuess_eq`, `pomfrit_issuer_hits`, `pomfrit_issuer_prU_hit`,
   `pomfrit_attack_test`): in every honest run of `Spec/PomFRIT.lean` (correct proof system and
   signer), the Issuer's guess `t ⊕ hash_to_target(σ)` is exactly `r`, the witness prefix
   (`WIT_OFF_R = 0`); so for every tape its query `π(d) − r[0..16)` is Θ, its predictor succeeds
   with probability 1 (the hypothesis of item 3 fails for every `ε_PU < 1`), and the test of
   Proposition 4.1 accepts every real `c_mult` column for every hash function, while a uniform
   column passes for only `#S` of `|B|` values (`card_attack_test_ideal`).

**The "margin exactly 2¹²⁸" remark, checked.** The redemption witness is `r ‖ s ‖ …` with
`R_BYTES = 16 = λ/8` (`redeem.hpp:74-75`), so `w[0..λ)` is exactly `r` (item 5), and `s` starts
at bit 128. Towards the Moderator, whose view (`nf`, contexts, Anchor Set, the proof) does not
depend on `r` (it never sees `t`), `ε_PU = 2⁻¹²⁸` holds for every adversary
(`moussakaRedeem_main_zk_uniform`): the same per-query term as the patched layout, and no more,
since `r` has exactly 128 bits. Towards an Anchor that also issued the token (it knows
`t = Com(nf, ctx_iss, ctx_red, r)`), `ε_PU` is the one-wayness of Keccak-p[800] in `r`, as for
issuance (`security/moussaka.md` §3.2), whose generic estimate `(q+1)/2¹²⁸` again has margin
exactly 2¹²⁸. The remark is accurate, but only for the non-colluding case it is unconditional.

**Still on paper, for ZK on `main`:**
- H1–H4 and H8, unchanged from §6 (`ε_rho`, `ε_prog`, `ε_hide`);
- the identical-until-bad coupling H5 ≈ H6: that the two hybrids agree off the event "some H₅
  query hits a sibling label" (lazy sampling of H₅ at the sibling points). Only the inequality it
  feeds is in Lean (`prU_le_add_of_iff_off`);
- that, before the first hit, an oracle adversary's queries are functions `Q_k(aux, view, ω)` with
  `ω` (H₅ answers, the uniform `c_mult` of H6, the uniform responses of H7, the grinding outcome)
  independent of the secret and the tape: the instantiation of item 3 from an oracle adversary;
- the per-query selection of one proof via `iv` (`ε_iv`) and the union over proofs that are not
  modelled jointly; the `Q_P·2^{−λ}` term for `Θ = 0`;
- that the opened seeds and Δ, on which `forcedOf` depends, are fixed (the Lean bound holds for
  every value) and that the predictor can sample them as the simulator does;
- the (PU) bound itself for the colluding cases: one-wayness of Keccak-p[800] in `r`, an
  assumption (`security/moussaka.md` §3.2, `security/ratatouille.md`);
- the identification of the `main` code with the model (by inspection, `main:` citations above);
- for PomFRIT, that `rank F ≤ λ < n_mult` (so `#S/|B|` is small); the bit-level link from
  `Spec/PomFRIT.lean`'s byte `r` to the witness bit vector is a hypothesis (`hw`, the layout of
  `Arith/PomFRIT.lean`).

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
  `t` related `x = h` to `w_pre = r`. [Lean] `ZK/TwoPhase.lean` (§10.1) for the executable
  prover: the simulator samples `(ctr, Δ)` from its own coins first and outputs π₁ (uniform
  fields, the verifier's `chal1`) before any instance exists; the ideal prover's step 2 is
  uniform given π₁ for every adaptive choice of `(x, w_suf)` (`proveIdeal2_close`).

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

All files are under `lean/VoleMole/ZK/` (and `Privacy/LeanProver.lean`, `Privacy/PomFRITLean.lean`,
`Privacy/MoussakaLean.lean`, `Privacy/MoussakaNC.lean`, `Privacy/RatatouilleLean.lean`, §10.1; `Privacy/ZeroKnowledgeRO.lean`,
`Privacy/MoussakaRO.lean`, `Privacy/RatatouilleRO.lean`, `ZK/TwoPhaseRO.lean`, `ZK/TwoPhaseIC.lean`,
`ZK/TwoPhaseReadsRO.lean`, `Privacy/PomFRITRO.lean`, §10.2; `Privacy/Resample.lean`,
`ZK/IdealCipherP.lean`, `ZK/HopsPatch.lean`, `ZK/AdaptRO.lean`, `Privacy/AdaptiveRO.lean`,
`Privacy/MoussakaRA.lean`, `Privacy/RatatouilleRA.lean`, `ZK/TwoPhaseAd.lean`,
`Privacy/PomFRITRA.lean`, `Privacy/PomFRITRAGame.lean`, `ZK/CollideAd2.lean`,
`Privacy/PomFRITRAH.lean`, §10.3; `ZK/TwoPhasePerm.lean`,
`ZK/IdealCipherPermP.lean`, `ZK/HopsPatchPerm.lean`, `Privacy/PermRO.lean`, `Privacy/PermRA.lean`,
§10.4; `ZK/SharedH3.lean`, `ZK/SharedH3Two.lean`, `ZK/SharedH3RA.lean`, `ZK/SharedH3One.lean`,
`Privacy/SharedH3RO.lean`, `Privacy/SharedH3PomFRIT.lean`, `Privacy/SharedH3RA.lean`,
`Privacy/SharedH3PomFRITRA.lean`, `ZK/SharedH3Tail.lean`, `Privacy/SharedH3PomFRITRAH.lean`,
`ROM/SharedH3Reads.lean`, §10.5; `Privacy/SeedXOF.lean`, `Privacy/SeedXOFGames.lean`,
`ROM/SeedXOFReads.lean`, `Privacy/SeedXOFNC.lean`, §10.6; `ZK/VerifyReadsRO.lean`,
`Privacy/MoussakaNCRO.lean`, `Privacy/MoussakaNCSh.lean`, §10.7; `ZK/ReadsMany.lean`,
`Privacy/PomFRITMany.lean`, `Privacy/MoussakaMany.lean`, `Privacy/RatatouilleMany.lean`,
`Privacy/PomFRITAdaptive.lean`, §10.8). There is no `sorry` and no `axiom`. `#print axioms` lists
only `propext`, `Classical.choice` and `Quot.sound`.

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
| **`main` layout:** the view `(d, c_i, forced labels)` is witness-independent (also with the masked responses), but Θ = π(d) − π(w) is determined by it and `w[0..λ)` | `mainView_card`, `mainView_indep`, `mainView_responses_indep`, `mainView_theta`, `mainView_theta_card` | §4.1 |
| **`main` layout:** `Pr[a query hits a sibling label] = Pr[an explicit predictor guesses w[0..λ) from aux]`; `q` queries (with the responses, several proofs sharing the secret) `≤ q·ε_PU` under (PU) as a hypothesis; `≤ q·2^{−λ}` when aux is constant | `MainLayout.prU_hit_eq`, `MainLayout.prU_exists_hit_le`, `MainLayout.prU_exists_hit_responses_le`, `MainLayout.prU_exists_hit_le_of_uniform`, `MainLayout.prod` | §4.1, H6 |
| Identical until bad: `Pr[E] ≤ Pr[E'] + Pr[Bad]` if `E`, `E'` agree off `Bad` | `prU_le_add_of_iff_off` | H6 |
| **`main` layout, per relation:** `w[0..16) = r`, the opening read by the constraint systems; the bound for a token's two proofs jointly; Moussaka redemption towards the Moderator `≤ q·2⁻¹²⁸` | `moussakaIssue_labelPrefix`, `moussakaRedeem_labelPrefix`, `ratatouilleIssue_labelPrefix`, `ratatouilleSpend_labelPrefix`, `encodeIssueWitness_take`, `encodeRedeemWitness_take`, `moussaka_main_zk`, `ratatouille_main_zk`, `moussakaRedeem_main_zk_uniform` | §4.1, §7.1 |
| **`main` layout, PomFRIT:** the Issuer's `t ⊕ h(σ)` is `r` in every honest run; its sibling query hits with probability 1; the attack test accepts every real proof, a uniform `c_mult` only with probability `#S/|B|` | `issuerGuess_eq`, `pomfrit_issuer_hits`, `pomfrit_issuer_prU_hit`, `pomfrit_attack_test`, `attack_test_real`, `card_attack_test_ideal` | §4, §4.1 |
| Grinding: first-hit law `|Aᶜ|ⁿ|Ω|^{N−1−n}`, uniform on A, unique; abort law | `card_isFirstHit`, `isFirstHit_uniform_on_A`, `isFirstHit_unique`, `card_noHit` | H2 |

The patched-layout results are in `lean/VoleMole/ZK/LabelRows.lean`. The `main`-layout results
are in `Labels.lean` (sibling label, attack), `Main.lean` (the (PU) bound) and `Relations.lean`
(per relation, PomFRIT), labelled as statements about the unpatched layout.

The protocol privacy theorems (`lean/VoleMole/Privacy/`) use zero knowledge as a hypothesis on the
abstract proof systems of `Spec/*`: `Privacy.ZeroKnowledge R prove sim ε` (per proof, the
prover's output under uniform `rho` and the simulator's, from the instance alone, are `ε`-close
for every valid witness, against distinguishers that may know it; `ε = 0` is equality of output
distributions), and a two-phase, delayed-instance version for PomFRIT
(`Privacy.PomFRIT.ZeroKnowledge`, derived for the Lean prover in §10.1). This is the conclusion of
§6's hybrids with the fix. On `main` no
efficient simulator satisfies it, since the distinguisher may know `w[0..λ)` and run the test of
Proposition 4.1 (§4). For PomFRIT it fails for every simulator: phase 1 sees no instance, so the
simulated proof cannot depend on `r`, while the test for the real `r` accepts every real proof
(`pomfrit_attack_test`); and the Issuer even learns `r` in the protocol (`pomfrit_issuer_hits`).

**Proved only on paper for the view models above** (for the executable prover, §10.1 mechanizes the
hybrids in the random-oracle and ideal-cipher model, and §10.2–10.6 the multi-proof games; what
remains there is listed in §10.1, "What remains assumed", §10.3, §10.5, §10.7 and §10.8,
"Open", and §10.6, "What remains"):
- the random-oracle and lazy-sampling steps (H1, H2 programming, H6 identical-until-bad, and the
  reduction of adaptive H₅ queries to functions of a Θ-independent view). For the `main` layout,
  the probability bound that follows (union over `q` queries, each a function of the view, aux
  and independent coins) is in Lean (§4.1); for the patched layout, the per-query count is
  (`card_query_hits_sibling_responses`), and for the executable prover the union over adaptive
  `H₅` queries is mechanized with `H₅` a uniform table (§10.1, `lab_rom_query`);
- the PRP/GGM hiding of H8 (spec Lemma 10.24), and for H4 the step from AES to an ideal cipher
  (H4 itself is mechanized in the ideal-cipher model, with uniform-function rows,
  `hide_rom_query`, and with uniform-permutation rows read forward and backward, the PRP/PRF
  switching term included, `hide_rom_query_perm`; §10.1);
- the completeness identities (H3) for the models (for the executable prover they are proved,
  §10.1);
- the identification of the Lean model with the C++ (§7.1, by inspection);
- the claim that `rank F ≤ λ < n_mult` makes the attack's test sound on `main`. `n_mult` is
  inferred from the proof sizes, not computed from the generated tables.

### 10.1 The executable prover (`ZK/Sim.lean` … `ZK/Exec.lean`, `ZK/TwoPhase.lean`, `Privacy/*Lean.lean`)

The statements above are about models of the views. For the executable Lean prover
(`Verifier/Prover.lean`, which reproduces the C++ proofs byte for byte, README §8) the hybrids are
mechanized down to one probabilistic hypothesis on the prover's tape, with an executable
simulator, and that hypothesis is derived from one hypothesis per hop (H1, grinding, H4, H6), of
which the random-oracle ones are proved with the hashed domain a uniform table:

| Statement | Lean | Hybrids |
|---|---|---|
| The simulator: `(ctr, Δ)` as the first accepted `H₂³` answer of its own coins, the opening from sampled commitments and seeds, uniform `c_i`, `c_mult`, `ũ`, `d`, `ã`; `simulateRO` also returns the hash record with `H₂³` programmed at `chal2 ‖ qs_check ‖ ã ‖ c ‖ 11` (`c ≤ ctr`) | `Sim.simulate`, `Sim.simulateRO`, `Sim.program` | §5 |
| The verifier with the programmed record accepts the simulated proof whenever its run reaches `chal3` (only `H₂³` changes, at points starting with the proof's `chal2`) | `verify_program_accept`, `simulateRO_accept` | §5, H8 |
| **The simulated proof is accepted under the programmed record, unconditionally except for `Δ = 0`** (faest-arch-opt's tables, any CTR PRG, any hash record): every simulated proof passes `check_format` (size `proofBytes`, grinding byte of the accepted `Δ` zero) and its opening reconstructs for every `iv`; `Δ' = Δ·W_CRT ≠ 0` unless `Δ = 0` (`tDL_eq_zero`). Over the simulator's coins, the simulation fails or its proof is rejected with probability `≤ noHitProb + 1/\|A\| ≤ 2^{−2¹⁵} + 2⁻¹¹¹ ≤ 2⁻¹¹⁰` (no grinding hit, or the first hit is `Δ = 0`: the event `GrindBad`, as for the real prover) | `simulate_checkFormat`, `simulate_reconstruct`, `simulate_reaches`, `simulateRO_accept'`, `pr_simulateRO_reject`, `pr_simulateRO_reject_num`, `pr_simulateRO_reject_110` (`ZK/SimAcceptFull.lean`); with the second-moment bound `≤ 2^{−2¹⁵} + 2⁻¹¹⁴ ≤ 2⁻¹¹³`: `pr_simulateRO_reject_114`, `pr_simulateRO_reject_113` (`ZK/SimAcceptFull.lean`) | §5, H8 |
| The ideal-tape prover: the prover's code with its random sources (iv, opening, `(ctr, Δ)`, the small VOLEs' `u^{(i)}`, `u_hi`, the `H₅` answers at the sibling labels) read from a tape; its tags are the verifier's `q + Δ·u` | `Sim.proveIdeal`, `Sim.IdealTape` | H1–H4, H6 (as replaced) |
| **The real prover is the ideal-tape prover at its own run's tape** (no probability) | `prove_eq_proveIdeal`, `Sim.tapeOf` | H3 |
| **On a uniform tape, the ideal-tape prover's output is distributed exactly as the simulator's**: corrections and `d` (one-time pads), `c_mult` (sibling answers, `N_MASK ≤ 32`), the CRT masks (`u_mask` uniform from uniform pads: a kernel-checked certificate for faest-arch-opt's tables), `ũ`, `ã` (KOS/QuickSilver bijection, coefficients through `ũ` only), grinding (`IsFirstHit` law) | `proveIdeal_close`, `balanced_crtVal_tables`, `maskInvOk_tables`, `upush_cmult`, `upush_resp`, `qsProve_eq` | H2, H5–H7, §7.4 |
| **Label rows:** with the tape uniform, Θ is uniform and independent of the proof; a guess of Θ from the proof is right with probability exactly `2^{−8·labelBytes}` | `proveIdeal_theta_close`, `prove_guess_theta` | H6 |
| **Reduction:** every distinguisher's advantage, real vs. simulated proofs, *equals* its advantage, real tape vs. uniform tape, seen through the ideal-tape prover | `zk_reduction` | — |
| **Zero knowledge** from the tape hypothesis `TapeHyp … ε`: `Close ε (prove … ∘ rho) (simulate p)`; in the form of `Privacy.ZeroKnowledge` for a statement family with dedicated label rows; for faest-arch-opt's tables with BAVC and CRT completeness proved and the tape hypothesis from the hop hypotheses (error `ε_rho + ε_grind + ε_bavc + ε_lab`) | `prove_close`, `labelRows_zeroKnowledge`, `labelRows_zeroKnowledge_tables` | all |
| **The tape hypothesis from one hypothesis per hop**, by a proved hybrid argument: H1 (`H3Hyp`: `H₃`'s answer at the seed input is close to uniform, `ε_rho`), grinding (`GrindHyp`: the `H₂³` answers at the grinding points of a prefix that is a function of the seed and `iv_pre`, `ε_grind`), H4 (`HideHyp`: for every `iv` and `Δ`, the hidden part of a commitment from a uniform root seed, i.e. the hidden commitments, the opened seeds, all `u^{(i)}` and `u_hi`, `ε_bavc`), H6 (`LabHyp`: on a uniform tape, the `H₅` answers at the sibling labels it determines against uniform ones, through the ideal-tape prover, `ε_lab`); `TapeHyp … (ε_rho + ε_grind + ε_bavc + ε_lab)`. The deterministic steps: the real run's sibling answers are the ones its tape determines (`fillSib_tapeAt_eq`, from `step1_realAt`), the seed slots past the opened ones are not read; for PomFRIT, `TapeHyp2` with the abort term `noHitProb` (the fallback block is read only if no grinding answer is accepted) | `HopHyps`, `tape_close_of_hops`, `tapeHyp_of_hops` (`ZK/Hops.lean`, `ZK/Exec.lean`), `HopHyps2`, `tapeHyp2_of_hops` (`ZK/TwoPhaseHops.lean`); `Privacy.Close.of_agree`, `Close.prod`, `Close.pi` (`Privacy/Hybrid.lean`) | H1, H2, H4, H6 |
| **The random-oracle hops, with the hashed domain a uniform table** on the inputs the hop reads (`Hashes.withTable`): H1 holds with `ε = 0`, and `≤ q₃·2⁻¹²⁸` against a distinguisher that reads the `H₃` table at `q₃` inputs; grinding holds with `ε = 0`, and programming `H₂³` at the grinding points (as `simulateRO`) is perfect also for a distinguisher that reads the table; H6 is identical until a sibling input is read, for every run that reads the `H₅` table on a known set. Generic: a uniform table's answers at distinct points are uniform; programming is a bijection; identical until a programmed point is read | `h3_rom`, `h3_rom_query`, `grind_rom`, `grind_rom_program`, `lab_rom` (`ZK/HopsROM.lean`); `Privacy.close_restrict`, `pr_program_eq`, `abs_pr_hidden_le`, `abs_pr_hidden_one_le` (`Privacy/Hybrid.lean`) | H1, H2, H6 |
| **What the prover reads.** The grinding prefix (step 1 at the seed and `iv_pre`, then `chal2 ‖ qs_check ‖ ã`) is the same for any two hash records that agree off `H₂³`, so with `H₂³` a table the grinding hops hold for the prover's own prefix computed with the table. The ideal-tape prover reads `H₅` only at the active gate inputs `iv ‖ e ‖ L_e(q) ‖ 5` (the verifier's: `c_mult`'s forced gate hashes, `L(q ⊕ Δ·u) = L(q) ⊕ γ_e·u_pre`, and the CRT reconstruction's); the sibling input is `iv ‖ e ‖ (L_e(q) ⊕ u_pre) ‖ 5`, and a gate input determines its gate and offset | `realPre_pendAt_congr`, `grind_rom_prover`, `grind_rom_program_prover`, `proveIdeal_h5_congr`, `labelOf_tagCols`, `forcedInput_eq`, `siblingInput_eq`, `gateInputsOff_getD_inj` (`ZK/HopsRead.lean`); `sibInput_eq` (`ZK/HopsH6.lean`) | H2, H6 |
| **H6 in the ROM with oracle access**: with `H₅` a uniform table on the sibling inputs and dedicated label rows, the H6 hop costs `≤ (q₅ + 1)·2⁻¹²⁸` against every distinguisher of the proof and the table that reads the table at `q₅` keys (chosen adaptively). The prover reads a sibling input only if `u_pre = 0`; a query is one only if `u_pre` equals the query's guess, a function of the shared tape and the proof's fields; `u_pre` is the label-row pad `Θ` (injectively), uniform and independent of them (`upush_fieldsOf`, as for `prove_guess_theta`) | `lab_rom_query`, `lab_rom_hyp`, `pr_bad_le`, `bad_mem_guesses`, `uPre_eq_thetaW`, `thetaW_injective` (`ZK/HopsH6.lean`) | H6 |
| **H4 in the ideal-cipher model** (the cipher a uniform table `E`, key ↦ row, the rows uniform functions: the PRF view of an ideal cipher; the BAVC rebuilt proof-only with the cipher as a parameter, `hiddenOutE`, equal to the executable `hiddenOut` at `E = AES`): the GGM hybrid replaces the rows of the nodes on the hidden paths (at most `τ·13 = 221`) by independent uniform rows, one node at a time in heap order, at `(4607 + q)·2⁻¹²⁸` each (the node's value is uniform and is used only as a key; the two experiments differ only if it is the key of one of the other `2L − 1 = 4607` nodes or of one of `A`'s `q` table queries; programming the table at it is perfect); with all of them replaced, the hidden part reads the new rows at distinct points (four tweak roles, counters, distinct opened nodes) and is exactly the ideal hidden part (commitments and seeds are the values, each `u^{(i)}` is the opened leaves' part XOR the hidden leaf's blocks, `u_hi` a truncation). Bound `221·(4607 + q)/2¹²⁸` against a distinguisher of the hidden part and the table that reads the table at `q` keys; `HideHypIC p (221·4607/2¹²⁸)` | `hiddenOutE`, `hiddenOut_eq`, `prg_eq_prgR`, `keyAt_aes`, `xIn_sib`, `hidOfRows_point`, `hide_puncture`, `hidSet_card` (`ZK/HopsH4.lean`); `IC.rowAt`, `IC.hop`, `IC.puncture`, `IC.pr_mem_reset_le`, `IC.rowAt_congr_points` (`ZK/IdealCipher.lean`); `pts_injective`, `fold_xor_diff`, `p5F_injective`, `final_close`, `exper_final`, `hide_rom_query`, `HideHypIC`, `hideHypIC_holds` (`ZK/HopsH4Ideal.lean`) | H4 |
| **The hops composed in one random-oracle and ideal-cipher experiment** (one proof, label rows, `SmallParams`): the hash record `recOf Hb … pre G3 G2 G5` with `H₃` (seed inputs), `H₂³` (grinding points) and `H₅` (sibling inputs) independent uniform tables and every other domain, and these off those inputs, the base record's; the BAVC's cipher a uniform table `E` in the proof-only cipher-parametric prover `proveE` (the hidden part of the commitment is `hiddenOutE E`; the rest of the proof as the executable prover's, which recomputes the opened subtrees with its PRG (`HasPrg`: any instance, AES in the executable code); the grinding prefix `pre` any function of `G5`, `E` and the coins), equal to the executable prover at `E = AES` and the executable prefix. Against a distinguisher that sees the proof and `G3`, `G5`, `E` (not `G2`) and reads them adaptively at `q₃`, `q₅`, `q_E` keys: `proveE` vs. `simulate` with independent tables, advantage `≤ q₃·2⁻¹²⁸ + 0 + 221·(4607 + q_E)·2⁻¹²⁸ + (q₅ + 1)·2⁻¹²⁸`. The hybrids of `tape_close_of_hops`, each hop with the other tables fixed and averaged over; the ideal-tape prover reads neither `H₃` nor `H₂³` | `zk_rom_ic`, `joint_h1`, `joint_grind`, `joint_h4`, `joint_tape`, `joint_h6`, `joint_sim`, `proveE`, `proveE_rows`, `proveE_aes`, `proveE_recOf_aes`, `proveP_prove`, `recOf`, `proveIdeal_agreeOff`, `fillSib_agreeOff` (`ZK/HopsJoint.lean`) | H1, H2, H4, H6 |
| **The hops composed with the `H₂³` table visible** (one proof, label rows, faest-arch-opt's tables): the record `recH Hb … G3 G2 G5` with `H₃` (seed inputs), `H₂³` (**every** grinding point `pre ‖ ctr ‖ 11` with a `preLen`-byte prefix) and `H₅` (**every** 37-byte input `iv ‖ e ‖ L ‖ 5`, `Tab5F`) independent uniform tables, every other domain the base record's; the real world is the executable prover with this record, for any CTR PRG (`HasPrg`, AES in the executable code); BAVC hiding for that PRG assumed (`HideHyp`, `ε_bavc`). The simulator outputs `simulate` and the `H₂³` table programmed at the grinding points of the prefix `chal2 ‖ qs_check ‖ ã` it recomputes from its own proof as the verifier does (`vPre`, with the `H₅` table; the points of `simulateRO` when the run reaches `chal3`), at the counters `c ≤ ctr` (`Δ` at `ctr`, its rejected answers below) or at every counter (equal in law: a swap of the answers past `ctr`). Against a distinguisher that sees the proof and all three tables, reads `H₃` and `H₅` adaptively at `q₃`, `q₅` keys and `H₂³` without limit: advantage `≤ q₃·2⁻¹²⁸ + Pr[GrindBad] + ε_bavc + (q₅ + 1)·2⁻¹²⁸`, with `Pr[GrindBad] ≤ noHitProb + Pr[Δ' = 0]` (no accepted grinding answer, or a zero lifted `Δ`) `≤ 2⁻¹¹³` (`grindBad_le_113`, below); there is no `q₂` term. (i) In hybrid H2, outside `GrindBad`, the run returns a proof whose recomputed prefix is the prover's grinding prefix (the run is a real run for a record built for it, and the recomputation is complete on real runs, from `verify_proveCommit`'s proof). (ii) After programming (exact) and switching the programmed points to the recomputed ones (`≤ Pr[GrindBad]`), the view is a function of the output, the grinding answers and the tables, and every later hop keeps the grinding answers fixed: H4 per `iv_pre` and answers, the tape (`tapeEquiv`), H6 (the recomputation reads `H₅` only at the prover's active inputs, so it adds no reads), and the simulator (`proveIdeal_close` per shared tape) | `zk_rom_h23`, `zk_rom_h23_ro`, `recH`, `simTab`, `simTabRO`, `sim_ro_eq`, `GrindBad`, `grindBad_le`, `hyb3_vPre`, `prove_recAt`, `prePrefix_size`, `joint2_h1`, `joint2_prog`, `joint2_keys`, `joint2_h4`, `joint2_tape`, `joint2_h6`, `joint2_sim`, `lab_rom_hyp_sG`, `proveIdeal_close_shared`, `vIn5_proveIdeal` (`ZK/HopsH23.lean`); `vPre`, `vPre_proveCommit`, `vPre_eq_verify` (`ZK/VerifyPre.lean`); H6 for the table on every 37-byte input: `lab_romG`, `pr_bad_leG`, `proveIdeal_table_congrG` (`ZK/HopsH6.lean`) | H1, H2, H4, H6 |
| **The cipher as a parameter of the executable code**: the BAVC (`children`, `leafCom`, commit and `reconstruct`), the VOLE expansion (`prgWords`, `convertToVoleAt`), the prover (`smallVoleUWords`, `uMaskOf`, `voleGen`, `prove`) and the verifier call the CTR PRG through the class `HasPrg`, whose only global instance is AES (the executables are unchanged); every lemma from the bridge theorems to `zk_rom_h23`'s chain is stated for any instance. `icPrg E`: the CTR PRG of a cipher table `E` (on 16-byte keys); `icPrg aesTable` is the executable instance, so the prover, the reconstruction, the VOLE expansion, the verifier and `vPre` with `icPrg aesTable` are the executable ones; the commitment's hidden part with `icPrg E` is `hiddenOutE E` | `HasPrg`, `aesPrg` (`Verifier/Prg.lean`); `icPrg`, `icPrg_aes`, `hiddenOut_rows`, `hiddenOut_ic`, `keyAt_rows` (`ZK/HopsH4.lean`); `prove_icPrg_aes`, `reconstruct_icPrg_aes`, `convertToVoleAt_icPrg_aes`, `verify_icPrg_aes`, `vPre_icPrg_aes` (`ZK/HopsIC.lean`) | H4 |
| **The hops composed in the random-oracle and ideal-cipher model with `H₂³` visible** (one proof, label rows, faest-arch-opt's tables, `SmallParams`): the record `recH Hb … G3 G2 G5` of the row above (`H₅` on every 37-byte input, a table that does not depend on the cipher) and the cipher a uniform table `E`, independent; the real world is the **executable prover run with the ideal cipher** (`Prover.prove` at `icPrg E`: the cipher in the whole commitment, hidden and opened part, and the VOLE expansion); the simulator outputs `simulate` and `H₂³` programmed at the grinding points of the prefix it recomputes from its proof with the verifier's recomputation at `icPrg E`. Against a distinguisher that sees the proof, the three tables and `E`, reads `H₃`, `H₅`, `E` adaptively at `q₃`, `q₅`, `q_E` keys and `H₂³` without limit: advantage `≤ q₃·2⁻¹²⁸ + Pr[GrindBad] + 221·(4607 + q_E + 4607)·2⁻¹²⁸ + (q₅ + 1)·2⁻¹²⁸`. The chain of `zk_rom_h23` for each fixed `E` before and after H4 (its completeness step holds for every cipher: prover and verifier use the same PRG), and H4 jointly over the root seed and `E` (`hide_rom_query`), with the honest recomputation's reads counted: after H4 the view is a function of the hidden part and `E`, and the prover's public part and the simulator's recomputation read `E` only at the nodes `BAVC.reconstruct` rebuilds from the opening (at most `2L − 1 = 4607`; the proof's opening, `Δ` and `iv_pre` are the tape's) | `zk_rom_ic_h23`, `zk_pre_h4`, `zk_post_h4`, `joint3_h4`, `viewIC`, `viewKeys`, `viewIC_congr`, `rdKeys`, `rdKeys_card`, `reconstruct_ic_congr`, `convertToVoleAt_ic_congr`, `leafKey_reconstruct`, `hyb3_ic_congr`, `vPre_ic_congr`, `hyb3_ok_fields` (`ZK/HopsIC.lean`) | H1, H2, H4, H6 |
| **The grinding term numerically** (faest-arch-opt's tables, `2³²` uniform grinding answers): the accepted set has `|A| ≥ 2¹¹¹` (Markov on the box `[0, 120)¹⁷` of hidden-index tuples, whose summed open count the kernel evaluates in one pass over the tree; the open count is the number of internal nodes with exactly one child on a hidden path); `noHitProb = (1 − |A|/2¹²⁸)^{2³²} ≤ 2^{−2¹⁵}`; an accepted `Δ` with `Δ' = 0` is `0` (`W_CRT` injective), and the first accepted answer is `0` with probability `≤ 1/|A| ≤ 2⁻¹¹¹`; so `Pr[GrindBad] ≤ 2^{−2¹⁵} + 2⁻¹¹¹ ≤ 2⁻¹¹⁰` (`2⁻¹¹³` by the second moment, next row, which the headline bounds use for `Pr[GrindBad]`) | `card_accSet_ge`, `openCount_eq_sum`, `hid_iff`, `enc`, `deltaIndex_enc`, `sum_openCount`, `go_val`, `markov` (`ZK/AcceptCount.lean`); `noHitProb_eq`, `noHitProb_le`, `firstHit_some`, `pr_firstHit_le`, `pr_hitZero_le`, `tDL_eq_zero`, `grindBad_num`, `grindBad_le_110`, `zk_rom_ic_h23_num`, `zk_rom_h23_num` (`ZK/GrindNum.lean`) | H2 |
| **The grinding term by the second moment** (faest-arch-opt's tables): Chebyshev on the same box `[0, 120)¹⁷` with centre `90`: on the box the open count is `2287 − Z`, `Z` the number of internal nodes off every hidden path (`openCount_add_Z`; the `17` hidden leaves are distinct), and `Σ Z² = Σ_{v,w} U2(v, w)` over pairs of internal nodes, `U2` the number of tuples avoiding both; related pairs (one below the other) give `U(ancestor)`, disjoint ones `P(c v + c w)` (`desc_chain`: the ancestors of a node form a chain), so the kernel sums the related pairs on one pass over the tree (`go2`, `≈ 25 000` products) and the disjoint ones through the histogram of the `136` distinct count vectors of the `2303` internal nodes (`hist`, `136²` products). Mean `≈ 104.28`, variance `≈ 24.29`: `|A| ≥ 2¹¹⁴` (`≈ 2¹¹⁴·²`). So `Pr[first accepted answer = 0] ≤ 2⁻¹¹⁴` and `Pr[GrindBad] ≤ 2^{−2¹⁵} + 2⁻¹¹⁴ ≤ 2⁻¹¹³`, and the headline bounds hold with `2⁻¹¹³` | `card_accSet_ge_114`, `cheb`, `openCount_add_Z`, `sum_Z`, `sum_Z2`, `card_off2`, `sum_U2`, `go2_spec`, `hist_sum`, `desc_chain` (`ZK/AcceptVar.lean`); `go2`, `hist`, `rd_val`, `aAll_val`, `sz_val`, `rs_val` (`ZK/AcceptVarData.lean`); `pr_hitZero_le_114`, `grindBad_num_114`, `grindBad_le_113` (`ZK/GrindNum.lean`) | H2 |
| **Completeness in the random-oracle model, without `Δ' ≠ 0`** (faest-arch-opt's tables, any CTR PRG): in the record `recH` (`H₃`, `H₂³`, `H₅` uniform tables) with `ρ` uniform, the executable prover fails or the executable verifier (same record) rejects its proof with probability `≤ Pr[GrindBad] ≤ 2⁻¹¹³`, for every statement and witness with `ZKHyp`: outside `GrindBad` of the answers at the prover's prefix (uniform: the prefix does not read `H₂³`) the run is hybrid H2's, which returns a proof whose `Δ` is the first accepted answer (`hyb3_delta`), so `verify_prove_tables` applies with `Δ' ≠ 0`. Also with the ideal cipher; per relation for the privacy games' statements; for two phases whenever the continuation continues (`realRun2`, via `real_form` and `hyb2'_ok`), and for PomFRIT's Lean prover | `hyb3_delta`, `prove_recH_complete`, `pr_grindBad_preR`, `complete_rom`, `complete_rom_ic`, `moussakaIssue_complete_rom`, `moussakaRedeem_complete_rom`, `ratatouilleIssue_complete_rom`, `ratatouilleSpend_complete_rom`, `realRun2_complete`, `complete2_rom`, `pomfritRedeem_complete_rom` (`ZK/CompleteRO.lean`) | H3 |
| **H4 with AES as uniformly random permutations** (the cipher a table `π : Blk → Perm Blk` of independent uniform permutations, `PCipher`; the BAVC computed with its rows, `hiddenOutE (cf π)`; the distinguisher reads whole permutations at `q` keys, so forward and inverse queries). (i) *The GGM hybrid* replaces the rows of the `≤ 221` hidden-path nodes by independent uniform permutations, one node at a time in heap order. The node's value is its parent's (already replaced) permutation at the node's input, and the rest of the experiment reads that permutation only at the sibling's input and, for the root, at the `nHi` `u_hi` blocks (`rdH`, `hidOfRows_rd`); a fresh value of a uniform permutation given its values on `S` is one of `q` candidates with probability `≤ q/(2¹²⁸ − \|S\|)` (double counting with the neighbours `swap(σ x₀, b)·σ`, `b ∉ σ(S)`). Each hop costs `(4607 + q)/(2¹²⁸ − (nHi + 1))`. (ii) *The switching term*: after the hybrid the hidden part reads the replaced permutations at the same distinct points as in the PRF view; within each row these are samples without replacement, which are `Pr[collision]`-close to independent uniform values (exactly: all collision-free value tuples have equally many permutation preimages, `Perm.exists_extending_pair`). A hidden internal node's row is read at most once (its opened child; two opened nodes never share a parent, `oPar_inj`), so only the `τ = 17` hidden leaves (2 commitment + `VOLE_COL_BLOCKS` VOLE blocks) and the root (`nHi` `u_hi` blocks + at most one opened child) contribute: `switchEps = (17·C(2 + VOLE_COL_BLOCKS, 2) + C(nHi + 1, 2))·2⁻¹²⁸`. **Bound** `221·(4607 + q)/(2¹²⁸ − (nHi + 1)) + switchEps`. For the relations' parameters `nHi = 1` and `switchEps` is `1548·2⁻¹²⁸` (PomFRIT), `3231·2⁻¹²⁸` (Moussaka and Ratatouille issuance), `5526·2⁻¹²⁸` (Moussaka redemption), `28102·2⁻¹²⁸ ≈ 2⁻¹¹³·²` (Ratatouille spend), far below the hybrid's `≈ 2⁻¹²⁰·²·(4607 + q)` | `hide_rom_query_perm`, `hide_puncture_perm`, `hidOfRows_rd`, `rdH`, `oPar_inj`, `grpH`, `grpH_cov`, `grpH_sum`, `switchEps`, `restr_closePm`, `exper_finalPm` (`ZK/HopsH4Perm.lean`); `IC.pr_perm_fresh_le`, `IC.pr_perm_reset_le`, `IC.rowAt_congr_par`, `IC.hopPm`, `IC.puncturePm`, `IC.experPm_empty`, `IC.experPm_close`, `IC.close_evalPts`, `IC.card_fiber_eq`, `IC.pr_not_injOn_le`, `IC.pr_not_injPts_le` (`ZK/IdealCipherPerm.lean`) | H4 |
| **The headline with AES as random permutations**: `zk_rom_ic_h23` with the cipher of the whole BAVC and VOLE expansion the rows of a uniform permutation table `π` (the executable prover at `icPrg (cf π)`, the simulator's recomputation with the same rows), the distinguisher seeing `π` and reading it at `q_E` keys (whole permutations). The hops before and after H4 hold for every cipher, so for the rows of every `π`; H4 is `hide_rom_query_perm` with the honest recomputation's `≤ 4607` reads counted. Advantage `≤ q₃·2⁻¹²⁸ + 2⁻¹¹³ + 221·(4607 + q_E + 4607)/(2¹²⁸ − (nHi + 1)) + switchEps + (q₅ + 1)·2⁻¹²⁸`; as `ZeroKnowledgeRO` on the shared tables `ShPm p = Tab2G p × Tab5F × PCipher` with budgets `BudgetPm` (error `εROPm`) | `zk_rom_ic_h23_perm`, `zk_rom_ic_h23_num_perm`, `joint3_h4_perm`, `viewICPm`, `viewKeysPm`, `viewICPm_congr` (`ZK/HopsICPerm.lean`); `zk_ro_perm`, `lean_zeroKnowledgeRO_perm`, `ShPm`, `BudgetPm`, `realROPm`, `progROPm`, `εROPm` (`ZK/ReadsROPerm.lean`) | H1, H2, H4, H6 |
| **Cipher rows as a parameter**: the shared tables `ShG R p = Tab2G p × Tab5F × (Blk → R)` for a row type `R` with `CipherRow R` (a row as a function of the blocks), the read algebra, the prover's, simulator's and programming's reads and the games stated for every `R`; zero knowledge as classes on `R` (`ZKRow`, `ZK2Row`, `ZK2ARow`, `ZKPRow`) with function rows (`Sh p`, the PRF view) and permutation rows (`ShPm p`) as instances | `CipherRow`, `CipherRow.fn`, `rowFn`, `rowFn_congr`, `ShG`, `ZKRow`, `ZKRow.fn`, `lean_zeroKnowledgeROG` (`ZK/ReadsRO.lean`); `CipherRow.perm`, `ZKRow.perm` (`ZK/ReadsROPerm.lean`); `ZK2Row` (`ZK/TwoPhaseReadsRO.lean`); `ZK2ARow` (`ZK/TwoPhaseAd.lean`); `ZKPRow`, `εAdG`, `h23G` (`ZK/AdaptRO.lean`) | §10.4 |
| **Two-phase zero knowledge with AES as random permutations** (plain, and with the continuation reading the tables after step 1): the chains of `zk2_rom_ic_h23`, `zk2_rom_ic_h23A` with H4 `hide_rom_query_perm` on the view at the rows of `π`; errors `εROPm p q₃ (q₅ + q_k5) (q_E + q_kE)` and `εROPm p (q₃ + q_k3) (q₅ + q_k5) (q_E + q_kE)` | `zk2_rom_ic_h23_perm`, `zk2_rom_ic_h23_num_perm`, `joint3_h4_2_perm`, `viewIC2Pm_congr`, `zk2_rom_ic_h23A_perm`, `zk2_rom_ic_h23A_num_perm`, `joint3_h4_2A_perm`, `viewIC2APm_congr`, `viewIC2A_kcongr`, `zk2_ro_perm`, `zk2_adaptive_perm`, `ZK2Row.perm`, `ZK2ARow.perm` (`ZK/TwoPhasePerm.lean`) | §10.4 |
| **H4 with the permutation table patched on `PE`** (rows fixed at the keys an earlier reader saw): a node's value must also avoid `PE`; `221·(4607 + q + \|PE\|)/(2¹²⁸ − (nHi + 1)) + switchEps`; zero knowledge with `H₅` and the permutation table patched, error `εROPmP` | `IC.hopPmP`, `IC.puncturePmP`, `IC.pr_secretPm_mem_candsP`, `IC.experPmP_empty`, `IC.experPmP_close` (`ZK/IdealCipherPermP.lean`); `hide_puncture_permP`, `exper_finalPmP`, `hide_rom_query_permP`, `joint3_h4P_perm`, `zk_rom_ic_h23P_perm`, `zk_roP_perm`, `εROPmP`, `εAdPm`, `ZKPRow.perm` (`ZK/HopsPatchPerm.lean`) | §10.4 |
| **The privacy theorems with AES as random permutations** (every §10.2 and §10.3 theorem at permutation rows) | `anonymityRO_lean_num_perm`, `unlinkabilityRO_lean_num_perm`, `blindnessRO_lean_num_perm` (`Privacy/PermRO.lean`); `anonymityRA_lean_num_perm`, `unlinkabilityRA_lean_num_perm`, `blindnessRA_lean_num_perm`, `blindnessRAH_lean_num_perm` (`Privacy/PermRA.lean`); the generic `*_leanG`, `*_lean_numG` | §10.4 |
| **BAVC completeness**: the prover's opening at any `Δ` reconstructs its leaf keys off the hidden leaves and its commitments (the walks as folds over the node index; opened nodes, placement, top-down derivation) | `Bridge.bavcComplete` (`Verifier/Bridge/BAVCComplete.lean`) | H3 |
| **CRT completeness**: the verifier's CRT masks are `ṽ_mask + u_mask·Δ'` for every `Δ` (gate labels `L^{γ_e}`, `c_mult` read back, `r̃` bilinear, and the tables' bilinear identity `L_c(a) = a·W_crt[c]`, checked in the kernel on all `120 · 128` basis pairs) | `Bridge.crtComplete`, `Bridge.crt_core`, `CrtCheck.Lc_eq`, `CrtCheck.crtCheck_eq` (`Verifier/Bridge/CrtComplete.lean`, `CrtCheck.lean`) | H3 |
| The privacy theorems with the Lean prover: Moussaka issuer hiding/unlinkability, Ratatouille unlinkability | `Privacy.Moussaka.anonymity_lean`, `Privacy.Ratatouille.unlinkability_lean` (`Privacy/LeanProver.lean`) | — |
| **Newton interpolation is correct**: `InterpOk d` for `d + 1 < 2⁶⁴` (the code's divided-difference table is the recurrence `D(a, m)`; the Newton form interpolates its window, by Neville's identity; Horner's rule builds it) | `Interp.interpOk`, `interpOk_two`, `interpOk_nine`, `interpolate_correct`, `newton_interp` (`ZK/Interp.lean`) | H3 |
| **Two phases, delayed instance** (PomFRIT): with the instance and the witness suffix chosen by any continuation from step 1's output (buffer and `chal1`), the real run is the ideal-tape run at its own tape (step 2: `proveCommit_eq_proveIdeal` for any split of the witness; step 1: `step1_real`); on a uniform tape the ideal run is distributed as the simulated one: step 1's `c_i`, `c_mult`, `ũ`, `d[0..|r|)` are uniform (so the simulator outputs them, and the verifier's `chal1`, before the instance exists), and `d[|r|..)` and `ã` stay uniform given them for every instance and suffix picked (`ã` is a bijection of the QuickSilver masks for every value of `ũ` and of the instance; `(c_i, d)` a bijection of the row pads for every suffix choice that reads `d[0..|r|)` only) | `realRun2_eq`, `idealPhase1_real`, `proveIdeal2_close`, `upush_respAd`, `upush_rowsAd`, `upush_fieldsAd` (`ZK/TwoPhase.lean`) | H2, H5–H7 |
| **Two-phase zero knowledge** from the two-phase tape hypothesis `TapeHyp2`, and for PomFRIT's Lean prover (`leanProver`: `issue_request_with_seed`, then `finalize_issue` for the instance `(pk, h)` and `s`) in the form of `Privacy.PomFRIT.ZeroKnowledge`, with every deterministic hypothesis proved for valid continuations (`P(s) = h ⊕ r`); blindness with the Lean prover on the label-row layout; completeness of `pomfritVerify` on the final signature | `twoPhase_close`, `twoPhase_close_tables`, `Privacy.PomFRIT.lean_zeroKnowledge`, `runHyp2_lean`, `blindness_lean`, `blindness_lean_shake`, `pomfritVerify_complete_tables` (`Privacy/PomFRITLean.lean`) | all |
| **Ratatouille, assembled**: the issuance and spend statements with label rows, the spec's witness encodings (`encode_issue_witness`, `encode_spend_witness`, with the committed Keccak states and the carries), the primitives `leanPrim` (proofs as the spec's label-row-sized vectors, `Spec.Ratatouille.Sizes.labelRows`); `ZKHyp` for every instance and witness; Theorem 2 with only the tape hypotheses, hiding and the hash record's output lengths left (with SHAKE only the hop hypotheses and hiding: `≤ 4(ε_rho + ε_grind + ε_bavc + ε_lab)_I + 4(…)_S + 2ε_hide`) | `Privacy.Ratatouille.issue_holds`, `spend_holds`, `carries_testBit`, `zkHypI`, `zkHypS`, `unlinkability_label_rows`, `unlinkability_label_rows_shake` (`Privacy/RatatouilleLean.lean`) | — |
| **Moussaka, assembled**: the issuance and redemption statements of `Verifier/Relations.lean` with label rows, `ZKHyp` for every well-formed instance (the spec's witness encodings satisfy the `Arith` systems for every combination); Theorem 4(a) with only the tape hypotheses, hiding and the hash record's output lengths left (with SHAKE only the hop hypotheses and hiding: `≤ 4(ε_rho + ε_grind + ε_bavc + ε_lab)_I + 4(…)_R + 2ε_hide`) | `Privacy.Moussaka.issue_holds`, `redeem_holds`, `zkHypI`, `zkHypR`, `anonymity_label_rows`, `anonymity_label_rows_shake` (`Privacy/MoussakaLean.lean`) | — |
| **Moussaka against a Moderator that sees no issuance** (Theorem 4(b), corrected; `security/moussaka.md` §6): only the two redemption proofs are simulated, and nothing is assumed of the issuance proofs or of `Com`. `≤ 4εR + 2·(φ₀ + φ₁)` (`φ_c`: Anchor `c`'s `derive_preimage` fails on a uniform Client's commitment; sound index rule), `≤ 4εR` for one Anchor, `≤ 4εR + 2·(δ₀²⁵⁶ + δ₁²⁵⁶)` with the vinegar hash a random oracle; with the Lean redemption prover down to the tape or hop hypotheses (`4(ε_rho + ε_grind + ε_bavc + ε_lab)_R + 2·(φ₀ + φ₁)`). In the ROM and ideal-cipher model, with the Anchors verifying the issuance proofs on the shared tables: §10.7 (`anonymityNCRO_lean_num`) | `anonymityNC`, `unlinkabilityNC`, `anonymityNC_vinegarRO`, `pr_fail_vinegar`, `anonymityNC_label_rows`, `anonymityNC_label_rows_shake`, `unlinkabilityNC_label_rows` (`Privacy/MoussakaNC.lean`) | — |
| **Zero knowledge with the tables visible, as a notion**: `ZeroKnowledgeRO R prove sim prog Adm ε` (for every instance and witness and every admissible distinguisher of the output, the proof's `H₃` slice and the shared tables, the real experiment and the simulated one with the tables programmed by `prog x c` are `ε`-close); `hop_ro`, the hybrid step of a game whose proofs share the tables (the proofs simulated before have programmed them, the real proof of the step runs on the programmed tables): the zero-knowledge error at the reduction's budget **plus the collision term** `δ = Pr[the real proof's output changes with the earlier programming]` | `ZeroKnowledgeRO`, `ZeroKnowledgeRO.transfer`, `hop_ro`, `hop_ro_unused` (`Privacy/ZeroKnowledgeRO.lean`) | §10.2 |
| **What the executable prover and the programming read** (the shared tables `Sh p = Tab2G p × Tab5F × Cipher`): reads as finite key sets that may depend on the tables (`Rd5`, `RdE`, `Rd3`; `IsProg` for a map that only reprograms `H₂³`), with their algebra (`bind`, `comp_prog`, `IsProg.comp`); the prover with the ideal cipher reads the cipher only at the rows of its GGM tree's `2L − 1 = 4607` nodes (the tree, the leaves' commitments, the small VOLEs, the sender columns and `u_hi`), and `H₅` only at its `2·312` gate inputs (`c_mult`'s two label hashes per gate); the simulator's programming reads `H₅` at `312` and the cipher at `4607` keys (the verifier's recomputation, `vIn5`, `rdKeys`); a simulation that produced no proof programs independently of its statement | `Rd5`, `RdE`, `Rd3`, `IsProg`, `treeNode_ic_congr`, `expandTree_ic_congr`, `commit_ic_congr`, `voleGenAt_ic_congr`, `realROb_rdE`, `realRO_rdE`, `voleGenAt_h5_congr`, `proveCommit_agreeOff_h5`, `realROb_rd5`, `realRO_rd5`, `progRO_isProg`, `progRO_of_error` (`ZK/ReadsRO.lean`) | §10.2 |
| **What the executable verifier reads** (the record `recV` of the shared tables: `H₂³`, `H₅` the tables; the ideal-cipher PRG of the cipher table; `verRO`): `H₅` only at its `nMult = 312` gate inputs (`vIn5`, as its prefix recomputation), the cipher only at the `2L − 1 = 4607` nodes of the tree it reconstructs (`rdKeys`), `H₂³` only at `chal3`'s input (the recomputed prefix, the counter, `11`), and no `H₃`; so an honest verification of a real proof reads `624 + 312` `H₅` and `4607 + 4607` cipher keys | `verify_h5_congr`, `verify_ic_congr`, `verify_h23_congr`, `verify_agreeOff_h3`, `recV`, `verRO`, `verRO_rd5`, `verRO_rdE`, `verRO_comp_rd5`, `verRO_comp_rdE` (`ZK/VerifyReadsRO.lean`) | §10.7 |
| **`zk_rom_ic_h23_num` as `ZeroKnowledgeRO`**: the executable prover with the ideal cipher (`realRO`) and the programming simulator (`simulate`, `progRO`) for every statement family with dedicated label rows, against the distinguishers with budgets `(q₃, q₅, q_E)` (`Budget`), error `εRO q₃ q₅ q_E = q₃·2⁻¹²⁸ + 2⁻¹¹³ + 221·(4607 + q_E + 4607)·2⁻¹²⁸ + (q₅ + 1)·2⁻¹²⁸` | `zk_ro`, `lean_zeroKnowledgeRO`, `Budget`, `εRO`, `εRO_mono` (`ZK/ReadsRO.lean`); `leanPI_zkRO`, `leanPR_zkRO` (`Privacy/MoussakaRO.lean`), `leanPIR_zkRO`, `leanPSR_zkRO` (`Privacy/RatatouilleRO.lean`) | §10.2 |
| **Moussaka issuer hiding and unlinkability in the ROM and ideal-cipher model** (four proofs sharing the tables, the adversary's guess sees all tables): `≤ 8·εRO(q₃, q₅ + 1872, q_E + 13821) + 2·δI₁ + Σ_b (δL b + δR b) + 2·εhide` for the Lean prover with SHAKE (generic: the four zero-knowledge errors at the reductions' budgets) | `anonymityRO`, `anonymityRO_lean`, `realGameRO`, `viewRO`, `hop0RO`, `hop1RO`, `hopLRO`, `hopRRO`, `deltaI1`, `deltaL`, `deltaR`, `simGameRO_iff`, `hiding_hopRO`, `idealGameRO_eq` (`Privacy/MoussakaRO.lean`) | §10.2 |
| **Ratatouille unlinkability in the ROM and ideal-cipher model**: the same structure and bound (`2·δI₁ + Σ_w (δS₁ w + δS₂ w)`); the simulated world is `Ratatouille.view` for the Issuer that also sees the tables programmed as a function of the requests (`Vtab`), so `simGame_iff`, `stage_ideal`, `idealGame_iff` apply verbatim | `unlinkabilityRO`, `unlinkabilityRO_lean`, `realGameR`, `viewR`, `hopI0R`, `hopI1R`, `hopS1R`, `hopS2R`, `deltaI1R`, `deltaS1R`, `deltaS2R`, `Vtab`, `viewR_tab`, `simGameR_iff`, `hiding_hopR`, `idealGameR_eq` (`Privacy/RatatouilleRO.lean`) | §10.2 |
| **Two-phase zero knowledge in the ROM and ideal-cipher model with `H₂³` visible** (PomFRIT's flow, label rows, faest-arch-opt's tables, `SmallParams`): the record `recH Hb (st1 st) r G3 G2 G5` (`H₃` at step 1's seed inputs `r ‖ μ₁ ‖ ρ ‖ 3`), the cipher a uniform table `E`; the real world is the executable two-phase run `realRun2` (`voleGen`, then `proveCommit` for the instance and suffix the continuation picks from step 1's output) with `icPrg E`; **the continuation `K G5 E` may read `H₅` and the cipher** at `q_k5`, `q_kE` keys (not `H₃`, `H₂³`): in a game it is the rest of the game up to this proof's instance. The simulator outputs `simRun2 Hb` (its coins, and the cipher for the verifier's `chal1`) and programs `H₂³` (`simTab2`) at the grinding points of the prefix it recomputes from its final proof for the instance picked from its step-1 output (`outPre2`; at the empty prefix if the continuation stops). Advantage `≤ q₃·2⁻¹²⁸ + Pr[GrindBad] + 221·(4607 + (q_E + q_kE) + 4607)·2⁻¹²⁸ + ((q₅ + q_k5) + 1)·2⁻¹²⁸`, and with `2⁻¹¹³` for `Pr[GrindBad]`: the single-phase bound at the budget plus the continuation's reads. The hybrids of `zk_rom_ic_h23` for `proveIdeal2`: the real run is `hyb2'` at `H₃`'s answer and the table's answers at `preP` (the instance's prefix, or the empty one if the continuation stops: then no grinding answer is read, `hyb2'_none`); H1, programming (exact), and in one hop the programmed points switched to the recomputed ones **and the fallback block to a uniform one** (`≤ Pr[GrindBad]`: outside it an answer is accepted, so the fallback block is unread, and the run is a real two-phase run for a record built for it, `realRun2_recAt2`, on which `vPre` recomputes `pre2`, `hyb2'_vPre`), so the abort term `noHitProb` of `tapeHyp2_of_hops` is inside `Pr[GrindBad]`; H4 jointly over the root seed and `E` (the two-phase view reads `E` at the reconstruction's `≤ 4607` nodes, `hyb3'_ic_congr`, `viewIC2_congr`, plus the continuation's reads); the tape; H6 (`lab2_hyp`, `pr_bad2`: the queries' guesses of `u_pre` are functions of the shared tape and the adaptive fields `fieldsAd`, independent of `Θ`, `upush_fieldsAdθ`; the continuation's `H₅` reads are guesses too); the simulator (`proveIdeal2_close_at`) | `zk2_rom_ic_h23`, `zk2_rom_ic_h23_num`, `zk2_pre_h4`, `zk2_post_h4`, `joint3_h4_2`, `zk2_h1`, `zk2_prog`, `zk2_keys`, `zk2_tape`, `zk2_h6`, `zk2_sim`, `real_form`, `hyb2'_vPre`, `realRun2_recAt2`, `proveIdeal2_h5_congr`, `vIn5_proveIdeal2`, `Hyp2` (`ZK/TwoPhaseRO.lean`, `ZK/TwoPhaseIC.lean`); `proveIdeal2_close_at`, `upush_fieldsAdθ` (`ZK/TwoPhase.lean`) | §10.2 |
| **The two-phase prover as `ZeroKnowledgeROS`** (zero knowledge with tables whose simulator may read the tables it does not program: here the cipher, for `chal1`, and the continuation's reads): instances `(b, K)` (binder, table-reading continuation, `Hyp2RO`), error `εRO q₃ (q₅ + q_k5) (q_E + q_kE)`; the reads: step 1 reads `H₅` at `624`, the cipher at `4607` keys and not `H₂³`; the real run what step 1 and the continuation read (step 2 neither); the simulated run the cipher at `4607` keys plus the continuation's reads; its programming `H₅` at `312`, the cipher at `2·4607` keys plus the continuation's | `ZeroKnowledgeROS` (`Privacy/ZeroKnowledgeRO.lean`); `zk2_ro`, `lean_zeroKnowledgeROS2`, `realRO2`, `simRO2`, `progRO2`, `Hyp2RO`, `step1_rd5`, `step1_rdE`, `step1_agreeOff_h23`, `realRO2_rd5`, `realRO2_rdE`, `simRO2_rd5`, `simRO2_rdE`, `progRO2_isProg` (`ZK/TwoPhaseReadsRO.lean`) | §10.2 |
| **PomFRIT blindness in the ROM and ideal-cipher model** (two sessions on the same tables, each with its `H₃` slice; the Issuer's guess sees all tables with a budget, its responses do not read them): the spec's protocol (`realSession`, `Layout.labelRows`) with the Lean prover on the tables (`leanProverRO`); `≤ 4·εRO(q₃, q₅ + 1248, q_E + 18428) + δ(A) + δ(A.swap)` with the collision term `δ` explicit | `blindnessRO`, `blindnessRO'`, `blindnessRO_lean`, `realGameRO`, `realGameRO_iff`, `realGameRO_true`, `AdversaryRO.swap`, `hop0`, `hop1`, `G1_G1'`, `deltaRO`, `G2_swap`, `G2c_swap`, `swapS` (`Privacy/PomFRITRO.lean`) | §10.2 |
| **The programming-collision terms, bounded**: the real prover reads `H₂³` only at its own grinding prefix (`prove_recH_eq`), so a programming at prefix blocks (`ProgAt`) changes it only if its block is programmed; the simulated opening reconstructs and the programmed block ends with the simulator's uniform `ã` (`16·(d − 1)` bytes, at `72 …` of the `72 + 16·(d − 1)`-byte prefix); completeness of the recomputation on real proofs outside `GrindBad`; with a second application of zero knowledge (distinguisher `TailIn`, budget `(0, 312, 4607)`), `Pr[collision] ≤ 2⁻¹¹³ + εRO(0, 312, 4607) + noHitProb + |T|·2^{−8·16(d−1)}` for programmed tails in a fixed set `T` | `prove_recH_eq`, `realRO_progAt`, `realRO_vPre`, `realRO_ne_tail`, `ProgAt`, `progRO_progAt`, `reconstruct_openingOf`, `vPre_simAssemble`, `preTail`, `simTail`, `preTail_outPre`, `pr_simTail_mem`, `pr_collide_zk` (`ZK/CollideRO.lean`); two phases: `realRun2_h23_congr`, `realRun2_out1`, `preTail_outPre2`, `pr_simCoins_tail_le` (`ZK/CollideRO2.lean`) | §10.2 |
| **The privacy theorems in the ROM and ideal-cipher model with every term explicit**: Moussaka `δI₁ ≤ noHitProb + 2⁻¹⁰²⁴`, `δL ≤ 2⁻¹¹³ + εRO(0, 312, 4607) + noHitProb + 2·2⁻¹⁰²⁴`, `δR ≤ … + 3·2⁻¹⁰²⁴`, so `≤ 8·εRO(q₃, q₅ + 1872, q_E + 13821) + 4·(2⁻¹¹³ + εRO(0, 312, 4607)) + 6·noHitProb + 12·2⁻¹⁰²⁴ + 2·εhide`; Ratatouille the same; PomFRIT `δ(A) ≤ noHitProb + 2⁻¹²⁸`, so `≤ 4·εRO(q₃, q₅ + 1248, q_E + 18428) + 2·noHitProb + 2·2⁻¹²⁸` | `deltaI1_le`, `deltaL_le`, `deltaR_le`, `anonymityRO_lean_num` (`Privacy/MoussakaDelta.lean`); `deltaI1R_le`, `deltaS1R_le`, `deltaS2R_le`, `unlinkabilityRO_lean_num` (`Privacy/RatatouilleDelta.lean`); `deltaRO_le`, `blindnessRO_lean_num` (`Privacy/PomFRITDelta.lean`) | §10.2 |
| **Zero knowledge for a statement chosen by an adversary that reads the tables** (one proof, ROM and ideal cipher): the statement and witness are a function of the proof's `H₃` slice and the shared tables, read at `s₃`, `s₂`, `s₅`, `s_E` keys adaptively and consistently (`SReads`); then the real proof (fresh 16-byte `ρ`) or the simulated one (`H₂³` programmed); a distinguisher of the reader's output, the proof and the tables with budget `(q₃, q₅, q_E)`, `H₂³` free. Advantage `≤ εAd = εRO(q₃, q₅, q_E) + (s₃ + s₅ + 1 + 221·s_E)·2⁻¹²⁸ + [s₂ > 0]·(2⁻¹¹³ + εROP(0, 312, 4607; s₅, s_E) + 2·noHitProb + 2·s₂·2^{−8·16(d−1)})`. Lazy sampling of the reader's view (an involution of a uniform pair), then the chain with the tables patched at the reader's queries: the hops other than H6 and H4 hold for every value of `H₅` and the cipher, H6 and H4 with patched tables cost `(|P₅| + 1)·2⁻¹²⁸` and `221·|P_E|·2⁻¹²⁸` more, the `H₃` patch costs `Pr[ρ ∈ P₃]`, the `H₂³` patch the simulated block (uniform `ã`) and the real block (a second application of zero knowledge) among the patched blocks; the adaptive collision bound; the simulator's programming as a consistent reader | `zk_adaptive`, `zk_adaptive_at`, `zk_patched`, `zk_roP`, `lean_zeroKnowledgeROA`, `pr_collide_adaptive`, `pr_preTail_mem`, `pr_simBlk_mem`, `realRO_g3_congr`, `progRO_patch2`, `SReads`, `SReads.comp_prog`, `CProg`, `progRO_cprog`, `vIn5_ic_congr`, `rdKeys_ic_congr`, `εAd` (`ZK/AdaptRO.lean`); `zk_rom_ic_h23P`, `zk_pre_h4Φ`, `joint2_h6P`, `lab_rom_hyp_sGP`, `joint3_h4P`, `hide_rom_queryP` (`ZK/HopsPatch.lean`); `IC.hopP`, `IC.punctureP` (`ZK/IdealCipherP.lean`); `pr_resample` (`Privacy/Resample.lean`); `ZeroKnowledgeROA`, `hop_roA` (`Privacy/AdaptiveRO.lean`) | §10.3 |
| **Moussaka anonymity with an interaction that reads the tables**: responses, Anchor Sets and digests are functions of the requests, the four slices and the shared tables (budget `(i₃, i₂, i₅, i_E)` per slice position, consistent); `≤ 4·εRO(i₃ + q₃, q₅ + i₅ + 1872, q_E + i_E + 13821) + 4·εAd(9; q₃, q₅ + 1248, q_E + 13821; i₃, i₂, i₅ + 624, i_E + 9214) + 4·(i₃·2⁻¹²⁸ + 2⁻¹¹³ + εROP(0, 312, 4607; i₅ + 624, i_E + 9214)) + 6·noHitProb + 12·2⁻¹⁰²⁴ + 2·εhide` | `AdversaryRA`, `viewRA`, `hop0RA`, `hop1RA`, `hopLRA`, `hopRRA`, `deltaLA_le`, `deltaRA_le`, `anonymityRA`, `anonymityRA_lean_num` (`Privacy/MoussakaRA.lean`) | §10.3 |
| **Ratatouille unlinkability with an interaction that reads the tables**: each stage of the Issuer's interaction (issuance responses and `d₁`; round 1's response and `d₂`) is a function of what it has seen, the four slices and the shared tables (budget `(i₃, i₂, i₅, i_E)` per stage and slice position, consistent), read on the tables as the simulations before it programmed them; `≤ 4·εRO(2i₃ + q₃, q₅ + 2i₅ + 1872, q_E + 2i_E + 13821) + 2·εAd(9; i₃ + q₃, q₅ + i₅ + 1248, q_E + i_E + 13821; i₃, i₂, i₅ + 624, i_E + 9214) + 2·εAd(9; q₃, q₅ + 936, q_E + 13821; 2i₃, 2i₂, 2i₅ + 1560, 2i_E + 23035) + 6·i₃·2⁻¹²⁸ + 4·(2⁻¹¹³ + εROP(0, 312, 4607; 2i₅ + 1560, 2i_E + 23035)) + 6·noHitProb + 12·2⁻¹⁰²⁴ + 2·εhide` | `AdversaryRA`, `transR`, `viewRA`, `hopI0RA`, `hopI1RA`, `hopS1RA`, `hopS2RA`, `sReads_Sx1`, `sReads_Sx2`, `deltaS1A_le`, `deltaS2A_le`, `view_congr`, `simGameRA_iff`, `unlinkabilityRA`, `unlinkabilityRA_lean_num` (`Privacy/RatatouilleRA.lean`) | §10.3 |
| **PomFRIT blindness with an Issuer whose interaction reads every table, `H₂³` included**: the interaction's joint reads (`IBudgetH`: both slices and the shared tables jointly, `i₂` `H₂³` keys) taken out by lazy sampling of `H₂³` before the hybrids (`pr_resampleC`), the existing theorem applied to the Issuer that reads an independent `Γ` in place of `H₂³` (`AdversaryRA.subst`, whose guess patches `H₂³` at the interaction's read set); the collision term (a real session's grinding block meets the interaction's `H₂³` reads) by a second application of two-phase zero knowledge, after which the block's tail is the simulator's uniform `ã`: `≤ 2⁻¹¹³ + εz(6i₃, 6i₅ + 2184, 6i_E + 18428) + 2i₂·2⁻¹²⁸` per session and world; no simulator change | `pr_tail2A`, `realRun2_outPre2`, `outPre2_rd5`, `outPre2_rdE`, `tailEv2`, `pr_simCoins_tail_mem` (`ZK/CollideAd2.lean`); `SReadsP`, `IBudgetH`, `AdversaryRA.subst`, `IBudget.subst`, `GBudget.subst`, `pr_resampleC`, `pr_G0RA_resample`, `G0_at_iff_subst`, `K1R`, `hyp2RA_R1`, `qf0`, `qf1`, `pr_bad0H`, `pr_bad1H`, `G0RA_subst_close`, `blindnessRAH_lean_numG`, `blindnessRAH_lean_num` (`Privacy/PomFRITRAH.lean`); `blindnessRAH_lean_num_perm` (`Privacy/PermRA.lean`); `sReadsP_runT`, `AdversaryOC.iBudgetH`, `blindnessOCH_lean_num`, `blindnessOCH_lean_num_perm` (`ROM/PrivacyReads.lean`) | §10.3 |
| **Table-reading interactions as oracle computations** (no consistency hypothesis): an interaction written as a VCVio `OracleComp` over the tables (`TSpec`: the `H₃` slices, `H₂³`, `H₅`, the cipher rows), run deterministically on them (`runT`), is a consistent table reader with its syntactic query budget (`QBudget`, VCVio's `IsQueryBoundP` per slice and per shared table): the read sets are its query log (`qlog`, `runT_congr`). The single-proof theorem and the six headline privacy bounds for such interactions, bounds unchanged, `IBudget` derived (`AdversaryOC.iBudget`); a budget cannot be dropped (`not_sReads_slice`: the reader that outputs its slice has no consistent query sets of fewer than `2¹²⁸` keys) | `TSpec`, `runT`, `qlog`, `runT_congr`, `countP_qlog_le`, `QBudget`, `sReads_runT`, `sReads_runT₁`, `not_sReads_slice`, `zk_adaptive_oc`, `OCReader`, `lean_zeroKnowledgeROA_oc` (`ROM/TableReads.lean`); `AdversaryOC`, `AdversaryOC.toRA`, `AdversaryOC.iBudget`, `anonymityOC_lean_num`, `anonymityOC_lean_num_perm`, `unlinkabilityOC_lean_num`, `unlinkabilityOC_lean_num_perm`, `blindnessOC_lean_num`, `blindnessOC_lean_num_perm`, and with `H₂³` queries `sReadsP_runT`, `blindnessOCH_lean_num`, `blindnessOCH_lean_num_perm` (`ROM/PrivacyReads.lean`) | §10.3 |
| **One shared `H₃`, the model**: `H₃` on the seed inputs `x ‖ ρ ‖ 3` (`|x| < 1024`) as columns of the shared tables' rows (`RowH R = R × (Pre → Bytes 32)`; row `ρ` carries `H₃(x ‖ ρ ‖ 3)` for every prefix `x`; read as the cipher row by the prover); a proof's slice is the column at its prefix `wPrefix ‖ μ₁` (`h3At s (preKey …)`); the executable prover with the one-`H₃` record (`recOne`: `H₃` on every seed input, `seedEnc` injective) is the prover with that slice (`prove_recOne`); the prover reads `H₃` only at its seed input for every witness (`prove_h3_congr`, `realROb_g3_congr'`, `step1_h3_congr`, `realRun2_h3_congr`, `realRO2_g3_congr'`) | `Pre`, `preKey`, `H3Row`, `RowH`, `CipherRow.rowH`, `h3At`, `setK`, `swapK`, `pr_setK`, `pr_prod_setK`, `rd5_h3At`, `rdE_h3At`, `rd3_setK`, `rd5_setK`, `rdE_setK`, `splitH`, `combH` (`ZK/SharedH3.lean`); `preBytes`, `seedEnc`, `seedEnc_injective`, `recOne`, `prove_recOne` (`ZK/SharedH3One.lean`) | §10.5 |
| **Zero knowledge with one shared `H₃`** (statement fixed): the slice prover's theorem at `(q_E, q₅, q_E)` (the proof's column re-sampled, `pr_setK`; the distinguisher reads it through rows) with no hypothesis on the prefixes; the rows' `H₃` columns are extra uniform data for the slice prover (`ZKRow.rowH`, `ZK2ARow.rowH`, `ZKPRow.rowH`); two-phase with a continuation that reads the shared tables, the replaced column included (`zk2_shared`, `zk2_sharedA`, via `zk2_adaptive`); collision terms unchanged (`pr_h3At_slice`) | `ZeroKnowledgeRO.shared`, `dCol`, `Budget.dCol`, `pr_h3At_slice`, `ZKRow.rowH` (`ZK/SharedH3.lean`); `zk2_shared`, `zk2_sharedA`, `ZK2ARow.rowH` (`ZK/SharedH3Two.lean`) | §10.5 |
| **Zero knowledge with one shared `H₃`, the statement chosen from the tables**: against readers and distinguishers that read no slot slice, the proof's column exchanged with an independent slice off the reader's rows (`swapOff`, a measure-preserving involution keeping the reader's view), error `ε(q_E, q₅, q_E) + s_E·2⁻¹²⁸` (the fresh `ρ` is a row the reader read: the only cost of reading a future proof's prefix); collision events likewise | `withH`, `hcols`, `swapOff`, `swapOff_swapOff`, `agT_swapOff`, `ZeroKnowledgeROA.shared`, `pr_h3At_sliceA`, `pr_mem_rows_le`, `ZKPRow.rowH` (`ZK/SharedH3RA.lean`) | §10.5 |
| **The privacy games with one shared `H₃`**, no prefix-collision term: Moussaka `≤ 8·εRO(q_E + 13824, q₅ + 1872, q_E + 13824) + 4·(2⁻¹¹³ + εRO(0, 312, 4607)) + 6·noHitProb + 12·2⁻¹⁰²⁴ + 2·εhide`, Ratatouille the same, PomFRIT `≤ 4·εRO(q_E + 18428, q₅ + 1248, q_E + 18428) + 2·noHitProb + 2·2⁻¹²⁸`; with a table-reading interaction (`+ 8·(i_E + 9214)·2⁻¹²⁸` Moussaka, `+ 4·(i_E + 9214)·2⁻¹²⁸ + 4·(2i_E + 23035)·2⁻¹²⁸` Ratatouille, none for PomFRIT) and as oracle computations; function and permutation rows | `anonymitySh_numG`, `anonymitySh_num`, `anonymitySh_num_perm`, `unlinkabilitySh_numG`, `unlinkabilitySh_num`, `unlinkabilitySh_num_perm`, `leanPISh`, `leanPRSh`, `leanPIRSh`, `leanPSRSh`, `realGameSh`, `deltaI1_sh`, `deltaL_sh`, `deltaR_sh`, `deltaI1R_sh`, `deltaS1R_sh`, `deltaS2R_sh` (`Privacy/SharedH3RO.lean`); `blindnessSh`, `blindnessSh_numG`, `blindnessSh_num`, `blindnessSh_num_perm`, `realGameSh`, `hop0Sh`, `hop1Sh`, `deltaRO_sh`, `AdversaryRO.SliceFree` (`Privacy/SharedH3PomFRIT.lean`); `anonymityRASh_numG`, `anonymityRASh_num`, `anonymityRASh_num_perm`, `unlinkabilityRASh_numG`, `unlinkabilityRASh_num`, `unlinkabilityRASh_num_perm`, `deltaLA_sh`, `deltaRA_sh`, `deltaS1A_sh`, `deltaS2A_sh` (`Privacy/SharedH3RA.lean`); `blindnessRASh`, `blindnessRASh_numG`, `blindnessRASh_num`, `blindnessRASh_num_perm`, `hop0RASh`, `hop1RASh`, `deltaSh_le`, `AdversaryRA.at_free` (`Privacy/SharedH3PomFRITRA.lean`); `anonymityOCSh_num`, `unlinkabilityOCSh_num`, `blindnessOCSh_num` and `_perm` (`ROM/SharedH3Reads.lean`) | §10.5 |
| **PomFRIT with an Issuer that also reads `H₂³`, one shared `H₃`**: the lazy sampling of `H₂³` on the coins with the sessions' slices their columns (`τC`), the substituted Issuer under `blindnessRASh_numG`; the collision term by `pr_tail2A` for the prover that reads its column (the column re-sampled, `pr_prod_setK`): `≤ 2⁻¹¹³ + εz(6i_E + 13824, 6i₅ + 2184, 6i_E + 18431) + 2i₂·2⁻¹²⁸` per session and world; `≤ 4·εRO(q_E + 6i_E + 23035, q₅ + 6i₅ + 1872, q_E + 6i_E + 23035) + 2·noHitProb + 2·2⁻¹²⁸ + [i₂ > 0]·4·εcolSh` | `pr_tail2Sh` (`ZK/SharedH3Tail.lean`); `ConsP.free`, `AdversaryRA.at_freeH`, `realGameRASh_iff'`, `τC`, `pr_G0RASh_resample`, `qf0Sh`, `qf1Sh`, `K1RSh`, `pr_bad0HSh`, `pr_bad1HSh`, `G0RASh_subst_close`, `blindnessRAHSh_numG`, `blindnessRAHSh_num`, `blindnessRAHSh_num_perm` (`Privacy/SharedH3PomFRITRAH.lean`); `blindnessOCHSh_num`, `_perm` (`ROM/SharedH3Reads.lean`) | §10.5 |
| **Moussaka 4(b′) with one shared `H₃`**: an issuance prover that ignores its slot slice makes the slice hop exact (`pr_slice_free`), so no `4·q₃·2⁻¹²⁸`; with the Lean provers reading their columns, `≤ 4·εRO(q_E + 23038, q₅ + 2496, q_E + 23038) + 2·(noHitProb + 2⁻¹⁰²⁴) + 2·(φ₀ + φ₁)`; the seed-XOF hop applied to both non-colluding games | `SliceFreeP`, `pr_slice_free`, `sim_fresh_NC_free`, `anonymityNCRO_free`, `unlinkabilityNCRO_free`, `realGameNCSh`, `deltaNC_sh`, `anonymityNCSh_leanG`, `anonymityNCSh_num`, `anonymityNCSh_num_perm`, `anonymityNCSh_vinegarRO`, `unlinkabilityNCSh_num`, `unlinkabilityNCSh_num_perm` (`Privacy/MoussakaNCSh.lean`); `seedGameNCRO`, `seedGameNCSh`, `anonymityNCRO_lean_num_seed`, `unlinkabilityNCRO_lean_num_seed`, `anonymityNCSh_num_seed`, `unlinkabilityNCSh_num_seed` and `_perm_seed` (`Privacy/SeedXOFNC.lean`) | §10.6, §10.7 |

`lake exe zk_sim [TESTS [main\|labelrows [FILTER]]]` runs, on all 18 KAT runs of each layout: the
equation `prove = proveIdeal ∘ tapeOf` (all pass), the simulator with the programmed oracle
(accepted; rejected without programming), and the ideal-tape prover on a pseudorandom tape with
`H₂³` programmed at its grinding points (accepted; not run for PomFRIT, whose instance depends on
`chal1`). About 15–60 s per run. The simulator's acceptance check is implied by
`simulateRO_accept'` (`ZK/SimAcceptFull.lean`) whenever the run's `Δ ≠ 0`, so it is redundant
as a check of the theorem's conditions and kept as a smoke test of the executable code.

**What remains assumed.**
- **The hop hypotheses** (`HopHyps`, `ZK/Hops.lean`), from which the tape hypothesis
  `TapeHyp Hs T st w ε` (`ZK/Exec.lean`: the real run's tape, `tapeOf … rho` for uniform `rho`,
  is `ε`-close to a uniform ideal tape through the ideal-tape prover) is proved with
  `ε = ε_rho + ε_grind + ε_bavc + ε_lab` (`tapeHyp_of_hops`; for PomFRIT `HopHyps2`,
  `tapeHyp2_of_hops`, with `+ ε_abort`, `ε_abort = noHitProb = (|Aᶜ|/2¹²⁸)^{2³²}` by
  `Grinding.card_noHit`, `≤ 2^{−2¹⁵}` by `noHitProb_le`, `ZK/GrindNum.lean`). Each is a `Close`
  bound on a small explicit experiment for a fixed hash record; as every statement against all
  distinguishers in `Privacy/Basic.lean`, that is an idealization (a fixed record's `H₃` cannot map 16 bytes of `rho` to 32 uniform bytes against
  every distinguisher). Their status:
  - **H1** (`H3Hyp`, `ε_rho`) and **grinding** (`GrindHyp`, `ε_grind`): proved in the ROM, with the
    hashed domain a uniform table on the inputs the hop reads (`ZK/HopsROM.lean`): both exact
    (`h3_rom`, `grind_rom`), H1 `≤ q₃·2⁻¹²⁸` for a distinguisher that reads the `H₃` table at `q₃`
    inputs (`h3_rom_query`: §3's `Q₃·2⁻¹²⁸`; the term for two proofs sharing `rho` concerns several
    proofs), and programming `H₂³` at the grinding points is perfect (`grind_rom_program`; §3's
    `ε_prog` concerns queries before `chal2` is fixed, i.e. several proofs). The prover's grinding
    prefix does not read `H₂³` (`realPre_pendAt_congr`), so both hold for the prover's own prefix
    computed with the table (`grind_rom_prover`, `grind_rom_program_prover`). Modelling steps left:
    the domain is a random oracle (SHAKE128, with L0's domain separation, `ROM/DomainSep.lean`), and
    the lazy oracle restricted to the hop's inputs is the table.
  - **H4** (`HideHyp`, `ε_bavc`, §3's `ε_hide`): proved in the ideal-cipher model, with the
    cipher a uniform table of uniform-function rows (`ZK/IdealCipher.lean`, `ZK/HopsH4.lean`,
    `ZK/HopsH4Ideal.lean`): `HideHypIC p (221·4607·2⁻¹²⁸)` (`hideHypIC_holds`, averaged over the
    table, for every `iv` and `Δ`) and `≤ 221·(4607 + q)·2⁻¹²⁸` against a distinguisher that also
    reads the table at `q` keys (`hide_rom_query`), for parameters with fewer than `2³²` blocks
    per PRG call (`SmallParams`, `smallParams_of_le`). The BAVC is rebuilt proof-only with the
    cipher as a parameter (`hiddenOutE`), and is the executable commitment at `E = AES`
    (`hiddenOut_eq`). **With the rows uniform permutations** and the distinguisher reading whole
    permutation rows (forward and inverse queries), `≤ 221·(4607 + q)/(2¹²⁸ − (nHi + 1)) +
    switchEps` (`hide_rom_query_perm`, `ZK/HopsH4Perm.lean`): the GGM hybrid with permutation rows
    and the PRP/PRF switching term `switchEps = (17·C(2 + VOLE_COL_BLOCKS, 2) + C(nHi + 1, 2))·2⁻¹²⁸`
    of the hidden leaves' and the root's rows (every other hidden row is read at most once; the
    earlier paper estimate `221·B²·2⁻¹²⁹` over all hidden rows overcounted), `≤ 2⁻¹¹³·²` for the
    relations' parameters. Modelling step left: AES is an ideal cipher (a uniform permutation per
    key). `tape_close_of_hops` composes `HideHyp` for the fixed AES; the
    ideal-cipher version is plugged in through the proof-only cipher-parametric prover `proveE`
    (`zk_rom_ic`, below) and, with the cipher in the whole executable prover and verifier
    (`HasPrg`, `icPrg E`), through `zk_rom_ic_h23` (below).
  - **H6** (`LabHyp`, `ε_lab`): proved in the ROM with §3's bound for one proof: with `H₅` a
    uniform table on the sibling inputs and dedicated label rows, `ε_lab ≤ (q₅ + 1)·2⁻¹²⁸` against a
    distinguisher that reads the table at `q₅` keys, adaptively (§3's `Q₅ + n_mult·Q_V + Q_P` with
    `Q_P = 1`: `q₅` counts every `H₅` query, including the `n_mult` of each verification the
    distinguisher runs) (`lab_rom_hyp`, `lab_rom_query`,
    `ZK/HopsH6.lean`): the ideal-tape prover reads `H₅` only at the active labels
    (`proveIdeal_h5_congr`), a sibling input only if `u_pre = Θ = 0`, and each query is a sibling
    input only if it guesses `Θ` from the shared tape and the proof's fields, of which `Θ` is
    independent. Modelling steps left: as for H1 (SHAKE as a random oracle; the lazy oracle on the
    sibling inputs is the table; the `H₅` inputs outside them are answered by the fixed record).
    The same bound holds with `H₅` a table on every 37-byte input (`lab_romG`, `pr_bad_leG`, the
    layout of `zk_rom_h23` and `zk_rom_ic_h23`, whose table does not move with the cipher).
    On `main` this hop fails (§4).
  - **Composed** (`zk_rom_ic`, `ZK/HopsJoint.lean`): for one proof, with `H₃`, `H₂³`, `H₅`
    independent uniform tables on the hops' inputs (every other domain fixed: `mu`, `H₁`, `H₄`,
    `H₂¹`, `H₂²`, the combination, and the three domains off those inputs) and the BAVC's cipher a
    uniform table, the cipher-parametric prover `proveE` (equal to the executable prover at AES,
    `proveE_recOf_aes`) is `q₃·2⁻¹²⁸ + 221·(4607 + q_E)·2⁻¹²⁸ + (q₅ + 1)·2⁻¹²⁸`-close to the
    simulator against a distinguisher that reads the `H₃`, `H₅` and cipher tables adaptively at
    `q₃`, `q₅`, `q_E` keys; it does not read `H₂³`. With that access the composition is proved in
    the ROM for the executable prover, with BAVC hiding assumed (`zk_rom_h23`, `zk_rom_h23_ro`,
    `ZK/HopsH23.lean`, for any CTR PRG): the simulator programs `H₂³` at the grinding points of the
    prefix it recomputes from its proof (`simulateRO`'s points), and the advantage is
    `q₃·2⁻¹²⁸ + Pr[GrindBad] + ε_bavc + (q₅ + 1)·2⁻¹²⁸` against a distinguisher that also reads
    `H₂³` without limit (no `q₂` term; outside `GrindBad` the recomputed points are the prover's,
    `hyb3_vPre`). Both at once (`zk_rom_ic_h23`, `ZK/HopsIC.lean`): the executable prover and
    verifier call their CTR PRG through `HasPrg` (AES for the executables), so they run unchanged
    with the cipher a uniform table `E` (`icPrg E`; the executable ones at `E = aesTable`,
    `icPrg_aes`) in the whole commitment and VOLE expansion, and `hyb3_vPre` holds for every cipher;
    with `H₃`, `H₂³`, `H₅` (now a table on every 37-byte input, which does not move with the cipher)
    and `E` independent and uniform, the executable prover with `icPrg E` is
    `q₃·2⁻¹²⁸ + Pr[GrindBad] + 221·(4607 + q_E + 4607)·2⁻¹²⁸ + (q₅ + 1)·2⁻¹²⁸`-close to the
    programming simulator against a distinguisher that reads `H₃`, `H₅`, `E` at `q₃`, `q₅`, `q_E`
    keys and `H₂³` freely. The second `4607` is the honest recomputation's reads of `E` (the prover's
    public part and the simulator's recomputed prefix read it only at the nodes the reconstruction
    rebuilds, `rdKeys`, at most `2L − 1`); they are values of nodes off the hidden paths, which the
    GGM hybrid's candidates already contain, so an argument inside `IC.hop` would remove the term.
    **The grinding term is numeric** (`ZK/AcceptCount.lean`, `ZK/GrindNum.lean`):
    `Pr[GrindBad] ≤ 2^{−2¹⁵} + 2⁻¹¹¹ ≤ 2⁻¹¹⁰` for faest-arch-opt's tables (`grindBad_num`,
    `grindBad_le_110`), and `≤ 2^{−2¹⁵} + 2⁻¹¹⁴ ≤ 2⁻¹¹³` with the second moment (below,
    `grindBad_le_113`), so `zk_rom_ic_h23_num` and `zk_rom_h23_num` state the two bounds above
    with `2⁻¹¹³` in place of `Pr[GrindBad]`, as does every numeric error term built on them
    (`εRO`, `εROP`, `εROPm`, `εROPmP`, `εAd*`, `h23*`). The pieces:
    - *The accepted set* `A` (zero grinding byte, at most `T_OPEN = 105` opened seeds) has
      `|A| ≥ 2¹¹¹` (`Accept.card_accSet_ge`; sampling gives `|A| ≈ 0.4·2¹²⁰ ≈ 2¹¹⁸·⁷`). The open
      count is the number of internal nodes with exactly one child on a hidden path
      (`openCount_eq_sum`, from `walk_spec`), and a node is on a hidden path iff a hidden leaf
      descends from it (`hid_iff`). Every tuple of hidden indices is the `Δ` of some 16-byte
      string with zero grinding byte (`enc`, `deltaIndex_enc`, injective). On the box
      `S = [0, 120)¹⁷` of index tuples the number of tuples with `v` off every hidden path is a
      product `Π_i (120 − c_i(v))`, so `Σ_{Δ ∈ S} openCount Δ` is a sum over the tree that the
      kernel evaluates in one pass (`go_val`, `decide +kernel`, a few seconds; mean `≈ 104.28`).
      Markov gives `≥ 120¹⁷ − Σ/106 ≈ 2¹¹¹·⁵` accepted tuples in `S`. This is a lower bound, not the
      exact size: the 17 hidden leaves are interleaved across one tree, so an exact count needs a
      dynamic program whose state is the subset of vectors below each node (`2¹⁷` states), out of
      the kernel's reach; and Markov on all `2¹²⁰` tuples fails (mean `≈ 106.38 > 105`).
    - *No accepted answer*: `noHitProb = (1 − |A|/2¹²⁸)^{2³²}` (`noHitProb_eq`) `≤ (1 − 2⁻¹⁷)^{2³²}
      ≤ 2^{−2¹⁵}` (`noHitProb_le`). This is also the PomFRIT abort term `ε_abort` of
      `blindness_lean_shake`.
    - *`Δ' = 0`*: the event is about the **first accepted answer** (the `Δ` the prover outputs).
      An accepted `Δ` with `Δ' = Δ·W_CRT = 0` is `Δ = 0` (`tDL_eq_zero`: `W_CRT` is injective by
      the kernel-checked left inverse `Bridge.liftInvOk_tables`, so the 120 bits vanish, and
      acceptance zeroes the grinding byte). So `GrindBad` implies no hit, or a first hit at `0`
      (`grindBad_imp`), and `Pr[first hit = 0] = Σ_n |Aᶜ|ⁿ(2¹²⁸)^{N−1−n}/(2¹²⁸)^N ≤ 1/|A| ≤ 2⁻¹¹¹`
      (`pr_hitZero_le`, from `card_isFirstHit` and the geometric sum): given a hit, `Δ` is uniform
      on `A`. The paper's `2⁻¹²⁰` is the probability of `Δ' = 0` for a uniform `Δ'`; but the
      accepted `Δ` is uniform on `A` only, so `Pr[Δ' = 0] = Pr[hit]/|A|`, and
      `|A| ≤ 2¹²⁰` makes `2⁻¹²⁰` a lower bound. With `|A| ≈ 0.397·2¹²⁰` (sampling, `2·10⁶` draws)
      the true value is `≈ 2⁻¹¹⁸·⁶⁷`.
    - *The second moment* (`ZK/AcceptVar.lean`, `ZK/AcceptVarData.lean`, `ZK/GrindNum.lean`):
      Chebyshev on the same box gives `|A| ≥ 2¹¹⁴` (`card_accSet_ge_114`), so
      `Pr[Δ' = 0] ≤ 2⁻¹¹⁴` (`pr_hitZero_le_114`) and `Pr[GrindBad] ≤ 2^{−2¹⁵} + 2⁻¹¹⁴ ≤ 2⁻¹¹³`
      (`grindBad_num_114`, `grindBad_le_113`); every headline bound uses `2⁻¹¹³`
      (`zk_rom_ic_h23_num` is about `2⁻¹⁰⁷·⁰` at zero budgets). The second moment is
      `Σ_{v,w} U2(v, w)` over pairs of internal nodes; two nodes are related (then `U2` is `U` of the
      ancestor) or have disjoint subtrees (then `U2 = P(c v + c w)`), and the `2303` internal nodes
      have only `136` distinct count vectors, so the kernel needs `≈ 25 000` products for the
      related pairs and `136²` for the rest (`≈ 2 min` in all). What is left between `2⁻¹¹⁴` and
      `2⁻¹¹⁸·⁶⁷`: the box (`120¹⁷ ≈ 2¹¹⁷·⁴`; on all `2¹²⁰` tuples the mean `≈ 106.38` exceeds
      `105`, so no moment bound applies there) and the slack of a second-moment bound at a
      threshold `0.35 σ` above the mean (the accepted fraction of the box is `≈ 0.56`, Cantelli
      certifies `≈ 0.11`). An exact count needs the subset of vectors placed below each node as
      state (`2¹⁷` states and subset convolutions at the top of the tree, or an inclusion–exclusion
      over `2¹⁷` subsets of vectors), out of the kernel's reach.
    - *Completeness* (`ZK/CompleteRO.lean`): the same event is the whole completeness error. In
      the record `recH` with `ρ` uniform, the executable prover fails or `verify` rejects its proof
      with probability `≤ Pr[GrindBad] ≤ 2⁻¹¹³` (`complete_rom`; `complete_rom_ic`; per relation
      `moussakaIssue_complete_rom`, …, `ratatouilleSpend_complete_rom`; two phases
      `complete2_rom`, `pomfritRedeem_complete_rom`), with no assumption on `Δ'`.

    Beyond one proof (§10.2, §10.3): with several proofs on shared tables each hybrid step
    costs a programming-collision term `δ`, bounded in Lean (`pr_collide_zk`, `deltaI1_le`,
    `deltaRO_le`, …: `≤ 2⁻¹¹³ + εRO(0, 312, 4607) + noHitProb + 3·2⁻¹⁰²⁴` for a redemption or
    spend, `≤ noHitProb + 2⁻¹⁰²⁴` for the second issuance, `≤ noHitProb + 2⁻¹²⁸` for PomFRIT); the
    privacy corollaries are proved for Moussaka, Ratatouille and PomFRIT with every term explicit
    (`anonymityRO_lean_num`, `unlinkabilityRO_lean_num`, `blindnessRO_lean_num`, for adversaries
    whose interaction does not read the tables; PomFRIT on the two-phase `zk2_rom_ic_h23_num`,
    whose continuation may read `H₅` and the cipher), and with an interaction that reads the
    tables (`zk_adaptive`, `zk2_adaptive`; `anonymityRA_lean_num`, `unlinkabilityRA_lean_num`,
    and `blindnessRA_lean_num` for an Issuer that reads every table but `H₂³`;
    `blindnessRAH_lean_num` for one that reads `H₂³` too, with explicit collision terms, §10.3).
    The per-proof `H₃` slices of these games are not a modelling step any more: with one shared
    `H₃`, as in the scheme, every game is mechanized again (the PomFRIT Issuer that reads `H₂³`
    included) with no prefix-collision (`ε_iv`-type) term (§10.5), and the seed-XOF hop to the
    real Clients is mechanized for all of them (§10.6). Moussaka's non-colluding mode is
    mechanized with the honest Anchors running the Lean verifier on the same tables, with
    per-proof slices and with one shared `H₃`, and with the real Clients' seeds
    (`anonymityNCRO_lean_num`, `anonymityNCSh_num`, `unlinkability*`, `*_seed`, §10.7). Left
    open: the modelling steps (SHAKE as a random oracle, AES as an ideal cipher), the hiding of
    `Com`, and the game-specific items of §10.3, §10.5 and §10.7 ("Open") and §10.6 ("What
    remains"). The PRP/PRF switching term is proved in the games as well:
    every privacy theorem above also holds with the cipher's rows uniform permutations read
    forward and backward (§10.4, `Privacy/PermRO.lean`, `Privacy/PermRA.lean`). The `*_shake` theorems, which take
    the fixed-record `HopHyps`, are unchanged: the random-oracle results replace them rather than
    discharge them.
- **Deterministic hypotheses**, per statement and witness (`ZKHyp`, `RunHyp`): the statement's
  evaluator is a system of degree `≤ d`, `1 ≤ d`, that the witness satisfies for every `chal1` and
  combination (for PomFRIT, for every instance the continuation picks: `RunHyp2`); `N_MASK ≤ 32`;
  `maskInvOk T` (proved for `CrtGen.tables`, `maskInvOk_tables`); correct interpolation
  `InterpOk d` (proved, `Interp.interpOk`); `BAVCComplete` and `CrtComplete` (the two correctness
  facts of the completeness theorem: proved, `Bridge.bavcComplete` for every `Δ`, and
  `Bridge.crtComplete` for `CrtGen.tables` when the label rows are corrected rows, as for all five
  relations; the general theorems keep them as hypotheses for arbitrary tables). For Moussaka
  (`anonymity_label_rows`), Ratatouille (`unlinkability_label_rows`) and PomFRIT
  (`blindness_lean`) all of them are proved, so these theorems assume only the tape hypotheses,
  hiding (Moussaka, Ratatouille) and the hash record's output lengths, the last proved for SHAKE
  (`*_shake`: `hashesWF_shake`, which also take the tape hypotheses from the hop hypotheses, so
  each proof's error is the sum of the named terms); Moussaka's
  zero-knowledge hypotheses are needed only for well-formed instances (`IssueRelW`, `RedeemRelW`:
  the lengths the C++ types fix, at most 64 Anchors).
- *Discharged:* `simulateRO_accept` assumes the simulated proof's run reaches `chal3`; all three
  conditions are proved (`ZK/SimAcceptFull.lean`): the format check and the reconstruction always
  (`simulate_checkFormat`, `simulate_reconstruct`), `Δ' ≠ 0` unless the simulator's `Δ` is `0`
  (`simulate_reaches`). So `simulateRO_accept'` assumes only `¬ HitZero`, and the simulated proof
  is accepted except with probability `≤ noHitProb + 1/|A| ≤ 2⁻¹¹³` (`pr_simulateRO_reject*`,
  `pr_simulateRO_reject_113`).
  `zk_sim`'s check that the programmed verifier accepts the simulated proof is therefore implied
  by these theorems on every run whose `Δ ≠ 0` (it stays in the executable as a smoke test; its
  other checks, `proveIdeal (tapeOf …) = prove` on the KAT inputs, the unprogrammed rejection and
  the ideal-tape proof's acceptance on a pseudorandom tape, are not instances of these theorems).
- **PomFRIT** (two-phase, delayed instance `h = hash_to_target(…, chal1, …)`):
  `Privacy.PomFRIT.ZeroKnowledge` is derived for the Lean prover with label rows
  (`lean_zeroKnowledge`) from the two-phase tape hypothesis `TapeHyp2` (`ZK/TwoPhase.lean`: the
  tape of a two-phase run, with step 1's output as a fallback block used only if no grinding
  answer is accepted), itself from the hop hypotheses `HopHyps2` (`ZK/TwoPhaseHops.lean`;
  `blindness_lean_shake`: `≤ 4(ε_rho + ε_grind + ε_abort + ε_bavc + ε_lab)`). In the ROM and
  ideal-cipher model (§10.2, `blindnessRO_lean_num`) no tape or hop hypothesis is left, and the
  collision terms are bounded (`δ(A) ≤ noHitProb + 2⁻¹²⁸`, `deltaRO_le`). Once picked, the instance `(pk, h)` is fixed, so the witness `r ‖ s`
  satisfies its system for every `chal1` and combination. `Spec/PomFRITLayout.lean` states the
  protocol on the label-row layout (5579-byte proofs; `hash_to_target` reads `ũ` and `d` at its
  offsets), and `Privacy.PomFRIT.blindness` holds for either layout.
- **Ratatouille:** `Spec.Ratatouille`'s proof sizes are a parameter (`Sizes.main`,
  `Sizes.labelRows`); `unlinkability_label_rows` is on the label-row layout. The spend statement
  has no key digest in its instance encoding (the spec's key is its public map), unlike
  `hash_instance`; zero knowledge does not depend on the encoding.


### 10.2 Privacy in the random-oracle and ideal-cipher model (`Privacy/ZeroKnowledgeRO.lean`, `ZK/ReadsRO.lean`, `Privacy/MoussakaRO.lean`, `Privacy/RatatouilleRO.lean`, `ZK/TwoPhaseRO.lean`, `ZK/TwoPhaseIC.lean`, `ZK/TwoPhaseReadsRO.lean`, `Privacy/PomFRITRO.lean`, `ZK/CollideRO.lean`, `ZK/CollideRO2.lean`, `Privacy/*Delta.lean`)

The `*_shake` privacy theorems go through `Privacy.ZeroKnowledge`, whose distinguishers see the
proof only, so they take the fixed-record hop hypotheses. Here the privacy adversary sees the
random tables too, and the four proofs of a Moussaka or Ratatouille game share them.

**The notion.** `ZeroKnowledgeRO R prove sim prog Adm ε`: the prover reads its randomness `ρ`,
its private table `g` (its slice of `H₃`: `H₃` at `wPrefix ‖ μ₁ ‖ ρ ‖ 3`) and the shared tables
`s`; the simulator outputs a proof from its coins only and programs the shared tables
(`prog x c s`); for every admissible distinguisher of `(output, g, s)` the two experiments are
`ε`-close. For the executable prover (`realRO`: `Prover.prove` with the record `recH` and the
ideal-cipher PRG `icPrg E`) and the simulator (`simulate`, `progRO` = `simTab`), with the shared
tables `Sh p = Tab2G p × Tab5F × Cipher` and admissibility `Budget p q₃ q₅ q_E` (reads of the
slice, of `H₅` and of the cipher bounded, each with the rest fixed and adaptively; `H₂³` free),
this is `zk_rom_ic_h23_num` (`zk_ro`, `lean_zeroKnowledgeRO`), with
`εRO q₃ q₅ q_E = q₃·2⁻¹²⁸ + 2⁻¹¹³ + 221·(4607 + q_E + 4607)·2⁻¹²⁸ + (q₅ + 1)·2⁻¹²⁸`.

**The model of a game.** One shared `Sh` (issuance and redemption, issuance and spend have the
same `qsDegree = 9`, hence the same `H₂³` key set), and one `H₃` slice per proof. A global `H₃`
restricted to the four slices is four independent tables when the four `(μ₁, wPrefix)` differ;
the games do not force this (two Clients with equal `(nf, r)`, probability `≤ 2⁻¹⁹²` for
independent nullifiers), so this modelling step carries the `ε_iv`-type term, on paper. (§10.5
states the games with one shared `H₃` instead; the term is not needed, and the step is not a
black-box consequence of the slice games.) The
adversary's guess sees all tables, with a budget `(q₃, q₅, q_E)`; **its interaction (responses,
Anchor Sets, digests, amounts) does not read the tables**: the zero-knowledge theorem is for a
statement fixed before the tables are drawn, and the redemption and spend statements are the
adversary's choices. (§10.3 lifts this for Moussaka and Ratatouille, with a zero-knowledge theorem
for statements chosen from the tables, and for PomFRIT, with a two-phase theorem for a continuation
that reads the tables after step 1, except `H₂³`, and then for an Issuer that reads `H₂³` too.) Each slot of the game has an output on the tables the game runs on, an
`H₂³` programming (identity for a real proof) and its slice; real proofs run on the tables
programmed by the slots simulated so far; a redemption or spend programs only if its round runs
(§6's rule), so that no programmed point depends on a world's hidden choice.

**The hybrids** (`hop_ro`). The proofs are replaced in game order (issuances, then redemptions or
spends): the statement of the replaced proof is then fixed by the coins of the simulated ones,
which do not read the tables. Step `j` applies the zero-knowledge theorem to the distinguisher
`(o, g, s) ↦ F γ o g (L γ s)`, `L γ` the earlier simulations' programming and `F γ` the rest of the
game (later proofs real), so its budget is the adversary's plus the reads of the later real
proofs (`624` `H₅` keys and `4607` cipher keys each: `realRO_rd5`, `realRO_rdE`) plus those of the
earlier programmings (`312`, `4607` each: `progRO_isProg`); the four budgets are at most
`(q₃, q₅ + 3·624, q_E + 3·4607)`. The step's real side is the real proof run on the programmed
tables `L γ s`, the zero-knowledge theorem's on the original ones; the difference is the explicit
collision term

    δ_j = Pr[ prove_j(ρ, g, L γ s) ≠ prove_j(ρ, g, s) ],

zero for the first proof. After the four steps the view is a function of the commitments, the
nullifiers, the simulator coins and the tables; hiding (for the reduction with the coins and the
tables fixed: a non-uniform reduction, which in an implementation samples the tables lazily) and
the exchange of the fresh nullifiers finish as before. For Ratatouille the programmed tables are a
function of the requests the Issuer sees and of the coins (`Vtab`; a simulation that produced no
proof programs independently of its statement, `progRO_of_error`, and otherwise the statement is
in the request, `issueReqC_mk`, `parse_toBytes`), so the simulated world is `Ratatouille.view` for
the Issuer `A.at (Vtab …) sl` and `simGame_iff`, `stage_ideal`, `idealGame_iff` apply verbatim.

**The bounds** (Lean, `#print axioms`: `propext`, `Classical.choice`, `Quot.sound`):

    Moussaka (anonymityRO_lean):     |Pr[W₀] − Pr[W₁]| ≤ 8·εRO(q₃, q₅ + 1872, q_E + 13821)
                                       + 2·δI₁ + Σ_b (δL b + δR b) + 2·εhide
    Ratatouille (unlinkabilityRO_lean): |Pr[W_{b₁,b₂}] − Pr[W_{b₁',b₂'}]| ≤ 8·εRO(…same…)
                                       + 2·δI₁ + Σ_w (δS₁ w + δS₂ w) + 2·εhide

`8·εRO(q₃, q₅ + 1872, q_E + 13821) = 8·(2⁻¹¹³ + 221·(23035 + q_E)·2⁻¹²⁸ +
(q₃ + q₅ + 1873)·2⁻¹²⁸)`, about `2⁻¹⁰²·⁷` plus `8·(q₃ + q₅ + 221·q_E)·2⁻¹²⁸`.

**The collision terms, in Lean** (`ZK/CollideRO.lean`, `Privacy/MoussakaDelta.lean`,
`Privacy/RatatouilleDelta.lean`). The real proof `j` reads `H₂³` only at its grinding points
`pre_j ‖ c ‖ 11` (`pre_j = chal2 ‖ qs_check ‖ ã`, computed without `H₂³`: `prove_recH_eq`, the
executable prover is hybrid H2's run at its slice's seed and `iv_pre` and the table's answers at
`pre_j`), and an earlier simulation `i` programs exactly the keys of the prefix block
`blk(outPre_i)` (`progRO_progAt`, `ProgAt`); so a collision needs `blk(pre_j)` to be a programmed
block (`realRO_progAt`, `realRO_ne_tail`). **The layout:** `preLen = 56 + 16 + 16·(d − 1) =
72 + 16·(d − 1)`, `200` bytes for `d = 9`, with `ã` in bytes `72 … 199`; the simulated opening
reconstructs (`reconstruct_openingOf`: right size, at most `T_OPEN` seeds, zero padding), so the
prefix recomputed from a simulated proof is `chal2 ‖ qs_check ‖ ã` with `|chal2 ‖ qs_check| = 72`
(`vPre_simAssemble`), and the last `16·(d − 1) = 128` bytes of the programmed block (`preTail`)
are the simulator's uniform `ã_i` — or, if the simulation produced no proof, the tail of the empty
prefix's block, a constant (`simTail`, `preTail_simBlk`). This is where the `2⁻¹⁰²⁴` comes from: a
`128`-byte uniform field.

*Issuance `1` against issuance `0`* (`deltaI1_le`, `deltaI1R_le`): `pre₁` does not depend on
issuance `0`'s coins, so `δI₁ ≤ noHitProb + 2⁻¹⁰²⁴` (`pr_simTail_eq_le`), as on paper (`0` for
Ratatouille with `T_init = 0`).

*Redemptions and spends* (`deltaL_le`, `deltaR_le`, `deltaS1R_le`, `deltaS2R_le`): their
statements are chosen after the adversary saw the simulated requests, so `pre_j` may depend on the
`ã_i`; but given the context, the earlier simulations' tails form a fixed set `T` of `n` values
(`n = 2` for the first redemption or spend, `3` for the second). **`pr_collide_zk`**: if
`blk(pre_j)` is programmed, then `preTail(blk(pre_j)) ∈ T`; unless the grinding outcome at `pre_j`
is bad (`GrindBad`, `≤ 2⁻¹¹³`: the answers at `pre_j` are uniform, `pr_grindBad_preRO`), the real
proof is produced and the verifier recomputes `pre_j` from it (`realRO_vPre`, from `hyb3_vPre`:
completeness of the recomputation on real proofs, which needs `Δ' ≠ 0` as well as a hit), so
`TailIn T` — "the tail of the prefix recomputed from the output is in `T`", reading `H₅` at `312`
and the cipher at `4607` keys and nothing of `H₃` — holds for the real proof; by zero knowledge
(`zk_ro`, a second application, at budget `(0, 312, 4607)`) its probability is at most the
simulated one plus `εRO(0, 312, 4607)`, and for the simulated proof the tail is its own uniform
`ã_j` (`≤ noHitProb + n·2⁻¹⁰²⁴`, `pr_simTail_mem`). So

    δ_j ≤ 2⁻¹¹³ + εRO(0, 312, 4607) + noHitProb + n·2⁻¹⁰²⁴,   n = 2, 3,

and `0` where the Client's check fails and no proof is computed. **Corrections to the paper
bound** `εRO(0, j·312, j·4607) + (j−1)·2⁻¹⁰²⁴ + 2·noHitProb`: (i) the completeness of the
recomputation needs `¬GrindBad` (no hit, *or* a zero lifted `Δ'`), so the grinding term is
`Pr[GrindBad] ≤ 2⁻¹¹³`, not `noHitProb` (the paper's argument misses the `Δ' = 0` event,
`≤ 2⁻¹¹⁴`); (ii) the simulated `ã_j` must avoid all `n` earlier tails, `n·2⁻¹⁰²⁴` (the paper's
`(j − 1)` undercounts by one); (iii) the distinguisher compares tails with the fixed `T`, so it
need not recompute the earlier prefixes: the budget is `(0, 312, 4607)` for every `j`; (iv) an
earlier simulation without a proof needs no extra `noHitProb`: its fixed tail is in `T`. All
differences are below `2⁻¹⁰⁰`.

    Moussaka (anonymityRO_lean_num):     |Pr[W₀] − Pr[W₁]| ≤ 8·εRO(q₃, q₅ + 1872, q_E + 13821)
        + 4·(2⁻¹¹³ + εRO(0, 312, 4607)) + 6·noHitProb + 12·2⁻¹⁰²⁴ + 2·εhide
    Ratatouille (unlinkabilityRO_lean_num): the same bound for any two worlds.

`εRO(0, 312, 4607) = 2⁻¹¹³ + (221·13821 + 313)·2⁻¹²⁸ ≈ 2⁻¹¹³ + 2⁻¹⁰⁶·⁵`, so the collision terms add
about `2⁻¹⁰⁴·⁴` (`noHitProb ≤ 2^{−2¹⁵}`, `noHitProb_le`); the total is about `2⁻¹⁰²·³` plus
`8·(q₃ + q₅ + 221·q_E)·2⁻¹²⁸` (`εhide` aside).

**PomFRIT.** The two-phase prover first needs its own theorem (`ZK/TwoPhaseRO.lean`,
`ZK/TwoPhaseIC.lean`, `zk2_rom_ic_h23_num`): the chain of `zk_rom_ic_h23` for `proveIdeal2`, the
simulator programming `H₂³` at the prefix it recomputes for the instance the continuation picks
from its step-1 output, and the fallback block switched to a uniform one in the hop that switches
the programmed points (both are needed only outside `GrindBad`), so the error is the single-phase
one. In a game, the instance of a session is chosen after the Issuer has seen **both** requests,
and the other session's request depends on the tables (its step 1 reads `H₅` and the cipher; a
simulated one reads the cipher for `chal1`): the theorem therefore lets the continuation read `H₅`
and the cipher at a bounded number of keys (not `H₃` of this proof, not `H₂³`), and these reads are
paid as the distinguisher's in the H4 and H6 hops. As a notion, `ZeroKnowledgeROS` (the simulator
may read the tables it does not program; `zk2_ro`, `lean_zeroKnowledgeROS2`), with the reads of
`ZK/TwoPhaseReadsRO.lean`.

*The game* (`Privacy/PomFRITRO.lean`). `realGameRO`: the spec's protocol on `Layout.labelRows`
(`realSession`, `issueRequestOf`, `finalizeIssue`) with the Lean prover on the shared tables and
each session's `H₃` slice (`leanProverRO`); `hash_to_target`, `XOF_seed` (the games draw its
outputs; §10.6 adds the seeds and the XOF) and the refresher commitment stay SHAKE, and the Issuer's key, messages and responses do
not read the tables (§10.3 lifts this, `H₂³` included), its guess sees all of them. World `true` is world `false` for the Issuer with
the sessions' roles exchanged (`A.swap`, `realGameRO_true`). Rewritten (`realGameRO_iff`, no
probability): a session's step 2 runs only if **both** responses pass the Clients' checks
(`bothOK`), since only then are the signatures revealed; this makes the simulators' programming
symmetric in the two sessions. Hybrids of world `false`:

* `G0 → G1` (`hop0`): `zk2_ro` for session `0`; the reduction runs session `1` for real (`624`
  `H₅`, `4607` cipher keys), and session `0`'s continuation reads session `1`'s step 1 (the same):
  `εRO(q₃, q₅ + 1248, q_E + 9214)`. No collision term: nothing was programmed before.
* `G1 → G2` (`hop1`): `zk2_ro` for session `1`; the reduction simulates session `0` and applies
  its programming, computed from session `1`'s output (`312` `H₅` keys, `3·4607` cipher keys), and
  session `1`'s continuation reads the simulated session `0`'s `chal1` (`4607` cipher keys):
  `εRO(q₃, q₅ + 312, q_E + 18428)`; plus the collision term
  `δ(A) = Pr[session 1, run for real, reads H₂³ differently on the tables session 0 programmed]`
  (`deltaRO`, `G1_G1'`). Session `0`'s programming depends on session `1`'s request (through
  `bothOK`), which the reduction reads off session `1`'s output.
* `G2` for `A` and for `A.swap` are equal (`G2_swap`): the requests `h ⊕ r` are re-parametrized as
  one-time pads and exchanged between the positions, with the slices (`swapS`, an involution); the
  simulated sessions, their signatures and their programming depend on the responses only through
  `bothOK`, which is symmetric (`bothOK_swap`, `simRun2_kcongr`, `progK_kcongr`).

    PomFRIT (blindnessRO_lean):  |Pr[W₀] − Pr[W₁]| ≤ 4·εRO(q₃, q₅ + 1248, q_E + 18428)
                                   + δ(A) + δ(A.swap)

(`blindnessRO`: the four errors at their own budgets.) `4·εRO(q₃, q₅ + 1248, q_E + 18428)` is about
`2⁻¹⁰³·⁴` plus `4·(q₃ + q₅ + 221·q_E)·2⁻¹²⁸`. *The collision term, in Lean*
(`ZK/CollideRO2.lean`, `Privacy/PomFRITDelta.lean`, `deltaRO_le`): `δ(A) ≤ noHitProb + 2⁻¹²⁸`.
Session `1`'s real run reads `H₂³` only at the grinding points of its instance's prefix `pre2`,
and none if its continuation stops (`realRun2_h23_congr`, from `real_form` and `hyb2'_none`). If
it continues, both responses passed the Clients' checks (`bothOK`, symmetric), so session `0`'s
continuation continues too (`kOf_isSome`, `realRun2_out1`: session `1`'s step-1 output is the one
its request was computed from); if session `0`'s grinding succeeded, the block it programs ends
with its uniform `ã₀` (`16` bytes for PomFRIT's `d = 2`, `preLen = 88`; `preTail_outPre2`).
Session `1`'s prefix is computed from its coins, the tables and session `0`'s *request*, which does
not read `ã₀` (`s1C_tail`), so the collision has probability `≤ 2⁻¹²⁸` and the failed grinding
`noHitProb` (`pr_simCoins_tail_le`). The paper's `≲ 2⁻¹²⁸ + 2⁻¹¹⁰` holds, with the second term
`noHitProb ≤ 2^{−2¹⁵}`: "the recomputation stops early" happens only if session `0`'s grinding
failed, since a stopping continuation of session `0` means session `1` stops too.

    PomFRIT (blindnessRO_lean_num):  |Pr[W₀] − Pr[W₁]| ≤ 4·εRO(q₃, q₅ + 1248, q_E + 18428)
                                       + 2·noHitProb + 2·2⁻¹²⁸

The two sessions'
`H₃` slices are independent tables when their `r` differ (`2⁻³⁶⁰` otherwise), as in the other two
games (§10.5: with one shared `H₃` no such term is needed).

### 10.3 Statements chosen from the tables (`Privacy/Resample.lean`, `ZK/IdealCipherP.lean`, `ZK/HopsPatch.lean`, `ZK/AdaptRO.lean`, `Privacy/AdaptiveRO.lean`, `Privacy/MoussakaRA.lean`, `Privacy/RatatouilleRA.lean`, `ZK/TwoPhaseAd.lean`, `Privacy/PomFRITRA.lean`, `Privacy/PomFRITRAGame.lean`, `ZK/CollideAd2.lean`, `Privacy/PomFRITRAH.lean`)

§10.2's games assume that the adversary's interaction does not read the tables, because `zk_ro`
is for a statement fixed before the tables are drawn. Here the statement and witness are chosen by
an adversary `S` that reads the tables first.

**The experiment** (`zk_adaptive`, `ZK/AdaptRO.lean`). The tables are `t = (g, s)`: the proof's
`H₃` slice and the shared `Sh = H₂³ × H₅ × E`. `S : t ↦ x` reads them adaptively at `s₃`, `s₂`,
`s₅`, `s_E` keys (`SReads`: query sets `Q t`, bounded per table, and **consistent**: a table that
agrees with `t` on `Q t` has the same queries and the same output; every deterministic query
algorithm is consistent, and the reduction below needs it: a reader that reads a key only when
the key is zero breaks it; for oracle computations it is a theorem, see *Interactions as oracle
computations* below). The real world runs `realRO` for `(stOf x, wOf x)` with a fresh `ρ` on
`t`; the simulated world outputs `simulate` from fresh coins and programs `H₂³` (`progRO`) on `t`.
A distinguisher sees `x`, the output and the (programmed) tables, with budget `(q₃, q₅, q_E)` and
`H₂³` free. `S` saw the tables before the programming, the distinguisher sees them after.

**The bound** (`εAd d q₃ q₅ q_E s₃ s₂ s₅ s_E`, `d` the prefix degree):

    εAd = εRO(q₃, q₅, q_E) + (221·s_E + s₅ + 1)·2⁻¹²⁸ + s₃·2⁻¹²⁸
          + [s₂ > 0]·(2⁻¹¹³ + εRO(0, 312, 4607) + (221·s_E + s₅ + 1)·2⁻¹²⁸
                      + 2·noHitProb + 2·s₂·2^(−8·16(d−1))).

- `s₃·2⁻¹²⁸`: the prover's randomness `ρ` is **16 bytes** (`proveSeedBytes = 16`, `Bytes 16`), not
  32, and the prover reads its slice only at `ρ` (`realRO_g3_congr`): `S` read the seed input
  with probability `≤ s₃·2⁻¹²⁸`.
- `(s₅ + 1)·2⁻¹²⁸`: H6. A sibling input among `S`'s `H₅` queries is a guess of the label-row pad
  `Θ` (`lab_rom_query_sGP`); `S`'s `H₅` reads cost what the distinguisher's cost (the `+ 1` is
  the prover's own `Θ = 0`, counted a second time).
- `221·s_E·2⁻¹²⁸`: H4. A hidden GGM node's key among `S`'s cipher queries (`IC.hopP`: each of the
  `≤ 221` hops costs `(4607 + q + |P|)·2⁻¹²⁸`).
- The `H₂³` term. `S` may read `H₂³` at the grinding points of the real proof before the proof
  exists, or at the block the simulator later programs. The simulated block's tail is the
  simulator's uniform `ã` (`16·(d − 1)` bytes, `128` for `d = 9`), or a constant if it produced
  no proof: `≤ noHitProb + s₂·2⁻¹⁰²⁴` (`pr_simBlk_mem`). For the real prover the tail is the
  real `ã`, which is pseudorandom; it is bounded by a second application of the theorem
  (`pr_preBlk_mem`, as `pr_collide_zk`): `≤ 2⁻¹¹³ + εROP(0, 312, 4607) + noHitProb + s₂·2⁻¹⁰²⁴`.
  So the expected `s₂·2^(−8·|ã|)` holds for the simulated block, and for the real one up to the
  second zero-knowledge error (`≈ 2⁻¹⁰⁶·⁴`). That is a limit of the proof, not an attack. Without
  `H₂³` reads (`s₂ = 0`) the term is `0`.

Numerically, `εAd(0, 0, 0; 0, 0, 0, 0) ≈ 2⁻¹⁰⁷·⁰ = εRO(0, 0, 0)`, and `≈ 2⁻¹⁰⁵·⁷` with
`s₂ = 1`. **There is no attack in the restriction**: an interaction that reads the tables costs
the same order as the guess's reads.

**The proof.**
1. *Lazy sampling of `S`'s view* (`Privacy.pr_resample`): the involution
   `(t, t') ↦ (mix (Q t) t t', mix (Q t) t' t)` of a uniform pair gives
   `Pr_t[F(S t, t)] = Pr_{t,t'}[F(S t, mix (Q t) t t')]`. With the outer `t` fixed, the statement
   is fixed and the tables are a fresh `t'` **patched** at `Q t` with `t`'s values
   (`pr_resample_le`, `abs_pr_resample_le`).
2. *A fixed statement, all four tables patched on fixed sets* (`zk_patched`). The `H₅` and cipher
   patches go through the chain. Every hop but H6 and H4 holds for every value of those tables
   (`zk_pre_h4Φ`, `joint2_tapeΦ`, `joint2_simΦ`: the hops with `H₅` any function `φ` of a uniform
   table). H6 runs with the `H₅` table patched (`joint2_h6P`, `lab_rom_hyp_sGP`), H4 with the
   cipher patched (`joint3_h4P`, `hide_rom_queryP`, `IC.punctureP`). Together this is
   `zk_rom_ic_h23P` and `zk_roP`, with error `εROP = εRO + 221·|P_E|·2⁻¹²⁸ + (|P₅| + 1)·2⁻¹²⁸`. The
   `H₃` and `H₂³` patches are handled at the top. The real proof on the patched tables is the one
   on the `H₅`/cipher-patched tables unless `ρ ∈ P₃` or its grinding block is patched
   (`realRO_g3_congr`, `realRO_progAt`). The simulator's programming commutes with the `H₂³` patch
   unless its block is patched (`progRO_patch2`).
3. *Assembly*: `zk_adaptive`. In the abstract form `Privacy.ZeroKnowledgeROA`
   (`Privacy/AdaptiveRO.lean`) the theorem is `lean_zeroKnowledgeROA`. There the statement is
   optional (`stw : X → Option (I × W)`): with none, no proof is produced and nothing is
   programmed.

**Collision terms with adaptive statements** (`pr_collide_adaptive`). A programming at blocks
whose tails lie in a fixed set `T` changes the real proof of a statement read off the tables with
probability `≤ s₃·2⁻¹²⁸ + 2⁻¹¹³ + εROP(0, 312, 4607; s₅, s_E) + noHitProb + |T|·2^(−8·16(d−1))`.

**Readers through a programming** (`SReads.comp_prog`, `CProg`, `progRO_cprog`). In a game, a later
proof's statement is read off the tables as earlier simulations programmed them. The simulator's
programming is consistent: its block, its answers and its `H₅` and cipher reads are determined by
the tables on those reads (`rdKeys_ic_congr`, `vIn5_ic_congr`). So the composed reader is
consistent, with `312` more `H₅` keys and `4607` more cipher keys per programming.

**Interactions as oracle computations** (`ROM/TableReads.lean`, `ROM/PrivacyReads.lean`).
`SReads` is a semantic hypothesis on a function of the tables. It cannot hold for every function:
the reader `t ↦ t.1` that outputs its whole slice has no consistent query sets of fewer than
`2¹²⁸` slice keys (`not_sReads_slice`), so a budget must be stated somewhere. Consistency, on the
other hand, is automatic once the reads are part of the computation's syntax:
- *The table oracle* (`TSpec n R m`): a VCVio `OracleSpec` with one query per key of the `n`
  `H₃` slices, of `H₂³` (prefixes of `m` bytes), of `H₅` and of the cipher (a whole row). An
  `OracleComp (TSpec n R m) X` has no sampling: it is a query tree, run on the tables by
  answering each query with the table's entry (`runT`, `TKey.read`).
- *Consistency by construction* (`runT_congr`): answers agreeing with the tables on the run's
  query log (`qlog`) give the same log and the same output. *The budget is syntactic*
  (`QBudget a₃ a₂ a₅ a_E`: VCVio's `IsQueryBoundP` for each slice and each shared table; closed
  under `pure`, `bind`, `mono`), and it bounds the log (`countP_qlog_le`).
- **`sReads_runT`**: an oracle computation within `QBudget a₃ a₂ a₅ a_E`, run with slice `j` and
  the shared tables taken from `t` and the other slices fixed, is `SReads p · a₃ a₂ a₅ a_E`, the
  read sets being the log's keys. With one slice: `sReads_runT₁`; the single-proof theorems
  `zk_adaptive_oc` and `lean_zeroKnowledgeROA_oc` (admissible readers `OCReader`).
- *The games* (`AdversaryOC` in each protocol's namespace): the interaction's stages are oracle
  computations over the four (PomFRIT: two) slices and the shared tables (Moussaka: the
  transcript at a pair of requests; Ratatouille: stage 1, and stage 2 at a request; PomFRIT: the
  key and messages, and the responses at a pair of requests), the rest as in `AdversaryRA`;
  `toRA` runs them on the game's tables, and `AdversaryOC.iBudget` derives `IBudget` from
  `QBudget` (for PomFRIT with `a₂ = 0`). **`anonymityOC_lean_num`**, **`unlinkabilityOC_lean_num`**,
  **`blindnessOC_lean_num`** and their `_perm` versions are the `*RA_lean_num(_perm)` bounds,
  unchanged, for `A.toRA`, with `QBudget` in place of `IBudget`. For a PomFRIT Issuer that
  queries `H₂³`, `sReadsP_runT` gives the joint budget `IBudgetH` from `QBudget` with any `a₂`
  (both slices read by one computation), and **`blindnessOCH_lean_num`** (`_perm`) is
  `blindnessRAH_lean_num` (`_perm`) for `A.toRA` (below).

The `*RA` theorems keep `IBudget` for functions of the tables: a consistent reader partitions the
tables into subcubes on which it is constant, and such a partition need not come from a query
tree with the same budget, so `SReads` is the more general form. VCVio's `IsQueryBoundP` lives in
`ROM/`, the only directory that imports VCVio.

**Moussaka with a table-reading interaction** (`Privacy/MoussakaRA.lean`).
- *The adversary* (`AdversaryRA`): its responses and choices read the four slices and the shared
  tables. Its budget `IBudget i₃ i₂ i₅ i_E` is per slice position, consistent.
- *The game* (`viewRA`): `viewRO` with the interaction fixed to the transcript (`fixT`,
  `transOf`), computed on the slices and on the tables after the issuances (programmed by the
  issuance simulations in the hybrids; `u = t` in the real game).
- *The issuance hops*: `hop_ro`, with the interaction's reads added to the distinguisher's budget
  (`F0A_budget`, `F1A_budget`).
- *The redemption hops*: `hop_roA` (`Privacy/AdaptiveRO.lean`: `hop_ro` with the statement read off
  the tables, the earlier programming allowed to depend on it), with `ZeroKnowledgeROA` for the
  transcript read through the two issuance programmings (`sReads_SxL`, `sReads_SxR`: budget
  `(i₃, i₂, i₅ + 624, i_E + 9214)`). Their collision terms are `deltaLA_le` and `deltaRA_le`, by
  `pr_collide_adaptive`.
- *The end*: the simulated world is a function of the commitments, the nullifiers, the coins, the
  slices and the tables (`simGameRA_iff`). Hiding and the nullifier exchange finish as before.

The bound:

    Moussaka (anonymityRA_lean_num):  |Pr[W₀] − Pr[W₁]| ≤
        4·εRO(i₃ + q₃, q₅ + i₅ + 1872, q_E + i_E + 13821)
      + 4·εAd(9; q₃, q₅ + 1248, q_E + 13821; i₃, i₂, i₅ + 624, i_E + 9214)
      + 4·(i₃·2⁻¹²⁸ + 2⁻¹¹³ + εROP(0, 312, 4607; i₅ + 624, i_E + 9214))
      + 6·noHitProb + 12·2⁻¹⁰²⁴ + 2·εhide.

This is about `2⁻¹⁰¹·⁹` without budgets (`2⁻¹⁰¹·⁶` if the interaction reads `H₂³`), against
`2⁻¹⁰²·³` for the table-oblivious interaction (`anonymityRO_lean_num`). The difference comes from
the issuance programmings' reads, which the redemption hops count as the reader's.

**Ratatouille with a table-reading interaction** (`Privacy/RatatouilleRA.lean`).
- *The adversary* (`AdversaryRA`): the interaction has two stages. Stage 1 (`msg₁`) is the two
  issuance responses and `d₁`, from the issuance requests. Stage 2 (`msg₂`) is the response to
  round 1 and `d₂`, also from round 1's request, so it reads spend 1's proof. Each stage reads the
  four slices and the shared tables, with the budget `IBudget i₃ i₂ i₅ i_E` per stage and slice
  position, consistently.
- *The game* (`viewRA`): `viewR` with the messages fixed to the transcript (`fixR`, `transR`).
  Each message reads the tables as the simulations before it programmed them: stage 1 after the
  issuances, stage 2 after the issuances and round 1 (round 1 programs only if it runs). The
  transcript computes round 1's request on the tables after the issuances, so it needs no
  provisional round: those tables do not depend on the spends' programming. With real slots
  nothing is programmed (`realGameRA`).
- *The issuance hops* (`hopI0RA`, `hopI1RA`): `hop_ro`, with both stages, the two real spends and
  the guess as the distinguisher. Each real proof is counted once (`rd5_viewRA`), so `H₅` is read
  at `2i₅ + q₅ + 3·624` keys and each slice at `2i₃ + q₃` keys.
- *Round 1's hop* (`hopS1RA`): `hop_roA` with `ZeroKnowledgeROA`. The statement (round 1's token
  and `d₁`) is read by stage 1 through the two issuance programmings (`sReads_Sx1`:
  `(i₃, i₂, i₅ + 624, i_E + 9214)`). Stage 2, which reads round 1's proof, is part of the
  distinguisher (`FS1A`, budget `(i₃ + q₃, i₅ + q₅ + 1248, i_E + q_E + 13821)`) with round 2's
  real proof and the guess.
- *Round 2's hop* (`hopS2RA`): the statement is read by the whole transcript (`Sx2`). Stage 2
  reads through round 1's programming, which depends on stage 1's messages (`SReads.bind`), so
  the budget is `(2i₃, 2i₂, 2i₅ + 1560, 2i_E + 23035)` (`sReads_Sx2`: `5·312`, `5·4607`).
- *The collision terms* (`deltaS1A_le`, `deltaS2A_le`) come from `pr_collide_adaptive`, at the
  readers' budgets. The statement for the bound is the one whenever round 1's or 2's token passes
  the Client's checks, which is when a real proof is computed.
- *The end* (`simGameRA_iff`): the simulated world is `Ratatouille.view` for the Issuer at fixed
  simulator coins, slices and tables (`atRA`). Its messages read `U₁ tr`, `U₂ tr rq`, the
  programmed tables as functions of the requests it has seen. The two Issuers give the same view
  (`view_congr`), since stage 2 matters only if round 1 runs. Hiding and the exchange of the
  nullifiers finish as before.

The bound:

    Ratatouille (unlinkabilityRA_lean_num):  |Pr[W(b₁, b₂)] − Pr[W(b₁', b₂')]| ≤
        4·εRO(2i₃ + q₃, q₅ + 2i₅ + 1872, q_E + 2i_E + 13821)
      + 2·εAd(9; i₃ + q₃, q₅ + i₅ + 1248, q_E + i_E + 13821; i₃, i₂, i₅ + 624, i_E + 9214)
      + 2·εAd(9; q₃, q₅ + 936, q_E + 13821; 2i₃, 2i₂, 2i₅ + 1560, 2i_E + 23035)
      + 6·i₃·2⁻¹²⁸ + 4·(2⁻¹¹³ + εROP(0, 312, 4607; 2i₅ + 1560, 2i_E + 23035))
      + 6·noHitProb + 12·2⁻¹⁰²⁴ + 2·εhide.

This is about `2⁻¹⁰¹·⁶` without budgets (`2⁻¹⁰¹·²` if the interaction reads `H₂³`), against
`2⁻¹⁰²·³` for the table-oblivious interaction (`unlinkabilityRO_lean_num`).

**Two-phase: a continuation that reads the tables after step 1** (`ZK/TwoPhaseAd.lean`). In
PomFRIT the instance of a session is picked by the Issuer's response, which sees the request
computed from the session's step-1 output `o₁`; an Issuer that reads the tables reads them at keys
that depend on `o₁`. So the two-phase statement is not "fixed, then patched" as in `zk_adaptive`:
the base statement and the witness prefix `r` are fixed (in PomFRIT they are the Client's), and
the continuation `K G3 G5 E : Cont2` reads, at each `o₁`, the proof's `H₃` slice at `q_k3` keys,
`H₅` at `q_k5` and the cipher at `q_kE` keys (`QK3 o₁ …`, …; each with the other tables fixed), and
not `H₂³`. A continuation that reads before step 1 (a statement chosen from the tables) is the
special case of key sets independent of `o₁`.

- *The runs read the continuation only at their step-1 output* (`proveIdeal2_kcongr`,
  `hyb2'_kcongr`, `hyb3'_kcongr`, `simRun2_kcongr'`, `outPre2_kcongr'`), which two tables agreeing
  on the keys read give the same: no resampling is needed.
- *H1* (`zk2_h1A`): `A v G3` (the hybrid-H2 run at the uniform seed `v`, the continuation at the
  slice `G3`) reads the slice at the distinguisher's keys and the continuation's keys at `out1 v`:
  `≤ (q₃ + q_k3)·2⁻¹²⁸` by `h3_rom_query`, whose reads may depend on `v`.
- *Programming, the recomputed points, the tape, the simulator* (`zk2_progA`, `zk2_keysA`,
  `zk2_tapeA`, `zk2_simA`): pointwise in the tables, so they hold for a continuation depending on
  them.
- *H6* (`zk2_h6A`, from `lab2_hyp`) and *H4* (`joint3_h4_2A`, from `hide_rom_query`, with
  `viewKeys2A`): the hops' query sets may depend on the output, so the continuation's keys at the
  output's step 1 are added to the distinguisher's.
- *Assembly*: `zk2_rom_ic_h23A`, `zk2_rom_ic_h23A_num`:
  `εRO(q₃ + q_k3, q₅ + q_k5, q_E + q_kE)`. In the games' form, **`zk2_adaptive`** (`Hyp2RA`: the
  continuation `K : Tab3 → Sh p → Cont2` at the slice and the unprogrammed shared tables, not
  reading `H₂³`, `Rd3`/`Rd5`/`RdE` at each `o₁`; `realRO2`, `simRO2`, `progRO2` with `K g`).

**PomFRIT with a table-reading Issuer** (`Privacy/PomFRITRA.lean`, `Privacy/PomFRITRAGame.lean`).
- *The Issuer* (`AdversaryRA`): `pk sl s`, `msg b sl s`, `respond t₀ t₁ i sl s` and the guess
  (`sl` the two slices, `s` the shared tables). At fixed tables it is an `AdversaryRO`
  (`AdversaryRA.at`). *The interaction's budget* (`IBudget i₃ i₅ i_E`): the key-and-messages stage
  (`keyOf`) and the response stage at every pair of requests (`respOf`) are consistent table
  readers (`SReads`) of each slice (the other fixed) and the shared tables, at most `i₃`, `i₅`,
  `i_E` keys and **no `H₂³` key**; so the Issuer at programmed tables is the Issuer at the original
  ones (`IBudget.at_h23`). `hash_to_target`, `XOF_seed` (drawn by the games; §10.6) and the refresher
  commitment stay SHAKE, outside the tables.
- *The game* (`realGameRA`): `realGameRO` for the Issuer at the game's slices and tables. *The
  hybrids*: `G0`, `G1`, `G1'`, `G2` of §10.2 at the Issuer at the original tables (`G0RA`, …).
- *Reads*: a function of the Issuer reads it only at its key and messages and at its responses to
  the requests the function computes (`kOf_congr`, `view2_congr`, `D0_congr`, `D1_congr`; with
  them fixed, `AdversaryRA.fix`: `kOf_fixR`, `kOf_fixS`, `D0_fix`, `D1_fix`). Session `0`'s
  continuation in hop 0 (`K0`) reads its slice at `2i₃`, `H₅` at `2i₅ + 624`, the cipher at
  `2i_E + 4607` keys (the key stage, session `1`'s step 1 for its request, the response stage:
  `hyp2RA_R`); session `1`'s in hop 1 (`K1`) at `2i₃`, `2i₅`, `2i_E + 4607` (`hyp2RA_S`); the
  reductions (`budget_D0A`, `budget_D1A`) add the same stages to `budget_D0`, `budget_D1`. The
  interaction is thus counted twice per hop, as the continuation's reads and as the reduction's,
  and the other session's step 1 once more than needed.
- *The hops*: `hop0RA`, `hop1RA` (`zk2_adaptive`); the collision term `deltaRA` (`deltaRO`'s
  event at the Issuer at the tables) `≤ noHitProb + 2⁻¹²⁸` (`deltaRA_le`, from `deltaRO_event'`:
  session `1`'s prefix is computed from the Issuer at the tables and session `0`'s request, neither
  of which reads session `0`'s `ã₀`); `G2RA_swap` (`swapS` at the Issuer at the tables, inverted
  by the one of the exchanged Issuer).

The bound:

    PomFRIT (blindnessRA_lean_num):  |Pr[W₀] − Pr[W₁]| ≤
        4·εRO(q₃ + 4i₃, q₅ + 4i₅ + 1872, q_E + 4i_E + 23035) + 2·noHitProb + 2·2⁻¹²⁸.

This is about `2⁻¹⁰³·²` without budgets, against `2⁻¹⁰³·⁴` for the table-oblivious interaction
(`blindnessRO_lean_num`); hop 0 alone is `εRO(q₃ + 4i₃, q₅ + 4i₅ + 1872, q_E + 4i_E + 13821)`,
hop 1 `εRO(q₃ + 4i₃, q₅ + 4i₅ + 312, q_E + 4i_E + 23035)`.

**PomFRIT with an Issuer that also reads `H₂³`** (`ZK/CollideAd2.lean`, `Privacy/PomFRITRAH.lean`).

*Why `blindnessRA` needs `a₂ = 0`.* Its hybrids are those of §10.2 at the Issuer at the original
tables, and that is sound only because the Issuer at the programmed tables is the Issuer at the
original ones (`IBudget.at_h23`). With `H₂³` reads that fails in three places: (1) the two-phase
simulator programs `H₂³` at the zero-prefix block when its continuation stops (`simTab2` at
`outPre2 = ∅`), and the stop decision could read that block; (2) the programming hop
(`zk2_progA`, exact by `pr_program_eq`) needs the programmed points to be independent of
`H₂³`, while a continuation that read the real prefix's block makes them depend on it; (3) the
reductions see only programmed tables and would compute the other session's responses on them.

*What is proved instead.* Nothing is changed in the hybrids or the simulator: the interaction's
`H₂³` reads are taken out of the game **before** the hybrids, and the existing theorem is applied
to an Issuer that does not read `H₂³`.
- *The budget* (`IBudgetH i₃ i₂ i₅ i_E`): the key stage and the response stage at every pair of
  requests are consistent readers of both slices and the shared tables **jointly** (`SReadsP`),
  at most `i₃` keys of each slice and `i₂`, `i₅`, `i_E` keys of `H₂³`, `H₅`, the cipher. The
  per-slice form of `IBudget` is not enough: the guess below recomputes the interaction's `H₂³`
  read set, and has to do so consistently as either slice varies.
- *Lazy sampling of `H₂³`* (`pr_resampleC`, `Privacy.pr_resample` with the reader depending on
  the other coins; `pr_G0RA_resample`): with the tapes, `H₅` and the cipher fixed, the interaction
  at the actual requests (step 1 does not read `H₂³`) reads `H₂³` at a set `Q(Γ)` of at most `2i₂`
  keys, consistently. So world `false` is the game in which the interaction reads an independent
  table `Γ`, and the sessions and the guess run on `H₂³` patched with `Γ` on `Q(Γ)`.
- *The substituted Issuer* (`AdversaryRA.subst`): its interaction reads `Γ` in place of `H₂³`
  (`IBudget.subst`: no `H₂³` key), and its guess patches the `H₂³` table it sees with `Γ` at the
  interaction's read set, which it recomputes from the requests it is shown and the tables
  (`GBudget.subst`: `(q₃ + 2i₃, q₅ + 2i₅, q_E + 2i_E)`). Its real game differs from the resampled
  one only in that its sessions run on the unpatched table (`G0_at_iff_subst`), i.e. unless a real
  session reads `H₂³` at a patched key (`badH`). `blindnessRA_lean_numG` applies to it for every
  `Γ`; world `true` is world `false` for the exchanged Issuer, with the exchanged read sets
  (`swap_subst`, `IBudgetH.swap`).
- *The collision term* (`pr_bad0H`, `pr_bad1H`, from `ZK.Sim.pr_tail2A`). A real session reads
  `H₂³` only at the grinding points of its prefix `chal2 ‖ qs_check ‖ ã` (`realRun2_h23_congr`),
  so `badH` means that the interaction's read set meets the session's grinding block
  (`run_patch_mem`). `pr_tail2A` bounds this for a two-phase run whose continuation `K` does not
  read `H₂³` and a read set `Qf` computed from step 1's output: unless the grinding outcome at
  the real prefix is bad (`2⁻¹¹³`), the block is the one recomputed from the proof
  (`realRun2_outPre2`); by two-phase zero knowledge (`ZK2ARow.zk2A`, the distinguisher
  `tailEv2`, which reads the continuation's and the read set's keys and the recomputation's `312`
  `H₅` and `4607` cipher keys) it meets `Qf` with the simulated proof's probability, and the
  simulated block's tail is the simulator's uniform `ã` (16 bytes for `d = 2`), on which `Qf`
  does not depend (`pr_simCoins_tail_mem`, `simRun2_o1_tail`): `≤ |Qf|·2⁻¹²⁸`. It is applied to
  session `0` with its continuation `K0` and to session `1` with `K1R` (session `0` real,
  `hyp2RA_R1`), both at the substituted Issuer, with the read sets `qf0`, `qf1`:

      εcol = 2⁻¹¹³ + εRO(6i₃, 6i₅ + 2184, 6i_E + 18428) + 2i₂·2⁻¹²⁸   per session and world

(`εRO` for function rows; for a general row type the error `εz` of §10.4).

The bound (`blindnessRAH_lean_num`; `blindnessRAH_lean_numG` for every row type,
`blindnessRAH_lean_num_perm` with `εROPm`):

    PomFRIT (blindnessRAH_lean_num):  |Pr[W₀] − Pr[W₁]| ≤
        4·εRO(q₃ + 6i₃, q₅ + 6i₅ + 1872, q_E + 6i_E + 23035) + 2·noHitProb + 2·2⁻¹²⁸
      + [i₂ > 0]·4·(2⁻¹¹³ + εRO(6i₃, 6i₅ + 2184, 6i_E + 18428) + 2i₂·2⁻¹²⁸).

This is about `2⁻¹⁰²·³` with `i₂ ≥ 1` and the other budgets zero (the collision part alone about
`2⁻¹⁰³·⁴`), against `2⁻¹⁰³·²` for `blindnessRA_lean_num`. The interaction's reads count six times
in the main term (twice more than in `blindnessRA`: the substituted Issuer's guess recomputes
them), so for `i₂ = 0` `blindnessRA_lean_num` is the better bound. The collision term matches
Moussaka's and Ratatouille's `H₂³` terms (`h23Term` in `εAd`): a second zero-knowledge
application and `2⁻¹¹³` for the real prefix, the read count times `2^(−8·|ã|)` for the simulated
one; it uses no `noHitProb` because the event requires a produced proof.

**Open.** (Done since earlier versions of this list: a PomFRIT interaction that reads `H₂³`,
above, under the joint budget; consistency for interactions written as oracle computations, above;
AES as random permutations, §10.4; one shared `H₃`, §10.5, the Issuer that reads `H₂³`
included.)
- *`H₂³` reads under per-slice budgets* (PomFRIT, `IBudget` with `i₂ > 0`): not covered; the
  substituted Issuer's guess must recompute the interaction's `H₂³` reads jointly (`IBudgetH`).
- *A two-phase zero-knowledge theorem with a continuation that reads `H₂³`* (`zk2_adaptive`
  without `h2`): not stated; it would need the simulator change and the collision terms listed
  above, and the game does not need it.
- An adaptive base statement or witness prefix in `zk2_adaptive` (not needed for PomFRIT).
- *The consistency of an interaction given as a bare function of the tables* (`SReads`): a
  hypothesis, necessarily so for the budget (`not_sReads_slice`); for one written as an oracle
  computation it is a theorem (`*OC_lean_num`, `*OC_lean_num_perm`). A randomized interaction is
  a mixture of deterministic ones (its coins fixed, as the games' requests are). The guess's
  budget (`Rd3`, `Rd5`, `RdE`, `Budget`) is still semantic; it needs no consistency (it is only an
  upper bound on reads, by query sets that may depend on the tables).

### 10.4 The privacy games with AES as random permutations (`ZK/ReadsRO.lean`, `ZK/ReadsROPerm.lean`, `ZK/TwoPhasePerm.lean`, `ZK/IdealCipherPermP.lean`, `ZK/HopsPatchPerm.lean`, `Privacy/PermRO.lean`, `Privacy/PermRA.lean`)

§10.2 and §10.3 model AES as an ideal cipher whose rows are uniform *functions* (the PRF view).
The single-proof theorem with uniform *permutations* (`lean_zeroKnowledgeRO_perm`, §10.1) left the
games on function rows. Here every game is stated **once**, for an abstract type of cipher rows,
and instantiated twice.

**The abstraction.**
- *Cipher rows* (`CipherRow R`, `ZK/ReadsRO.lean`): the shared tables are
  `ShG R p = Tab2G p × Tab5F × (Blk → R)`, one row per key, read as a function of the blocks by
  `CipherRow.row` (`rowFn E : Cipher` the whole table). The executable prover, the verifier and the
  simulator's recomputation run with the CTR PRG of the rows (`icPrg (rowFn s.2.2)`); the
  adversary sees and reads the table itself. Instances: **function rows** `Blk → Blk`
  (`CipherRow.fn`, `row = id`, `Sh p = ShG (Blk → Blk) p`) and **permutation rows**
  `Equiv.Perm Blk` (`CipherRow.perm`, `ShPm p`), where reading a row at a key reads the whole
  permutation: forward and inverse queries.
- *The read algebra* (`Rd5`, `RdE`, `Rd3`, `IsProg`, `Budget`, `ProgAt`, `SReads`, `CProg`, `Tb`,
  `mixT`, `patch5E`, `patch2`, …) and the prover's, the simulator's and the programming's reads
  (`realROb_rdE`, `realROb_rd5`, `progRO_isProg`, `realRO2_rdE`, `simRO2_rdE`, `progRO2_isProg`,
  `step1_rdE`, `outPre_rdE`, `progRO_cprog`, …) are stated for any `R`: they only use that a
  table agreeing at a key has the same row there (`rowFn_congr`).
- *Zero knowledge as structure*: the theorems each game uses are classes on `R`, whose fields are
  the theorems in the games' form:
  `ZKRow R` (`zk_ro`, an error `εz p q₃ q₅ q_E`), `ZK2Row R` (`zk2_ro`, the same error at the
  continuation's reads added), `ZK2ARow R` (`zk2_adaptive`), `ZKPRow R` (`zk_roP`, an error
  `εP p q₃ q₅ q_E |P5| |PE|` with the `H₅` and cipher tables patched on fixed sets; `h23G`,
  `εAdG` the errors of §10.3 with it). Function rows: `ZKRow.fn` (`εRO`), `ZK2Row.fn`,
  `ZK2ARow.fn`, `ZKPRow.fn` (`εROP`); permutation rows: `ZKRow.perm` (`εROPm`),
  `ZK2Row.perm`, `ZK2ARow.perm`, `ZKPRow.perm` (`εROPmP`).
- *The games* (`Privacy/MoussakaRO.lean`, `RatatouilleRO.lean`, `PomFRITRO.lean`, the `*Delta`
  and `*RA` files, `ZK/CollideRO.lean`, `ZK/AdaptRO.lean`, `ZK/TwoPhaseAd.lean`) take the row type
  as a parameter of the adversary (`AdversaryRO R`, `AdversaryRA R`) and of the tables, and the
  Lean-prover bounds are proved once (`*_leanG`, `*_lean_numG`); the theorems of §10.2 and §10.3
  (`anonymityRO_lean_num`, …, with their statements unchanged but for `AdversaryRO (Blk → Blk)`)
  are their instances at function rows. Moussaka's and Ratatouille's generic bounds split the
  issuance and redemption/spend errors (`4·εz(pI; …) + 4·εz(pR; …)`), since the permutation
  error depends on the parameters through `nHi` and `switchEps`.

**The permutation-row zero-knowledge theorems** (new for this section).
- *Two phases* (`ZK/TwoPhasePerm.lean`): `zk2_rom_ic_h23_perm`, `zk2_rom_ic_h23_num_perm`, error
  `εROPm p q₃ (q₅ + q_k5) (q_E + q_kE)`; with the continuation reading the tables after step 1,
  `zk2_rom_ic_h23A_perm`, `zk2_rom_ic_h23A_num_perm`, error
  `εROPm p (q₃ + q_k3) (q₅ + q_k5) (q_E + q_kE)`. As for one proof, the hops before and after H4
  hold for every cipher (`zk2_pre_h4`, `zk2_post_h4`, `zk2_pre_h4A`, `zk2_post_h4A` at
  `icPrg (cf π)`), and H4 is `hide_rom_query_perm` applied to the view at the rows of `π`
  (`viewIC2Pm`, `viewIC2APm`): its congruence (`viewIC2Pm_congr`, `viewIC2APm_congr`) changes the
  distinguisher's permutation table, then the view's rows (`viewIC2_congr`, `viewIC2A_congr` with
  a constant continuation), then the continuation (for `zk2A` only at the run's step-1 output,
  `viewIC2A_kcongr`). In the games' form: `zk2_ro_perm`, `zk2_adaptive_perm`.
- *The patched H4 with permutation rows* (`ZK/IdealCipherPermP.lean`, `ZK/HopsPatchPerm.lean`):
  the table `IC.patchT PE WE π` (fixed permutations at the keys `PE`, uniform elsewhere) is again
  a table of independent uniform permutations off `PE`; in the GGM hop the node's value is fresh in
  its parent's (replaced) permutation, and programming the table at it is perfect unless it is a
  candidate or in `PE` (`IC.hopPmP`, `(N + q + |PE|)/(|K| − s)`; `IC.puncturePmP`,
  `IC.experPmP_empty`, `IC.experPmP_close`). With the switching term unchanged
  (`exper_finalPmP`: the replacement permutations are fresh), `hide_rom_query_permP`:
  `221·(4607 + q + |PE|)/(2¹²⁸ − (nHi + 1)) + switchEps`. The chain (`joint3_h4P_perm`,
  `zk_rom_ic_h23P_perm`: `zk_pre_h4Φ`, `zk_post_h4P` for every cipher) gives `zk_roP_perm` with

      εROPmP p q₃ q₅ q_E n₅ n_E = q₃·2⁻¹²⁸ + 2⁻¹¹³ + 221·(4607 + q_E + 4607 + n_E)/(2¹²⁸ − (nHi + 1))
                                   + switchEps p + (q₅ + 1)·2⁻¹²⁸ + (n₅ + 1)·2⁻¹²⁸,

  and `εAdPm`, `h23Pm` (§10.3's `εAd`, `h23Term` with `εROPmP`).

**The privacy theorems with AES as random permutations.**

    Moussaka (anonymityRO_lean_num_perm):  |Pr[W₀] − Pr[W₁]| ≤
        4·εROPm(pI; q₃, q₅ + 1872, q_E + 13821) + 4·εROPm(pR; q₃, q₅ + 1872, q_E + 13821)
      + 4·(2⁻¹¹³ + εROPm(pR; 0, 312, 4607)) + 6·noHitProb + 12·2⁻¹⁰²⁴ + 2·εhide
    Ratatouille (unlinkabilityRO_lean_num_perm): the same with pS for pR
    PomFRIT (blindnessRO_lean_num_perm):  4·εROPm(pP; q₃, q₅ + 1248, q_E + 18428)
      + 2·noHitProb + 2·2⁻¹²⁸

    Moussaka (anonymityRA_lean_num_perm):
        4·εROPm(pI; i₃ + q₃, q₅ + i₅ + 1872, q_E + i_E + 13821)
      + 4·εAdPm(pR; 9; q₃, q₅ + 1248, q_E + 13821; i₃, i₂, i₅ + 624, i_E + 9214)
      + 4·(i₃·2⁻¹²⁸ + 2⁻¹¹³ + εROPmP(pR; 0, 312, 4607; i₅ + 624, i_E + 9214))
      + 6·noHitProb + 12·2⁻¹⁰²⁴ + 2·εhide
    Ratatouille (unlinkabilityRA_lean_num_perm):
        4·εROPm(pI; 2i₃ + q₃, q₅ + 2i₅ + 1872, q_E + 2i_E + 13821)
      + 2·εAdPm(pS; 9; i₃ + q₃, q₅ + i₅ + 1248, q_E + i_E + 13821; i₃, i₂, i₅ + 624, i_E + 9214)
      + 2·εAdPm(pS; 9; q₃, q₅ + 936, q_E + 13821; 2i₃, 2i₂, 2i₅ + 1560, 2i_E + 23035)
      + 6·i₃·2⁻¹²⁸ + 4·(2⁻¹¹³ + εROPmP(pS; 0, 312, 4607; 2i₅ + 1560, 2i_E + 23035))
      + 6·noHitProb + 12·2⁻¹⁰²⁴ + 2·εhide
    PomFRIT (blindnessRA_lean_num_perm):
        4·εROPm(pP; q₃ + 4i₃, q₅ + 4i₅ + 1872, q_E + 4i_E + 23035) + 2·noHitProb + 2·2⁻¹²⁸
    PomFRIT (blindnessRAH_lean_num_perm, the interaction reading H₂³):
        4·εROPm(pP; q₃ + 6i₃, q₅ + 6i₅ + 1872, q_E + 6i_E + 23035) + 2·noHitProb + 2·2⁻¹²⁸
      + [i₂ > 0]·4·(2⁻¹¹³ + εROPm(pP; 6i₃, 6i₅ + 2184, 6i_E + 18428) + 2i₂·2⁻¹²⁸)

Each is the function-row bound with every `εRO` (`εROP`, `εAd`) replaced by its permutation-row
counterpart: the hop denominator `2¹²⁸ − (nHi + 1)` for `2¹²⁸` (`nHi = 1`), and one switching term
`switchEps ≤ 2⁻¹¹³·²` per error term. Without budgets the RO bounds are about `2⁻¹⁰²·³`
(Moussaka, Ratatouille) and `2⁻¹⁰³·⁴` (PomFRIT), within `0.01` bits of the function-row bounds.

**What did not need porting.** Nothing in the games, the collision bounds (`pr_collide_zk`,
`pr_collide_adaptive`, `deltaRO_le`, `deltaRA_le`) or the adaptive layer uses that the rows are
functions: they read the cipher through key sets, and a whole permutation row is a key's entry.
The only permutation-specific steps are the H4 hops above (plain, two-phase, two-phase with an
adaptive continuation, patched), each the function-row chain around `hide_rom_query_perm` or
`hide_rom_query_permP`.

### 10.5 One shared `H₃` (`ZK/SharedH3.lean`, `ZK/SharedH3Two.lean`, `ZK/SharedH3RA.lean`, `ZK/SharedH3One.lean`, `Privacy/SharedH3RO.lean`, `Privacy/SharedH3PomFRIT.lean`, `Privacy/SharedH3RA.lean`, `Privacy/SharedH3PomFRITRA.lean`, `ZK/SharedH3Tail.lean`, `Privacy/SharedH3PomFRITRAH.lean`, `ROM/SharedH3Reads.lean`)

§10.2–§10.4 give every proof of a game its own independent `H₃` slice. The scheme has one `H₃`.

**What the code hashes.** The seed and `iv_pre` are `H₃(witness_prefix ‖ μ ‖ ρ ‖ 3)`
(`voleith.hpp:168-185`; Lean `Prover.voleGen`, `Hs.hash .h3 ((wPrefix ++ mu1 ++ rho).push 3)`):
the per-proof **prefix** is `wPrefix ‖ μ₁` (the whole witness for Moussaka and Ratatouille,
`WITNESS_PREFIX_BYTES = WITNESS_BYTES`; PomFRIT's `r`, `uov::M` bytes, with the delayed `μ` of the
refresher commitment) and the fresh per-proof randomness is the 16-byte `ρ` (`ProveSeed`; the
tree `iv` is derived, `iv = H₄(iv_pre ‖ μ)`, so there is no separate random IV or salt). A
slice is `ρ ↦ H₃(prefix ‖ ρ ‖ 3)`; two proofs share a slice iff they share the prefix (Moussaka,
Ratatouille: the two Clients' `(nf, r)`, or the tokens' openings; PomFRIT: the two sessions' `r`
and refresher commitments). Issuance and redemption (spend) prefixes have different lengths
(`256 + 32` vs `343 + 32`; `240 + 32` vs `847 + 32` bytes), so their inputs never meet.

**The model.** `H₃` on the seed inputs `x ‖ ρ ‖ 3` with `|x| < 1024` is a uniform table indexed by
`(x, ρ)` (`seedEnc` is injective, `seedEnc_injective`). It is put into the shared tables: each
cipher row also carries `H₃`'s column at that `ρ` (`RowH R = R × (Pre → Bytes 32)`, `Blk = Bytes 16`
is `ρ`'s type; the prover, verifier and simulator read a row as its cipher part, `CipherRow.rowH`).
A proof's slice is the column at its prefix (`h3At s (preKey (wPrefix ‖ μ₁))`), and the shared
provers (`leanPISh`, `leanPRSh`, `leanPIRSh`, `leanPSRSh`, PomFRIT's sessions in `realGameSh`)
compute their prefix from the witness and statement they are called with, so the redemption and
spend prefixes, chosen through the adversary's choices, are those of the code. `prove_recOne`: the
executable prover with the record that has **one** `H₃` on every seed input (`recOne`) is the
shared prover. The adversary reads `H₃` through rows: a read of `H₃(x ‖ ρ ‖ 3)` is a read of row
`ρ`, counted with its cipher queries in `q_E` (`i_E` for an interaction); the games' slot slices are
still drawn but read by no prover (Moussaka, Ratatouille: the guess may read them, for free;
PomFRIT and the table-reading interactions: no slice reads, `SliceFree`, `IBudget 0 …`,
`GBudget 0 …`).

**Why the slice games do not give this directly.** The paper's step is: the restrictions of one
`H₃` to the four prefixes are four independent tables when the prefixes differ, up to `ε_iv`
(`≤ 2⁻¹⁹²`, two Clients with equal nullifiers; PomFRIT `2⁻³⁶⁰`). That is true, but it does not turn a
shared-`H₃` adversary into a slice-model one: the reduction would have to answer the adversary's
`H₃` queries at the proofs' prefixes from the slices, and the prefixes contain the Clients'
secrets (`r`, `nf`, the refresher), which the reduction does not know, while an unbounded
adversary may (`Com` is only computationally hiding). And the redemption and spend prefixes are
chosen by the adversary after it has read `H₃`, possibly at those very prefixes (a "future
prefix" read), so "the four restrictions" are not restrictions to four fixed inputs. The
mechanized route avoids both: the hybrid argument runs on the shared tables, and each hop
re-samples the replaced proof's column.

**Zero knowledge with one shared `H₃`.**
- *Statement fixed* (`ZeroKnowledgeRO.shared`): write the tables as the column at the proof's
  prefix overwritten by an independent uniform slice (`pr_setK`: this keeps them uniform); then the
  real proof reads an independent slice, and the slice prover's theorem applies to the
  distinguisher that writes it into the column (`dCol`: its row reads are slice reads, budget
  `(q_E, q₅, q_E)`). No hypothesis on the prefixes: another proof with the same prefix is part of
  the distinguisher and reads this slice at its own `ρ` (one row each, `rdE_h3At`: every real
  proof reads `4607 + 1` rows), which `εRO`'s `q₃·2⁻¹²⁸` term pays for. This is where the birthday
  bound over the proofs' `ρ` sits: `2⁻¹²⁸` per pair of proofs, within the main term.
- *Two phases* (`zk2_sharedA`, `zk2_shared`): the same, the continuation reading the shared tables
  at bounded keys, the replaced column included: in PomFRIT's hop 0, session `0`'s continuation runs
  session `1`'s step 1, which reads session `0`'s column when the two prefixes coincide. After the
  re-sampling this continuation reads the proof's own slice, so the adaptive two-phase theorem
  (`zk2_adaptive`, `ZK2ARow`) is used even for the non-adaptive PomFRIT game.
- *Statement chosen from the tables* (`ZeroKnowledgeROA.shared`): the prefix is known only after
  the reader ran, and the reader may have read that column. Exchange the independent slice with
  the column at the chosen prefix, **off the rows the reader read** (`swapOff`): for a reader with
  consistent read sets this is a measure-preserving involution that keeps the reader's output and
  reads (`agT_swapOff`); afterwards the real proof's slice agrees with the independent one at
  every row the reader did not read, so the two experiments agree unless the fresh `ρ` is one of
  the reader's `s_E` rows (`pr_mem_rows_le`), and the simulated side is unchanged (`swapOff_map`:
  the programming commutes with the exchange). Error `ε(q_E, q₅, q_E) + s_E·2⁻¹²⁸`, for readers and
  distinguishers that read no slot slice (`SReads p · 0 s₂ s₅ s_E`, `Budget p 0 q₅ q_E`).
  `pr_h3At_sliceA`: the same for the games' collision events.
- With the `H₃` columns as extra row data the slice prover keeps its theorems
  (`ZKRow.rowH`, `ZK2ARow.rowH`, `ZKPRow.rowH`, by averaging over the columns), so function and
  permutation rows are covered by the same statements (`εz (RowH R) = εz R`).

**The bounds** (all `#print axioms`: `propext`, `Classical.choice`, `Quot.sound`):

    Moussaka (anonymitySh_num):       8·εRO(q_E + 13824, q₅ + 1872, q_E + 13824)
                                       + 4·(2⁻¹¹³ + εRO(0, 312, 4607)) + 6·noHitProb + 12·2⁻¹⁰²⁴ + 2·εhide
    Ratatouille (unlinkabilitySh_num): the same
    PomFRIT (blindnessSh_num):        4·εRO(q_E + 18428, q₅ + 1248, q_E + 18428) + 2·noHitProb + 2·2⁻¹²⁸

    Moussaka, table-reading interaction (anonymityRASh_num):
        4·εRO(q_E + i_E + 13824, q₅ + i₅ + 1872, q_E + i_E + 13824)
      + 4·εAd(9; q_E + 13822, q₅ + 1248, q_E + 13822; 0, i₂, i₅ + 624, i_E + 9214)
      + 4·(2⁻¹¹³ + εROP(0, 312, 4607; i₅ + 624, i_E + 9214)) + 8·(i_E + 9214)·2⁻¹²⁸
      + 6·noHitProb + 12·2⁻¹⁰²⁴ + 2·εhide
    Ratatouille (unlinkabilityRASh_num):
        4·εRO(q_E + 2i_E + 13824, q₅ + 2i₅ + 1872, q_E + 2i_E + 13824)
      + 2·εAd(9; q_E + i_E + 13822, q₅ + i₅ + 1248, q_E + i_E + 13822; 0, i₂, i₅ + 624, i_E + 9214)
      + 2·εAd(9; q_E + 13821, q₅ + 936, q_E + 13821; 0, 2i₂, 2i₅ + 1560, 2i_E + 23035)
      + 4·(2⁻¹¹³ + εROP(0, 312, 4607; 2i₅ + 1560, 2i_E + 23035))
      + 4·(i_E + 9214)·2⁻¹²⁸ + 4·(2i_E + 23035)·2⁻¹²⁸ + 6·noHitProb + 12·2⁻¹⁰²⁴ + 2·εhide
    PomFRIT (blindnessRASh_num):
        4·εRO(q_E + 4i_E + 23035, q₅ + 4i₅ + 1872, q_E + 4i_E + 23035) + 2·noHitProb + 2·2⁻¹²⁸

and the same for interactions written as oracle computations (`anonymityOCSh_num`,
`unlinkabilityOCSh_num`, `blindnessOCSh_num`: zero slice queries) and with permutation rows
(`*_num_perm`: `εROPm`, `εAdPm`, `εROPmP`).

**PomFRIT with an Issuer that also reads `H₂³`** (`ZK/SharedH3Tail.lean`,
`Privacy/SharedH3PomFRITRAH.lean`). §10.3's proof (`blindnessRAH_lean_num`) redone on the shared
tables, for an Issuer whose joint budget reads no slot slice (`IBudgetH 0 i₂ i₅ i_E`; its `H₃`
reads are row reads, in `i_E`) and whose guess reads none (`GBudget 0 q₅ q_E`):
- *The game* is `realGameRASh` (§10.5's PomFRIT game with a table-reading Issuer); such an Issuer
  is the same at every slot slices (`AdversaryRA.at_freeH`), so the shared game is the slice game
  at the tape `τR z` whose sessions' slices are their columns (`realGameRASh_iff'`).
- *Lazy sampling of `H₂³`* (`pr_G0RASh_resample`): `τR` reads only the rows, so on the coins other
  than `H₂³` it is a map `τC`, and `pr_resampleC` applies to the interaction at `τC c`. World
  `false` is again the game of the substituted Issuer `A.subst Γ` up to `badH` (a real session
  reads `H₂³` at a patched key), and `A.subst Γ` reads no slot slice and no `H₂³`, so
  `blindnessRASh_numG` applies to it (guess budget `(0, q₅ + 2i₅, q_E + 2i_E)`).
- *The collision term* (`pr_bad0HSh`, `pr_bad1HSh`): the session's run reads its column at its
  prefix, the continuation and the read set read the shared tables, the other session's column
  through one row (`rdE_h3At`) and possibly the session's own column (equal prefixes).
  **`pr_tail2Sh`** is `pr_tail2A` for this prover: overwrite the session's column with an
  independent slice (`pr_prod_setK`; the tables stay uniform), after which the run reads the slice
  and the continuation's and read set's reads of it are row reads (`rd3_setK`), so `pr_tail2A`
  applies at `RowH R` (`εz (RowH R) = εz R`):
  `εcolSh = 2⁻¹¹³ + εz(6i_E + 13824, 6i₅ + 2184, 6i_E + 18431) + 2i₂·2⁻¹²⁸` per session and world
  (`13824 = 3·(4607 + 1)`, `18431 = 13824 + 4607`).

The bound:

    PomFRIT (blindnessRAHSh_num):  |Pr[W₀] − Pr[W₁]| ≤
        4·εRO(q_E + 6i_E + 23035, q₅ + 6i₅ + 1872, q_E + 6i_E + 23035) + 2·noHitProb + 2·2⁻¹²⁸
      + [i₂ > 0]·4·(2⁻¹¹³ + εRO(6i_E + 13824, 6i₅ + 2184, 6i_E + 18431) + 2i₂·2⁻¹²⁸),

about `2⁻¹⁰²·³³` with `i₂ = 1` and no other budget (`2⁻¹⁰³·²²` without `H₂³` reads, the main term
alone; the collision part `2⁻¹⁰³·⁴⁴`), against `2⁻¹⁰²·³³` for `blindnessRAH_lean_num` (computed
exactly, `noHitProb` neglected). `blindnessRAHSh_numG` for every row type, `blindnessRAHSh_num_perm`
with `εROPm` (about `2⁻¹⁰²·³³`); for oracle computations `blindnessOCHSh_num` (`_perm`), the joint
budget from `QBudget … 0 i₂ i₅ i_E` (`AdversaryOC.iBudgetH`). No simulator change and no
prefix-collision term. Each is the slice-model bound with the slice-read
budget `q₃` (`i₃`) replaced by the row budget plus the other real proofs' rows (`4607 + 1` each),
and, for the adaptive Moussaka and Ratatouille hops, `(rows the interaction read)·2⁻¹²⁸` per
redemption or spend hop and per collision term. In PomFRIT a session's prefix is fixed by its
coins before the Issuer reads anything, so no such term appears there; its collision term is
bounded pointwise as before (`deltaRO_sh`, `deltaSh_le`: `≤ noHitProb + 2⁻¹²⁸`). Without budgets the
totals are within `0.01` bits of those of §10.2–§10.4 (`8·13824·2⁻¹²⁸ ≈ 2⁻¹¹¹`).

**On the paper's `ε_iv`.** As a bound on the probability that two proofs' prefixes coincide,
`2⁻¹⁹²` (Moussaka, Ratatouille; equal `(nf, r)` has probability `2⁻³²⁰`, equal `nf` `2⁻¹⁹²`) and
`2⁻³⁶⁰` (PomFRIT) are right. But it is not the price of sharing `H₃`: (i) with the hybrid argument
on the shared tables the term is not needed at all, the proofs' prefixes may coincide; (ii) the
step "one `H₃` = independent slices up to `ε_iv`" is not a black-box reduction (above), so the
paper's argument for the slice model is incomplete rather than its bound wrong. What sharing
`H₃` actually costs is a fresh `ρ` meeting an `H₃` row read by someone else (another proof with the
same prefix, the adversary, or an interaction that read a future proof's prefix), `2⁻¹²⁸` per read,
already inside the slice-model bounds' `q₃·2⁻¹²⁸` term (and `i₃·2⁻¹²⁸` in §10.3) once those reads
are counted. The slice-model theorems are unchanged; the shared-model ones are new theorems.

**Open.** (Done since earlier versions of this list: PomFRIT with an Issuer that reads `H₂³`,
above.) The model counts the adversary's `H₃`
reads with its cipher queries (`q_E`), so the bounds charge `221·2⁻¹²⁸` per `H₃` read where `2⁻¹²⁸`
would do; a separate `H₃` budget would need the shared tables to carry `H₃` as a separate
component (not possible with the games' `ShG R p` shape) and changes nothing beyond that factor.

### 10.6 The seed-XOF hop (`Privacy/SeedXOF.lean`, `Privacy/SeedXOFGames.lean`, `ROM/SeedXOFReads.lean`, `Privacy/SeedXOFNC.lean`)

**What the hop is.** Every honest request draws 32 fresh OS bytes and expands them with a
domain-separated SHAKE128 XOF into its randomness:
- PomFRIT: `(ρ, refresher, r) = XOF_seed(POMFRIT_SEED_DST ‖ seed ‖ dig(pk) ‖ msg)`
  (`pomfrit.cpp:150-161`, `Spec.PomFRIT.expandSeed`);
- Moussaka: `nf ‖ r ‖ ρ_iss = SHAKE128(ISSUE_SEED_DST ‖ seed)`, `ρ_red =
  SHAKE128(REDEEM_SEED_DST ‖ seed')` (`moussaka.cpp:58-85`, `expandIssueSeed`,
  `expandRedeemSeed`);
- Ratatouille: `(nf, r, ρ) = SHAKE128(DST ‖ seed)`, with the issue and the spend DST
  (`ratatouille.cpp:63-84`, `Spec.Ratatouille.expandSeed`).

The VOLEitH prover takes `ρ` as an input (`ProveSeed`, `voleith.hpp:75, 152`), and zero knowledge
is a statement about the prover with uniform `ρ`. So **no zero-knowledge theorem assumes the hop**;
only the protocol games do. The games of §10.2–§10.5 (and `Privacy/*.lean`) draw the XOF's
outputs uniformly (`issueRequest_eq`, `redeemRequest_eq`, `issueRequestWithSeed_eq`,
`spendRequestWithSeed_eq`). The hop replaces the real Clients (G0: uniform seeds, the outputs the
random-oracle XOF at the seeds, the adversary querying the XOF) by these games (G1: uniform
outputs). The notes argue it on paper: PomFRIT's G0 → G1 (`security/pomfrit.md` §8.2,
`2·Q_X·2⁻²⁵⁶`), Ratatouille's H1 (`security/ratatouille.md` §6, `q_H·Q_P·2⁻²⁵⁶`), and Moussaka's
deviation D7 ("none in the ROM", `security/moussaka.md` §2; Theorem 4 has no term for it).

**The model.**
- *The XOF table* `g : K → R`, uniform, one cell per key. A cell holds everything the XOF answers
  at inputs starting with the key. For PomFRIT the key is the seed and the cell is the column of
  answers at every context `dig(pk) ‖ msg`, in a finite context type `Ctx` with an encoding
  `enc : Bytes → Ctx` (`XofP Ctx = Coins 32 → Ctx → XOut`; with `Ctx` the byte strings up to a
  length bound and `enc` the inclusion, the XOF on every input of that length, as `H₃` is modelled
  on `|x| < 1024`). For Moussaka and Ratatouille the key is `(domain, seed)` and the cell the output
  (`XofM`, `XofR`; a Moussaka redemption reads the `16`-byte component of its cell).
- *Reads*: `RdX f q`, `f` reads at most `q` cells, adaptively (the shape of `Rd3`, `Rd5`, `RdE`).
  An adversary's query reads the cell of the query's key.
- *The adversary at table `g`* is `A g`, an adversary of the existing game. Its run in the game,
  at every fixed tape, reads at most `q_g` cells (`hg`); for PomFRIT its key and messages, which
  fix the sessions' contexts, at most `q_k` (`hk`). Every hypothesis of the existing theorem is
  required of `A g` for every `g`.
- *The game with the seeds* (`seedGame`; `seedGameP`, `seedGameM`, `seedGameR`, and per game
  `seedGameRO`, `seedGameSh`, `seedGameRA`, `seedGameRASh`): the tape is the seeds, the rest of
  the game's tape and the XOF table; request `i` reads its cell `g (x c i)` (at its context), and
  the game's tape is built from those cells (`insP`, `insM`, `insR`).

**The hop.** `abs_pr_seed_le`: the run with the real cells `g ∘ x c` and the run with independent
uniform cells (the table untouched) are `Pr[x c not injective] + δ` apart, where `δ` bounds
`Pr_c[∃ i, x c i ∈ F]` for a fixed set `F` of `q` keys. For injective keys, programming the table
at them is perfect, and the runs differ only if the adversary reads a programmed cell
(`abs_pr_hidden_le`), at a key set that depends on the table, the cells and the rest of the tape
but not on the seeds; then average over the seeds. `abs_pr_seedGame_sub_le` lifts it into a
two-world game: if uniform cells give the uniform tape (`hinsP`, `hinsM`, `hinsR`, with
`pr_cols` for PomFRIT's columns read at the Issuer's contexts), the game with uniform cells is the
original game averaged over the XOF table, and every existing privacy theorem holds at every
table. The seed counting: `pr_bool_exists_mem_le`, `pr_bool_not_injective_le` (two seeds, one key
each), `pr_dom_exists_mem_le`, `pr_dom_not_injective_le` (two seeds in each of two domains: a key
lies in one domain, where it can hit one of two seeds).

**The theorems** (each the existing theorem's bound plus twice the per-world hop):

    PomFRIT:               + 2·(2·(q_k + q_g) + 1)·2⁻²⁵⁶
    Moussaka, Ratatouille: + 2·(2·q_g + 2)·2⁻²⁵⁶

- PomFRIT: `blindnessRO_lean_num_seed`, `blindnessRA_lean_num_seed`,
  `blindnessRAH_lean_num_seed`, `blindnessSh_num_seed`, `blindnessRASh_num_seed`,
  `blindnessRAHSh_num_seed`, and for an interaction written as an oracle computation
  `blindnessOC_lean_num_seed`, `blindnessOCH_lean_num_seed`, `blindnessOCSh_num_seed`,
  `blindnessOCHSh_num_seed` (`ROM/SeedXOFReads.lean`).
- Moussaka: `anonymityRO_lean_num_seed`, `anonymityRA_lean_num_seed`, `anonymitySh_num_seed`,
  `anonymityRASh_num_seed`, `anonymityOC_lean_num_seed`, `anonymityOCSh_num_seed`; the
  non-colluding games of §10.7 (`Privacy/SeedXOFNC.lean`): `anonymityNCRO_lean_num_seed`,
  `unlinkabilityNCRO_lean_num_seed`, `anonymityNCSh_num_seed`, `unlinkabilityNCSh_num_seed`, the
  Anchors' signers `sk g` correct for `A g`'s keys and the abort term bounded uniformly in the
  table (`φ₀ + φ₁ ≤ φ` at every `g`).
- Ratatouille: `unlinkabilityRO_lean_num_seed`, `unlinkabilityRA_lean_num_seed`,
  `unlinkabilitySh_num_seed`, `unlinkabilityRASh_num_seed`, `unlinkabilityOC_lean_num_seed`,
  `unlinkabilityOCSh_num_seed`.
- Each with a `_perm_seed` version (AES as random permutations): 52 theorems. The existing
  theorems are unchanged.

**On the notes' bounds.**
- *PomFRIT.* The note's `|Pr[b' = b] − 1/2|` is half the left/right difference, so its hop costs
  `(2Q_X + 1)·2⁻²⁵⁶` in the Lean bound's terms (`Q_X = q_k + q_g`), against the note's
  `2Q_X·2⁻²⁵⁶`. The note names the seed collision but does not charge it. In the full random-oracle
  model its bound is still right: for `µ₀ ≠ µ₁` the two inputs differ even when the seeds collide,
  and for `µ₀ = µ₁` the two worlds are the same. The `2⁻²⁵⁶` comes from the model, which keys the
  table by the seed alone. Lemma DS (c) (`n_seed·Q·2⁻²⁵⁶`, the overlap F-DS2) is a separate
  step.
- *Ratatouille.* `q_H·Q_P·2⁻²⁵⁶` over-counts the query term (a query hits one seed of its own
  domain: `2q`, not `4q`, in the four-proof game) but **misses the seed collisions**. Two
  issuances, or two spends, with equal seeds have equal `(nf, r, ρ)`, while H1 gives them
  independent values, so the two games differ there. The hop costs `(2q_g + 2)·2⁻²⁵⁶` per world; in general
  `(Σ_d n_d·q_d + Σ_d C(n_d, 2))·2⁻²⁵⁶` for `n_d` requests in domain `d`, read `q_d` times
  (`abs_pr_seed_le` is stated for any number of requests).
- *Moussaka.* Theorem 4 has no term for the hop (D7: "none in the ROM"). An adversary that
  queries the XOF at a seed recovers that Client's `nf`, so the hop is not free: `(2q_g + 2)·2⁻²⁵⁶`
  per world, as for Ratatouille.

All are negligible next to the zero-knowledge terms (`≈ 2⁻¹⁰²`).

**What remains.**
- *Independence of the seed XOFs from the proof system's oracles.* The tables are independent by
  construction. For Moussaka and Ratatouille this is Lemma DS part (a): the domains A4–A7 are
  disjoint from every other (`Protocols/DomainSeparation.lean`, `clean_pairwise`), and one oracle
  with disjoint domains is the per-domain oracles (`ROM/DomainSep.lean`). This is the same
  modelling step as for every other table of the games. For PomFRIT's seed XOF the domain
  overlaps proof-system domains (finding F-DS2), and its independence is part (c), on paper
  (`n_seed·Q·2⁻²⁵⁶`). The proposed `APP_TAG` byte would make it part (a).
- *The adversary's XOF access* is a semantic read budget on its run in the game (`RdX`, as the
  guess's `Rd3`, `Rd5`, `RdE`), not a VCVio oracle computation. Its consistency is not needed (it
  is only an upper bound on reads).
- *PomFRIT's contexts* lie in a finite type: messages beyond the length bound of `Ctx` (with
  `enc` injective) are not covered.
- *Fixed sizes*: two (PomFRIT) or four (Moussaka, Ratatouille) requests, as in the games. The hop
  lemma itself is general. (The games with further sessions, §10.8, keep uniform seed-XOF outputs.)
- *Which games*: the hop is applied to the random-oracle games (the 26 games above, each with
  `_perm`), Moussaka's non-colluding ones of §10.7 included. The abstract games of
  `Privacy/{Moussaka,Ratatouille,PomFRIT}.lean`, `Privacy/MoussakaNC.lean`, and their Lean-prover
  versions (`*_label_rows`, `blindness_lean`, `*_shake`) keep the uniform XOF outputs.
- SHAKE128 as a random oracle remains a modelling step, as everywhere.

### 10.7 Moussaka's non-colluding mode in the random-oracle model (`ZK/VerifyReadsRO.lean`, `Privacy/MoussakaNCRO.lean`, `Privacy/MoussakaNCSh.lean`, `Privacy/SeedXOFNC.lean`)

Theorem 4(b′) (`security/moussaka.md` §6) simulates only the two redemption proofs; the issuance
proofs are never shown to the Moderator, but the honest Anchors **verify** them. In the
random-oracle and ideal-cipher model the verification runs on the same tables as every proof, so
each redemption hop's reduction recomputes the refusal bit: it runs both issuance proofs and both
verifications itself, on the tables it is given.

**The verifier's reads** (`ZK/VerifyReadsRO.lean`; the executable `Verifier.verify` with the
record `recV` of the shared tables and `icPrg`, unchanged). The verifier reads `H₅` only at the
gate inputs of its key columns (`verify_h5_congr`: the inputs `vIn5` of its prefix recomputation
`vPre`, at most `nMult = 312`), the cipher only at the nodes of the tree it reconstructs from the
opening (`verify_ic_congr`: `rdKeys`, at most `4607`: the reconstruction, the leaves'
commitments, the VOLE expansion off the hidden leaves), `H₂³` only at `chal3`'s input
(`verify_h23_congr`) and no `H₃` (`verify_agreeOff_h3`). As `Rd5`/`RdE` budgets: `verRO_rd5`
(`312`), `verRO_rdE` (`4607`); composed with a real proof, `verRO_comp_rd5`, `verRO_comp_rdE`
(`624 + 312`, `4607 + 4607`). The constants are the simulator's programming's (`progRO_isProg`),
which recomputes the same prefix.

**The game** (`realGameNCRO`): Client `c`'s `issue_request` with the issuance prover on the tables
(its own `H₃` slice), Anchor `c`'s `issue_response` (the Lean verifier `leanVI` on the tables, then
`derive_preimage` of any signer correct for its key), `finalize_issue`, §6's refusal rule, and the
redemptions with the redemption prover on the tables; the adversary's guess sees the redemptions or
the refusal, the four `H₃` slices and the tables (`AdversaryNCRO.Budget`: `q₃` per slice, `q₅`,
`q_E`, `H₂³` freely). Its choices (contexts, keys, Anchor Sets, digests) do not read the tables.

**The hops.**
- *Redemptions simulated* (`hopL_NCRO`, `hopR_NCRO`). The hybrids run the issuance requests and the
  verifications on the tables **after** the redemption simulations' `H₂³` programming
  (`gameNCROS`); with real redemptions nothing is programmed, so the first hybrid is the real game
  (`realGameNCRO_iff`). Then a real issuance proof or verification reading a point a simulated
  redemption programmed is not an event to bound: it is part of the reduction, which needs only
  the read budgets, `2·(624 + 312) + 624 = 2496` `H₅` and `2·(4607 + 4607) + 4607 = 23035`
  cipher keys beyond the adversary's (the right hop: `2184`, `23035`, the left simulation's
  programming included). The redemption statements must not depend on the tables: the would-be
  token `tokW` (`derive_preimage` on the commitment) is the Client's token whenever the
  redemptions happen (`tokDNC_eq_tokW`), and the simulations program only if all four Client
  checks of `tokW` pass (`okW`, which the refusal bit implies: `okW_of_GV`). The left hop has no
  collision term; the right one has `deltaNC` (the right real redemption reads `H₂³` at the left
  simulation's block), `≤ noHitProb + 2⁻¹⁰²⁴` (`deltaNC_le`): the right statement does not
  depend on the left simulation's coins, so its prefix's `ã` is the simulation's uniform `ã` with
  that probability (`pr_simTail_eq_le`), and otherwise the programming misses its block
  (`realRO_ne_tail`). (In 4(a) the redemption statements are chosen after the simulated
  requests, which is why `deltaL_le` needs a second zero-knowledge application.)
- *The issuance slices the guess sees made independent* (`sim_fresh_NC`, `2·q₃·2⁻¹²⁸`): the
  final swap exchanges the Clients' tapes, and the guess sees their slices. An issuance proof
  reads its slice only at its randomness (`SliceAt`; for the Lean prover `realRO_h3_val`:
  `Prover.prove` reads `ρ` only through `H₃`), so seeing the slice or an independent one differs
  only if the guess reads it at `ρ`, which is independent of its view (`abs_pr_fiber`,
  `abs_pr_slice_hop`).
- *The abort hop* (`fresh_hyb_NC`, `φ₀ + φ₁`) and *the swap* (`hybFresh_eq`), as in
  `Privacy/MoussakaNC.lean`; with one Anchor the simulated game is already symmetric
  (`simFresh_eq_one`, any index rule).

**Results.** For every type of cipher rows (`ZKRow R`; `anonymityNCRO` for any proof systems with
read budgets):

    anonymityNCRO_lean_num:   |Pr[W₀] − Pr[W₁]| ≤ 4·εRO(q₃, q₅ + 2496, q_E + 23035)
                                 + 2·(noHitProb + 2⁻¹⁰²⁴) + 2·(φ₀ + φ₁) + 4·q₃·2⁻¹²⁸,

about `2⁻¹⁰³·²` plus the budget terms and the abort term; `anonymityNCRO_lean_num_perm` with
`εROPm`; `anonymityNCRO_vinegarRO` with the abort term `2·(δ₀²⁵⁶ + δ₁²⁵⁶)` averaged over the
Anchors' vinegar tables; `unlinkabilityNCRO_lean_num`, `_perm` (one Anchor, any index rule) the
same without `2·(φ₀ + φ₁)`. Nothing is assumed of the issuance proofs' zero knowledge or of `Com`.

**With one shared `H₃`** (`Privacy/MoussakaNCSh.lean`). The game `realGameNCSh` is
`realGameNCRO` with the issuance and redemption provers reading their columns at their prefixes
(`leanPISh`, `leanPRSh`, §10.5); the Lean verifier reads no `H₃`; the adversary reads `H₃` through
the rows (`q_E`).
- *The redemption hops* are `hopL_NCRO`, `hopR_NCRO` unchanged, with `leanPRSh_zkRO`
  (`ZeroKnowledgeRO.shared`: the error at the row budget, `εz(q_E', q₅', q_E')`). Each shared
  prover reads one row more (its `ρ`), so the reductions' row budgets are `q_E + 23038` (left:
  both issuance proofs and the right redemption, `3·(4607 + 1)`, both verifications `2·4607`) and
  `q_E + 23037` (right: the left simulation's programming `4607` instead of a proof).
  `deltaNC_sh`: the collision term is the slice model's (`pr_h3At_slice`), so `deltaNC_le`.
- *The slice hop is exact.* In the slice model the final swap exchanges the Clients' tapes, slices
  included, while the guess sees the slices labelled by Client, hence `sim_fresh_NC`'s
  `2·q₃·2⁻¹²⁸` per world. Here the issuance proofs read the shared tables, which the swap does not
  exchange, and the slot slices are read by the guess alone: for an issuance prover that ignores
  its slot slice (`SliceFreeP`) the game is a function of the slot slice only through the guess's
  argument, and replacing it by an independent slice is a relabelling of uniform coins
  (`pr_slice_free`, `sim_fresh_NC_free`: equality). `anonymityNCRO_free`,
  `unlinkabilityNCRO_free` are `anonymityNCRO`, `unlinkabilityNCRO` without the slice term.

The bound:

    anonymityNCSh_num:   |Pr[W₀] − Pr[W₁]| ≤ 4·εRO(q_E + 23038, q₅ + 2496, q_E + 23038)
                            + 2·(noHitProb + 2⁻¹⁰²⁴) + 2·(φ₀ + φ₁),

about `2⁻¹⁰³·²²` plus the budget terms and the abort term (`2⁻¹⁰³·²³` for `anonymityNCRO_lean_num`
at zero budgets; computed exactly, `noHitProb` neglected); `anonymityNCSh_num_perm` (`εROPm`),
`anonymityNCSh_vinegarRO`, `unlinkabilityNCSh_num` (`_perm`) without `2·(φ₀ + φ₁)`. The
`4·q₃·2⁻¹²⁸` slice term is gone. The guess's `H₃` reads are still paid, inside the
zero-knowledge error: a row read costs `4·(1 + 221)·2⁻¹²⁸` (`εRO`'s `q₃` and `q_E` slots), the
shared model's over-charge of an `H₃` read as a cipher read (§10.5, "Open"), where a slice read in
the slice model costs `8·2⁻¹²⁸` (`εRO`'s `q₃` slot and the slice term). So the slice term was an
artifact of the per-Client slices, not a cost of `H₃` reads; with budgets the two bounds are of
the same order (`≈ 2⁻⁵⁴·²` at `q₅ = q_E = 2⁶⁴`, and `q₃ = 2⁶⁴` in the slice model).

**With the real Clients' seeds** (`Privacy/SeedXOFNC.lean`, §10.6): the non-colluding game has
the 4(a) game's tape, so `seedGameM` applies (`seedGameNCRO`, `seedGameNCSh`); the Moderator `A g`
and the Anchors' signers `sk g` may depend on the XOF table; `anonymityNCRO_lean_num_seed`,
`anonymityNCSh_num_seed` (the abort term bounded uniformly, `φ₀ + φ₁ ≤ φ`),
`unlinkabilityNCRO_lean_num_seed`, `unlinkabilityNCSh_num_seed`, each with `_perm_seed`, add
`2·(2q_g + 2)·2⁻²⁵⁶`.

**Open.** The adversary's choices (contexts, keys, Anchor Sets, digests) do not read the tables
(no `RA`/`OC` version).

### 10.8 Many sessions (`ZK/ReadsMany.lean`, `Privacy/PomFRITMany.lean`, `Privacy/MoussakaMany.lean`, `Privacy/RatatouilleMany.lean`, `Privacy/PomFRITAdaptive.lean`)

Every game above has the challenge sessions only: two (PomFRIT) or four (Moussaka, Ratatouille)
requests. A deployment has many sessions on the same random oracle and cipher, and the adversary
(the Issuer, or the colluding Anchors and Moderator) takes part in all of them.

**The games.** The adversary serves `m = |ι|` further honest sessions besides the challenge, on
the same tables, each with its own randomness, `(nf, r)` or refresher and `r`, and its own `H₃`
slices, concurrently with the challenge:
- *PomFRIT* (`AdversaryN`, `realGameN`): a key and a message per further session (any keys);
  every Client sends its request (step 1 on the tables); the Issuer answers **every** session
  after seeing **every** request; every Client finalizes (step 2). The guess sees all requests,
  the challenge signatures in message order only if both challenge sessions complete (`outcome`),
  every further session's outcome, all slices and the tables. The game is defined directly on
  `realSession`; for each tape `c` of the further sessions it is, by definition (`realGameN_iff`,
  `Iff.rfl`), `realGameRA` of the Issuer `A.red c` that runs them.
- *Moussaka* (`AdversaryN`, `realGameN`): an issuing key per further Client; after **every**
  issuance request the adversary answers every Client and chooses the Anchor Set and digest of each
  challenge side and of each further Client; each further Client finalizes and redeems at its own
  index in its set (`issX`, `redX`: the spec's `issue_request`, `finalize_issue`, `redeem_request`
  with the Lean provers on the tables). The guess sees every issuance request, the challenge
  redemptions or the refusal (§6's rule, as before), every further redemption, all slices and the
  tables. The game is `realGameRA` of the adversary served by the further Clients
  (`AdversaryN.withClients idx c`).
- *Ratatouille* (`AdversaryN`, `realGameN`): stage 1 sees **every** issuance request and gives the
  challenge responses, `d₁`, and a response and a spend amount per further Client; each further
  Client finalizes and spends once, with round 1 (`issXR`, `spXR`: `issue_request_with_seed`,
  `finalize_issue`, `spend_request_with_seed`); stage 2 sees round 1's request **and every further
  spend request**. The game is `realGameRA` of the Issuer served by the further Clients.
- *PomFRIT with `N` challenge pairs* (`AdversaryP`, `realGameP`, worlds `w : Fin N → Bool`): pair
  `j` has a key and two messages, its first session signs `µ^j_{w j}`; all `2N` requests are sent,
  the Issuer answers every session after every request, and the guess sees each pair's signatures
  (if both of its sessions complete), all slices and the tables: the left-or-right game with `N`
  queries.
- *Moussaka with `N` challenge pairs* (`AdversaryP`, `realGameP`, worlds `w : Fin N → Bool`): two
  issuing keys per pair; after **every** issuance request the adversary answers every Client and
  chooses both sides' Anchor Sets and digests of every pair; side `s` of pair `j` redeems Client
  `w j ^^ s`'s token (`outAt`, §6's rule per pair: both redemptions if all four checks pass, else
  none); the guess sees all issuance requests, every pair's outcome, all slices and the tables.
- *Ratatouille with `N` challenge pairs* (`AdversaryP`, `realGameP`, worlds `w : Fin N → Bool ×
  Bool`): stage 1 sees **every** pair's issuance requests and gives every response and every
  pair's `d₁`; each pair's round 1 runs (Client `b₁` spends) if §6's rule allows it; stage 2 sees
  every pair's round-1 request **for the pairs whose round 1 runs** (`rq1Of`) and gives every
  round-1 response and `d₂`; each pair's round 2 runs as in the two-session game (`roundsOf`); the
  guess sees all issuance requests, every pair's rounds, all slices and the tables.
- *PomFRIT with an adaptive schedule* (`AdversaryAd`, `realGameAd`): `m₁` further sessions before
  the challenge, `m₂` between the challenge requests and the challenge responses, `m₃` after the
  challenge outcome, **one after the other**: each further session's key and message and the
  Issuer's response to it are chosen from all earlier requests and outcomes (`runSeq`, each session
  run to the end, `fullX`); the challenge key and messages from the first `m₁`, the challenge
  responses from everything before them; the guess sees everything.

In each game the adversary's interaction does not read the tables (as in the `RO` games); its
guess reads them with a budget (`AdversaryN.Budget`, and `AdversaryP.Budget`, `AdversaryAd.Budget`
likewise: each challenge slice at `q₃` keys, `H₅` at `q₅`, the cipher at `q_E`, `H₂³` and the
further sessions' slices freely).

**The proof: a reduction to the table-reading games.** For a fixed tape `c` of the further
sessions, an honest session is a function of the tables. So the game is the two-session game of
§10.3 (`realGameRA`) for the adversary that runs the further sessions itself: its interaction
computes their messages on the tables it is given, its guess the rest. Hence for every `c`
`blindnessRA_lean_numG`, `anonymityRA_lean_numG`, `unlinkabilityRA_lean_numG` apply, and averaging
over `c` (`abs_pr_prod_sub_le`) gives the bound. Nothing in §10.2's or §10.3's hybrids changes:
the further sessions are part of the distinguisher in every hop and run on whatever tables that
hop's game runs on, so they add **no collision term**; they add their reads to the budgets.

That needs the further sessions to be **consistent** table readers (`SReads`, §10.3), not only
bounded ones (`Rd5`, `RdE`), since the `RA` theorems resample what the interaction read:
- *Step 1 of the two-phase prover* (`step1_cons`): a table that agrees with `s` on step 1's `624`
  gate inputs and its tree's `4607` nodes, whatever its `H₂³`, has the same keys and the same
  output. The tree's nodes are read off the cipher top-down (`treeNode_ic_congr`), and the sender
  columns and `u_pre`, hence the `H₅` inputs, read only them (`vgIn5_ic_congr`). So a PomFRIT
  request is `SReads` with `(0, 0, 624, 4607)` (`s1R_sreads`, `sessX_req_sreads`).
- *The single-phase prover* (`realRO_sreads`): of `H₅` at its `624` gate inputs, the cipher at its
  `4607` nodes and `H₂³` at the `nGrind = 2³²` grinding points of its prefix: the proof reads
  `H₂³` only there (`prove_recH_eq`, so `realRO_h23_congr`), and the prefix itself is read off the
  `H₅` and cipher keys (`preRO_cons`). For Moussaka's and Ratatouille's issuance requests and
  Ratatouille's spend requests (a proof only when the Client's checks pass, and then the witness
  is in `R_spend`).
- *Families* (`SReads.pi`, `Rd5.pi`, `RdE.pi`): `m` readers read together read `m` times the bound.

The budgets of the composed adversary (`red_iBudget`, `red_gBudget`, `withClients_iBudget`,
`withClients_gBudget`):

| | interaction `(i₃, i₂, i₅, i_E)` | guess `(q₃, q₅, q_E)` |
|---|---|---|
| PomFRIT | `(0, 0, 624m, 4607m)` (`IBudget`, no `H₂³`) | `(q₃, q₅ + 624m, q_E + 4607m)` |
| Moussaka | `(0, 2³²m, 624m, 4607m)` | `(q₃, q₅ + 2·624m, q_E + 2·4607m)` |
| Ratatouille | `(0, 2·2³²m, 2·624m, 2·4607m)` (stage 2 also runs the spends) | `(q₃, q₅ + 2·624m, q_E + 2·4607m)` |

**The bounds** (Lean, `#print axioms`: `propext`, `Classical.choice`, `Quot.sound`; each for every
row type with `ZKRow` (`*_numG`), function rows and permutation rows (`_perm`)):

    PomFRIT (blindnessN_lean_num):  ≤ 4·εRO(q₃, q₅ + 5m·624 + 1872, q_E + 5m·4607 + 23035)
                                        + 2·noHitProb + 2·2⁻¹²⁸
    Moussaka (anonymityN_lean_num): anonymityRA_lean_num at i₃ = 0, i₂ = 2³²m, i₅ = 624m,
                                        i_E = 4607m and the guess's budget above
    Ratatouille (unlinkabilityN_lean_num): unlinkabilityRA_lean_num at i₃ = 0, i₂ = 2·2³²m,
                                        i₅ = 2·624m, i_E = 2·4607m and the guess's budget above

All linear in `m`; the per-session cost is the H4 hop's `221·4607·2⁻¹²⁸ ≈ 2⁻¹⁰⁸` per cipher-read
budget slot, about `5·4 = 20` slots for PomFRIT (`εRO`'s four hops, each reading the further
sessions five times: once in the guess, four times through the interaction), so `≈ 2⁻¹⁰³·⁷` per
session. In numbers, with `n = m + 2` sessions in all:

| | `n·2^{-k}`, `k` | `n = 2²⁰` | `n = 2³²` | Lean |
|---|---|---|---|---|
| PomFRIT | `103` | `2⁻⁸³` | `2⁻⁷¹` | `blindnessN_lean_le`, `_2pow20`, `_2pow32` |
| Moussaka | `102` | `2⁻⁸² + 2·εhide` | `2⁻⁷⁰ + 2·εhide` | `anonymityN_lean_le`, `_2pow20`, `_2pow32` |
| Ratatouille | `101` | `2⁻⁸¹ + 2·εhide` | `2⁻⁶⁹ + 2·εhide` | `unlinkabilityN_lean_le`, `_2pow20`, `_2pow32` |

each plus `4·(q₃ + q₅ + 221·q_E)·2⁻¹²⁸` (PomFRIT) or `8·(q₃ + q₅ + 221·q_E)·2⁻¹²⁸` (the others)
for the guess's own budget. (The exact per-session coefficients are `0.61·2⁻¹⁰³`,
`0.97·2⁻¹⁰³` and `2.31·2⁻¹⁰³`; the constants fit in the remaining `2·2⁻ᵏ`.)

**`N` challenge pairs** (`blindnessP_lean_numG`, `_num`, `_num_perm`): a hybrid over the pairs
(`abs_sub_le_mul_of_steps`, from `abs_sub_le_sum_of_steps`: consecutive hybrids `ε_k`-close give
`Σ ε_k`; `abs_sub_le_mul_of_worlds` packages it for worlds `Fin N → β`). Step `k` changes pair
`k`'s world; at it, the game is the one-pair game of `A.hop k v` with the other `2(N − 1)` sessions
as further sessions in their current worlds (`realGameP_iff`, the tape split `splitP`), so it costs
`εPair = blindnessN`'s bound at `m = 2(N − 1)`. In numbers (`blindnessP_lean_le`)
`≤ N·(2N·2⁻¹⁰³ + 4·(q₃ + q₅ + 221·q_E)·2⁻¹²⁸)`: `2⁻⁶⁴` for `2N ≤ 2²⁰` sessions, `2⁻⁴⁰` for
`2N ≤ 2³²` (`blindnessP_lean_2pow20`, `_2pow32`).

- *Moussaka* (`anonymityP_lean_numG`, `_num`, `_num_perm`): the same hybrid; at step `k` the other
  pairs' `2(N − 1)` Clients are further Clients of `anonymityN` (`A.hop idx k v`: Client `c` of pair
  `j` redeems at side `v j ^^ c`, `splitM` gives it that side's redemption tape), and the hop's
  guess rebuilds each other pair's outcome from its two Clients' redemptions and §6's rule on the
  commitments (`outAt_eq`: `allOk` is `allOkT` on the requests, `allOk_eq_allOkT`, and then each
  side's redemption is its Client's `redX`). Each step costs `εPairM`, `anonymityN`'s bound at
  `m = 2(N − 1)`; in numbers (`anonymityP_lean_le`) `≤ N·(2N·2⁻¹⁰² + 8·(q₃ + q₅ + 221·q_E)·2⁻¹²⁸ +
  2·εhide)`: `2⁻⁶³` for `2N ≤ 2²⁰` Clients, `2⁻³⁹` for `2N ≤ 2³²` (`_2pow20`, `_2pow32`), plus `N`
  times the budget and hiding terms. Hiding is assumed for every hop's reductions.
- *Ratatouille* (`unlinkabilityP_lean_numG`, `_num`, `_num_perm`): the other pairs cannot be
  `unlinkabilityN`'s further Clients (those spend once; a pair has two rounds, the second after
  the Issuer's round-1 response), so each step is a direct reduction to the two-session
  table-reading game: `A.hop k c v` runs the other pairs itself with their tapes `c` (its stage 1
  their issuances, its stage 2 also their round-1 spends, its guess also their round-2 spends;
  `realGameP_iff`, `realGameRA_hop`), and `unlinkabilityRA_lean_numG` applies for every `c`
  (`realGameP_hybrid`, averaging over `c`). Its stage 2 must hide pair `k`'s round-1 request
  when §6's rule refuses round 1, without pair `k`'s tokens: the rule is computed from the
  Issuer's view (`ok1Of_eq_pub`: both responses are preimages of the commitments in the requests,
  `tkOk`, and the balance affords `d₁`; honest finalized tokens are valid, `fin_issXR`). Budgets
  (`hop_iBudget`, `hop_gBudget`): the interaction `(0, 3(N−1)·2³², 3(N−1)·624, 3(N−1)·4607)` (the
  other pairs' issuances and round-1 spends, consistent readers by `issXR_sreads`, `spXR_sreads`),
  the guess `(q₃, q₅ + 4(N−1)·624, q_E + 4(N−1)·4607)`. Each step costs `εPairR`; in numbers
  (`εPairR_le`, `unlinkabilityP_lean_le`) `≤ N·(N·2⁻¹⁰¹ + 8·(q₃ + q₅ + 221·q_E)·2⁻¹²⁸ + 2·εhide)`:
  `2⁻⁶³` for `2N ≤ 2²⁰` Clients, `2⁻³⁹` for `2N ≤ 2³²` (`_2pow20`, `_2pow32`).

All three are quadratic in the number of sessions: each of the `N` steps pays, in its H4 hop, for
the cipher reads of all other sessions.

**Is the quadratic term inherent?** No; it is an artifact of how the H4 hop is charged, together
with a modelling choice. Precisely:

1. *The hop charges keys, not points.* H4 (`ZK/HopsH4.lean`, `HopsH4Ideal.lean`) replaces the
   cipher **rows** of the `≤ 221` hidden-path nodes of the proof under hop and charges every read
   of such a row, at any input: `≤ 221·(4607 + q)·2⁻¹²⁸` for `q` reads by the distinguisher. In the
   `N`-pair game the distinguisher of pair `k`'s hops includes the other sessions, whose tree keys
   are uniform and independent of pair `k`'s hidden keys; each of their `4607` reads hits a hidden
   row with probability exactly `221·2⁻¹²⁸`, and summing over the hops sums over ordered pairs of
   sessions. A single joint hybrid with one bad event ("some read, by an honest session or the
   adversary, at a hidden key of some proof") does not change the order: that event has probability
   `≈ n·221·n·4607·2⁻¹²⁸ ≈ n²·2⁻¹⁰⁸` for `n = 2N` sessions — `2⁻⁶⁸` at `n = 2²⁰`, `2⁻⁴⁴` at
   `n = 2³²`, against the proved `2⁻⁶⁴`, `2⁻⁴⁰` — and it really occurs with about that probability
   (a birthday bound on 128-bit keys). So **no key-level argument is linear**; the joint hybrid
   would only save the constant (`≈ 16`).
2. *A key collision alone is harmless.* What a hidden node contributes is the cipher's values at
   the finitely many points `pts` (key, CTR input) that the hidden part reads (`HopsH4Ideal.lean`
   already isolates them: `pts_injective`, `IC.rowAt_congr_points`). Another session's read at a
   colliding key but at a different input sees an independent value (function rows; a `2⁻¹²⁸`
   correction for permutation rows). The CTR inputs contain the proof's `iv = H₄(iv_pre ‖ µ)`
   (`voleith.hpp:188-194`), fresh per proof, so an honest–honest point collision needs a key
   collision **and** an input collision: `≲ C(n, 2)·221·4607·L²·2⁻²⁵⁶` with `L` the counters per
   node (`< 2³²`, `SmallParams`): `≈ 2⁻¹⁰⁹` at `n = 2³²` even with `L = 2³²`, and in practice far
   below. With point-level charging and fresh ivs, an adversary's cipher query also targets the
   proofs whose input sets contain its input, so its term is `≈ q_E·221·2⁻¹²⁸` once for the whole
   game rather than once per pair. The resulting bound is linear in `n`: the per-proof terms (the
   grinding `2⁻¹¹³`, the proof's own `221·4607·2⁻¹²⁸`, the H6 and slice terms) once per proof, of
   order `n·2⁻¹⁰⁵`, plus the adversary's budget terms once.
3. *What is inherent.* The linear per-proof terms, and the adversary's budget terms. With a **shared
   or predictable iv** the quadratic loss would be real: expand each revealed GGM seed of every
   proof once (two cipher queries) and look the children up among all proofs' revealed seeds; a hit
   means a revealed seed equals another proof's hidden-path node, whose hidden child then follows,
   breaking that proof's hiding. With `≈ 2·n·221` queries this succeeds with probability
   `≈ (n·221)²·2⁻¹²⁸` up to the positions' factor — an `n²` advantage, but bought with `q_E ∝ n`
   queries, i.e. the multi-target term `q_E·n·221·2⁻¹²⁸` of a key-level bound. The per-proof iv is
   what removes it.
4. *Why Lean cannot state the linear bound yet.* (a) In the Lean model `H₄` is the concrete SHAKE
   (`Hashes.shake`; only `H₃`, `H₂³`, `H₅` and the cipher are tables), so distinct sessions' ivs
   are not known to differ; a linear bound needs `H₄` as a table of the game (or a hypothesis
   that the sessions' ivs differ). (b) H4 would have to puncture the cipher at the points `pts`
   instead of whole rows, and (c) the hybrid would have to replace all `2N` proofs with one bad
   event over all hidden points. The key-level `N`-pair bounds above are the best this proof
   structure gives up to a constant.

**Adaptive schedules** (`Privacy/PomFRITAdaptive.lean`; PomFRIT). A session run inside the
interaction must be a consistent reader of `H₂³` too: **step 2 of the two-phase prover is**.
`fullX_sreads`: a whole further session (`fullX`: request, the Client's checks and step 2 on the
Issuer's response `ρ(request)`) is `SReads` with `(0, 2³², 624, 4607)`: step 1's keys
(`step1_cons`, `full_step1`), the prefix read off them (`preX_cons`: `pendAt_step1`, `realPre_h5`),
the signature read off step 1 and `H₂³` (`sigR_tables`, `proveCommit_agreeOff_h5`) and `H₂³` only
at the prefix's `2³²` grinding points when the response passes the checks (`sigR_h23`: `sigOf_oR`,
`oR_fix` and `realRun2_h23_congr` for the Issuer `respAdv` that answers `ρ`; `finish_of_not_valid`
otherwise). Sequential sessions compose (`runSeq_sreads`), and a reader of the shared tables is a
joint reader of both slices (`SReadsP.of_shared`). For each tape `c` of the further sessions the
adaptive game is the `RAH` game (§10.3) of the Issuer `A.red c` that runs them in its key stage,
its response stage and its guess (`realGameAd_iff`, `Iff.rfl`), with budgets `IBudgetH` `(0,
(m₁+m₂)·2³², (m₁+m₂)·624, (m₁+m₂)·4607)` (`red_iBudgetH`) and guess `(q₃, q₅ + (m₁+m₂+m₃)·624,
q_E + (m₁+m₂+m₃)·4607)` (`red_gBudget`); `blindnessRAH_lean_numG` and averaging over `c` give

    blindnessAd_lean_num:  ≤ 4·εRO(q₃, q₅ + M·624 + 6m·624 + 1872, q_E + M·4607 + 6m·4607 + 23035)
                             + 2·noHitProb + 2·2⁻¹²⁸ + h23H(0, m·2³², m·624, m·4607),
                           m = m₁ + m₂, M = m₁ + m₂ + m₃,

in numbers (`blindnessAd_lean_le`) `≤ n·2⁻⁹² + 4·(q₃ + q₅ + 221·q_E)·2⁻¹²⁸` for `n = M + 2`
sessions: `2⁻⁷²` at `n = 2²⁰`, `2⁻⁶⁰` at `n = 2³²` (`_2pow20`, `_2pow32`; `_num_perm`, `_numG`).
Linear, but the per-session term, `≈ 2⁻⁹³`, is the `RAH` collision term's charge of `2·2⁻¹²⁸` per
`H₂³` **key** the interaction reads (`pr_bad0H`, `pr_bad1H`), and each session run inside the
interaction reads `2³²` keys, all with one prefix. The challenge's grinding block is hit only if a
read's prefix equals the challenge prefix, whose tail `ã` is uniform; counting prefixes instead of
keys would make it `≈ 8·2⁻¹²⁸` per session, and the bound `≈ n·2⁻¹⁰¹`. Not done.

**What the model assumes.** The further sessions' `H₃` slices are independent tables, as in every
slice game (§10.2: two sessions with equal `(nf, r)` or `(r, binder)` would share `H₃` inputs; on
paper `C(n, 2)·2⁻¹⁹²` for Moussaka and Ratatouille's nullifiers, `C(n, 2)·2⁻³⁶⁰` for PomFRIT, about
`2⁻¹²⁹` at `n = 2³²`); hiding of `Com` is assumed for the explicit reductions of every composed
adversary (the further sessions' tapes fixed, a non-uniform reduction).

**Open.**
- *Adaptive schedules for Moussaka and Ratatouille.* PomFRIT's are done (`blindnessAd_lean_num`,
  above). For Moussaka and Ratatouille, further Clients started inside or after the challenge's
  interaction fit the existing `RA` games (their interactions may read `H₂³`, `IBudget`'s `i₂`, and
  a whole single-phase session is a consistent reader, `realRO_sreads`), but sessions **before**
  the challenge cannot influence the challenge keys, contexts and balance: those are constants of
  the `RA` adversaries (`AdversaryRA.pk`, `ctxIss`, `ctxRed`; `pk`, `ctx`, `tInit`). The missing
  piece is an `RA` game whose key stage reads the tables (as PomFRIT's does), and its proof.
- *A linear bound for `N` challenge pairs* (the paragraph above): `H₄` as a table of the game,
  point-level puncturing in H4, and one joint hybrid over all proofs.
- *A prefix count in the `RAH` collision term*, for adaptive PomFRIT `≈ n·2⁻¹⁰¹` instead of
  `n·2⁻⁹²`.
- *Other games.* Further sessions in the shared-`H₃` games (§10.5: the prover reading its column),
  the seed-XOF games (§10.6: their XOF reads in `q_X`), the non-colluding games (§10.7).
- *Interactions that read the tables* in the many-session games (the `RA` form): the composed
  adversary's interaction is `SReads` by `SReads.bind` with the adversary's own reads; not stated.
