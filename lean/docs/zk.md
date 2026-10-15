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
`Privacy/MoussakaLean.lean`, `Privacy/RatatouilleLean.lean`, §10.1). There is no `sorry` and no `axiom`. `#print axioms` lists
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

**Proved only on paper** (for the executable prover, §10.1 reduces these to the tape hypothesis):
- the random-oracle and lazy-sampling steps (H1, H2 programming, H6 identical-until-bad, and the
  reduction of adaptive H₅ queries to functions of a Θ-independent view). For the `main` layout,
  the probability bound that follows (union over `q` queries, each a function of the view, aux
  and independent coins) is in Lean (§4.1); for the patched layout, the per-query count is
  (`card_query_hits_sibling_responses`), and for the executable prover the union over adaptive
  `H₅` queries is mechanized with `H₅` a uniform table (§10.1, `lab_rom_query`);
- the PRP/GGM hiding (H4/H8, imported from spec Lemma 10.24);
- the completeness identities (H3) for the models (for the executable prover: §10.1);
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
| **BAVC completeness**: the prover's opening at any `Δ` reconstructs its leaf keys off the hidden leaves and its commitments (the walks as folds over the node index; opened nodes, placement, top-down derivation) | `Bridge.bavcComplete` (`Verifier/Bridge/BAVCComplete.lean`) | H3 |
| **CRT completeness**: the verifier's CRT masks are `ṽ_mask + u_mask·Δ'` for every `Δ` (gate labels `L^{γ_e}`, `c_mult` read back, `r̃` bilinear, and the tables' bilinear identity `L_c(a) = a·W_crt[c]`, checked in the kernel on all `120 · 128` basis pairs) | `Bridge.crtComplete`, `Bridge.crt_core`, `CrtCheck.Lc_eq`, `CrtCheck.crtCheck_eq` (`Verifier/Bridge/CrtComplete.lean`, `CrtCheck.lean`) | H3 |
| The privacy theorems with the Lean prover: Moussaka issuer hiding/unlinkability, Ratatouille unlinkability | `Privacy.Moussaka.anonymity_lean`, `Privacy.Ratatouille.unlinkability_lean` (`Privacy/LeanProver.lean`) | — |
| **Newton interpolation is correct**: `InterpOk d` for `d + 1 < 2⁶⁴` (the code's divided-difference table is the recurrence `D(a, m)`; the Newton form interpolates its window, by Neville's identity; Horner's rule builds it) | `Interp.interpOk`, `interpOk_two`, `interpOk_nine`, `interpolate_correct`, `newton_interp` (`ZK/Interp.lean`) | H3 |
| **Two phases, delayed instance** (PomFRIT): with the instance and the witness suffix chosen by any continuation from step 1's output (buffer and `chal1`), the real run is the ideal-tape run at its own tape (step 2: `proveCommit_eq_proveIdeal` for any split of the witness; step 1: `step1_real`); on a uniform tape the ideal run is distributed as the simulated one: step 1's `c_i`, `c_mult`, `ũ`, `d[0..|r|)` are uniform (so the simulator outputs them, and the verifier's `chal1`, before the instance exists), and `d[|r|..)` and `ã` stay uniform given them for every instance and suffix picked (`ã` is a bijection of the QuickSilver masks for every value of `ũ` and of the instance; `(c_i, d)` a bijection of the row pads for every suffix choice that reads `d[0..|r|)` only) | `realRun2_eq`, `idealPhase1_real`, `proveIdeal2_close`, `upush_respAd`, `upush_rowsAd`, `upush_fieldsAd` (`ZK/TwoPhase.lean`) | H2, H5–H7 |
| **Two-phase zero knowledge** from the two-phase tape hypothesis `TapeHyp2`, and for PomFRIT's Lean prover (`leanProver`: `issue_request_with_seed`, then `finalize_issue` for the instance `(pk, h)` and `s`) in the form of `Privacy.PomFRIT.ZeroKnowledge`, with every deterministic hypothesis proved for valid continuations (`P(s) = h ⊕ r`); blindness with the Lean prover on the label-row layout; completeness of `pomfritVerify` on the final signature | `twoPhase_close`, `twoPhase_close_tables`, `Privacy.PomFRIT.lean_zeroKnowledge`, `runHyp2_lean`, `blindness_lean`, `blindness_lean_shake`, `pomfritVerify_complete_tables` (`Privacy/PomFRITLean.lean`) | all |
| **Ratatouille, assembled**: the issuance and spend statements with label rows, the spec's witness encodings (`encode_issue_witness`, `encode_spend_witness`, with the committed Keccak states and the carries), the primitives `leanPrim` (proofs as the spec's label-row-sized vectors, `Spec.Ratatouille.Sizes.labelRows`); `ZKHyp` for every instance and witness; Theorem 2 with only the tape hypotheses, hiding and the hash record's output lengths left (with SHAKE only the hop hypotheses and hiding: `≤ 4(ε_rho + ε_grind + ε_bavc + ε_lab)_I + 4(…)_S + 2ε_hide`) | `Privacy.Ratatouille.issue_holds`, `spend_holds`, `carries_testBit`, `zkHypI`, `zkHypS`, `unlinkability_label_rows`, `unlinkability_label_rows_shake` (`Privacy/RatatouilleLean.lean`) | — |
| **Moussaka, assembled**: the issuance and redemption statements of `Verifier/Relations.lean` with label rows, `ZKHyp` for every well-formed instance (the spec's witness encodings satisfy the `Arith` systems for every combination); Theorem 4(a) with only the tape hypotheses, hiding and the hash record's output lengths left (with SHAKE only the hop hypotheses and hiding: `≤ 4(ε_rho + ε_grind + ε_bavc + ε_lab)_I + 4(…)_R + 2ε_hide`) | `Privacy.Moussaka.issue_holds`, `redeem_holds`, `zkHypI`, `zkHypR`, `anonymity_label_rows`, `anonymity_label_rows_shake` (`Privacy/MoussakaLean.lean`) | — |

`lake exe zk_sim [TESTS [main\|labelrows [FILTER]]]` runs, on all 18 KAT runs of each layout: the
equation `prove = proveIdeal ∘ tapeOf` (all pass), the simulator with the programmed oracle
(accepted; rejected without programming), and the ideal-tape prover on a pseudorandom tape with
`H₂³` programmed at its grinding points (accepted; not run for PomFRIT, whose instance depends on
`chal1`). About 15–60 s per run.

**What remains assumed.**
- **The hop hypotheses** (`HopHyps`, `ZK/Hops.lean`), from which the tape hypothesis
  `TapeHyp Hs T st w ε` (`ZK/Exec.lean`: the real run's tape, `tapeOf … rho` for uniform `rho`,
  is `ε`-close to a uniform ideal tape through the ideal-tape prover) is proved with
  `ε = ε_rho + ε_grind + ε_bavc + ε_lab` (`tapeHyp_of_hops`; for PomFRIT `HopHyps2`,
  `tapeHyp2_of_hops`, with `+ ε_abort`, `ε_abort = noHitProb = (|Aᶜ|/2¹²⁸)^{2³²}` by
  `Grinding.card_noHit`). Each is a `Close` bound on a small explicit experiment for a fixed hash
  record; as every statement against all distinguishers in `Privacy/Basic.lean`, that is an
  idealization (a fixed record's `H₃` cannot map 16 bytes of `rho` to 32 uniform bytes against
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
  - **H4** (`HideHyp`, `ε_bavc`, §3's `ε_hide`): assumed. It names only AES and the parameters: for
    every `iv` and `Δ`, the hidden part of a commitment from a uniform root seed is close to
    uniform (spec Lemma 10.24: GGM, leaf commitments and leaf PRGs with AES as an ideal cipher or
    PRP, the four roles' inputs distinct, `Bridge.ctrBlock_ne_of_roles`). The executable AES is
    not parametrized by a cipher, so neither the ideal-cipher model nor the GGM hybrid over the
    `τ` hidden paths is instantiated (`Close.pi` gives the `τ·ε` composition for per-path
    hypotheses).
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
    On `main` this hop fails (§4).
  - The ROM results are per hop, each with its own table, while `tape_close_of_hops` composes the
    fixed-record hypotheses; composing the ROM versions into one bound for a single random record
    (its domains independent tables) is on paper.
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
- `simulateRO_accept` assumes the simulated proof's run reaches `chal3` (checked by `zk_sim`).
- **PomFRIT** (two-phase, delayed instance `h = hash_to_target(…, chal1, …)`):
  `Privacy.PomFRIT.ZeroKnowledge` is derived for the Lean prover with label rows
  (`lean_zeroKnowledge`) from the two-phase tape hypothesis `TapeHyp2` (`ZK/TwoPhase.lean`: the
  tape of a two-phase run, with step 1's output as a fallback block used only if no grinding
  answer is accepted), itself from the hop hypotheses `HopHyps2` (`ZK/TwoPhaseHops.lean`;
  `blindness_lean_shake`: `≤ 4(ε_rho + ε_grind + ε_abort + ε_bavc + ε_lab)`). Once picked, the instance `(pk, h)` is fixed, so the witness `r ‖ s`
  satisfies its system for every `chal1` and combination. `Spec/PomFRITLayout.lean` states the
  protocol on the label-row layout (5579-byte proofs; `hash_to_target` reads `ũ` and `d` at its
  offsets), and `Privacy.PomFRIT.blindness` holds for either layout.
- **Ratatouille:** `Spec.Ratatouille`'s proof sizes are a parameter (`Sizes.main`,
  `Sizes.labelRows`); `unlinkability_label_rows` is on the label-row layout. The spend statement
  has no key digest in its instance encoding (the spec's key is its public map), unlike
  `hash_instance`; zero knowledge does not depend on the encoding.
