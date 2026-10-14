# L7 (Keccak and arithmetic): constraints ⇒ relation

This note proves the Keccak and integer-arithmetic half of Lemma L7 (see `README.md`). For
Moussaka issue, Ratatouille issue, the Keccak parts of Moussaka redeem, and the Keccak, adder,
range and conservation parts of Ratatouille spend, it shows that **any bit vector `w` satisfying
every uncombined constraint satisfies the stated relation** for the decoded witness `Dec(w)`.

The UOV public-map evaluation and the Moussaka selector are treated as black boxes; they are
covered by `L7-uov.md`. All citations are to branch `voleith-label-rows` (commit `d5def9c`), which differs from `6d7113e` in the
relation headers only by the `CRT_DEDICATED_LABEL_ROWS` flag; the constraints are unchanged.

Status: **[paper + tests]**. The proof is complete, given the following:
- a few facts about finite objects, verified by exhaustive or basis tests that amount to proofs
  (§2.3);
- the correspondence, by inspection, between the test harness and the relation code (§6).

No soundness bug was found.

## 0. Corrections to the task statement

- The permutation is **Keccak-p[800, 12]**, not Keccak-f[1600]. It has 25 lanes of 32 bits and
  runs rounds 10..21 of Keccak-f[800] (`src/keccak/tables.hpp:43-51`,
  `include/vole_mole/keccak.hpp:10-13`).
- There is **no sponge**. Every commitment and tag is one call of the permutation on a fixed-layout
  100-byte state, truncated to its first bytes:
  - Moussaka `commit`: `src/moussaka/moussaka.cpp:89-95`;
  - Ratatouille `commit` and `tag`: `src/ratatouille/ratatouille.cpp:94-107`.
  So there is no padding, no rate or capacity, and no multi-block absorption to check. Domain
  separation comes from the 7-byte DST at offset 0 (`src/dst.hpp:33,48,54`).

  The relations are *stated* in terms of exactly these functions, so for L7 the KAT conformance of
  `keccak_p800` to FIPS 202 is irrelevant. That conformance is still tested
  (`tests/keccak/test_keccak.cpp` `KnownAnswers`, against `tests/keccak/keccak_ref.py`, which
  self-checks against `hashlib.sha3_256`).

## 1. Semantics of a constraint

L4 delivers a vector `w ∈ {0,1}^ℓ ⊂ F_{2^128}^ℓ` on which every uncombined constraint polynomial
vanishes. A constraint is the polynomial over `F = F_{2^128}` obtained by reading the relation code
with these meanings:
- `qs_bit` / `quicksilver_gf2` addition is `+` in `F`;
- `qs_mul` is `·` in `F`;
- `poly1(c)` is the constant `c ∈ {0,1}`;
- `qs_to_gfsecpar` is the identity;
- `from_8_byte(b)` is a fixed element of `F`.

L4 / faest-arch-opt is responsible for the QuickSilver prover and verifier types computing the MAC
algebra of exactly this polynomial. That includes the custom bit products in `src/qs_bit.hpp:31-73`.

**Fact 1.1 (bits stay bits).** `{0,1} = F_2` is a subfield of `F`. So every expression built from
witness bits and constants with `+` and `·` alone evaluates to an element of `F_2`, with `+` = XOR
and `·` = AND. This covers every `qs_bit` expression in the Keccak circuit and the adder. In
particular:
- the χ lambda `a + (b+1)·c` (`src/keccak/segmented.hpp:133-136`) evaluates to `a ⊕ (¬b ∧ c)`;
- the χ⁻¹ lambda `a + (b+1)·(c + (d+1)·e)` (`segmented.hpp:159-166`) evaluates to
  `a ⊕ (¬b ∧ (c ⊕ (¬d ∧ e)))`.

A constraint `X + Y = 0` with `X, Y ∈ F_2` holds iff `X = Y`.

The test harness `PlainQS` (`tests/test.hpp`) implements exactly this reading: bits as `bool`
with XOR and AND, and field values as `poly_secpar`. Tests that run the relation code on `PlainQS`
therefore evaluate the constraint polynomials at `w`.

## 2. Keccak segments

### 2.1 Notation

Write `S = F_2^800`, with bit `i` of a state being bit `i mod 8` of byte `⌊i/8⌋`, and
`i = 32(5y+x)+z` (`src/keccak/tables.hpp:67-69`). The circuit defines, for round `j`:
- `L` = π∘ρ∘θ, which is `keccak_theta_rho_pi` (`src/keccak/circuit.hpp:29-60`);
- `L⁻` = `keccak_theta_rho_pi_inverse` (`circuit.hpp:94-155`);
- `N_j` = ι_j∘χ, the non-linear part of `keccak_round` (`circuit.hpp:68-91`), instantiated with
  the χ lambda of `segmented.hpp:131-139`;
- `N_j⁻` = `keccak_iota_chi_inverse` (`circuit.hpp:161-187`), instantiated with the χ⁻¹ lambda of
  `segmented.hpp:158-168`;
- `R_j = N_j ∘ L`, which is `qs_keccak_round` (`segmented.hpp:131-139`).

`R*_j` is the lane-based round `round800` in `src/keccak/keccak.cpp:17-50` with constant
`KP800_RC[j]`. The relations' `keccak_p800 = R*_11 ∘ … ∘ R*_0` (`include/vole_mole/keccak.hpp:25-28`,
`keccak.cpp:54-74`).

### 2.2 Structural facts (by inspection)

- **(S1)** `keccak_theta_rho_pi` and `keccak_theta_rho_pi_inverse` are templates over `T` that use
  only `T + T`, with no constants (`circuit.hpp:29,94`). Each output bit is therefore a fixed XOR of
  input bits, so both maps are `F_2`-linear.
- **(S2)** In `round800`, θ, ρ and π (`keccak.cpp:20-39`) use only XOR and rotations, so they form an
  `F_2`-linear map `L*`. χ (`keccak.cpp:41-46`) is `b[x,y] ⊕ (¬b[x+1,y] ∧ b[x+2,y])`, the same formula
  and the same indices as the circuit (`circuit.hpp:77-81`). ι XORs `KP800_RC[j]` into lane 0, which
  is the bits `idx(0,0,z)` (`keccak.cpp:48-49` vs `circuit.hpp:84-89`). Lanes are packed little-endian
  (`keccak.cpp:59-61`), which matches the bit numbering. Hence `R*_j = N_j ∘ L*`.
- **(S3)** `N_j⁻` first applies ι_j, an involution. It then applies χ⁻¹ row-wise and writes its
  output in index order (y, x, z), which is `idx` order (`circuit.hpp:166-186`).
- **(S4)** χ, χ⁻¹ and ι act on the 160 rows `(y,z)` independently.

### 2.3 Finite facts (verified by tests that amount to proofs)

- **(F1)** `L⁻ ∘ L = L ∘ L⁻ = id_S`. Both are linear (S1), so it suffices to check all 800 unit
  vectors. Test: `tests/keccak/test_keccak.cpp:243` `LinearLayerInverseOnBasis`.
- **(F2)** `N_j⁻ ∘ N_j = N_j ∘ N_j⁻ = id_S` for every `j < 12`, with the χ and χ⁻¹ lambdas *as used to
  generate constraints*. By (S4) it suffices that every row takes all 32 values, and `row_state(v)`
  for `v < 32` achieves this in every row. The test isolates `N_j` as `qs_keccak_round(L⁻(s))`,
  using F1. The same test also checks `N_j` against an independently written
  `a ⊕ (¬b∧c)` with ι. Test: `test_keccak.cpp:259` `ChiInverseExhaustive`.
- **(F3)** `R*_j = R_j` for every `j < 12`. By (S2) and (F2):

      N_j⁻(R*_j(v)) = N_j⁻(N_j(L*(v))) = L*(v).

  `RoundMatchesLanesOnBasis` (`test_keccak.cpp:306`) checks `N_j⁻(R*_j(v)) = L(v)` for `v = 0` and
  all 800 unit vectors. So `L* = L` on a basis, and both are linear (S1, S2), so `L* = L`. Hence
  `R*_j = N_j ∘ L = R_j`.
- **(F4)** The map `β : {0,1}^8 → F`, `β(b) = Σ_j b_j·from_8_byte(2^j)` (the function `qs_byte`,
  `segmented.hpp:299-307`), is injective and equals `from_8_byte`. This is checked exhaustively
  over the 256 bytes (`test_keccak.cpp:457` `ByteEmbeddingIsInjective`).

### 2.4 Segment soundness

`qs_keccak` (`segmented.hpp:284-293`) runs `segment_constraint<k>` for `k = 0, 1`, then
`FINAL_ROUNDS = 3` forward rounds. The layout is `SEGMENTS = {{3,2},{2,2}}` (`segmented.hpp:69-70`):
- `SEGMENT_START = (0, 5, 9)`;
- `5 + 4 + 3 = 12` rounds (`static_assert` at `:86`);
- degrees `max(2³,3²) = 9` and `max(2²,3²) = 9`, and the output has degree `2³ = 8` (`:98-104`).

The degrees are tracked in the types and bounded by `static_assert(QS::max_degree >= QS_DEGREE)`
(`:287`). They matter for L4, not for L7.

**Lemma 2.1 (one segment).** Fix segment `k`, with `a = SEGMENT_START[k]`, forward `f`, backward
`b ≥ 1`, and `e = a+f+b = SEGMENT_START[k+1]`. Let `s` be the incoming state (as polynomials) and
`s'` the 800 witness bits at `8·(wit_off_states + 100k)` (`segmented.hpp:248-253`). If all 800
constraints of the segment (`:266`) hold at `w`, then

    s' = R_{e−1} ∘ … ∘ R_a (s).

*Proof.* By Fact 1.1, constraint `i` says `lin_i = bwd_i` in `F_2`, so `lin = bwd` as vectors. Here:
- `fwd = R_{a+f−1}∘…∘R_a(s)`: `qs_keccak_rounds` (`:144-154`) recurses through `first_round + 1`,
  and all intermediate rounds are full.
- `lin = L(fwd)` (`:262`).
- `bwd = B(s')`, with `B = N_{a+f}⁻ ∘ L⁻ ∘ N_{a+f+1}⁻ ∘ … ∘ L⁻ ∘ N_{e−1}⁻`, unrolling
  `qs_keccak_rounds_inverse_partial` (`:176-186`).

Let `G = N_{e−1} ∘ L ∘ … ∘ L ∘ N_{a+f}`. Then `G ∘ B = id` by telescoping with F1 and F2. Applying
`G` to `lin = B(s')` gives

    s' = G(L(fwd)) = (N_{e−1}L)∘…∘(N_{a+f}L)(fwd) = R_{e−1}∘…∘R_{a+f}(fwd).  ∎

Lemma 2.1 also shows that the segment's constraints have the *unique* solution `s' = G(lin)`, the
true round output. The test `SegmentBackwardSideIsInjective` (`test_keccak.cpp:377`) checks
`G(B(s)) = s` on the code as instantiated, for 50 states per segment.

**Lemma 2.2 (permutation).** Let `s₀` be the input state passed to `qs_keccak`, and suppose all
`NUM_SEGMENT_CONSTRAINTS = 1600` segment constraints hold. Then for `i < num_out_bits` the returned
bit `out_i` equals bit `i` of `keccak_p800(s₀)`.

*Proof.* By Lemma 2.1 twice, the committed states are `s₅ = R₄∘…∘R₀(s₀)` and
`s₉ = R₈∘…∘R₅(s₅)`. The final segment (`:291-292`) computes `R₁₁∘R₁₀∘R₉(s₉)`; only the last round
is truncated to `num_out_bits`. In that round, χ reads the full `b = L(in)` (`circuit.hpp:74-81`),
and ι is applied to the bits with `z < num_out_bits` (`:85`). So the computed bits are a prefix of
the full round output. By F3, `R_j = R*_j`, and the composition is `keccak_p800(s₀)`. ∎

Nothing in the chain is left free:
- every bit of `s₅` and `s₉` enters `B`, which is a bijection;
- the input is tied to the witness by `qs_input` (§3);
- the last three rounds are computed, not committed;
- each relation compares the output bits it needs (§4–§5).

### 2.5 Input wiring

`qs_input` (`segmented.hpp:225-239`) makes bit `i` of the input either:
- witness bit `8·map[⌊i/8⌋] + (i mod 8)`, if `map[⌊i/8⌋] ≥ 0`; or
- the constant bit `i` of `public_state`.

Each input byte is therefore either a constant or a copy of one witness byte. For such an affine
map, two witness evaluations decide whether `qs_input(w) = encode(Dec(w))` holds for *all* `w`,
where `encode` copies decoded fields (or constants) bytewise:
1. a witness whose relevant bytes are pairwise distinct, which pins down the source byte of every
   copied position;
2. its bytewise complement, so that a position holding a public constant cannot depend on `w`.

The `KeccakInput(s)IsCommitmentInput` tests below do exactly this. (`input_map_is_valid`, checked
statically, adds that each witness byte is used once, but soundness does not need that.)

## 3. Bit constraints

| Relation | Bit constraints | Coverage |
|---|---|---|
| Moussaka issue | `src/moussaka/issue.hpp:183-185`, `i < ISSUE_WITNESS_BITS` | all bits |
| Ratatouille issue | `src/ratatouille/issue.hpp:171-173` | all bits |
| Ratatouille spend | `src/ratatouille/spend.hpp:348-350`, `i < SPEND_WITNESS_BITS` | all bits, carries included |
| Moussaka redeem | `src/moussaka/redeem.hpp:225-227` for `i < 8·REDEEM_WIT_OFF_B` (r, s, s₅, s₉); `:231-238` for the selector | every bit is either constrained to be a bit (`u < n`) or constrained to `0` (`u ≥ n`) |

So every witness coordinate is in `{0,1}`, and Fact 1.1 applies. (`qs_add_bit_constraint`,
`src/qs_bit.hpp:75-77`, is `x·(x+1) = 0`, whose roots in `F` are exactly `0` and `1`.)

## 4. Per-relation results

`Dec(w)` reads each named field from its witness offset.

### 4.1 Moussaka issue (`src/moussaka/issue.hpp`)

- **Statement:** `t = Com(nf, ctx_iss, ctx_red, r)` for some `nf`, `r`, `ctx_red`.
- **Commitment:** `Com(...) = keccak_p800(encode_com_state(...))[0..M)`
  (`src/moussaka/moussaka.cpp:89-95`).
- **Layout:** `"mous"‖VERSION‖"c0" ‖ r ‖ 0⁹ ‖ ctx_iss ‖ ctx_red ‖ nf ‖ 0¹²`
  (`src/moussaka/commit.hpp:33-48`).
- **Dec:** `r = w[0..16)`, `ctx_red = w[16..32)`, `nf = w[32..56)` (`issue.hpp:58-61`).

The constraint input is `qs_input(encode_com_state({}, ctx_iss, {}, {}), COM_TO_WIT)`
(`issue.hpp:188-190`, map `:67-80`). By §2.5 and the test
`tests/moussaka/test_issue.cpp:121` `IssueRelation.KeccakInputIsCommitmentInput`, it equals
`encode_com_state(nf, ctx_iss, ctx_red, r)` for every `w`. Here `ctx_iss` is a public constant;
`r`, `ctx_red` and `nf` come from the witness.

By Lemma 2.2 (with `num_out_bits = 8M = 360`), `out_i` is bit `i` of `Com`. The output constraints
`out_i + t_i = 0` for all `i < 360` (`issue.hpp:194-195`) give `t = Com(Dec(w))`, compared in full.
`WrongInstanceViolatesAConstraint` checks that each of the 360 bits of `t` is constrained. The new
test `Commitment.Layout` pins the layout above.

**Proved.**

### 4.2 Moussaka redeem, Keccak part (`src/moussaka/redeem.hpp`)

- **Witness:** `r = w[0..16)`.
- **Input:** `qs_input(encode_com_state(nf, ctx_iss, ctx_red, {}), REDEEM_COM_TO_WIT)`
  (`redeem.hpp:251-255`, map `:88-95`). The public `nf`, `ctx_iss` and `ctx_red` are constants.

By `test_redeem.cpp:279` `KeccakInputIsCommitmentInput`, this input equals
`encode_com_state(nf, ctx_iss, ctx_red, r)`. By Lemma 2.2 (all 800 bits), `out = keccak_p800(·)`,
so `qs_byte(out, k) = β(Com_k) = from_8_byte(Com_k)` (F4). `KeccakOutputBytesAreCommitment`
(`:303`) checks this for the honest witness.

Interface to `L7-uov.md`: the *uncombined* output constraints are the `M` components
`qs_byte(out,k) + Q(s)_k = 0`, combined by `l` at `redeem.hpp:270-276`. If `Q(s)_k = from_8_byte(y_k)`
for a byte `y_k` (the UOV half), then injectivity (F4) gives `y = Com(nf, ctx_iss, ctx_red, r)`,
i.e., `Q(s) = Com(...)`.

**Proved for the Keccak part.** The selector and `Q(s)` are in `L7-uov.md`.

### 4.3 Ratatouille issue (`src/ratatouille/issue.hpp`)

- **Statement:** `c = Com(nf, ctx_iss, T_init, r)`.
- **Layout:** `"rata"‖VERSION‖"c0" ‖ r ‖ 0⁹ ‖ ctx_iss ‖ ⟨t⟩₈ ‖ nf ‖ 0²⁰` (`src/ratatouille/commit.hpp:56-77`).
- **Dec:** `r = w[0..16)`, `nf = w[16..40)` (`issue.hpp:55-57`).
- **Input:** `encode_com_state({}, ctx_iss, T_init, {})` with `ISSUE_COM_TO_WIT` (`:176-180`, map
  `:64-75`). The public values `ctx_iss` and `T_init` (little-endian) are constants.

`tests/ratatouille/test_issue.cpp:162` `KeccakInputIsCommitmentInput` establishes the wiring. The
layout is pinned by the pre-existing `Commitment.Layout` (`:125`). With Lemma 2.2
(`num_out_bits = 256`) and the 256 output constraints (`issue.hpp:184-185`), `c = Com(Dec(w))`.

**Proved.**

### 4.4 Ratatouille spend (`src/ratatouille/spend.hpp`)

- **Statement:** V1–V4 (`spend.hpp:1-10`).
- **Dec:** read from `spend.hpp:92-102`: `r`, `t`, `x`, `c`, `nf'`, `t'`, `r'`, `s`, carries `k¹`
  and `k²`, then the states.

**V1, Com.** The input is `encode_com_state(nf, ctx_iss, 0, {})` with `SPEND_COM_TO_WIT`
(`:368-372`). The public `nf` and `ctx_iss` are constants, and the bytes of `r` and `⟨t⟩` come
from the witness. Lemma 2.2 (256 bits) and the constraints `com_out_i + c_i = 0` (`:373-376`)
give `c = Com(nf, ctx_iss, t, r)`, where `c` is the 256 witness bits at `SPEND_WIT_OFF_C`.

**V1, Tag.** The input is `encode_tag_state({}, 0)` with `SPEND_TAG_TO_WIT` (`:378-380`). The
bytes of `c` and `⟨x⟩` come from the witness: the *same* bytes of `c` as above, and the same `x` as
the adder. By Lemma 2.2 (`8M` bits) and F4, `qs_byte(tag_out,k) = from_8_byte(Tag(c,x)_k)`. With the
`M` uncombined components `qs_byte(tag_out,k) + P(s)_k = 0` (combined at `:385-395`) and the UOV
half, `P(s) = Tag(Com(nf, ctx_iss, t, r), x)`.

**V2.** The input is `encode_com_state({}, ctx_iss, 0, {})` with `SPEND_COM_NEXT_TO_WIT`
(`:398-402`), and the bytes of `nf'`, `⟨t'⟩` and `r'` come from the witness. Together with the
256 constraints against public `c'` (`:403-406`), this gives `c' = Com(nf', ctx_iss, t', r')`.

All three wirings are established, for every `w`, by `tests/ratatouille/test_spend.cpp:434`
`KeccakInputsAreRelationInputs`.

**V3 and V4 (adder and conservation).**

*Setup.* Values are read bitwise by `credit_bit(off,i) = 8·off + i` (`src/ratatouille/commit.hpp:54`).
This matches `encode_credits`, which is little-endian (`:36-42`), so the bits read are exactly the
bits of the integers that enter Keccak as `⟨t⟩`, `⟨x⟩` and `⟨t'⟩`. The public `d` enters as the
constant bits `(d ≫ i) & 1` (`spend.hpp:360`).

*Range (V4).* `t`, `x` and `t'` are 64 witness bits each, and `d` is a public `uint64`, so all four
lie in `[0, 2⁶⁴)` by construction.

*Lemma 4.1 (adder).* Let `a_i`, `b_i` (`i < 64`) and `k_1..k_64` be bits, `k_0 = 0`, with the
constraints of `qs_add_credits` (`spend.hpp:194-212`):

    k_{i+1} = a_i b_i + a_i k_i + b_i k_i     (:205-207).

Let `σ_i = a_i + b_i + k_i` (`:203`) and `σ_64 = k_64` (`:210`). Then

    Σ_{i≤64} σ_i 2^i = A + B,   where A = Σ a_i 2^i and B = Σ b_i 2^i.

*Proof.* By Fact 1.1, `k_{i+1} = maj(a_i, b_i, k_i)` and `σ_i = a_i ⊕ b_i ⊕ k_i`. Checking the 8
cases gives `a_i + b_i + k_i = σ_i + 2k_{i+1}` in ℤ. Multiply by `2^i` and sum over `i < 64`; the
carries telescope:

    A + B + Σ_{i<64} k_i 2^i = Σ_{i<64} σ_i 2^i + Σ_{i<64} k_{i+1} 2^{i+1},

so `A + B = Σ_{i<64} σ_i 2^i + 2⁶⁴ k_64`. ∎

*Conservation.* The constraints `sum1_i + sum2_i = 0` for all `i ≤ 64` (`spend.hpp:363-365`)
make the two 65-bit vectors equal. By Lemma 4.1, applied to `(t, x, k¹)` and `(t', d, k²)`,

    t + x = t' + d   in ℤ.

Since `t' ∈ [0, 2⁶⁴)`, this is exactly V3, `t' = t + x − d`, with `0 ≤ t + x − d < 2⁶⁴`. It also
answers the questions in the task:
- *Can the change exceed the balance through carry wrap?* No. Both sums are computed in 65 bits,
  and `t + x ≤ 2⁶⁵ − 2`, so nothing wraps, and `d ≤ t + x` follows from `t' ≥ 0`.
- *Is the range check complete?* Yes. A satisfying `t'` with `t' + d = t + x` exists only if
  `t + x − d ∈ [0, 2⁶⁴)`; otherwise no assignment satisfies the constraints.

Tests:
- `AdderExhaustiveSmall` (`test_spend.cpp:371`) runs over every `a`, `b` with 4 low (resp. 4 high)
  bits and every value of the 5 adjacent carries. The constraints hold iff `k = carries(a,b)`, and
  then the sum is `a + b`. The high-bits case covers the carry out of bit 63.
- `ConservationExhaustiveSmall` (`:399`) runs the full relation on grids of `t'`, `d`, including
  values near `2⁶⁴`. The V3 constraints hold iff `t + x = t' + d` in ℤ.
- The pre-existing `RejectsOutOfRangeChange` and `RejectsUnconservedCredits` corroborate.

**Nullifier.** `nf` is public and enters the current-state commitment as a constant, so the
certified state is bound to the presented nullifier. `nf'` is secret and enters `c'` only.

**Proved for V1 (Keccak part), V2, V3 and V4.** `P(s) = Tag(...)` is in `L7-uov.md`.

## 5. Loophole checklist

| Possible loophole | Status |
|---|---|
| Witness bit without a bit constraint | none (§3) |
| Committed state not tied to the input | no: the segment-0 forward side starts at `qs_input` (Lemma 2.1) |
| Committed state partly free | no: all 800 bits enter `B`, which is a bijection (F1, F2) |
| Missing final rounds | no: 5 + 4 + 3 = 12, static-asserted; the final 3 rounds are computed |
| Output compared only partially | Moussaka issue compares all `8M` bits of `t`; Ratatouille compares all 256 bits of `c`/`c'` and `c`; redeem and Tag compare all `M` bytes via injective `β` (F4) |
| Public bytes wrong, or a witness byte misplaced | excluded by the two-point wiring tests (§2.5) |
| χ / χ⁻¹ lambdas differ from the plain round | F2 tests the QS lambdas themselves, via `PlainQS` |
| Lane-based permutation differs from the circuit | F3, proved on a basis |
| Carry wrap / overflow | no (§4.4) |
| Sum bits treated as field elements, not bits | the `σ_i` are `qs_bit` sums of bits; by Fact 1.1 they are XORs |

## 6. What rests on tests or inspection rather than proof

- **(S1)–(S4)**: by inspection of short loops; cited above.
- **F1–F4**: by tests that enumerate the whole finite domain (32 row values × 160 rows × 12 rounds;
  800 basis vectors; 256 bytes). They rely on (S1)–(S4) to reduce to that domain.
- **Wiring (§2.5).** The tests call `qs_input` with the *same* map constant and the same
  public-state expression as the relation's `constraints`. That the expression is the same is by
  inspection of the cited lines; the tests do not intercept the call inside `constraints`.
- **Semantics (§1).** The `PlainQS` reading equals the polynomial that the real QuickSilver types
  commit to. This is the responsibility of L4 and faest-arch-opt.
- **Adder (Lemma 4.1).** A paper proof; the tests only corroborate it.
- **FIPS 202 conformance** of `keccak_p800`: by KAT only. L7 does not need it (§0).

## 7. Tests added

All tests pass in `build-keccak`. `meson test` passes all 17 suites.

- **`tests/keccak/test_keccak.cpp`:**
  - `LinearLayerInverseOnBasis`, `ChiInverseExhaustive`, `RoundMatchesLanesOnBasis`: F1–F3.
  - `SegmentsAcceptTrueTrace`: 20 inputs; the output equals `keccak_p800`.
  - `SegmentBackwardSideIsInjective`: `G∘B = id` for both segments.
  - `SegmentsRejectWrongStates`: random states, and states at distance 1 and 2 from the true
    state, violate their own segment.
  - `InputPlacesBytes`, `ByteEmbeddingIsInjective`: F4.
- **`tests/moussaka/test_issue.cpp`:** `IssueRelation.KeccakInputIsCommitmentInput`,
  `Commitment.Layout`.
- **`tests/moussaka/test_redeem.cpp`:** `KeccakInputIsCommitmentInput`,
  `KeccakOutputBytesAreCommitment`.
- **`tests/ratatouille/test_issue.cpp`:** `IssueRelation.KeccakInputIsCommitmentInput`.
- **`tests/ratatouille/test_spend.cpp`:** `AdderExhaustiveSmall`, `ConservationExhaustiveSmall`,
  `KeccakInputsAreRelationInputs`.
