# L7 (UOV part): arithmetization soundness for the UOV-based constraints

Scope: the UOV evaluation and the selector of
- PomFRIT redeem (`src/pomfrit/redeem.hpp`), in full;
- Moussaka redeem (`src/moussaka/redeem.hpp`): the bit, selector, parity and weight constraints,
  and the output constraint `l(Q(s)) = l(out)`;
- Ratatouille spend (`src/ratatouille/spend.hpp`): the constraint `l(P(s)) = l(Tag(c, x))`.

The Keccak segments, the adder and the range checks are black boxes here (see `L7-keccak.md`). We
use only their interface: if their uncombined constraints hold at a bit vector `w`, then the
committed output bits `out[8k+j]` equal bit `j` (LSB first) of byte `k` of the stated Keccak
output.

Line numbers refer to branch `voleith-label-rows` (commit `d5def9c`; merged to `main` as `64fd1a4`, with the opt-in flag `CRT_DEDICATED_LABEL_ROWS` replaced by the opt-out `REUSE_CRT_WITNESS`, which Moussaka and Ratatouille set; see `lean/docs/zk.md`, "Status on `main`") (relation headers shifted by up to 6
lines relative to `6d7113e` by the `CRT_DEDICATED_LABEL_ROWS` flag; the constraints are unchanged). Subproject paths are relative to
`subprojects/`.

## 0. Conventions and constraint values

**Fields.** `F = GF(2^128) = GF(2)[X]/(X^128 + X^7 + X^2 + X + 1)`. `poly128` addition is XOR and
`(a*b).reduce_to<128>()` is the product in `F` (`faest-arch-opt/polynomials_constants.hpp:11`,
`polynomials.hpp:309-320`). `K = GF(256) = GF(2)[x]/(x^8 + x^4 + x^3 + x + 1)` is pqov's field
(`pqov/src/gf16.h:79-97`, `gf256_mul`; the 0x11b modulus). A byte `a = Σ_b a_b 2^b` stands for
`Σ_b a_b x^b ∈ K`.

**The embedding.** Let `β_0 = 1` and `β_b = gf8_in_gf128[b-1]` for `b = 1..7`
(`faest-arch-opt/polynomials_constants.cpp:6-14`). Define the `GF(2)`-linear map

    ι : K → F,   ι(Σ_b a_b x^b) = Σ_b a_b β_b.

**Witness decoding.** Witness bit `i` is bit `i mod 8` (LSB first) of witness byte `⌊i/8⌋`
(`faest-arch-opt/quicksilver.hpp:439`: `poly1::load(witness[index / 8], index % 8)`). For
`w ∈ F^ℓ` and a byte offset `o`, write `B_o(w) := Σ_{b<8} β_b w_{8o+b} ∈ F`. When `w` is a bit
vector, `B_o(w) = ι(byte o of w)`.

**Constraint values.** Each `add_constraint(e)` call adds one constraint. Its *value* `f_e(w*)` is
the expression `e`, evaluated with field arithmetic in `F` at the committed values `w* ∈ F^ℓ`.
This means:
- `get_witness_bit(i)` is `w*_i`;
- `load_witness_8_bits_and_combine(8o)` is `B_o(w*)`;
- a public constant `c ∈ F` (or `poly1` `c ∈ {0,1}`) is `c`;
- `+`, `*`, degree lifts, `qs_to_gfsecpar` and `qs_mul` act as addition, multiplication and the
  identity.

This is the quantity L4 works with. For the verifier, an expression of formal degree `d` has key
`K(Δ) = Σ_{i≤d} c_i Δ^i` with `c_d = f_e(w*)`, given the VOLE correlations `q_j = v_j + w*_j Δ`.
This follows by structural induction over the operations of `faest-arch-opt/quicksilver.hpp`:
- a constant at degree `d` is `c·Δ^d` (`:664-685`);
- a lift multiplies by `Δ^{d-d'}` (`:716-724`);
- `+` adds keys;
- `*` multiplies keys (`:791-803`);
- `combine_8_bits` is `Σ_b β_b q_{j+b}` (`:905-918`; `from_8_self`, `polynomials.hpp:1066-1072`);
- `vole_mole::detail::qs_mul` falls back to the generic product for the verifier
  (`src/qs_bit.hpp:47-49, 68-70`).

The prover's types track the same top coefficient. Its `value()` follows the same arithmetic
(`quicksilver.hpp:884-903`; `src/qs_bit.hpp:35-46, 58-67`), and `add_constraint` asserts that it
is zero (`quicksilver.hpp:531`). `tests/test.hpp` `BasicPlainQS` evaluates exactly `f_e` on bit
vectors: bits are `bool`, and on `{0,1}` the operations `&` and `^` agree with `·` and `+` in `F`.
Its byte loader is `from_8_byte`, which is `ι` (Lemma 1).

"The uncombined constraints hold at `w`" means `f_e(w) = 0` for every non-combined constraint `e`.
For the single combined constraint per relation, it means `A_k(w) = 0` for every component `k`,
where `f_comb(w) = Σ_k l_k A_k(w)` is the decomposition given below. Each `A_k` is independent of
`l` and of `chal₂`, which is what L4's combination step needs.

## 1. Lemma 1: the GF(256) embedding [proof + exhaustive test]

**Claim.** (a) `uov::detail::embed` (`src/uov/circuit.hpp:35-37`), `faest-arch-opt`'s
`load_witness_8_bits_and_combine` (prover value and verifier key), and `keccak::detail::qs_byte`
(`src/keccak/segmented.hpp:300-307`) all use the map `ι`. (b) `ι` is an injective ring
homomorphism `K → F`.

*(a) Code.*
- `embed(a) = poly128::from_8_byte(a)` (`circuit.hpp:36`), which equals
  `from_8_poly1(bits of a)` (`polynomials.hpp:221-227`).
- `from_8_poly1(bits) = from_1(bits[0]) + Σ_{b≥1} bits[b]·gf8_in_gf128[b-1]`
  (`polynomials.hpp:1042-1048`), where `from_1(c) = c & 1` (`:216`) and `poly1 * poly128` masks
  with the bit (`:981-984`). So `embed(a) = Σ_b a_b β_b = ι(a)`.
- `load_witness_8_bits_and_combine(8o)` loads bits `8o..8o+7` (`quicksilver.hpp:500-517`) and
  calls `combine_8_bits`:
  - the prover sets `value() = from_8_poly1(bits)`, i.e. `B_o(w)` (`:897-900`), and combines each
    tag coefficient with `from_8_self`, which uses the same `β_b` (`:889-895`;
    `polynomials.hpp:1066-1072`);
  - the verifier combines keys with `from_8_self` (`:912-915`).

  The top coefficient is therefore `B_o(w*)` on both sides.
- `qs_byte(state, k) = state[8k] + Σ_{j≥1} state[8k+j]·from_8_byte(2^j)`, and
  `from_8_byte(2^j) = β_j`. So `qs_byte = Σ_j β_j·out_{8k+j}`, i.e. `ι(byte)` on bits.

*(b) Proof.* `ι` is additive by definition, since it is `GF(2)`-linear. Multiplicativity is
checked exhaustively:
- `tests/uov/test_uov.cpp:193` `EmbeddingIsHomomorphism` checks `ι(a)ι(b) = ι(a·b)` and
  `ι(a)+ι(b) = ι(a⊕b)` for all `2^16` pairs, using the test's `gf256_mul_plain`;
- `Gf256MulMatchesPqov` (`:182`) checks, for all pairs, that this function equals pqov's own
  `gf256_mul` (`pqov/src/gf16.h:80`).

`ι(1) = 1 ≠ 0` (`EmbeddingIsInjective`, `:332`). So `ker ι` is a proper ideal of the field `K`,
hence `0`, and `ι` is injective. The test also checks all `256·255/2` pairs directly.

*Tests of (a):*
- `WitnessBytesAreEmbedded` (`:360`): for all 256 byte values, random tags and a random `Δ`,
  the prover's combined value is `embed(a)`, the verifier's combined key is
  `tag + embed(a)·Δ`, and `BasicPlainQS` agrees.
- `KeccakOutputBytesAreEmbedded` (`:402`): `qs_byte = embed` for all 256 bytes.

These checks are exhaustive over `K`, so they count as proof.

**Corollary (Combination).** `Combination::combine(a) = Σ_k l_k ι(a_k)` (`circuit.hpp:79-85`).
`init` sets `t_k[2^b] = l_k ι(2^b)` (`:96-99`). For each `a ∈ [3,256)` that is not a power of two,
it sets `t_k[a] = t_k[a ⊕ low(a)] + t_k[low(a)]` (`:100-105`). Both indices are smaller than `a`,
so they are already set. By induction and linearity of `ι`, `t_k[a] = l_k ι(a)`. This is also
tested for all `k, a` (`CombinationCombinesEmbeddedComponents`, `:416`).

## 2. Lemma 2: the combined public-map evaluation [proof + tests]

Let `p^k_{ij} ∈ K` (`i ≤ j`) be the coefficients that `for_each_monomial`
(`src/uov/public_key.hpp:45-63`) passes for monomial `(i,j)` and component `k`. Define
`P_k(σ) := Σ_{i≤j} p^k_{ij} σ_i σ_j` over `K`.

**Claim 2a.** For any values `s ∈ F^N` and any `l ∈ F^M`, `qs_eval_combined_public_map`
(`src/uov/circuit.hpp:114-137`) has value

    E(s, l) = Σ_k l_k · Σ_{i≤j} ι(p^k_{ij}) s_i s_j.

In particular, `E(ι(σ), l) = Σ_k l_k ι(P_k(σ))` by Lemma 1.

*Proof.*
1. `for_each_monomial` visits each pair `(i,j)` with `0 ≤ i ≤ j < N` exactly once:
   - `i < V` gives `j ∈ [i,V)` (P1) and then `j ∈ [V,N)` (P2), at `:50-57`;
   - `i ≥ V` gives `j ∈ [i,N)` (P3), at `:58-62`.

   The values of `i` are non-decreasing, and every `i ∈ [0,N)` occurs (at least `(i,i)`).
2. In the evaluation loop, `zero_1 = s_0 + s_0` has value `0` (`circuit.hpp:122`).
   - `row` accumulates `c_{ij} s_j` with `c_{ij} = combine(p^·_{ij}) = Σ_k l_k ι(p^k_{ij})`
     (Corollary).
   - When `i` changes, `s_{current_i}·row` is added to `y` and `row` is reset (`:128-132`). After
     the loop, the last row is flushed (`:135`).

   By (1), `y = Σ_i s_i Σ_{j≥i} c_{ij} s_j`, which expands to the formula above.
3. With `s_i = ι(σ_i)`, the homomorphism gives `ι(p) ι(σ_i) ι(σ_j) = ι(p σ_i σ_j)`, and additivity
   gives the sum. ∎

`E` is a polynomial in `s` whose coefficients are linear in `l`. So
`E(s, l) = Σ_k l_k E_k(s)` with `E_k(s) := Σ_{i≤j} ι(p^k_{ij}) s_i s_j` independent of `l`.
Taking `l = e_k` gives `E(s, e_k) = E_k(s)`.

**Claim 2b.** `P` is pqov's public map, i.e. `P(σ) = PublicKey::eval(σ)`.

- The bytes passed are `pk_t.pk` (`src/uov/uov.cpp:108-112`), and `PublicKey::eval` calls
  `ov_publicmap_ct` on the same bytes (`uov.cpp:100-105`).
- The sizes match pqov's: `uov.cpp:35-40` asserts `V = _V`, `M = _O`, `N = _PUB_N`, and that the
  key is `P1 ‖ P2 ‖ P3` with pqov's block sizes.

*Code reading.* pqov's reference `ov_publicmap` (`pqov/src/ov_publicmap.c:440-457`, via
`accu_eval_quad_gf256`, `:170-270`) reads the key sequentially:
- P1: rows `i < v`, `j ∈ [i,v)`;
- P2: rows `i < v`, `j ∈ [v,n)`;
- P3: rows `i ∈ [v,n)`, `j ∈ [i,n)`.

Each step reads one `M`-byte vector, which is accumulated into `x_i x_j`. This is exactly
`for_each_monomial`'s order. `ov_publicmap_ct` (`:466-487`) uses the same layout:
- P1 and P3 are upper-triangular row-major (`batch_quad_trimat_eval`);
- P2 is `V` blocks of `O·M` bytes, i.e. offset `(i·O + (j−V))·M` (`gfmat_prod`).

*Tests.*
- `ForEachMonomialMatchesPqovLayoutForRandomKeys` (`tests/uov/test_uov.cpp:483`) evaluates
  `Σ p^k_{ij} σ_iσ_j` with `for_each_monomial` on 32 uniformly random raw key byte strings (not
  just keygen outputs) at random `σ`. It compares the result with both `ov_publicmap` and
  `ov_publicmap_ct`.

  All three functions are linear in the key and quadratic in `σ` (code reading). If two of them
  differed, Schwartz–Zippel would detect the difference on each sample with probability
  `≥ 1 − 3/256`. The chance of missing it is below `2^{−200}`.
- `PlainEvalWithUnitVectorsMatchesPqov` (`:435`) runs the actual circuit
  `qs_eval_combined_public_map` under `BasicPlainQS<2>`, with every unit vector `l = e_k`. It uses
  2 real keys at 7 points (0, all-ones, a derived preimage, 4 random). It checks
  `E(ι(σ), e_k) = ι(ov_publicmap(σ)_k)` for all `k`, and that `PublicKey::eval` agrees with
  `ov_publicmap`.
- `CircuitEvalCombinedPublicMapMatchesPlaintext` and `...UnitVectors` (`:268`, `:293`; existing)
  do the same with the real QuickSilver prover types for a derived `l`.

*Status.* 2a is proved. 2b is proved by code reading, plus the randomized identity test above.
Under the code-reading hypothesis (bilinear form) that test has error below `2^{−200}`. The
UOV/pqov spec defines `P` via `ov_publicmap`, so this is the stated `P`.

*Update (Lean).* For `ov_publicmap` the identity is now proved: `Pqov.ovPublicmap_eq_publicMap`
(`lean/VoleMole/Arith/Pqov.lean`) models its pointer walk, nibble buckets and `madd_reduce_gf256`
over an abstract commutative ring and proves it equal to the `for_each_monomial` layout, and
`lake exe arith_vectors` checks the model against pqov's output. `ov_publicmap_ct` (used by
`PublicKey::eval`) is not modelled; its agreement with `ov_publicmap` rests on the tests above.

## 3. Lemma 3: bit constraints [proof]

`qs_add_bit_constraint(x)` (`src/qs_bit.hpp:75-77`) adds `qs_mul(x, x + 1)`. Its value is
`w_i(w_i + 1)`. Over the field `F` this is zero iff `w_i ∈ {0,1}`.

Witness bits covered, per relation:
- **PomFRIT:** every `i < REDEEM_WITNESS_BITS = 8(M+N)` (`src/pomfrit/redeem.hpp:120-123`).
- **Ratatouille spend:** every `i < SPEND_WITNESS_BITS` (`src/ratatouille/spend.hpp:341-344`).
- **Moussaka redeem:**
  - every `i < 8·REDEEM_WIT_OFF_B` gets a bit constraint (`src/moussaka/redeem.hpp:218-221`);
  - for the selector bits `8·REDEEM_WIT_OFF_B + u`, `u < MAX_ANCHORS`, the code adds a bit
    constraint if `u < n` and the constraint `b_u = 0` (value `b_u`) otherwise (`:223-232`);
  - since `REDEEM_WITNESS_BITS = 8·REDEEM_WIT_OFF_B + MAX_ANCHORS` (`:79-81`), every witness bit
    is constrained to `{0,1}`, and to `0` for `u ≥ n`.

For L4 and the assembly: "every witness bit has a bit constraint" holds in the form "every witness
bit has a constraint that implies it is a bit". For Moussaka, the `b_u = 0` constraints are
degree 1, not of the form `x(x+1)`.

## 4. PomFRIT redeem [proved]

Witness layout: `r` = bytes `[0, M)` and `s` = bytes `[M, M+N)` (`redeem.hpp:42-45`). Bytes
decode as `ρ_k, σ_i ∈ K`. The combined constraint (`:125-142`) is
`lp + (lr + lh)` lifted to degree 2, where:
- `lp = E(S(w), l)` with `S_i(w) = B_{M+i}(w)` (`:126-131`);
- `lr = Σ_k l_k B_k(w)` (`:134-138`);
- `lh = Σ_k l_k ι(h_k)` (`:135-141`).

By Claim 2a,

    f_comb(w) = Σ_k l_k A_k(w),   A_k(w) = E_k(S(w)) + B_k(w) + ι(h_k).

`A_k` depends only on `w`, `pk` and `h`.

**Theorem.** Let `w` satisfy all uncombined constraints. Then `w` is a bit vector (Lemma 3), and
`P(σ) = h + ρ`. That is, `(ρ, σ)` is a valid witness for the instance `(pk, h)`.

*Proof.* By Lemma 1, `S_i(w) = ι(σ_i)` and `B_k(w) = ι(ρ_k)`. By Claim 2a,
`A_k(w) = ι(P_k(σ)) + ι(ρ_k) + ι(h_k) = ι(P_k(σ) + ρ_k + h_k)`. `A_k = 0` and injectivity give
`P_k(σ) = h_k ⊕ ρ_k` for all `k`. By Claim 2b, `P` is pqov's public map, so
`PublicKey::eval(σ) = h ⊕ ρ`. ∎

The converse also holds: an honest witness satisfies every constraint. There are
`REDEEM_NUM_CONSTRAINTS = 8(M+N) + 1` constraints (`:49-50`). Tests in
`tests/pomfrit/test_redeem.cpp`:
- `HonestWitnessSatisfiesAllConstraints` (incl. other challenges, keys, targets, and `r = 0`);
- `AnyWitnessBitFlipViolatesAConstraint`: every one of the 1312 bits violates the output
  constraint;
- `WrongInstanceViolatesAConstraint`: every component of `h`, and the key;
- `RejectsWrongComponents`: each single wrong component of `P(s) = h + r`.

## 5. Moussaka redeem: selector and UOV parts [proved, given the Keccak interface]

Instance: `n = |anchors|`, with `1 ≤ n ≤ MAX_ANCHORS = 64`. This is enforced by `AnchorSet`
(`src/moussaka/moussaka.cpp:139-142`), the only type through which the verifier receives anchors.
`RedeemRelation::constraints` itself indexes `b[u]` for `u < n` (`redeem.hpp:259-262`), so it
relies on `n ≤ MAX_ANCHORS`.

**Selector constraints** (`redeem.hpp:223-242`), with `b_u = w_{8·OFF_B + u}`:
- (S1) `b_u(b_u + 1) = 0` for `u < n`, and `b_u = 0` for `n ≤ u < 64`;
- (S2) parity: for `u = 0..62`, `π_u · b_{u+1} = 0`, where `π_u = Σ_{v≤u} b_v`. `prefix` is a
  `qs_bit` sum, i.e. field addition (`:235-239`);
- (S3) weight: `π_63 + 1 = 0` (`:242`).

**Lemma 4.** For a bit vector `b`, (S1)–(S3) hold iff `b = e_{u₀}` for some `u₀ < n`.

*Proof.* (⇐) Take `b = e_{u₀}`, `u₀ < n`. Then (S1) holds. For (S2), `π_u b_{u+1} ≠ 0` would need
`b_{u+1} = 1` (so `u+1 = u₀`) and `π_u = 1`, but `π_{u₀−1} = 0`. For (S3), `π_63 = 1`.

(⇒) For bits, `π_u` is the parity of `b_0..b_u`, since char `F = 2`. Suppose at least two bits
are set, and let `v₁ < v₂` be the two smallest set indices. Then `π_{v₂−1} = b_{v₁} = 1` and
`b_{v₂} = 1`, so (S2) at `u = v₂−1` fails. Hence at most one bit is set. (S3) says the parity is
1, so exactly one bit `u₀` is set. (S1) forces `u₀ < n`. ∎

Test: `SelectorConstraintsHoldIffOneHot` (`tests/moussaka/test_redeem.cpp:240`) checks the
(S1)–(S3) constraint indices of the real relation against "one-hot below `n`" (`n = 5`) for:
- all `b` of weight ≤ 2 (2080 vectors);
- all `b` supported on indices `< 8`;
- 128 random vectors.

The existing `RejectsWrongSelector` and `ParityConstraintsRejectOddWeight` also cover this.

**Output constraint** (`redeem.hpp:251-270`). With `S_i(w) = B_{OFF_S+i}(w)` (`:254-257`):
- `lq = Σ_{u<n} b_u · E^{(u)}(S(w), l)`, where `E^{(u)}` is Claim 2a's `E` for key `anchors[u]`
  (`:258-262`; `qs_mul<1,2>` has value `b_u·E`, `qs_bit.hpp:58-72`);
- `lout = Σ_k l_k O_k(w)` with `O_k(w) = Σ_j β_j out_{8k+j}(w)` (`:266-270`).

The constraint is `lout + lift(lq)`, so

    f_comb(w) = Σ_k l_k A_k(w),   A_k(w) = O_k(w) + Σ_{u<n} b_u E^{(u)}_k(S(w)).

`A_k` is independent of `l`: `b`, `E^{(u)}_k` and `O_k` do not involve `l`.

**Theorem.** Let `w` satisfy all uncombined constraints. Then:
1. `w` is a bit vector;
2. `b = e_{u₀}` for a unique `u₀ < n`;
3. `P_{u₀}(σ) = out`, where `out` is the first `M` bytes of the last Keccak segment's output.

Given the Keccak interface (`L7-keccak.md`), `out = Com(nf, ctx_iss, ctx_red, r)`. So `(r, σ, u₀)`
satisfies the stated relation: `σ` is a preimage of the commitment under the selected anchor key.

*Proof.* (1) is Lemma 3, and (2) is Lemma 4. For (3):
- `Σ_u b_u E^{(u)}_k = E^{(u₀)}_k(ι(σ)) = ι(P_{u₀,k}(σ))`, by Claim 2a and Lemma 1;
- `O_k(w) = ι(out_k)` by Lemma 1 (`qs_byte = ι` on bits).

`A_k = 0` gives `ι(out_k + P_{u₀,k}(σ)) = 0`, so `P_{u₀,k}(σ) = out_k` by injectivity. With
Claim 2b, this is `anchors[u₀].eval(σ) = out`. ∎

In particular, with one-hot `b`, the combined equation is `P_{u₀}(s) = target` and never a mixture
`Σ_u b_u P_u`. Without the parity constraints, `b` of odd weight would pass (S1) and (S3), and
the equation would select `Σ_{u∈b} P_u`. `ParityConstraintsRejectOddWeight` demonstrates this.
Duplicate keys in the instance are harmless: the theorem names an index `u₀`, and `P_{u₀}` is
that index's key.

## 6. Ratatouille spend: the UOV part [proved, given the Keccak interface]

With `S_i(w) = B_{SPEND_WIT_OFF_S+i}(w)` (`spend.hpp:380-383`), `lp = E(S(w), l)` for the key
`x.pk` (`:384`). `ly = Σ_k l_k T_k(w)` with `T_k(w) = Σ_j β_j tag_out_{8k+j}(w)` (`:385-388`), and
the constraint is `ly + lift(lp)` (`:389`). So

    f_comb(w) = Σ_k l_k A_k(w),   A_k(w) = T_k(w) + E_k(S(w)).

**Theorem.** Let `w` satisfy all uncombined constraints. Then `w` is a bit vector (Lemma 3), and
`P(σ) = tag`, where `tag` is the first `M` bytes of the Tag segment's output. Given the Keccak
interface, `tag = Tag(c, x)`, where `c`, `x` are the witness bytes at `SPEND_WIT_OFF_C` and
`SPEND_WIT_OFF_X`. The Keccak agent's part supplies `c = Com(nf, ctx_iss, t, r)`. Together these
give V1: `P(s) = Tag(Com(nf, ctx_iss, t, r), x)`.

*Proof.* `T_k(w) = ι(tag_k)` and `E_k(S(w)) = ι(P_k(σ))` (Lemma 1, Claim 2a). Then `A_k = 0` and
injectivity give `P_k(σ) = tag_k`, and Claim 2b identifies `P` with `pk.eval`. ∎

Existing tests: `tests/ratatouille/test_spend.cpp` (`HonestWitnessSatisfiesAllConstraints`,
`AnyWitnessBitFlipViolatesAConstraint`, `WrongInstanceViolatesAConstraint`).

## 7. Where we rely on tests rather than proof

| Fact | Basis |
|---|---|
| `ι` additive | definition (linear) |
| `ι` multiplicative | exhaustive test over `K×K` (= proof), with the test's GF(256) multiplication checked exhaustively against pqov's `gf256_mul` |
| `ι` injective | proof (field homomorphism with `ι(1)=1`), plus exhaustive test |
| witness loader, verifier key combination, `qs_byte` all equal `ι` | code reading, plus exhaustive test over all 256 bytes |
| `Combination` tables `= l_k ι(a)` | proof by induction, plus exhaustive test |
| `qs_eval_combined_public_map` `= Σ_k l_k ι(P_k)` | proof (Claim 2a), plus tests with unit vectors |
| `for_each_monomial` layout `=` pqov's `ov_publicmap` / `ov_publicmap_ct` | `ov_publicmap`: proved in Lean (`Arith/Pqov.lean`) for a model of the C code. `ov_publicmap_ct`: code reading, plus randomized identity test on random keys (miss probability `< 2^{−200}`, given the bilinear form) |
| QuickSilver top-coefficient semantics (`f_e`) | structural induction over `quicksilver.hpp` (§0); the "check polynomial" part belongs to L4 |
| selector ⇒ one-hot | proof (Lemma 4), plus tests |
| Keccak outputs `out`, `tag`, and `c = Com(…)` | black box (`L7-keccak.md`) |
| `1 ≤ n ≤ MAX_ANCHORS` | `AnchorSet` constructor (`moussaka.cpp:139`); not checked in `constraints()` |

## 8. Findings

No soundness bug was found in the UOV or selector arithmetization. Notes:
- Moussaka's selector bits for `u ≥ n` are constrained by `b_u = 0` (degree 1) rather than by a
  bit constraint. This is stronger, but L4/assembly should state the bit-vector conclusion as
  "every witness bit is constrained to `{0,1}`".
- `RedeemRelation::constraints` (Moussaka) indexes the fixed-size array `b` by `u < n` without
  checking `n ≤ MAX_ANCHORS`. This is safe only because every caller passes `AnchorSet::keys()`.
  It is not a soundness issue for the stated relation, whose instance requires
  `n ≤ MAX_ANCHORS`.
- The combined constraint's components `A_k(w*)` are fixed polynomials in `w*`, independent of
  `l = H(chal₂ ‖ dst)`, as L4's combination lemma requires. This holds for arbitrary `w* ∈ F^ℓ`,
  not just bit vectors (Claim 2a holds for arbitrary `s`).
