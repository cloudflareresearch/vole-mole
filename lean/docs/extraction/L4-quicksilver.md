# L4: QuickSilver with chall₂-dependent constraints (the sketch's Claim 3)

Status: **[paper]** (this file) and **[Lean]** for the algebraic and counting cores
(`lean/VoleMole/Seed/QuickSilver.lean`, see §9). The random-oracle step (§5–§6: what is fixed
before chall₂, and the joint distribution of `(chall₂, l)`) is on paper only.

Notation is as in `README.md`: `F = F_{2^128}`, a challenge is `Δ' ∈ F₂^{120}`, and
`Δ = e(Δ') = W_crt·Δ'` is the injective CRT lift. Also ℓ = WITNESS_BITS, `d` = QS_DEGREE (2 or 9),
and `n` = NUM_CONSTRAINTS. All arithmetic is in characteristic 2, so `+ = −`.

## 1. Statement

Fix a relation and an `H₂²` query of `P*` with input `y`, made for the first time. Write
`chall₂ = H₂²(y)`. From `y` and the queries `P*` made before it, define the following (§5):
- `x`, the statement, and hence the constraint circuits;
- the correction `d ∈ F₂^ℓ`;
- the canonical slope `u* ∈ F^ℓ` of L3 (§5), and `w* := u* + d ∈ F^ℓ`.

For `l ∈ F^M`, let `f(w*; l) ∈ F^n` be the constraint values (§3). One slot `k₀` may depend on
`l`, through `f_{k₀} = Σ_m l_m a_m(w*)`. The **uncombined constraints** are `f_k` for `k ≠ k₀`
together with `a_0, …, a_{M−1}`. In a relation with no combined slot, they are just the `f_k`.

**Lemma L4.** Let `B_y` be the event that some uncombined constraint is nonzero at `w*` and
`Σ_k χ_k(chall₂) f_k(w*; l) = 0`, where `l = H_comb(chall₂ ‖ dst)`. Then

    Pr_{chall₂}[B_y] ≤ ε_QS(n) + 2^{−128} + q_c·2^{−448},
    ε_QS(n) := 2^{−128} + (n − 1)²·2^{−192},

where `q_c` is the number of `H_comb` queries made before `y`. The last term is 0 for relations
without a combined slot, and so is the `2^{−128}`.

Suppose `B_y` does not occur. Then on **every** `H₂³` chain extending `y` (any `ã`, `qs_check`,
`ctr`), with `A` the chain's accepting set:
- either every uncombined constraint holds at `w*`, in which case `w* ∈ {0,1}^ℓ` and
  `u*[j] ∈ {0,1}` for every `j < ℓ` (this is `hbits`);
- or `|A| ≤ d`.

**Union.** Summing over the distinct `H₂²` inputs gives `q_{H₂²}·(ε_QS + 2^{−128} + q·2^{−448})`.
The README's `Q·(ε_QS + 2^{−128})`, with `Q` the number of `H₂³` queries, is **not** justified:
`P*` sees `chall₂` before it decides whether to spend `H₂³` queries on it (§8, finding 1).

Hypotheses used:
- **(H-L3)** L3 as stated in `L3-kos.md`: except with ε_KOS over chall₁, for the chain's
  `(ũ, h_V)` and *every* `A' ⊆ S` on which the KOS check passes, the witness rows and the
  QuickSilver mask rows `q̄_0..q̄_{d−2}` are affine in `e(Δ')` on `A'`. L4 applies this to
  `A_V := {Δ' ∈ S : the KOS check passes with the chain's (ũ, h_V)}`, which contains `A`.
- **(H-DS)** Domain separation (for agent L0). `H_comb(c) := SHAKE128(c ‖ dst)`, for `c` of 56
  bytes and `dst` the relation's `*_COMBINE_DST`, is an oracle independent of `H₂²` and of every
  other SHAKE use. Equivalently, the input set `{c ‖ dst : |c| = 56}` is disjoint from the inputs
  of all other SHAKE128 invocations of prover and verifier. The χ derivation needs no
  separation: χ is `chall₂` itself, parsed (§4). Also, the `H₂²` input determines `d`, the
  statement and `chall₁` (§5).
- **(H-stmt)** The statement is bound by `y`: by μ in the `H₂¹` input whose output is `chall₁`
  (non-delayed mode), or by μ at a fixed offset of `y` (delayed mode, PomFRIT). μ's `H₂⁰`
  preimage must be unique and must have been queried before `y`. Otherwise `P*` finds a preimage
  later, with probability `≤ (q² + q)·2^{−256}`. This term belongs with L0/L1.
- `d ≥ 1` (true: `d ∈ {2, 9}`).

## 2. The verifier's QuickSilver check in the code

Line numbers refer to branch `voleith-label-rows` (commit `d5def9c`), with faest-arch-opt patches 0001–0005.

Verifier, `voleith.hpp:451–497`:
1. `chall₂ = H₂²(chall₁ ‖ ũ ‖ h̃_V ‖ [μ] ‖ binder ‖ d ‖ 0x0A)` (`:456–467`). The whole correction
   `proof.correction()` (all `WITNESS_BYTES`) is hashed at `:465`. The prover hashes the same span
   at `:300`, after filling the prefix (`:245–250`, step 1) and the suffix (`:293–299`).
2. `q_j ← Q[j] + d_j·Δ` for the witness rows `j < WITNESS_BITS = ℓ` only (`:469–477`). On branch
   `voleith-label-rows` the loop bound is `OC::WITNESS_BITS`, no longer `VOLE_CORRECTION_ROWS`, which
   is now `ℓ + λ` (`constants.hpp:430–436`: `QUICKSILVER_ROWS + CRT_LABEL_ROWS`, the λ dedicated
   gate-label rows that get cross-tree corrections but no `d`). QuickSilver reads only `q[0..ℓ)` and
   the masks, so nothing below changes.
3. `quicksilver_state<S, true, d>(q, n, Δ, chall₂)`, then `Relation::constraints`, then
   `qs.verify(q_mask, ã, qs_check)` (`:480–485`).
4. `chall₃' = H₂³(chall₂ ‖ qs_check ‖ ã_1..ã_{d−1} ‖ ctr ‖ 0x0B)`, accepted iff it equals the
   proof's `chall₃` (`:487–497`).

**Verifier values** (`quicksilver.hpp:168–278, 664–918`). Each value has a formal degree `e`
(template parameter `deg`) and a MAC `m ∈ F`:
- witness bit `j` (`get_witness_bit`): degree 1, MAC `q_j`;
- constant `c` (`poly1` or `poly_secpar`) at degree `e`: MAC `c·Δ^e`, or `c` if `e = 0`
  (`:666–686`);
- `+`: same degree, MACs add (the C++ types enforce equal degree);
- `×`: degrees add, MACs multiply (`:791–839`). A product with a public constant is
  `const(c, 0) × x` (`:848–880`);
- raising `e → e'` (constructors `requires (deg > deg2)`): MAC times `Δ^{e'−e}` (`:716–746`);
- `combine_8_bits`: `Σ_j β_j m_j` with fixed `β_0 = 1`, `β_j = gf8_in_gf128[j−1]`
  (`:905–918`, `polynomials.hpp:1066–1072`). This is a sum of constant products.

vole-mole's own helpers (`qs_bit.hpp`, `keccak/segmented.hpp`, `uov/circuit.hpp`) touch MAC
coefficients directly only in prover branches (`requires { a.value_; }`). The verifier branch
always calls the faest operations above. I checked every `.mac`/`value()` use in `src/`.

`add_constraint(x)` (`:521–538`) raises `x` to degree `d` and feeds its MAC to both universal
hashes. So the verifier's MAC of constraint `k` is `E_k` evaluated by the rules above, with
`deg E_k = d`.

**ZKHash** (`init_hashers` `:359–378`, `finalize_hashes` `:307–321`, `universal_hash.hpp`).
`chall₂` has `(3λ + 64)/8 = 56` bytes, parsed as `r₀ ‖ r₁ ‖ s ‖ t`: `r₀, r₁, s ∈ F` (16 bytes each,
`load_dup` is a plain load) and `t` a 64-bit polynomial (`poly64::load`), i.e. an element of the
set `S₆₄ ⊆ F` of field elements of polynomial degree `< 64`, with `|S₆₄| = 2^64`.
- `uhasher_gfsecpar<S, 8>` (key `s`) is Horner's rule in blocks of 8 key powers.
- `uhasher_gfsecpar_64` (key `t`) is plain Horner: `state ← t·state + x`.
- `finalize_hashes` returns `r₀·H_s + r₁·H_t + mask`, reduced.

For inputs `m_0, …, m_{n−1}` (in `add_constraint` order), `H_s = Σ_k s^{n−1−k} m_k` (§4) and
`H_t = Σ_k t^{n−1−k} m_k`. So

    qs_check' = Σ_k χ_k m_k + mask,     χ_k := r₀ s^{n−1−k} + r₁ t^{n−1−k}.

This is the spec's ZKHash (v3 spec Fig. 4.4, §4.2.4).

**Masks** (`verify(q_mask, …)`, `:642–660`):

    mask = q̄_0 + Σ_{i=1}^{d−2} (ã_i + q̄_i)·Δ^i + ã_{d−1}·Δ^{d−1}.

## 3. The check polynomial and its top coefficient

**Constraint values.** For `w ∈ F^ℓ`, let `f_k(w)` be `E_k` evaluated with witness bit `j ↦ w_j`,
constants at any degree `↦` the constant, raisings `↦` identity, and `+`, `×` in `F`
(`QSExpr.value`). This polynomial function `F^ℓ → F` is what L7 must analyze. On bit vectors it
agrees with the honest prover's value bits.

**Proposition 1.** Fix a chain: `y`, then `chall₂`, then the `H₂³` input
`(chall₂, z := qs_check, ã_1..ã_{d−1}, ctr)`. Assume (H-L3) on `A_V ⊇ A`:
- `Q[j](Δ') = V*_j + u*_j·e(Δ')` for `j < ℓ`;
- `q̄_i(Δ') = a_i + b_i·e(Δ')` for `i < d − 1`.

Define

    p(X) := Σ_k χ_k·P_k(X) + Σ_{i<d−1} (a_i + b_i X) X^i + Σ_{i=1}^{d−1} ã_i X^i + z,

where `P_k := E_k` evaluated over `F[X]` with witness bit `j ↦ V*_j + w*_j X` and constant
`(c, e) ↦ c X^e`. Then:
1. `p(e(Δ')) = 0` for every `Δ' ∈ A`;
2. `deg p ≤ d`;
3. `[X^d] p = Σ_k χ_k f_k(w*)`, with no sign or scaling.

*Proof.* (1) Let `Δ' ∈ A` and `Δ = e(Δ')`. After step 2, `q_j = Q[j](Δ') + d_jΔ = V*_j + w*_j Δ`.
Every verifier operation in §2 is a ring operation or a multiplication by `Δ^k`, which commute
with evaluation `F[X] → F, X ↦ Δ`. So the MAC of constraint `k` is `P_k(Δ)` and the mask is the
middle two sums at `Δ`. `Δ' ∈ A` means the chain's `H₂³` input is the verifier's, so
`qs_check' = z`, i.e. `p(Δ) = qs_check' + z = 0`.

(2, 3) By induction on the circuit, a well-formed node of formal degree `e` evaluates to a
polynomial of degree `≤ e` whose `X^e` coefficient is its value:
- inputs `V*_j + w*_j X` have degree `≤ 1` and coefficient `w*_j`;
- `c X^e` has coefficient `c`;
- a sum of same-degree nodes adds the coefficients;
- for a product, `[X^{e₁+e₂}](PQ) = [X^{e₁}]P·[X^{e₂}]Q` when `deg P ≤ e₁` and `deg Q ≤ e₂`;
- raising multiplies by `X^k`.

So `deg P_k ≤ d` and `[X^d]P_k = f_k(w*)`. The mask terms have degree `≤ 1 + (d − 2) = d − 1`,
the `ã_i X^i` have `i ≤ d − 1`, and `z` is constant. ∎

So **masks, `ã` and `z` affect only coefficients `0..d−1`**. They may be anything, even chosen
after `chall₂`, without touching the top coefficient. The witness rows' offsets `V*` also enter
only lower coefficients. What L4 needs from L3 is exactly (H-L3) on `A_V`: affine witness rows
(any slope) and mask rows that are polynomials of degree `≤ d − 1 − i` in `Δ`. L3 gives degree
`≤ 1`.

By `card_le_natDegree`: if `Σ_k χ_k f_k(w*) ≠ 0` then `p ≠ 0` and `|A| ≤ deg p ≤ d`.

## 4. ZKHash as implemented, and Schwartz–Zippel

**Blocked Horner.** `uhasher_gfsecpar` keeps `(state, pow)`. `init(n)` sets
`pow = (n + 7) mod 8`. `update(x)` first replaces `state` by `s^8·state` and sets `pow = 7` if
`pow = −1`. It then adds `s^{pow}·x` (`key_pows[pow−1] = s^{pow}`, or `x` itself if `pow = 0`) and
decrements `pow`. Write `p = pow + 1`. The invariant after `k` updates is
`p_k ≤ n − k`, `8 | n − k − p_k` and `s^{n−k−p_k}·state_k = Σ_{i<k} s^{n−1−i} x_i`:
- It holds initially, since `p₀ = (n−1) mod 8 + 1`.
- If `p_k ≥ 1`, the exponent `n−k−p_k` is unchanged and `x_k` gets `s^{n−k−p_k}·s^{p_k−1}`.
- If `p_k = 0`, then `n − k ≥ 8`. The exponent drops by 8, which compensates the `s^8`, and `x_k`
  gets `s^{n−k−8}·s^7`.

After `n` updates, `p_n = 0` and `state = Σ_k s^{n−1−k} x_k`. `finalize` asserts `pow == −1`,
i.e. exactly `n` updates. In release builds that is `[[assume]]`. The tests check the counts for
four relations (`violated.size() == NUM_CONSTRAINTS`), and I recounted all five from the code (§7).

**Proposition 2 (Schwartz–Zippel for ZKHash).** For a fixed `f ∈ F^n ∖ {0}` and uniform
`(r₀, r₁, s, t) ∈ F × F × F × S₆₄`,

    Pr[Σ_k χ_k f_k = 0] ≤ 1/|F| + (n−1)²/(|F|·|S₆₄|) = ε_QS(n).

*Proof.* `Σ_k χ_k f_k = r₀ P(s) + r₁ P(t)`, where `P(X) = Σ_k f_k X^{n−1−k}` is nonzero, since
its coefficient at `X^{n−1−k}` is `f_k`, and has degree `≤ n−1`. If `(P(s), P(t)) ≠ (0, 0)`, the
solutions `(r₀, r₁)` form a line: `|F|` of the `|F|²` pairs. Otherwise `s` and `t` are roots:
at most `(n−1)` values of `s` and `(n−1)` values of `t`. So the count is
`≤ |F|²|S₆₄| + (n−1)²|F|²` out of `|F|³|S₆₄|`. ∎

This is the spec's Lemma 4.7 computation, `ε_QS = 2^{−λ} + ε₀ε₁`, without its side condition
`C + 1 ≤ 2^{13}`. Ratatouille spend has `n = 12282 > 2^{13}` and is still fine: the bound is
`2^{−128}(1 + 2^{−36.8})`. The crude bound `n/|F|` would give `2^{−114.4}`, so the 64-bit hash
matters.

## 5. What is fixed before chall₂

By (H-stmt), (H-L3) and L1, everything below is a function of `y` and of `P*`'s queries before
`y`:
- `chall₁` is the first 88 bytes of `y`. Its `H₂¹` preimage `x₁` fixes μ (non-delayed), `com`,
  `c_i`, `c_mult` and `iv`. By L1 these fix the committed data, and by L3 §2.2 the response
  function `r`.
- `ũ` and `h_V` are the next fixed-length fields of `y`. With `r` they fix
  `A_V = {Δ' ∈ S : K_c(Δ') = h_V}`.
- **Canonical `u*`.** If `|A_V| ≥ 2`, the affine form on `A_V` determines `u*` uniquely: two
  distinct `Δ'` have distinct `e(Δ')`. If `|A_V| ≤ 1`, set `u* := 0`. Then `|A| ≤ |A_V| ≤ 1 ≤ d`
  and the second alternative of L4 holds regardless. `u*` is thus fixed before chall₂, although
  L3's existential `u*` refers to `A`, which depends on chall₂.
- `d` is the last `WITNESS_BYTES` bytes of `y` before the final `0x0A`. The binder is variable
  length, but `d` is a fixed-length suffix, so it is unambiguous.
- In delayed mode, μ sits at the fixed offset after `h_V`.

So `w* = u* + d`, `x`, the circuits `E_k` (apart from `l`), the fixed constraint values
`g_k := f_k(w*)` for `k ≠ k₀`, and `a_m := a_m(w*)` are all fixed when `chall₂` is drawn. `chall₂`
is a fresh random-oracle output, uniform on `{0,1}^{448}` and independent of all of them.

## 6. Challenge-dependent constraints; proof of L4

**Structure of the combined slot.** PomFRIT redeem (`pomfrit/redeem.hpp:132–148`), Moussaka redeem
(`moussaka/redeem.hpp:259–276`) and Ratatouille spend (`ratatouille/spend.hpp:385–395`) each add
exactly one constraint built with `Combination l(chal2, *_COMBINE_DST)`.
- `l_m` is bytes `16m..16m+16` of `SHAKE128(chal2 ‖ dst)` (`uov/circuit.hpp:59–71`). Under (H-DS)
  and freshness this is uniform on `F^M`, with `M = 45`.
- `l` enters only through public constants, each linear in `l`: `l.coeff(m)`, `l.combine(a)`
  (built from `l_m·embed(2^b)` by XOR, hence linear in `l_m`) and `lh`. Every monomial of the
  combined circuit contains exactly one such constant.
- So `f_{k₀}(w; l) = Σ_m l_m a_m(w)`, where `a_m` is the value with `l := e_m` (the `m`-th unit
  vector). No other slot uses `l`.
- Moussaka issue and Ratatouille issue ignore `chall₂` (`/* chal2 */`).

So `f(w*; l) = update(g, k₀, Σ_m l_m a_m)` with `g` and `a` fixed before `chall₂` (§5).

**Proposition 3 (joint distribution).** Suppose some uncombined constraint fails, i.e.
`(∃ k ≠ k₀: g_k ≠ 0) ∨ a ≠ 0`. Let `c = chall₂` be uniform on `Ω := F³ × S₆₄` and `l` uniform on
`F^M`, independent. Then

    Pr[Σ_k χ_k(c) f_k(l) = 0] ≤ ε_QS(n) + 1/|F|.

*Proof.* Split the event:
- If `f(l) = 0`, then no `g_k` with `k ≠ k₀` is nonzero, so `a ≠ 0` and `Σ_m l_m a_m = 0`. For
  `a ≠ 0` that has probability exactly `1/|F|` (`card_combination_eq_zero`).
- Otherwise `f(l) ≠ 0`. For each fixed `l`, Proposition 2 bounds the probability over `c` by
  `ε_QS(n)`. Averaging over `l` gives the same bound.

The two cases add up. ∎

`χ` and `l` both depend on `chall₂`, so the vector `f(l)` is not fixed when `χ` is drawn. The
count over pairs `(c, l)` handles this: Proposition 2 is applied once per fixed `l`.

**From the ROM to the product space.** Condition on `P*`'s view before `y` is answered. `H_comb`
is then fixed on the at most `q_c` points already queried and uniform and independent elsewhere.
- If `chall₂ ‖ dst` was not queried before, which fails with probability `≤ q_c/2^{448}`, then
  `l = H_comb(chall₂ ‖ dst)` is uniform and independent of `chall₂`.
- Queries `P*` makes after seeing `chall₂` do not change `l`.

So `Pr[B_y] ≤ q_c·2^{−448} + ε_QS(n) + 2^{−128}`.

**Proof of L4.** Off `B_y`, if some uncombined constraint fails, then `Σ_k χ_k f_k(w*) ≠ 0`. This
coefficient depends only on `y` and `chall₂`, not on the chain's `ã`, `z` or `ctr`. By
Proposition 1, every chain extending `y` has `p ≠ 0` of degree `≤ d` vanishing on `e(A)`. Since `e`
is injective, `|A| ≤ d` (`card_le_natDegree`). Otherwise all uncombined constraints hold, and
then §7 below applies. ∎

**Bits.** In every relation each witness bit `j` has the constraint `w_j(w_j + 1)`
(`qs_add_bit_constraint`), except Moussaka redeem's unused selector bits `u ≥ |anchors|`, which
have `w_j` itself (`redeem.hpp:231–237`). If these hold at `w*`, then `w*_j ∈ {0,1}`, because
`x(x+1) = 0` forces `x ∈ {0, 1}` in a field. In characteristic 2, `u*_j = w*_j + d_j` with
`d_j ∈ {0,1}`, so `u*_j ∈ {0,1}`. This is `hbits` of `extraction_cases`. In odd characteristic
`u*_j = w*_j − d_j` could be `−1`, so characteristic 2 is genuinely used here (Claim 4 itself does
not need it).

## 7. Numbers

`n` is recounted from the `constraints` functions. `NUM_SEGMENT_CONSTRAINTS = 2·800`, `M = 45`,
`N = 119`, and `CREDIT_BITS = 64`. `ε_QS` does not depend on `d`. The degree enters only through
`|A| ≤ d`, i.e. the `d·2^{−λ}` term for chall₃.

| relation | d | n | `(n−1)²·2^{−192}` | ε_QS | per-`H₂²` total |
| --- | --- | --- | --- | --- | --- |
| PomFRIT redeem (1312 bit + 1 comb.) | 2 | 1313 | 2^{−171.3} | 2^{−128}(1+2^{−43.3}) | ≈ 2^{−127} |
| Moussaka issue (2048 + 1600 + 360) | 9 | 4008 | 2^{−168.1} | 2^{−128}(1+2^{−40.1}) | ≈ 2^{−128} |
| Moussaka redeem (2680+64+63+1+1600+1) | 9 | 4409 | 2^{−167.8} | 2^{−128}(1+2^{−39.8}) | ≈ 2^{−127} |
| Ratatouille issue (1920 + 1600 + 256) | 9 | 3776 | 2^{−168.2} | 2^{−128}(1+2^{−40.2}) | ≈ 2^{−128} |
| Ratatouille spend (6776+128+65+4800+256+1+256) | 9 | 12282 | 2^{−164.8} | 2^{−128}(1+2^{−36.8}) | ≈ 2^{−127} |

"Per-`H₂²` total" is `ε_QS + 2^{−128}` for the three relations with a combined slot and `ε_QS` for
the two issue relations. The `q_c·2^{−448}` term is omitted.

## 8. Findings

1. **The union is over `H₂²` queries, not `H₂³` queries.** Whether `chall₂` is bad is decided
   when `H₂²` answers, and `P*` may discard bad-looking `chall₂`. The assembly needs
   `q_{H₂²}·(ε_QS + 2^{−128})`. The same applies to ε_KOS, which should be counted per `H₂¹`
   query. This is numerically harmless (`q ≤ 2^{64}`), but the README's `Q·(…)` is not what the
   argument proves.
2. **An extra `q_c·2^{−448}` term:** the combination point `chall₂ ‖ dst` may have been queried
   before `chall₂` was drawn. Alternatively, absorb it into L0.
3. **L3 must be applied to `A_V` (fixed before chall₂), not to `A`.** It must yield a canonical
   `u*` (§5). L3 as written in `L3-kos.md` ("for every `A ⊆ S` on which the KOS check passes")
   supports this.
4. **The statement must be bound before chall₂ (H-stmt).** This adds a `(q²+q)·2^{−256}` term for
   L0/L1. Mechanized (classical, ROM + ideal cipher; `lean/docs/probabilistic-plan.md` §2g) for the
   five relations: the statement committed at an `H₂¹` input is the decoded first `H₂⁰` preimage
   of its `mu₁` field in the log before it, and it is the verifier's unless an `H₂⁰` answer equals
   the `mu₁` field of an earlier `H₂¹` input or an earlier `H₂⁰` answer, `≤
   (q₀+3)(q₂₁+q₀+4)·2^{−256}` in all (`ROM/StmtBind.lean`, `*_accept_le_adaptive`); the
   instance encodings must be injective on the statement family (they contain UOV key digests, an
   application-level hash). For PomFRIT's delayed μ (in the `H₂²` input) the same with `H₂²` in
   place of `H₂¹`, `(q₀+3)(q₂₂+q₀+4)·2^{−256}`, and no injectivity: the μ preimage binds the target
   `h(chal1)`, which is all the relation reads (`ROM/AdaptPomfrit.lean`).
5. The top coefficient is exactly `Σ_k χ_k f_k(w*)` with `χ_k = r₀ s^{n−1−k} + r₁ t^{n−1−k}`. There
   is no sign, since the characteristic is 2, and no scaling, since `add_constraint` raises every
   constraint to degree `d` by multiplying by `Δ^{d−e}`, which multiplies the top coefficient by 1.
6. The spec's Lemma 4.7 side condition `C + 1 ≤ 2^{13}` fails for Ratatouille spend, but the direct
   bound of §4 holds for every `n`.
7. With L4 as above, the README's statement holds after replacing `Q` by `q_{H₂²}` and adding the
   small terms of findings 2 and 4.

## 9. Lean (`lean/VoleMole/Seed/QuickSilver.lean`, namespace `VoleMole.Seed`)

| Paper | Lean |
| --- | --- |
| Verifier circuit model, constraint values | `QSExpr`, `QSExpr.eval`, `QSExpr.value`, `QSExpr.WF`, `QSExpr.deg` |
| Prop. 1 (2–3), per circuit | `QSExpr.eval_natDegree_coeff` |
| Bit constraint `x(x+1)` | `QSExpr.bitConstraint`, `value_bitConstraint` |
| Prop. 1 (2–3), check polynomial | `checkPoly`, `checkPoly_natDegree_coeff` |
| Masks and `ã` only reach degree `d − 1` | `maskPoly`, `maskPoly_natDegree_le` |
| `uhasher_gfsecpar` (blocked) and `uhasher_gfsecpar_64` are Horner | `blockedStep`, `blockedHash`, `blockedHash_eq_sum`, `blockedHash_ofFn`, `horner`, `horner_eq_sum` |
| ZKHash as computed, `χ_k` | `zkHash_eq_code`, `zkHash`, `zkCoeff`, `zkHash_eq_sum`, `zkHash_eq_eval` |
| Prop. 2 | `card_zk_bad_le`, `card_zkHash_eq_zero_le`, `zkHash_prob_le`, `epsQS` |
| Prop. 3 (product space) | `card_combined_bad_le`, `combined_prob_le` |
| L4's conclusion, as `hclaim3` | `claim3_of_good`, `claim3_of_circuit` |
| `hbits` | `bits_of_bit_constraints` |

`combined_prob_le` says: if `UncombinedFail g k₀ a`, then the fraction of
`(chall₂, l) ∈ (F × F × F × S) × F^M` with `zkHash(chall₂, update(g, k₀, Σ l_m a_m)) = 0` is
`≤ epsQS |F| |S| n + 1/|F|`. With `|F| = 2^{128}` and `|S| = 2^{64}` this is
`ε_QS(n) + 2^{−128}`.

**Not formalized:**
- §5 and the ROM step of §6: freshness, that `w*` and `x` are functions of `y`, and the
  `q_c·2^{−448}` term.
- That each relation's `constraints` code is the `QSExpr` modelled here. This is checked by reading
  the code (§2).
- The equality of `Combination`'s value with `Σ_m l_m a_m` (linearity in `l`).
- The constraint counts `n`.
