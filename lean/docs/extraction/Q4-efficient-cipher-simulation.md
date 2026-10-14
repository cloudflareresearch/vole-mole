# Q4: an efficient extractor for the quantum ideal cipher

Status: **[paper]**, with **[Lean]** for the combinatorial and arithmetic cores
(`lean/VoleMole/Seed/CipherSim.lean`). Part of README §L9. This note builds on
`Q1-quantum-ideal-cipher.md` (cited below as Q1) and answers its §6 ("what the extractor needs from
a simulator") and its §9.2 (the `multi` event).

Notation as in Q1: `N = 2^128`, `X = K = {0,1}^128`, `p = 1/(N(N−1))`, `δ = 8√(2p) ≈ 2^{−124.5}`,
`ι = (iv, twk)`, `x_c = x_c(ι)`, `f_ι(σ) = σ(x₀) ‖ σ(x₁)`.

## Summary

**Approach.** The extractor simulates the cipher as

    E_k  :=  A_{F(k)} ∘ ρ_k ,

where:
- `F : K → AGL(1, GF(2^128))` is a random function into the affine group, simulated by Zhandry's
  compressed oracle. Its database is the key database.
- `A_y` is the affine map `z ↦ α_y·z + β_y`.
- `ρ_k := SR^{H(k,·)}` is the Morris–Rogaway sometimes-recurse shuffle with swap-or-not rounds
  [MR14]. Its round keys and round bits come from a second random function `H`, simulated by a
  compressed oracle (or a `2q_H`-wise independent family).

Call this simulator `S*`. Its three properties:
- **No computational assumption.** Extraction uses only `F`'s database.
- **Efficient**, including inverse queries and superposed keys.
- **Extraction does not depend on `ρ`.** Because the affine group is sharply 2-transitive, the
  extraction analysis holds *for every fixed `ρ`*, with Q1's constants exactly.

**Main results.**
- **Theorem A (simulation).** For every adversary, even an unbounded one making any number of
  forward or inverse superposition queries, `S*` without `Ext` is `ε_sim`-close to the quantum ideal
  cipher, with

      ε_sim ≤ |K|·ε_FPC = 2^{128}·2^{−300} = 2^{−172}.

  The bound does not depend on `q`, so at `q = 2^64` it is still `2^{−172}`. The parameter is 2354
  swap-or-not rounds per stage, which is ≈ 3·10⁵ one-bit round-function calls per cipher
  evaluation.
- **Theorem B (exact extraction structure).** For every fixed `ρ`, `(Enc, Dec, Ext)` of `S*` is an
  instance of Q1's key-level framework with density exactly `p`. So all of Q1 §3–§4 and Q1
  Theorem 5.1 hold verbatim, with the same constants. In particular `δ = 8√(2p)` per cipher query,
  not doubled.
- **Theorem C (three-interface closeness).** `S*` is `ε_Sim(q, L)`-close to Q1's `S^IC` as a
  three-interface oracle (`Enc`, `Dec`, `Ext`), with

      ε_Sim(q, L) ≤ 2^{−172} + L·q·δ,

  where `L` is the number of `Ext` calls. This is what Q1 §6 asks for, so every Q1 bound transfers,
  including the H₄-based `multi` bound (Q1 Theorem 5.2).
- **ε_multi (§5).**
  - Proven at all `q`: `ε_multi ≤ (320/9)·q₁³/(N−1)`. For `q₁ ≲ 2^37` the H₄ bound
    `≈ 1.8·10⁷·(2q₁+q₄+1)⁵·2^{−256} + 2^{−127} + ε_Sim` also applies.
  - At `q = 2^64`, **no available technique gives a non-vacuous bound.**
  - Point-level analysis with compressed permutation oracles or the compressed ideal cipher
    ([CM26], [BH26]) gives `O(q³/N)` again. The obstruction is identified in §5.3; it is not
    specific to our simulator.
  - The true value is presumably `Θ(q³/N²) ≈ 2^{−64}` at `q = 2^64`: a real attack needs a 256-bit
    cross-key collision, about `2^85` quantum queries.
  - For scale, the QROM Fiat–Shamir term `q²/N` is also `≥ 1` at `q = 2^64`.

**Comparison with the candidates in the brief.**
- *Computational* (`E_k = P_{F(k)}`, strong qPRP `P`). The best published multi-instance step is
  Bhaumik–Huang's lifting, which costs `8q²·Adv_P`, and that factor is black-box optimal [BH26,
  Thm. 1, Prop. 1]. At `q = 2^64` this is `2^{131}·Adv_P`, which is vacuous for any `P` with
  ≤ 128-bit-level qPRP advantage. The candidate is dominated by `S*` (§6.1).
- *Compressed permutation oracles.* The error is `120q/√(N−q+1) + q(q+1)/(N−2q+1)` [CM26,
  Cor. 4.3], with no dependence on `|K|` [CM26, Cor. 4.17], and inverse queries are supported.
  Kim's version is `4q/2^{64}` [Kim26]. Both are vacuous at `q = 2^64`. Key-level use does not
  avoid the `√N`, because an adversary can spend all its queries on one key (§6.2).
- *Definitions.* With `S*`, the plain-model reductions (to UOV and to Keccak) are efficient and
  lose only `2^{−172}`. No relaxed, oracle-relative definition is needed (§6.3).

---

## 0. What "efficient extractor" must mean

The protocols' reductions run the adversary `A` against simulated oracles and extract a witness
from its output, for example a UOV preimage. This is DFMS-style online extraction [DFMS22]. A
reduction `B` against a plain-model assumption (UOV, Keccak) must itself be efficient. So it must
simulate every oracle `A` uses, including the quantum ideal cipher with forward and inverse
superposition queries over superposed keys, and the extractor must read the keys from that
simulation.

We use the following standard shape. There must be an efficient stateful `Sim` with interfaces
`Enc`, `Dec`, `Ext`, such that:

- **(Sim)** `|Pr[A^{IC} → 1] − Pr[A^{Sim} → 1]| ≤ ε_sim` for every `A` that does not use `Ext`.
  Here `A` includes the security game, the honest parties and the win check, all of which query the
  cipher.
- **(Ext)** In the `Sim` world, `Pr[V accepts ∧ R(x, Ext-derived witness) fails] ≤ ε_ext`.

Then `Pr[B wins] ≥ Pr_{IC}[A wins] − ε_sim − ε_ext`, and `B` is efficient. `S*` gives (Sim) with
`ε_sim = 2^{−172}` against unbounded `A`. It gives (Ext) by Theorems B and C combined with Q2.

## 1. The simulator `S*`

**Parameters.**
- `Y := ℤ_{N−1} × GF(2^128)`.
- Fix a generator `g` of `GF(2^128)^*`. For `y = (a, b)`, let `A_y(z) := g^a·z + b` and
  `A_y^{-1}(c) = g^{−a}·(c + b)`. The group `Y` is abelian, which is the setting of CFHL and DFMS
  (App. B). Q1 §6 uses the same group.
- `ρ_k := SR^{H(k,·)}` on `X ≅ [N]`, with the canonical split `p_M = M/2` [MR14, Fig. 1]. The
  stages are `M = 2^128, 2^127, …, 2^1`. Stage `M` runs `t_M` swap-or-not rounds:

      X' := K_{M,i} − X mod M;   X̂ := max(X, X');   if B_{M,i}(X̂) = 1 then X := X'.

  Then, if `X < M/2`, it recurses on `[M/2]`.
- The round keys `K_{M,i} ∈ [M]` and round bits `B_{M,i}(·)` are read from
  `H : K × (domain-separated indices) → {0,1}^128`.
- **Rounds.** `t_M = 2354` for every `M ≥ 4`, and `t_2 = 1`. That is 298,959 rounds in the worst
  case [Lean `sr_worst_case_rounds`].
- **Inverse.** Each swap-or-not round is an involution, since `X ↦ K − X` and the bit depends only
  on the unordered pair. So `ρ_k^{-1}` runs the stages in reverse:
  1. if `Y < M/2`, first invert the sub-shuffle on `[M/2]`;
  2. then undo the `t_M` rounds in reverse order.

  This uses the same `H` calls.

**Oracles.**
- `F : K → Y` uses the compressed oracle with standard (additive) queries [Zha19; CFHL21 App. A;
  DFMS22 App. B].
- `H` uses the compressed oracle, or a `2q_H`-wise independent family when the total number `q_H`
  of `H` calls is known in advance [Zha12a, Thm. 6.1].

**Interfaces.**
- `Enc(k, x)` is implemented on the sparse database as `cO_k = F_k Õ_k F_k`:
  1. Decompress `D_k` (`F_k`).
  2. If `D_k = ⊥` (key absent from the list), do nothing. Otherwise, with `y := D_k`:
     compute `ρ_k(x)` into an ancilla (`H`-queries), XOR `A_y(ρ_k(x))` into the answer register,
     and uncompute `ρ_k(x)`.
  3. Recompress (`F_k`).

  On reachable states without interleaved `Ext`, this equals "fetch `y = F(k)` by a standard query,
  use it, un-fetch". The explicit form fixes the action on `|⊥⟩` to the identity, as in Q1.
- `Dec(k, c)`: the same with `x = ρ_k^{-1}(A_y^{-1}(c))`.
- Both work coherently with the key, the direction and the inputs in superposition.
- `Ext_ι(t)`, for classical `ι` and `t = (t₀, t₁)` with `t₀ ≠ t₁` (otherwise output `∅`): the
  projective measurement of Q1 §3 on `F`'s compressed database, with outcomes `∅ / k / multi`. It
  is built from

      Π^k := Σ_{y ∈ Y : A_y(ρ_k(x₀)) = t₀ ∧ A_y(ρ_k(x₁)) = t₁} |y⟩⟨y|_{D_k},    Π^k|⊥⟩ = 0.

  It is implemented on the sparse database [DFMS22, App. B]:
  1. for each of the `≤ q` entries `(k, y)`, compute the predicate (2 evaluations of `ρ_k`);
  2. count the matches and write the outcome;
  3. uncompute.

**Cost.**
- `Enc`/`Dec`: one decompress/recompress of `D_k` (cost of 2 compressed `F`-queries) and `≤ 2·2·298,959` `H`-queries, plus `O(λ)` field operations per
  round.
- `Ext`: `O(q)` evaluations of `ρ`.
- With compressed oracles and no QRAM, every query costs `O(q·poly(λ))` gates, so the total is
  `poly(q, λ)`, i.e. `Õ(q²)` up to the constant factor of the round count. This is the same
  asymptotic overhead as every known straight-line QROM extractor (DFMS22's runs a compressed
  oracle too).
- A cheaper variant uses `H := PRF_{K*}` for a single-key quantum-secure PRF. This is one standard
  single-instance assumption and adds `Adv^{qprf}` to `ε_sim`. The statistical version needs no
  assumption at all.

## 2. Theorem A: statistical simulation

**Theorem A.** For any oracle algorithm `D` (unbounded, any number of forward and inverse queries,
keys and directions in superposition) that does not call `Ext`,

    | Pr[D^{S*} = 1] − Pr[D^{IC} = 1] |  ≤  |K|·ε_FPC,       ε_FPC := 2^{−300},

and also `≤ 8q²·ε_FPC` for `q`-query `D` [BH26, Thm. 1]. Numerically: `2^{−172}`, or `2^{−169}` at
`q = 2^64`.

*Proof.*
1. **`H`.** The compressed oracle is a perfect simulation of a uniform `H` [Zha19]. A `2q_H`-wise
   independent `H` gives exactly the same output distribution to any algorithm making `≤ q_H`
   queries to `H` [Zha12a, Thm. 6.1]. So take `H` uniform. Likewise, take `F` uniform.
2. **One key.** For uniform `H`, `ρ_k = SR^{H(k,·)}` is a δ-good shuffle with
   `δ = Σ_{M} ε_M` [MR14, Thm. 3]. "δ-good" with `q(N) = N` means the total-variation distance of
   the whole permutation from uniform is at most δ.
   - Each stage is `(M/2, ε_M)`-good with `ε_M ≤ Δ^{ub}_{SN}(M, M/2, t_M) = (2M^{3/2}/(t_M+2))·(3/4)^{t_M/2+1}`.
     This is the swap-or-not bound of [HMR12] as restated in [MR14, eq. (1)].
   - With `t_M = 2354`, each `ε_M ≤ 2^{−300}/127` [Lean `sn_stage_bound`, checked in `ℕ` after
     squaring]. For `M = 2`, `t_2 = 1` contributes zero error [MR14, §5].
   - So `‖law(ρ_k) − U_{Sym(X)}‖_TV ≤ 2^{−300}`. 2354 is the least even round count that works
     for the top stage [Lean `sn_top_stage_tight`].
3. **Whitening.** `F(k)` is uniform and independent of `ρ_k`, and `A_{F(k)}` is a bijection of
   `Sym(X)` under left composition. So `‖law(A_{F(k)} ∘ ρ_k) − U‖ ≤ ‖law(ρ_k) − U‖`, and
   `A_{F(k)} ∘ U = U` in law.
4. **All keys.** The families `(F(k), H(k,·))` are independent across `k`. So the law of
   `(E_k)_{k∈K}` is a product of per-key laws, each within `ε_FPC` of uniform. The total-variation
   distance of a product is at most the sum, `|K|·ε_FPC` [Lean `keyed_tv_bound`].
5. **Conclusion.** `D`'s output distribution is a function of the classical oracle
   `(E_k, E_k^{-1})_k`, so its advantage is at most that distance. This is the argument of
   [Zha16/25, Lemma 3.7]. It covers superposition queries over keys, forward and inverse, with no
   query bound.
6. **Alternative.** The `8q²` form follows from [BH26, Thm. 1] with base oracles `SR^{H}` and a
   uniform permutation (statistical version, Remark 1 there). ∎

Remarks.
- Using a full-domain (full-security) PRF-to-PRP converter to simulate random permutations
  efficiently is noted in [HHM+26, App. A.1] (mix-and-cut with swap-or-not). It is also used by
  [BH26, Lemma 4] for keyed families. The idea is Zhandry's observation that full-domain classical
  security implies quantum security [Zha16/25, Lemmas 3.7–3.8].
- What is new here is combining it with the affine whitening, so that the key database is that of
  a small-range compressed oracle and extraction is exact (Theorem B).
- `ε_FPC` is a free parameter: its cost is linear in `log(1/ε_FPC)` [MR14, Thm. 4].

## 3. Theorem B: exact extraction structure, for every fixed `ρ`

**Theorem B.** Fix any permutation family `ρ = (ρ_k)_k`, for example `S*`'s family for a fixed
`H`. Then `S*` with this `ρ` satisfies the hypotheses of Q1 §2–§5, with:
- register alphabet `Y`;
- fibre density exactly `p`;
- union density `γ* ≤ 1/(N−1)`.

Hence the following hold with the same constants:
- Q1 Lemmas 3.1–3.2: `‖[cO, M]‖ ≤ δ = 8√(2p)` per `Enc`/`Dec` query;
- P1–P4;
- Theorem 4.2: dead leaves, other keys, persistence, `2(2q₂+1)²p`;
- Theorem 5.1: `ε_multi^free`;
- Corollary 5.3, except for its H₄ variant;
- the database bound `≤ q` (Lemma 2.1).

All of them hold for unbounded adversaries. In particular they hold conditioned on `H`, so also on
average over `H`.

*Proof.*
1. **Query shape.** By construction (§1), `Enc` restricted to key `k` is `F_k Õ_k F_k` with
   `Õ_k = |⊥⟩⟨⊥| ⊗ 1 + Σ_y |y⟩⟨y|_{D_k} ⊗ U_{k,y}`, for unitaries `U_{k,y}` on the adversary's
   registers (`U_{k,y}` XORs `A_y(ρ_k(x))`).
   - So `Enc` has exactly the form `cO_k = F_k O_k F_k` with `O_k` controlled by the computational
     basis of `D_k` and trivial on `|⊥⟩`. That is the only property Q1 §2–§4 use (Q1 §2, "Why the
     general machinery applies"). `Dec` is the same.
   - Equivalently, on reachable states the two standard `F`-queries "fetch / un-fetch" compose as
     `C·O^{std}·W·(O^{std})^{-1}·C`, because `C² = 1` and `W` does not touch `D`. This single
     `C`-conjugation is why `δ` is not doubled. Treating the two `F`-queries separately would give
     `16√(2p)`.
2. **Fibre density.** For `z_c := ρ_k(x_c)` (distinct, since `x₀ ≠ x₁`, Q1 §0) and `t₀ ≠ t₁`,
   exactly one `y ∈ Y` satisfies `A_y(z_c) = t_c` for `c = 0, 1` [Lean
   `affine_two_point_existsUnique`, `affine_two_point_card`]. And `|Y| = (N−1)·N` [Lean
   `affine_group_card`]. So `⟨u_Y|Π^k|u_Y⟩ = 1/|Y| = p` exactly. For `t₀ = t₁` no `y` works [Lean
   `affine_two_point_none`].
   - This is the only property of uniform `σ` used in Q1 Lemma 3.1, P2–P4 and Theorem 4.2.
3. **Union density.** For fixed `ρ`, keys `k ≠ k'` and a fixed `y'`,

       Pr_y[∃z : A_yρ_k and A_{y'}ρ_{k'} agree on {z, z⊞e₀}] ≤ Σ_z p = N·p = 1/(N−1)

   by the same count. This is Q1's (F2).
4. **Theorem 5.1.** Q1 Theorem 5.1 uses CFHL Theorem 5.17 with 1-local recognisability and this
   density. Here `F` *is* a random function with standard queries into an abelian group, 2 queries
   per cipher query, so Q1's "full-value reduction" is not even needed: `Q = 2q₁` as in Q1. ∎

**What does not transfer verbatim.** Q1 Theorem 5.2 (the H₄-based `multi` bound) uses
multi-point uniformity of a fresh permutation: probability `(3s/N)^{m'}` for `m'` prescribed
agreement points. A 2-dimensional whitening of a *fixed* `ρ` does not have this. Theorem C below
recovers Theorem 5.2 for `S*` (with `ρ = SR^{H}`) at an additive cost.

## 4. Theorem C: closeness to `S^IC` as a three-interface oracle

**Theorem C.** Consider an adversary that makes `q` cipher queries and `L` `Ext` calls, interleaved
arbitrarily, together with arbitrary random-oracle queries. The joint distribution of its output
and all `Ext` outcomes differs between `S*` and Q1's `S^IC` by at most

    ε_Sim(q, L) ≤ |K|·ε_FPC + L·q·δ  =  2^{−172} + L·q·8√(2p).

*Proof.*
1. **Replace `ρ` by an ideal family.** The whole experiment (adversary, `S*`'s `F`, and the `Ext`
   evaluations of `ρ`) is an algorithm with oracle access to the family `ρ`. By Theorem A, steps 1–4,
   which have no query bound, replacing `SR^{H}` by a uniformly random family `Π` costs
   `≤ |K|ε_FPC`.
2. **Change variables.** With `Π_k` uniform, fix a set `R` of right-coset representatives of
   `AGL(1)` in `Sym(X)`, and write `Π_k = A_{y₀} r_c` with `(y₀, c)` uniform. Put `y' := y·y₀`.
   - The basis relabelling `|y, y₀⟩ ↦ |y', y₀⟩` maps `F`'s compression on `y` to the same
     compression on `y'`, because `|u_Y⟩` and `|⊥⟩` are translation invariant.
   - The cipher is `E_k = A_{y'} r_c`, and `y₀` is never touched.
   - On the other side, `S^IC`'s register `σ_k ∈ Sym(X)` is `(y', c)` via the bijection
     `σ = A_{y'} r_c`, and `|u_Sym⟩ = |u_Y⟩|u_C⟩`.

   So both worlds act on the same purified registers `(y'_k, c_k)_k`. They differ only in the
   compression used:
   - `S^IC` swaps `|⊥⟩ ↔ |u_Y u_C⟩` (call it `F^{YC}_k`);
   - `S*` swaps `|⊥_Y, c⟩ ↔ |u_Y, c⟩` for every `c` (call it `F^Y_k`).

   Use the common space `H_k = span{|y,c⟩} ⊕ span{|⊥_Y, c⟩}` and identify `S^IC`'s `⊥` with
   `|⊥_Y, u_C⟩`.
3. **Compare in the purified picture.** Conjugate each world by its own global compression.
   - Cipher queries are then the same purified unitaries in both worlds: `U_{k, A_{y'} r_c}` on
     `|y', c⟩`, and the identity on every `⊥`-type state of `H_k` (§1 fixes this for `S*`; Q1 fixes
     it for `S^IC`). The initial states and all non-cipher operations are the same.
   - The only difference is that each `Ext` becomes the measurement built from
     `A_k := F^{YC}_k Π^k F^{YC}_k` (in `S^IC`) or from `B_k := F^Y_k Π^k F^Y_k` (in `S*`), with the
     same `Π^k` in both.
   - Observable outcomes live on non-oracle registers, so the final compressions do not matter.
4. **Per-key gap.** `‖A_k − B_k‖ ≤ ‖[F^{YC}_k, Π^k]‖ + ‖[F^Y_k, Π^k]‖ ≤ 2√(2p)`, since
   `FΠF − Π = [F,Π]F`. Both commutators are computed as in Q1 Lemma 3.1:
   - `⟨u_Y u_C|Π^k|u_Y u_C⟩ = p`;
   - in each `c`-block, `⟨u_Y|Π^k_c|u_Y⟩ = 1/|Y| = p`.
5. **Branches.**
   - `A_k` and `B_k` both annihilate `|u_Y u_C⟩` and its adjoint image. So both commute with the
     orthogonal projectors `R_S` ("exactly the keys in `S` are not in `|u_Y u_C⟩`").
   - Purified queries raise `|S|` by at most one, and `Ext` does not change it. So at any time the
     state is `Σ_{|S|≤q} R_S φ` (Q1 Lemma 2.1 in purified form).
   - On `R_S`, only the keys in `S` matter: for `k ∉ S`, `A_k = B_k = 0`.
   - Swapping the projector of one register in the `{∅, k, multi}` measurement changes it by at
     most `4‖A_k − B_k‖`. This is Q1 Lemma 3.2's four-group argument, which only uses that the
     change acts on one register.
   - So `‖(M_A − M_B) R_S φ‖ ≤ 4·|S|·2√(2p)·‖R_S φ‖ ≤ q·δ·‖R_S φ‖`, and by orthogonality of the
     `R_S`, `‖(M_A − M_B)φ‖ ≤ q·δ`.
6. **Hybrid.** A hybrid over the `L` `Ext` calls, with the measurements written as isometries
   writing an outcome register, gives `≤ L·q·δ` in Euclidean norm, which bounds the trace distance.
   ∎

**Consequence.** Q1 §6's requirement holds with `ε_Sim(q, L)`. So every Q1 bound holds for `S*` up
to `+ε_Sim`. Theorem B already gives all of them except Theorem 5.2 with no `L·q·δ` term. The extra
term matters only where Theorem C is needed, namely Theorem 5.2.

## 5. The `multi` event (binding of a leaf commitment)

`multi` at `Ext_ι(t)` means that two database keys open `t`. It is the ideal-cipher part of L1's
`ε_bind`.

### 5.1 What is proven for `S*`

| | statement | `q₁ = 2^30` | `2^37` | `2^50` | `2^64` |
|---|---|---|---|---|---|
| (i) free iv, all `q` (Thm B + Q1 Thm 5.1) | `(320/9)q₁³/(N−1)` | `2^{−32.8}` | `2^{−11.8}` | vacuous | vacuous |
| (ii) with `iv = H₄(…)` (Thm C + Q1 Thm 5.2), `θ ≤ 1/2` | `≈1.8·10⁷(2q₁+q₄+1)⁵2^{−256} + 2^{−127} + ε_Sim` | `≈2^{−74}` (if `L·q·δ` is small) | borderline | n/a | n/a |

In (ii), `ε_Sim = 2^{−172} + L·q·δ`. With `L = 2304` and `q = 2^30` that is `≈ 2^{−83}`.

**Final `ε_multi` at `q = 2^64`: no proven non-vacuous bound** (all rows are `≥ 1`). The
conjectured and attack-based value is `Θ(q³/N²) ≈ 2^{−64}` (§5.4).

### 5.2 Reduction: in `S*`, `multi` is a cipher-collision search

If `Ext_i` returns `multi`, then measuring `F`'s database and evaluating the `≤ q` keys at
`x₀(ι), x₁(ι)` yields `(k ≠ k', ι)` with `E_k(x_c) = E_{k'}(x_c)` for `c = 0, 1`. The extractor
can do this efficiently.

Writing `Π_k = A_{F(k)}^{-1} E_k`, the experiment becomes an algorithm with oracle `E` and
internal independent randomness `F`. By Theorem A (no query bound), `Pr_{S*}[multi_i]` is
therefore at most

    Pr[ an ideal-cipher adversary outputs (w, twk, k ≠ k') with E_k(x_c) = E_{k'}(x_c), c=0,1,
        x_c = H₄(w) ⊞ (c,0,0,twk) ]  +  2^{−172}.

So `ε_multi` is purely a **QICM search problem**: two-block cross-key collisions at H₄-derived
adjacent plaintexts. Any future bound for it transfers to `S*`. The extractor's efficiency costs
nothing here.

Two caveats:
- The searching adversary's query count includes the earlier `Ext` evaluations, `2q` per call.
  Bounds that degrade polynomially in `q` must account for this. Q1's key-level bounds do not,
  because they handle `Ext` as a diagonal measurement.
- This statement is unconditional, but the "efficient-reduction" reading is optional: the bound is
  information-theoretic.

### 5.3 Why point-level recording does not help yet

Option (a) in the brief: a compressed ideal cipher.
- Carolan–Majenz give each key an independent compressed permutation database with soundness
  `120q/√(N−q+1) + q(q+1)/(N−2q+1)`, independent of `|K|` [CM26, Cor. 4.3, 4.17].
- Bhaumik–Huang get `8q²·Δ_cpO` generically [BH26, Thm. 2].
- For *search* events, Carolan–Majenz's fundamental lemma adds the state distance `δ_N(T)` at the
  amplitude level [CM26, Lemma 5.1, Thm. 5.3]. So the soundness loss enters the probability as
  `δ_N(T)² ≈ 7744·T²/N`, not as `q/√N`.

The binding property `B` is: two keys with all four entries recorded at `{x₀(ι), x₁(ι)}` and equal,
for some `ι` with `iv` in the H₄ database. Its two-sided sparsity [CM26, (84)] is `Θ(t)` in the
worst case.
- A database in which many keys share the value at the partner point `x ⊞ e₀` gives a new
  forward entry `(k, x, ·)` up to `t` completing values. Inverse queries behave similarly.
- [CM26, Thm. 5.3] then gives `p ≲ (8/3)²·T³/N + δ_N(T)²`, i.e. `≈ 57·q³/N` with `T ≈ 2q`.
- That is no better than (i). With `q·√(2/N)`-type terms it is `≥ 2^{13.9}` at `q = 2^64`
  (`δ_N(2q)² ≈ 2^{13.9}`).

Two refinements fail for real reasons, not as artefacts:
- **Half-coincidences.** `E_k(z) = E_{k'}(z)` is a 128-bit cross-key collision. A quantum adversary
  creates them at rate `q³/N` (BHT). For `q ≳ 2^{43}` they genuinely exist in the database.
  Level-by-level induction on their number, as in Q1 Theorem 5.2 and [LZ19]-style multi-collision
  arguments, needs `θ ∼ q^{3/2}/√N < 1`, i.e. `q ≲ 2^{40}`.
- **Completion at a fixed input.** Completing a half-coincidence `(k, k', z)` at the partner point
  means hitting a prescribed value at the *fixed* input `(k, z⊞e₀)`. The true probability is
  `≈ C/N` for `C` half-coincidences, with no Grover gain.
  - The compressed-oracle transition-capacity method charges `√(1/N)` per query at that input. It
    re-randomises the recorded value with amplitude `O(1/√N)` each time, which gives `q²C/N`.
  - The resulting `q⁵/N²` (Q1 Thm 5.2) is this overcount.

Option (b) in the brief, `E_k = P_{F(k)}` with binding reduced to collisions of
`s ↦ P_s(x₀) ‖ P_s(x₁)` over a compressed `F`, has the same problem:
- For a *fixed* `ι`, CFHL gives `O(q³p) = O(q³/N²)`.
- But `ι` is adversarial through H₄. A full seed `s` determines all of `P_s`, so a new seed
  collides with an old one at *some* adjacent pair with probability `t/N`. This is exactly Q1's
  key-level obstruction, unchanged.
- Turning it into a plain-model collision-resistance assumption on `P` also fails: with the affine
  whitening needed for exact density, the seed-to-commitment map is trivially not collision
  resistant for chosen seeds (`A_y` can be solved for).

**Precise open lemma** (would give `ε_multi = O(q²/N)`, the scale of the Fiat–Shamir term). It has
two parts:
- (L-a) in [CM26]'s compressed ideal cipher, the maximal multiplicity of a value at one position
  across keys exceeds `m` with probability `≤ C_m·q^{2^{m+1}−1}/N^{2^m−1}`, the analogue of [LZ19]
  for random functions;
- (L-b) the sparsity argument with multiplicity `≤ m`.

Together these would give `ε_multi ≲ 16m·q²/N + δ_N(2q)² + C_m q^{2^{m+1}−1}/N^{2^m−1}`. With
`m = 3`, that is `O(q²/N)` for `q ≲ 2^{57}`.

### 5.4 Attack-based value

A real binding break needs `(k ≠ k', ι)` with a 256-bit collision `E_k(x_c) = E_{k'}(x_c)`,
`c = 0, 1`, at an H₄-derived `iv`.
- For a fixed `ι`, `k ↦ E_k(x₀) ‖ E_k(x₁)` is an exactly uniform function into distinct pairs. BHT
  collision search costs `≈ N^{2/3} = 2^{85.3}` queries.
- Fixing `z` first and then finding a matching `iv` by Grover over `iv_pre` adds `2^{64}`. It does
  not help.
- So the expected bound is `Θ(q³/N²) ≈ 2^{−64}` at `q = 2^64`, and `≈ 2^{−166}` at `q = 2^30`.

## 6. The candidates in the brief

### 6.1 Computational simulation `E_k = P_{F(k)}` (with a strong qPRP `P`)

- **F-collisions.** If `F(k) = F(k')`, two keys share a permutation. The quantum function-vs-injection
  distance is `O(q³/|S|)` [Zha15]. This can be avoided altogether by putting `k` itself in the
  tweak or seed.
- **Multi-instance step.** The naive hybrid fails. Three options:
  - *Small-range distributions* [Zha12b] give `O(q³/r) + r·Adv`, optimised to `≈ q^{1.5}·√Adv`.
    The hybrid also needs efficient simulation of the remaining random permutations, which is what
    `S*`'s `SR^{H}` provides.
  - *Lifting* [BH26, Lemma 4]: `TWK_K(t,x) = PRP_{PRF_K(t)}(x)` satisfies
    `Adv^{IC}_{TWK} ≤ Adv^{RO}_{PRF}(2q) + 8q²·Adv^{RP}_{PRP}(q) + 2^{−n}`. The `8q²` is black-box
    optimal [BH26, Prop. 1].
  - *Direct assumption:* a strong tweakable qPRP with 128-bit tweaks in superposition. Precedent
    for this kind of assumption is the QCB line of work on quantum-secure TBC modes. Any stateless
    efficient computational simulator of the QIC is such an object.
- **Numbers at `q = 2^64`.**
  - With `P` = AES-256 (conjectured qPRP advantage `≈ t²/2^{256} ≈ 2^{−128}` at `t ≈ 2^{64}`), the
    lifting bound is `2^{131}·2^{−128} = 8`: vacuous.
  - The small-range bound is `≈ 2^{96}·2^{−64}`: vacuous.
- **Circularity.** Instantiating `P` with AES is not circular: the QICM claim about AES is a
  heuristic, while the reduction's assumption would be a standard-model qPRP assumption. It is
  simply unnecessary, since `S*` uses no AES and no assumption.
- **Verdict:** dominated by `S*` (Theorem A: `2^{−172}` with no `q` dependence).

### 6.2 Compressed permutation oracles (statistical)

- **[CM26].** Advantage `≤ 120q/√(N−q+1) + q(q+1)/(N−2q+1)` for `3q − 1 ≤ N` [CM26, Cor. 4.3],
  claimed tight for that oracle.
  - **Keys:** no dependence on `|K|` [CM26, Cor. 4.17, 4.18].
  - **Inverse queries:** supported, including coherent direction and key.
  - **Efficiency:** efficient (partial-permutation databases).
- **[Kim26].** `4q/2^{n/2}` in its stated range (as reported in [BH26, §1.2]).
- **[Car25].** The original bound, `O(q³/N^{1/4})`.
- **[BH26, Thm. 2].** `8q²·Δ_cpO` for its compressed ideal cipher.
- **At `q = 2^64`:** `120·2^{64}/2^{64} = 120`, or `4` for [Kim26]. Vacuous. At `q = 2^{40}` the
  [CM26] bound is `≈ 2^{−17.1}`.
- **Does key-level use avoid the `√N`?** No. An adversary may put all `q` queries on one key, and
  then it faces one compressed permutation with the single-instance loss.
  - The `√N` belongs to the permutation compression, not to the key structure.
  - For search bounds the loss enters squared (`δ_N(T)² ≈ 7744T²/N`, §5.3). That is the same order
    as the Fiat–Shamir `q²/N`, but still `≥ 1` at `q = 2^64`.
- **Extraction.** No DFMS-style commutator or extraction theorem exists for these oracles. `S*`
  makes this moot: extraction never looks inside a permutation.
- **[MMW24]** (permutation superposition oracles) handles single input-output predicates and
  gives no list-of-pairs database. **[ACMT25]** uses [Car25]'s oracle for the sponge. Neither
  gives an efficient two-point key-level extractor.

### 6.3 Definitional options

- **Oracle-relative definitions.** Some QROM/QICM definitions count the oracle as unit cost, or
  give the extractor oracle access. Under such a definition, a reduction to UOV would need "UOV is
  hard for quantum algorithms with QIC access". That is an assumption relative to an inefficient
  oracle, and it is non-standard unless the QIC is efficiently simulable.
- **With `S*` the distinction disappears.**
  - UOV hardness implies UOV hardness relative to the QIC, up to `2^{−172}` (Theorem A).
  - DFMS-style online extraction, where the extractor *is* the oracle simulator [DFMS22], is
    achieved with an efficient simulator.
- So for PomFRIT one-more unforgeability (to UOV), and for Moussaka and Ratatouille unforgeability
  (to UOV and Keccak), the plain-model reductions are efficient. They lose `ε_sim = 2^{−172}`,
  plus Q1/Q2's extraction error, plus the game's own terms. No candidate-1 assumption is needed.

### 6.4 Commutation (item 4 of the brief)

Theorem B is the answer. In `S*`:
- the online-extraction measurement "find a database key `k` with `E_k(x_c) = t_c` for both `c`"
  is Q1's `Ext`, read from `F`'s database;
- it commutes exactly with random-oracle queries, adversary unitaries and other `Ext` calls;
- it `δ`-almost-commutes with each `Enc`/`Dec` query, `δ = 8√(2p)`, with no loss relative to Q1;
- correctness (P2, P3) and Lemma 5 (P4) hold with Q1's constants.

The brief's variant, "match one block, then evaluate the other", is implied: `Ext` checks both
blocks and evaluates `ρ_k` internally.

## 7. Interface for Q1/Q2

Q2 may use `S*` in place of `S^IC`:

- **(S0) Efficiency.**
  - `Enc`/`Dec`: one compressed-oracle step on `F` plus `≤ 1.2·10⁶` `H`-queries.
  - `Ext`: `O(q)` evaluations of `ρ` on the sparse `F` database.
  - Total `poly(q, λ)`, `Õ(q²)` gates without QRAM.
- **(S1) Simulation (Q1 I0).** Without `Ext`, `S*` is `2^{−172}`-close to the QICM for unbounded
  adversaries, with no query bound (Theorem A). Add this once to the final bound.
- **(S2) Q1 (I1)–(I4), (I6), (I7) hold verbatim with Q1's constants** (Theorem B):
  - `δ = 8√(2p)` per cipher query;
  - `2(2q₂+1)²p` for dead leaves, other keys and persistence;
  - P2 `2p`;
  - `√P_real ≤ √P_db + √(2p)`;
  - database `≤ q` keys.

  Here `q₁, q₂` count cipher queries (including the verifier's and extractor's). Each costs 2
  `F`-queries, already accounted for as in Q1.
- **(S3) (I5) `multi`.** `ε_multi ≤ min( (320/9)q₁³/(N−1),  ε_multi^{H₄}(q₁,q₄) + 2^{−172} + L·q·δ )`.
  - The second term holds only while `θ ≤ 1/2` (`q ≲ 2^{37}`). `L` is the number of `Ext` calls
    before the one in question.
  - Proven bounds are vacuous for `q ≳ 2^{40}`.
- **(S4) Any QICM bound transfers.** Any future QICM bound for two-block cross-key collisions at
  H₄-derived plaintexts transfers to `S*`'s `multi` with `+2^{−172}` (§5.2).

## 8. What is new and what is cited

**Cited and used:**
- [MR14] Thm. 3, Thm. 4, eq. (1); [HMR12] for the swap-or-not bound;
- [Zha16/25] Lemmas 3.7–3.8 (full-domain FPCs are quantum secure);
- [Zha12a] Thm. 6.1 (`2q`-wise independence) and [Zha19] (compressed oracle);
- [CFHL21] (abelian ranges, Thm. 5.17) and [DFMS22] (extraction measurement, App. B sparse
  representation);
- [BH26] Thm. 1, Prop. 1, Thm. 2, Lemma 4;
- [CM26] Cor. 4.3, 4.17, Lemma 5.1, Thm. 5.3;
- [HHM+26] App. A.1 (efficient statistical simulation of a random permutation via mix-and-cut
  with swap-or-not).

**New here, as far as I found:**
1. The simulator `S*`. It separates the *recording* randomness (affine whitening from a
   small-range compressed oracle, which gives the key database) from the *pseudorandomness*
   (a full-domain shuffle, simulated statistically). The result is an efficient, assumption-free
   QIC simulator whose error does not depend on `q`, and an extractor with Q1's exact constants.
2. Theorem B: exact extraction structure for *every* fixed `ρ`, with `δ` not doubled (the single
   `C`-conjugation argument).
3. Theorem C: three-interface closeness of two different key-level compressions (`F^Y` versus
   `F^{YC}`), proved by branch orthogonality.
4. §5: the reduction of `multi` to a QICM search problem, and the analysis of why current
   point-level and seed-level techniques stall at `O(q³/N)`, with the precise missing lemma.

**Gaps.**
- `ε_multi` for `q ≳ 2^{40}` (§5.3). Neither the simulator nor the efficiency question causes this.
- MR14's round counts are used through their stated TV bound. Only the arithmetic is in Lean, not
  the probability argument.
- The `Õ(q²)` cost of compressed-oracle simulation is polynomial but not concretely tight, as for
  every known QROM straight-line extractor.
- [BH26], [CM26], [Kim26] and [HHM+26] are 2026 preprints. Their statements were read from the
  arXiv and ePrint PDFs; [Kim26]'s constant is taken from [BH26, §1.2].

## References

- [ACMT25] G. Alagic, J. Carolan, C. Majenz, S. Tokat. *The Sponge is Quantum Indifferentiable.*
  FOCS 2025.
- [BH26] R. Bhaumik, Y.-H. Huang. *Indistinguishability Lifting for Keyed Oracles, Compressed Ideal
  Cipher, and More Applications.* arXiv:2610.04674, ePrint 2026/2324.
- [Car25] J. Carolan. *Compressed Permutation Oracles.* arXiv:2509.18586 (STOC 2026).
- [CFHL21] K.-M. Chung, S. Fehr, Y.-H. Huang, T.-N. Liao. *On the Compressed-Oracle Technique, and
  Post-Quantum Security of Proofs of Sequential Work.* EUROCRYPT 2021, arXiv:2010.11658.
- [CM26] J. Carolan, C. Majenz. *Compressed Permutation Oracles Revisited.* arXiv:2609.28469.
- [DFMS22] J. Don, S. Fehr, C. Majenz, C. Schaffner. *Online-Extractability in the Quantum
  Random-Oracle Model.* EUROCRYPT 2022, arXiv:2103.03085.
- [HHM+26] Y.-H. Huang, A. Hülsing, V. Maram, S. Ritsch, A. Saha. *Feistel Tools: Query-Recording
  and Reprogramming for QRPs.* ePrint 2026/146.
- [HMR12] V. T. Hoang, B. Morris, P. Rogaway. *An Enciphering Scheme Based on a Card Shuffle.*
  CRYPTO 2012.
- [Kim26] S. Kim. *Improved Soundness for Compressed Permutation Oracles and Tight Quantum Preimage
  and Collision Bounds for the Sponge.* ePrint 2026/2135.
- [LZ19] Q. Liu, M. Zhandry. *On Finding Quantum Multi-collisions.* EUROCRYPT 2019.
- [MMW24] C. Majenz, G. Malavolta, M. Walter. *Permutation Superposition Oracles for Quantum Query
  Lower Bounds.* arXiv:2407.09655.
- [MR14] B. Morris, P. Rogaway. *Sometimes-Recurse Shuffle: Almost-Random Permutations in
  Logarithmic Expected Time.* EUROCRYPT 2014, ePrint 2013/560.
- [RY13] T. Ristenpart, S. Yilek. *The Mix-and-Cut Shuffle: Small-Domain Encryption Secure against
  N Queries.* CRYPTO 2013.
- [Zha12a] M. Zhandry. *Secure Identity-Based Encryption in the Quantum Random Oracle Model.*
  CRYPTO 2012 (`2q`-wise independence, Thm. 6.1 of the full version).
- [Zha12b] M. Zhandry. *How to Construct Quantum Random Functions.* FOCS 2012 (small-range
  distributions).
- [Zha15] M. Zhandry. *A Note on the Quantum Collision and Set Equality Problems.* QIC 15 (2015).
- [Zha16/25] M. Zhandry. *A Note on Quantum-Secure PRPs.* ePrint 2016/1076, arXiv:1611.05564;
  Quantum (2025).
- [Zha19] M. Zhandry. *How to Record Quantum Queries, and Applications to Quantum
  Indifferentiability.* CRYPTO 2019.

Downloaded sources (scratchpad `papers/q4/`): arXiv 2610.04674, 2609.28469, 2509.18586,
1611.05564; ePrint 2013/560 and 2026/146 (via web.archive.org). [HMR12], [RY13], [LZ19], [Zha12a],
[Zha12b] and [Zha15] are cited from their restatements in these papers or from memory. Check
theorem numbers against the originals.
