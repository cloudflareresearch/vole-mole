# Two open reductions between the UOV assumptions

This note continues `lean/docs/security/uov-assumptions.md` (cited as **[UA]**). It treats two items
of [UA] §9:

- **A.** OMPR versus the τ-shift variant OMPR⊕τ (τ = 17), [UA] §6.
- **B.** CT-UF with a signing oracle on arbitrary targets versus OMPR, [UA] §5.4.

Notation is that of [UA] §1 and §3: `F = GF(256)`, `P : F^119 → F^45` the public map,
`D = derive_preimage`, `M = 45`, `|F^M| = 2^{360}`. `F^× = F ∖ {0}`. For a target `t`, its *class*
is `[t] = F^×·t` (255 targets if `t ≠ 0`).

Every statement is marked **[proved]** (full proof here), **[Lean]** (also machine-checked),
**[heuristic]** or **[conjecture]**. Nothing here changes the protocols.

## 0. Summary

**One new fact drives part B and adjusts part A.** `P` is homogeneous of degree 2 and squaring is a
bijection of `GF(256)`. So `s ↦ √μ·s` maps the preimages of `t` onto the preimages of `μ·t`
(Lemma S, §2). The targets that matter are classes `[t]`, not single targets.

| # | Statement | Status | Where |
|---|---|---|---|
| S | `P(λs) = λ²P(s)`; a preimage of `μt` (`μ ≠ 0`) gives a preimage of `t`, and good stays good | proved, Lean (`qmap_smul`, `scaled_preimage`) | §2 |
| B1 | **CT-UF as defined (`moussaka.md` §3.3, [UA] §3 item 10) is false.** One query `Sign(μ·Com(x*))`, `μ ∉ {0,1}`, gives a forgery with probability `1 − δ^{255}`, for every function `Com`. So no reduction CT-UF ⇐ OMPR exists unless OMPR is false. CT-UF^open, A-OMPI, UF-Tag, OMPR are not affected | proved, Lean (`ctuf_scaling_attack`) | §2 |
| B2 | The repaired notion CT-UF^× (freshness up to scalars) is **equivalent**, tightly, with `Com` an ideal permutation, to OMPR^free: OMPR in which only calls on challenge classes are charged. `OMPR^free ⇒ OMPR ⇒ A-OMPI`, tightly | proved | §3.1–3.2 |
| B3 | **Oracle separation.** There is an oracle world with a preimage-sampleable function for which OMPR holds unconditionally (advantage `≤ 2(4W+n)²·2^{−360}`) and OMPR^free, hence CT-UF^× for every `Com`, is broken with 2 free calls. So **no relativizing reduction** (black-box in `(P, D)`) proves CT-UF^× or OMPR^free from OMPR, with any loss | proved; counting core Lean (`combiner_count`) | §3.3 |
| B4 | OMPR^free ⇐ OMPR **for adversaries whose free calls are fixed before the targets**: by rewinding, with advantage `ε/3`, time `×8(Q_f+1)/ε`. `Q_f = 0` is A-OMPI | proved | §3.4 |
| B5 | What signatures on non-`Com` targets give for UOV: the class symmetry (B1), 255 preimages per target, and explicit restrictions of `P` to spans. No further combiner is known; the isotropic-pair one costs `≳ 2^{345}` calls | heuristic | §3.5 |
| A1 | `Adv^{ompr}(n, q) ≤ Adv^{ompr⊕τ}(n, q)`: the easy direction is tight | proved, Lean (`advOMPR_le_shift`, `advOMPRShift_mono`) | §4.1 |
| A2 | The shift cannot be absorbed into the key. `P ⊕ c` is not a UOV map. Its homogenization is a degenerate `(120, 45)` map whose preimage problem is again a shift problem, with one fixed `c` | proved | §4.2 |
| A3 | Turning a preimage of `y` into a preimage of `y ⊕ Δ`, for uniform `Δ`, **is** the UOV problem (tight) | proved | §4.3 |
| A4 | **Rewinding does not help in general.** In the generic model, every reduction OMPR⊕τ ⇒ OMPR that is black-box in the adversary and in `(P, D)`, with unlimited rewinding, any embedding and any number of targets and calls, succeeds with probability `≤ 2·τ^{−(q+1)} + V⁴·2^{−360}` against one explicit adversary (`τ ≥ 7`, `q ≥ 1`). Guessing achieves `τ^{−(q+1)}` | proved; inequality and counting Lean (`rewind_supermartingale`, `lottery_count`) | §4.4 |
| A5 | **Rewinding does help for some adversaries**: if all `D`-queries are on shifted targets of the first `N − 1` requests, a rewinding reduction has polynomial loss (`ε/3`, time `×8τ(τ(N−1)+1)/ε`) | proved | §4.5 |
| A6 | OMPR ⇒ OMPR⊕17 for UOV with polynomial loss: **open**. Any proof must use the algebra of `P` (by A4) in a way that A3 makes unlikely, or be non-black-box in the adversary. Follow-up (`ompr-shift-algebra.md`): using the algebra does not help a reduction that is black-box in the adversary, unless OMPR^free fails; no attack at τ = 17 | conjecture, obstacles | §4.6 |

**Answers to the two questions.**
- **A.** OMPR⊕τ ⇒ OMPR is tight. OMPR ⇒ OMPR⊕τ has no tight or polynomial-loss proof in the
  class of relativizing reductions, even with rewinding (A4); the `τ^{q+1}` of [UA] Prop. 8(a) is
  optimal there up to a factor 2. No separation for UOV itself is known and the generic bounds
  agree. The key cannot absorb the shift (A2).
- **B.** CT-UF as defined does not follow from OMPR with any loss: it is false (B1). Its repair
  CT-UF^× is exactly OMPR^free (B2), which no relativizing reduction derives from OMPR (B3). The
  reduction "explains" a non-`Com` query only when that query does not depend on the targets (B4)
  or when the adversary opens it (CT-UF^open, [UA] T4). **Moussaka must use CT-UF^open**; that
  proof stands.

---

## 1. Conventions

- **Games.** OMPR(n, q), OMPR⊕τ(N, q), A-OMPI, CT-UF_K, CT-UF^open_K as in [UA] §3. A one-more
  adversary *wins* if it outputs more preimages of distinct challenge indices than it made calls;
  this is the usual `q + 1` after `≤ q` calls (pad with calls on unused targets).
- **Ideal `Com`.** As in [UA] §5.4: `Com = KP800(·)|_{360}` on `D_Com` (576 free input bits),
  `KP800` a random permutation with inverse access, in standalone games only.
- **Generic preimage-sampleable function (generic PSF).** As in [UA] §6(c): a random function
  `F : X → Y`, `|X| = 2^{952}`, `|Y| = 2^{360}`, given by a forward oracle `Fwd` and a deterministic
  inversion oracle `Inv`. Lazily: `Inv(y)` on a new `y` returns a fresh uniform point `x_y` and
  sets `F(x_y) := y`; `Fwd(x)` on a point that is not an `Inv` answer returns a fresh uniform
  value. The lazy game is the definition. Point collisions cost `≤ V²·2^{−952}`, where `V` counts
  all values in play; this term is included in the bounds below without mention.
- **Relativizing reduction.** A reduction that uses the public map and the preimage oracle only
  through `Fwd` and `Inv`, and the adversary only as an oracle (it may rewind it). Its statement
  must then hold for every PSF and every adversary, also unbounded ones, in every oracle world.
  All reductions of [UA] except those through GPI are of this kind.

## 2. The scaling symmetry, and CT-UF

**Lemma S [proved, Lean].**
1. `P(λ·s) = λ²·P(s)` for all `λ ∈ F`, `s ∈ F^N`.
2. For every `μ ∈ F`, `(μ^{128})² = μ`. Write `√μ = μ^{128}`.
3. For `μ ≠ 0`, `Sc_μ : s ↦ √μ·s` is a bijection from the preimages of `t` onto the preimages of
   `μ·t`, with inverse `Sc_{μ^{−1}}`. It maps `Good` to `Good`, so it is a bijection
   `S^G_t → S^G_{μt}`.

*Proof.*
1. `P` is a sum of monomials `p·s_i·s_j` (pqov has no linear or constant terms). Lean: `qmap_smul`
   on the model of the expanded key, `publicMap_scale` for any sizes.
2. `μ^{256} = μ` in a field of 256 elements. Lean: `sq_pow_128`.
3. `P(√μ·s) = μ·P(s)`. For goodness: `vin(λs) = λ·vin(s)` and `L_{λv} = λ·L_v`, because `L_v` is
   linear in `v` ([UA] §1). So `L_{vin(√μ s)}` is invertible iff `L_{vin(s)}` is. Lean:
   `scaled_preimage` (the preimage part). ∎

Remarks.
- `P(0) = 0`. The target `0` has the trivial preimage `0`; `D(0)` returns a nonzero one.
- `D(μt)` is **not** `Sc_μ(D(t))`. The vinegars of distinct targets are independent ([UA] Lemma D).
  So the 255 calls `D(μt)`, `μ ∈ F^×`, give 255 independent good preimages of each target of the
  class. "One preimage per target" ([UA] §5.7, determinism) reads "one per call, 255 per class".
  All of them cost calls, so this does not touch OMPR.

**Theorem B1 (CT-UF is false) [proved, Lean].** For every function `Com : D_Com → F^M`, every
`K ≥ 1` and every key, there is an adversary against CT-UF_K ([UA] §3 item 10; `moussaka.md` §3.3)
with **one** `Sign` query, about 119 field multiplications, and

    Adv^{ct-uf}_{UOV,Com,K} ≥ 1 − δ(sk)^{255}.

*Proof.* Pick any `x* ∈ D_Com` and let `t = Com(x*)`.
- If `t = 0`, output `(1, x*, 0)`: `P(0) = 0`, and nothing was queried.
- Otherwise fix `μ ∉ {0, 1}`, query `s ← Sign_1(μ·t)` and output `(1, x*, √(μ^{−1})·s)`.
  - `μ·t ≠ t`, since `(μ − 1)·t ≠ 0`. So `Com(x*)` was never queried.
  - `P(√(μ^{−1})·s) = μ^{−1}·μ·t = t`.
  - `Sign_1` fails only if 255 vinegars are bad ([UA] §2).

Lean: `ctuf_scaling_attack` (`Spec/PqovScale.lean`), for the model `qmap` that `lake exe spec_kats`
checks against the C++. ∎

**Consequences.**
1. `moussaka.md` Lemma U is not only unproved ([UA] T4): its conclusion is false, unless OMPR is
   false. An OMPR adversary gains nothing from Lemma S, because a preimage of `μ·t_i` is a preimage
   of another challenge `t_j` only if `t_j ∈ [t_i]`, which has probability `≤ n²·2^{−353}`.
2. **CT-UF^open is not affected.** The attacker would have to open `μ·Com(x*)`. The proof of
   [UA] T4 counts challenge indices, not targets, and never uses that distinct targets need
   distinct calls. Its bound stands as stated.
3. A-OMPI, UF-Tag and det-FDH are not affected: their oracles sign hash outputs only, and two
   hash outputs lie in one class with probability `≤ q²·2^{−353}`.
4. PomFRIT is not affected. Its Issuer signs arbitrary targets, but the game counts signatures,
   and the reductions U1, U2 go through OMPR, which Lemma S does not touch (item 1). Sketch of the
   direct reason: turning one answer into two signatures needs `μ·(h ⊕ r) = h′ ⊕ r′` with the
   prefix sets fixed before `h`, `h′`, an event of probability about `Q_T²·255·17²·2^{−360}`.
5. Every "generic" argument about UOV preimages must be read up to this symmetry. [UA] §6(b)
   needs the wider class of embeddings `h_k = μ·t_{j(k)} ⊕ c_k`, with the same conclusion: aligning
   two shifts of one request needs `(μ₁ ⊕ μ₂)·t_j = δ_{k,a} ⊕ δ_{k,b}` or the analogous relation
   between two targets, of probability `≤ n²·2^{16}·2^{−360}` when the shifts do not depend on the
   targets.

**The repaired notion.**
- **CT-UF^×_K.** As CT-UF_K, but `A` wins only if `Com(x*) ≠ 0` and **no element of the class
  `[Com(x*)]`** was queried to any `Sign_j`.
- This is the least repair that keeps the arbitrary-target oracle. §3 shows what it costs.

## 3. Part B: CT-UF^× and OMPR

### 3.1 OMPR with free calls

**Definition (OMPR^free(n, Q)).** `A` gets `pk` and `t_1..t_n ← U(F^M)`, and makes `≤ Q` calls to
`D` on arbitrary targets. It wins with `(j, s)` such that `P(s) = t_j`, `t_j ≠ 0`, and no call was
made on an element of `[t_j]`.

- *One-more form.* Call a call *charged* to `j` if its target is in `[t_j]`, and *free* if it is
  charged to no index. `A` wins the one-more form if it outputs preimages of `c + 1` distinct
  indices, where `c` is the number of indices charged at least once. The two forms are equivalent,
  tightly: among `c + 1` indices one is uncharged; conversely, add to `(j, s)` the rescaled answers
  of one call per charged index.
- So OMPR^free is OMPR in which **calls on non-challenge targets are free**. It is the variant
  that [UA] §5.4 says Lemma U would need.
- It is A-OMPI ([UA] §3 item 9) with an additional oracle for arbitrary targets.

**Lemma 3.1 [proved].**
`Adv^{ompi}(n, Q) ≤ Adv^{ompr}(n, Q) ≤ Adv^{free}(n, Q) + n²·2^{−353}`.

*Proof.* The first inequality is [UA] T1(c). For the second, run the OMPR adversary unchanged.
Two targets lie in one class with probability `≤ C(n,2)·255·2^{−360}`, and some target is `0` with
probability `≤ n·2^{−360}`. Otherwise each call is charged to at most one index. After `≤ q` calls at most `q` indices are charged, so one of the
`q + 1` output indices is uncharged. ∎

So `OMPR^free ⇒ OMPR ⇒ A-OMPI`. The question of [UA] §9 is the converse of the first arrow.

### 3.2 CT-UF^× is OMPR^free

**Theorem B2 [proved].** With `Com` ideal (§1), `q_f` forward, `q_i` inverse and `q_S` `Sign`
queries:

    (a)  Adv^{ct-uf×}_{UOV,Com,1}(A) ≤ Adv^{free}(B; q_f + 1, q_S) + q_i·2^{−223.9} + (q_f + 1)²·2^{−800},
    (b)  Adv^{free}(B; n, Q) ≤ Adv^{ct-uf×}_{UOV,Com,1}(A; q_f = n, q_i = 0, q_S = Q) + n²·2^{−801},

and `Adv^{ct-uf×}_K ≤ K·Adv^{ct-uf×}_1`.

*Proof.*
(a) is the proof of Lemma U, which is correct for this target.
- `B` answers a fresh forward query on a `D_Com`-structured input with `t_j ‖ z`, `t_j` its next
  target, and all other queries uniformly. The two error terms are those of [UA] T4.
- `B` forwards every `Sign` query to `D`. It never needs to count them.
- On `A`'s output `(x*, s*)`, `B` evaluates `Com(x*)` (one more forward query). It is a challenge
  `t_j`, and no query was in `[t_j]`. `B` outputs `(j, s*)`.

(b) `A` picks `n` distinct inputs `x_1..x_n ∈ D_Com` and gives `B` the targets `t_j = Com(x_j)`.
- These are the 360-bit prefixes of `n` distinct values of a random permutation. Their distance
  from `n` independent uniform values is `≤ n²·2^{−801}`.
- `A` forwards `B`'s calls to `Sign`, and turns `B`'s output `(j, s)` into `(x_j, s)`. ∎

So, in the ideal-`Com` model, **CT-UF^× and OMPR^free are the same assumption.** The loss of the
opening requirement is exactly the freedom to make uncharged calls.

### 3.3 No relativizing reduction from OMPR

A *combiner* is a public procedure that turns preimages of some targets into a preimage of another
target. Lemma S is one, inside a class. OMPR^free says that there is no combiner across classes.
OMPR alone does not say that:

**The world 𝒲.** A generic PSF `(Fwd, Inv)` (§1), two public random functions
`π₁, π₂ : Y → Y`, and a public oracle

    Cmb(t, s₁, s₂):  if Fwd(s₁) = π₁(t) and Fwd(s₂) = π₂(t) then return x_t (the answer of Inv(t)), else ⊥.

`Cmb`'s internal use of `Inv` is not a call of the player.

**Theorem B3 [proved; counting in Lean].** In 𝒲:
1. **OMPR^free is broken.** With `n = 1` and 2 free calls, `Adv^{free} ≥ 1 − 2^{−359}`. The same
   adversary breaks CT-UF^× (the version without the scalar clause too) for every `Com`.
2. **OMPR holds.** Every algorithm with `n` targets, `c` calls to `Inv` and `W` other queries
   outputs preimages of `c + 1` distinct challenge indices with probability
   `≤ 2·(4W + n)²·2^{−360}`.

*Proof.*
1. Given `t`: call `s_i ← Inv(π_i(t))` for `i = 1, 2`, and output `Cmb(t, s₁, s₂)`. The calls are
   free unless `π_i(t) = t`.
2. Count a `Cmb` query as four queries (`π₁`, `π₂`, two `Fwd`), and the final check as `Fwd`
   queries. Let **Bad** be the event that
   - a fresh `Fwd` value equals a challenge target or a `π` value, in either order of appearance, or
   - a `π` value equals a challenge target or another `π` value.

   Each is a fresh uniform value hitting one of `≤ 4W + n` values, so
   `Pr[Bad] ≤ 2·(4W + n)²·2^{−360}`.

   Outside Bad, the only known preimage of a challenge target or of a `π` value `y` is `x_y`, and
   it is known only after `Inv(y)` or a successful `Cmb(y, ·, ·)`.
   - Let `Dset` be the set of targets of `Inv` calls (`|Dset| ≤ c`), `Eset` the other targets with a
     successful `Cmb` query, and `Ch` the challenge targets whose preimage is output.
   - `Ch ⊆ Dset ∪ Eset`.
   - A successful `Cmb(y, s₁, s₂)` needs `Fwd(s_i) = π_i(y)`, so `π₁(y), π₂(y) ∈ Dset ∪ Eset`.
   - Outside Bad, `π₁` and `π₂` are injective on `Eset`, their images are disjoint, and they
     contain no challenge target.
   - Lean `combiner_count`: then `|Ch| + |Eset| ≤ |Dset| ≤ c`. ∎

The reason is plain: `Cmb` trades two preimages for one. It never yields more preimages than
calls. But it converts *free* preimages into a challenge preimage, and only OMPR^free forbids that.

**Corollary B3′ [proved].** No relativizing reduction (§1) proves OMPR^free, or CT-UF^× with `Com`
a random oracle or ideal permutation, from OMPR: with any loss `L`, such a reduction `R`, run in 𝒲
with the adversary of item 1, is an algorithm with polynomially many queries that wins OMPR with
probability `≥ (1 − 2^{−359})/L`. By item 2, `L ≥ 2^{360}/(2·(4W + n)²) − 1`.
- Rewinding is covered: `R` may run the adversary any number of times.
- The adversary is efficient in 𝒲, so the statement does not rest on an unbounded adversary.

**What this means for UOV.**
- A proof of CT-UF^× from OMPR for UOV must use a property of `P` that fails in 𝒲: the absence of
  a combiner across classes. That property *is* OMPR^free. It is an assumption of its own.
- UOV is not combiner-free in the literal sense (Lemma S). This shows that generic-model evidence
  ([UA] §6(c); the paper's App. A) says nothing about combiners.
- This is not a separation for UOV itself. For UOV we know no attack on OMPR^free (§3.5).

### 3.4 A positive result: target-independent free calls

**Proposition B4 [proved].** Let `A = (A₁, A₂)` be an OMPR^free(n, ·) adversary of this form:
- `A₁(pk)` outputs targets `u_1..u_{Q_f}` and a state, **before** the challenge targets exist;
- `A₂` gets the state, the answers `D(u_i)`, and `t_1..t_n`. It queries `D` only on challenge
  targets `t_j` themselves, at most `q_c` times.

Let `ε = Adv^{free}(A)` and `r = ⌈8(Q_f + 1)/ε⌉`. Then there is `R`, running `A₁` once and `A₂`
`r` times, with

    Adv^{ompr}(R; r·n, Q_f + r·q_c) ≥ ε/3.

*Proof.*
- `R` runs `A₁`, and calls `D` on `u_1..u_{Q_f}`: `Q_f` calls.
- It runs `A₂` `r` times on the same state and answers, each time with `n` fresh targets of its own
  and fresh coins. It forwards the index queries.
- A call on a challenge target gives a challenge preimage: it costs 1 and gains 1.
- A successful run `i` outputs a preimage of a challenge target of run `i` on which no call was
  made: gain 1, cost 0. (If some `u_k` lies in a challenge class, that run cannot win on it, and
  the call was a bonus.)
- So `R` wins iff at least `Q_f + 1` runs succeed.
- Let `p` be the success probability of one run given `sk`, the state and the answers; `D` is a
  fixed function, so given these the runs are independent. `E[p] = ε`, hence
  `Pr[p ≥ ε/2] ≥ ε/2`.
- If `p ≥ ε/2`, the number of successes is binomial with mean `m ≥ 4(Q_f + 1)`. By the Chernoff
  bound, it is `< m/4` with probability `≤ e^{−9m/32} ≤ e^{−9/8} < 1/3`.
- So `R` wins with probability `≥ (ε/2)·(2/3)`. ∎

Remarks.
- `Q_f = 0` is A-OMPI, where the reduction is tight ([UA] T1(c)).
- The loss is in time and in the number of calls, not in the advantage: the `Q_f` wasted calls are
  paid once and amortized over `Q_f + 1` forgeries.
- The combiner adversary of §3.3 is outside the class: its free calls `π_i(t)` depend on the
  target. Rewinding it costs two new calls per run.
- In CT-UF^× terms the class is: every `Sign` query on a non-`Com` target is fixed before the
  first `Com` evaluation. This is not a natural restriction for Moussaka. CT-UF^open is.

### 3.5 What signatures on non-`Com` targets give, for UOV [heuristic]

An adversary with free answers `s_i = D(u_i)`, `i ≤ k`, holds:
1. **The classes** `[u_i]`, by Lemma S. This is what breaks CT-UF and is excluded in CT-UF^×.
2. **Up to 255 preimages per target**, from 255 calls on a class.
3. **`P` on the span of the answers**:

       P(Σ α_i s_i) = Σ α_i²·u_i + Σ_{i<j} α_i α_j·B(s_i, s_j).

   - This is `P` restricted to a subspace with a prescribed diagonal. Anyone can restrict `P` to a
     subspace; the diagonal is what the oracle adds.
   - *Isotropic pairs.* If `B(s_i, s_j) = 0`, the adversary gets preimages of the whole plane
     `span(u_i, u_j)`. To reach a given `t`, both targets must lie in a plane through `t`, which
     has `2^{16} − 256` usable targets. `B(s_i, s_j) = 0` is 45 conditions on independent good
     preimages, so it has probability about `2^{−360}` per pair. With `Q` calls there are
     `≤ Q·2^{15}` usable pairs. So this combiner needs `Q ≳ 2^{345}`.
   - With `k ≥ 45` answers, hitting `t` in the span is 45 quadratic equations in `k` unknowns
     with random cross terms: an MQ instance, not easier than restricting `P` to a random subspace.
4. **Samples of `U(S^G_u)`**, as in OMPR. Nothing more about `𝒪` than an OMPR adversary sees.

We know no combiner across classes. This is the content of the assumption OMPR^free.

**Can a reduction explain such queries?** Without `sk`, a reduction answers `Sign(u)` in one of
two ways.
- *By its own oracle.* This costs a call. It is free of loss only if the call is charged to a
  challenge (CT-UF^open, [UA] T4) or amortized (B4).
- *From a known preimage*: `u ∈ [P(s)]` for an `s` it chose. Then `u` must have been planted in
  the adversary's view. Only `Com` outputs can be programmed, so only `Com` targets can be
  explained this way (the GPI route of [UA] T4).

Observing the adversary's `Com` queries tells the reduction *that* a target is not a `Com` image,
not how to invert it. By B3 no other relativizing strategy exists.

### 3.6 Verdict on B

- CT-UF with an arbitrary-target oracle: **false** (B1). Replace it everywhere.
- CT-UF^× is the correct arbitrary-target notion. It equals OMPR^free (B2), which is strictly
  stronger than OMPR for relativizing reductions (B3), and follows from OMPR only for restricted
  adversaries (B4). For UOV it is a plausible but separate assumption (B5).
- **Moussaka should stay with CT-UF^open** ([UA] T4): it follows tightly from OMPR, and `B₂` has
  the openings. Nothing is gained by CT-UF^×.

## 4. Part A: OMPR and OMPR⊕τ

### 4.1 The easy direction is tight

**Proposition A1 [proved].** For all `τ ≥ 1`: `Adv^{ompr}(n, q) ≤ Adv^{ompr⊕τ}(n, q)`, and
`Adv^{ompr⊕τ} ≤ Adv^{ompr⊕τ′}` for `τ ≤ τ′`.

*Proof.* Request `k` with the single shift `0`; `h_k` is `t_k`. Calls and outputs are unchanged.
Shorter lists are allowed in the larger game. ∎

So OMPR⊕τ ⇒ OMPR without loss, and the only question is the converse.

*Lean* (`lean/VoleMole/Assumptions/Shift.lean`): `advOMPR_le_shift` (`τ ≥ 1`, adversary
`shiftZero B`, the runs correspond exactly) and `advOMPRShift_mono`. The guessing bound of [UA]
Prop. 8(a) is `advOMPRShift_le_guess`.

### 4.2 The shift cannot be absorbed into the key

**Proposition A2 [proved].** Let `c ∈ F^M`, `c ≠ 0`, and `P_c(s) = P(s) ⊕ c`.
1. `P_c` is not a UOV public map: it vanishes on no linear subspace, since `P_c(0) = c ≠ 0`.
2. Its homogenization `P̂_c(s, z) = P(s) ⊕ c·z²` on `F^{N+1}` vanishes on `𝒪 × {0}`, but:
   - it is degenerate: its polar form is `B̂((s,z),(s′,z′)) = B(s, s′)`, because `2czz′ = 0` in
     characteristic 2. The direction `z` is in the radical. This is not a uov-Ip key;
   - `P̂_c(s, λ) = h` iff `P(s) = h ⊕ λ²·c`. So a preimage of `h` under `P̂_c` is a preimage under
     `P` of **one of the 256 shifts** `h ⊕ μ·c`, `μ ∈ F`.
3. A translation of the domain does not shift targets: `s ↦ P(s + a)` has the fibres of `P`,
   translated.

*Proof.* Direct from `P(s + a) = P(s) ⊕ P(a) ⊕ B(s, a)` and Lemma S. ∎

Consequences.
- Absorbing a shift into the key only restates the problem: OMPR for the key `P̂_c` is a shift
  problem for `P` with the shift set `F·c`.
- A key carries one `c`. OMPR⊕τ has up to τ shifts per request, chosen by the adversary, different
  for each request. A reduction to OMPR cannot change its key per request, and its oracle is for
  `P`.
- The only public maps `(φ, T)` with `P ∘ φ = T ∘ P` that we know are the scalings of Lemma S.
  They act on targets linearly, not by translation.

### 4.3 Translating a preimage is the UOV problem

A reduction that could use a forgery for the "wrong" shift would solve the following.

**Translation problem.** `Adv^{tr}(A) = Pr[P(A(pk, s, Δ)) = P(s) ⊕ Δ]`, for `s ← U(F^N)`,
`Δ ← U(F^M)`.

**Lemma A3 [proved].** `Adv^{tr} = Adv^{uov}`: each problem reduces to the other with the same
advantage and running time (plus one evaluation of `P`). With `s ← U(Good)` instead, the advantages
differ by at most `δ` (and by `Adv^{gpi}(1)` computationally).

*Proof.* The target `y = P(s) ⊕ Δ` is uniform and independent of `s`.
- A UOV solver, run on `y`, solves translation.
- Given a UOV target `t`, sample `s ← U(F^N)` and set `Δ = t ⊕ P(s)`. This is a translation
  instance with the right distribution, and its solution is a preimage of `t`.
- `TV(U(Good), U(F^N)) = δ` ([UA] §2). ∎

Remarks.
- For a **fixed** `Δ ≠ 0` (shifts are chosen by the adversary, so not uniform), the problem is to
  solve `P(e) ⊕ B(s, e) = Δ` in `e`: the UOV problem for the translated map
  `e ↦ P(s + e) ⊕ P(s)`, with the same oil space ([UA] §6(c)). `Tr_Δ` and `Tr_{μΔ}` are
  equivalent by Lemma S. We have no reduction from the UOV problem for fixed `Δ`.
- `e = λ·s` gives `P(s + λs) = (1 + λ)²·P(s)`: again only the class of `P(s)`. It reaches
  `h ⊕ δ_b` from `h ⊕ δ_a` only if `h = (μ·δ_a ⊕ δ_b)/(1 ⊕ μ)`, which the uniform `h` avoids.

### 4.4 Rewinding does not help in general

[UA] Prop. 8(b) excludes *simple-embedding* reductions: one run, forwarding, `h_k = t_j ⊕ c_k`.
The next theorem removes all three restrictions, at the price of the generic model for `P`.

**The adversary `A**`** (for `q ≥ 1`, `N = q + 1` requests). It has private random functions
`S_k`, `G`, `a`, and access to the PSF.
1. For `k = 1..q+1`: it submits the shift list `δ_k = S_k(h_1..h_{k−1}) ∈ Y^τ` and receives `h_k`.
   Let `H = (h_1..h_{q+1})`.
2. It asks `D` for preimages of the *junk* targets `(u_1..u_q) = G(H) ∈ Y^q`, checks every answer
   with `Fwd`, and aborts if one is wrong.
3. It outputs, for every `k`, the forgery `(k, a_k, x_z)` with `a = a(H) ∈ [τ]^{q+1}` and
   `z = h_k ⊕ δ_{k,a_k}` (the answer `Inv(z)`, found by search).

`A**` is unbounded, makes `q` calls and always wins OMPR⊕τ(q+1, q). Its calls are useless to it;
they exist to make every run cost the reduction `q` calls.

**Theorem A4 [proved; inequality and counting in Lean].** Let `τ ≥ 7`, `q ≥ 1`. Let `R` be any
algorithm in the OMPR game for the generic PSF, with `n` targets, any number `c` of `Inv` calls,
`W` forward queries, and oracle access to `A**` as a next-message function (so `R` may rewind and
interleave runs at will, and choose every `h_k` as it likes), with `T` messages sent to `A**`.
Then

    Pr[R outputs preimages of c + 1 distinct challenge indices] ≤ 2·τ^{−(q+1)} + V⁴·2^{−360},

where `V = n + c + W + (τ + 1)(q + 1)·T` bounds the number of values of `Y` in play.

The guessing reduction of [UA] Prop. 8(a) succeeds against `A**` with probability `τ^{−(q+1)}`. So
for relativizing reductions the loss `τ^{q+1}` is optimal up to a factor 2, for every `q`, with or
without rewinding. For τ = 17 the loss is at least `2^{4.08(q+1) − 1}`.

*Proof.* Let `𝒯` be the set of challenge targets and `𝒰` the set of junk values revealed in the
execution.

*Step 1: bad events.* Each of the following is the event that a fresh uniform value of `Y` equals
one of at most `V³` values determined before it. There are at most `V` fresh values.
- (B1) A fresh `Fwd` value equals a value of `𝒯 ∪ 𝒰` already in play.
- (B2) A newly revealed junk value equals a value already in play: a target, a junk value, a
  candidate `h_k ⊕ δ_{k,a}`, a forward value, or the target of an `Inv` call.
- (B3) For one request of one run there are `a ≠ a′` with both candidates `h_k ⊕ δ_{k,a}`,
  `h_k ⊕ δ_{k,a′}` in `𝒯 ∪ 𝒰`. Then `δ_{k,a} ⊕ δ_{k,a′} = w ⊕ w′` with `w, w′ ∈ 𝒯 ∪ 𝒰`. The
  last revealed among the list `δ_k`, `w` and `w′` is fresh and must equal a value determined by
  the others. (Targets are fixed at the start; lists and junk are values of random functions at
  new points.)

So `Pr[Bad] ≤ V⁴·2^{−360}`. Assume no bad event from now on.

*Step 2: accounting.* `R` knows a preimage of a value `y ∈ 𝒯 ∪ 𝒰` only as `x_y`, obtained from
its own call `Inv(y)` or as the forgery of a completed run whose target is `y` (by B1).
- Let `K` be the number of *completed* runs: distinct `H` for which `R` answered all `q` junk
  queries correctly and received the output. Their `K·q` junk values are distinct and are not
  challenge targets (B2).
- If `R` wins, it holds preimages of `c + 1` challenge targets and of `K·q` junk values. At most
  `c` of these come from calls. So at least `K·q + 1` come from forgeries (Lean `lottery_count`).
- In particular `K ≥ 1`.

*Step 3: each run is a lottery.* For a run `H` and a request `k`, at most one shift `b_k(H)`
makes the candidate useful, i.e. in `𝒯 ∪ 𝒰` (B3). It is determined when `R` sends `h_k`: junk
revealed later misses all existing candidates (B2).
- `a(H)` is revealed only with the output of the completed run, and it is a value of a random
  function at a new point. So, given everything before, it is uniform on `[τ]^{q+1}`.
- Let `X_i` be the number of useful forgeries of the `i`-th completed run. Given the past, `X_i` is
  dominated by a binomial `Bin(q + 1, 1/τ)`.
- Step 2 says: `R` wins only if `Z_K := Σ_{i ≤ K}(X_i − q) ≥ 1` for the final `K ≥ 1`.

*Step 4: a supermartingale.* Let `θ = τ^{q+1}/2`. For `X ∼ Bin(q + 1, 1/τ)`,

    E[θ^{X − q}] = θ^{−q}·((τ − 1 + θ)/τ)^{q+1} ≤ 1          (Lean `rewind_supermartingale`).

- Paper proof: with `x = (τ − 1)/θ` the claim is `(1 + x)^{q+1} ≤ 2`. Now
  `(q + 1)·x = 2(q + 1)(τ − 1)/τ^{q+1} ≤ 1/2` for `τ ≥ 7` (Lean `four_mul_le_pow`), and
  `(1 + x)^{q+1}·(1 − (q+1)x) ≤ (1 + x)^{q+1}(1 − x)^{q+1} ≤ 1` by Bernoulli.
- `θ > 1`, so `θ^{X_i − q}` is monotone in `X_i`, and `M_j = θ^{Z_j}` is a non-negative
  supermartingale with `M_0 = 1`, however `R` schedules and chooses its runs.
- By Ville's inequality, `Pr[∃ j : M_j ≥ θ] ≤ 1/θ = 2·τ^{−(q+1)}`. ∎

Remarks.
- A reduction that keeps running `A**` and bets on every request wins with probability exactly
  `1/θ*`, with `θ*` the root `> 1` of `θ^q·τ^{q+1} = (τ − 1 + θ)^{q+1}` (the walk moves up by at
  most 1). For τ = 17: `θ* = 256` at `q = 1`, and `θ*/17^{q+1} → 1` quickly. So rewinding gains a
  factor `289/256 ≈ 1.13` at `q = 1` and less beyond. For `5 ≤ τ < 7` the
  bound `2·τ^{−(q+1)}` also holds (use `(1 + x)^n ≤ e^{nx}`).
- For `q = 0` there is no junk and guessing loses only τ ([UA] Prop. 8(a)).
- For `τ = 2`, `q = 1` the walk `Z` has zero drift and reaches 1 almost surely. A large τ matters.
- **Scope.** The theorem is about reductions that treat `(P, D)` as a black box. It says nothing
  about a reduction that uses the algebra of `P`. Lemma S does not help such a reduction here:
  it maps candidates to their classes, and the same lottery applies to classes.
- `A**` is not efficient. This is the usual form of a black-box lower bound: a reduction that
  works for all adversaries must work for it.

### 4.5 Rewinding helps against some adversaries

Theorem A4 does not say that rewinding is useless. It says that a reduction cannot tell `A**` from
an adversary it could exploit:

**Proposition A5 [proved].** Let `A` be an OMPR⊕τ(N, q) adversary such that
- every `D`-query of `A` is a shifted target `h_k ⊕ δ_{k,a}` of a request `k < N`, and
- `A` makes request `N` after all others and its output always contains a forgery for it.

Let `ε = Adv^{ompr⊕τ}(A)`, `C = τ(N − 1)` and `r = ⌈8τ(C + 1)/ε⌉`. Then there is `R`, running `A`
up to request `N` once and the rest `r` times, with `Adv^{ompr}(R; r, C) ≥ ε/3`.

*Proof.*
- `R` answers the requests `k < N` with uniform `h_k` of its own, and runs `A` until it has
  submitted the list of request `N`.
- It then runs the rest of `A` `r` times from this state (the `D` answers are a fixed function, so
  given the state the runs are independent). In run `i` it answers
  `h_N = t_i ⊕ δ_{N,c_i}` with a fresh challenge target `t_i` and a uniform `c_i`.
- It answers `D`-queries with its oracle. All of them lie in a fixed set of `≤ C` targets, so they
  cost `≤ C` calls over all runs.
- `h_N` is uniform and independent of `c_i`. So run `i` succeeds with a forgery for request `N` on
  shift `c_i` with probability `p/τ`, where `p` is the success probability given the state. Such a
  run gives a preimage of `t_i` for no call.
- `R` wins if `C + 1` runs do so. Conclude as in B4, with `E[p] = ε`. ∎

So the loss of the reduction depends on how the adversary's calls move when it is rewound. A
general proof would have to handle adversaries whose calls are fresh in every run, and A4 shows
that a relativizing reduction cannot.

### 4.6 Status of OMPR ⇒ OMPR⊕17, and obstacles

**Conjecture A6.** For UOV, the best attack on OMPR⊕τ(N, q) is the best attack on OMPR(τN, q):
choosing among τ shifted targets after seeing `h` does not help. Evidence: the generic bounds
coincide ([UA] Prop. 8(c)), Lemma A3, and the absence of a translation symmetry (A2).

**What a proof would need.**
1. *Not relativizing.* By A4, it must use the algebra of `P`, or the code of the adversary.
2. *Using the algebra.* The reduction must gain from a forgery for a shift it did not embed. For
   uniform shifts that is the UOV problem (A3). For chosen shifts it is the translated UOV
   problem, and a reduction that solves it does not need the adversary.
3. *Re-randomizing targets.* To make all τ candidates useful, the reduction needs challenge targets
   with prescribed differences `δ_a ⊕ δ_b`. OMPR targets are independent. The public symmetries
   of the target space are scalings (Lemma S), which do not produce prescribed differences.
4. *Knowing the shift in advance.* If the reduction can learn `a_k` before it fixes `h_k`, it
   embeds the right shift and loses nothing. This is what PomFRIT's first-phase extractor `E₁`
   does (`pomfrit.md` Lemma P), up to the event that the prover completes with another prefix.
   U1 is thus already the non-simple-embedding technique, with loss `Q₃·2^{−71}`, and
   [UA] Prop. 8(d) shows that this loss is optimal for it. An abstract OMPR⊕τ adversary offers
   nothing to extract.

**What a separation would need.** An attack on OMPR⊕τ for UOV that fails for OMPR: a way to use
the choice among τ targets with fixed differences. We found none. A meta-reduction in the style
of [BMV08] is not available: it needs to simulate `A**`'s forgeries, and preimages are not unique.

**Follow-up: `ompr-shift-algebra.md`.**
- Theorem R there extends A4 to UOV itself: a reduction that is black-box in the adversary only,
  with any use of `pk`, wins against `A**` (with forgeries `D(z)`) with probability
  `≤ 2·τ^{−(q+1)} + Adv^{free}_{UOV}(M) + V⁴·2^{−343}`. So item 2 above is closed for this class
  unless OMPR^free (§3.1) fails.
- Its §3 goes through the algebra (symmetries, polar form, kernel and oil translations, spans of
  preimages): no combiner. An affine symmetry never translates targets (Lean `affine_symmetry`).
- Its §4: collinear shifts `λ_a·c` remove one of the 45 equations. That is a gain of `≈ 2^{3.7}`
  for `τ ≥ 256` and none for τ = 17 (`256/17 = 2^{3.9}`). The conjecture is to be read for
  `τ ≤ 17`.

**Advice, unchanged from [UA] §6.** Keep U1 as the main statement and U2 under the explicitly
stronger OMPR⊕17. The protocol change [UA] §8 C2 removes the question.

## 5. Effect on the other notes

- `moussaka.md` §3.3: CT-UF is false as stated (B1). Theorem 1 must be read with CT-UF^open, as
  [UA] T4 already recommended. No protocol change: the issuance proof forces an opening of every
  signed target.
- [UA] §3 item 10, §5.4, §5.7, §6(b), §9: pointers to this note.
- `pomfrit.md` G1: still open; A4 extends the optimality of the guessing loss from
  simple-embedding to all relativizing reductions.

## 6. Lean

| Statement | Lean | File |
|---|---|---|
| `P(c·σ) = c²·P(σ)`, any sizes; for pqov's map | `publicMap_scale`, `qmap_smul` | `Spec/PqovScale.lean` |
| `(μ^{128})² = μ` in `GF(256)` | `sq_pow_128` | `Spec/PqovScale.lean` |
| A preimage of `μ·t` gives one of `t`; `μ·t ≠ t` | `scaled_preimage`, `scaled_target_ne` | `Spec/PqovScale.lean` |
| The one-query CT-UF attack (B1), for any correct oracle | `ctuf_scaling_attack` | `Spec/PqovScale.lean` |
| Combiner forest: `|Ch| + |Eset| ≤ |Dset|` (B3) | `combiner_count` | `Protocols/UOVAssumptions.lean` |
| `c + 1 + Kq ≤ c + w ⟹ Kq + 1 ≤ w` (A4, step 2) | `lottery_count` | `Protocols/UOVAssumptions.lean` |
| `4n(τ − 1) ≤ τ^n` for `τ ≥ 7`, `n ≥ 2` | `four_mul_le_pow` | `Protocols/UOVAssumptions.lean` |
| `((τ − 1 + θ)/τ)^{q+1} ≤ θ^q`, `θ = τ^{q+1}/2` (A4, step 4) | `rewind_supermartingale` | `Protocols/UOVAssumptions.lean` |
| OMPR^free (§3.1), targets on demand, single-forgery form | `advOMPRFree`, `FreeWin` | `Assumptions/TheoremR.lean` |
| A4, step 3 for one run: `Σ_a θ^{X(a)} ≤ (τ − 1 + θ)^{q+1}`; Ville's inequality for a stateful handler | `lottery_sum`, `potential_le` | `Assumptions/TheoremR.lean` |
| A1, on the games `advOMPR`, `advOMPRShift`; and [UA] P8(a), `Adv^{ompr⊕τ} ≤ τ^{q+1}·Adv^{ompr}` | `advOMPR_le_shift`, `advOMPRShift_mono`, `advOMPRShift_le_guess` | `Assumptions/Shift.lean` |

On paper only (except A1 and the guessing bound): the games, the lazy-sampling arguments, the
bad-event bounds, Ville's inequality in the generic model of A4, the Chernoff steps of B4 and A5,
and the ideal-permutation bookkeeping of B2. The variant of A4 for UOV itself (Theorem R of
`ompr-shift-algebra.md` §2) is mechanized with its games (`thmR`), up to its bad-event term. The goodness part of Lemma S (item 3) is on paper; it is not used by B1.

## 7. Open

- OMPR ⇒ OMPR⊕17 for UOV (Conjecture A6), by a proof that is not relativizing. By
  `ompr-shift-algebra.md` Theorem R it must also be non-black-box in the adversary, or break
  OMPR^free.
- OMPR^free for UOV: is there a combiner across classes? Cryptanalysis of §3.5, item 3.
- The translation problem for a fixed `Δ` versus the UOV problem (§4.3).
- A4 for `τ < 5` (other constants), and for a PSF that has the scaling symmetry built in.
- Other public pairs `(φ, T)` with `P ∘ φ = T ∘ P` (§4.2): we know only the scalings and did not
  prove that there are no others.
