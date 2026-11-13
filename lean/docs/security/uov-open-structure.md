# Two open questions on the UOV assumptions: meta-reductions and GPI

This note takes up two items of `uov-assumptions.md` §9 (cited below as [UA]):

- **Part A.** Turn the meta-reduction sketch of [UA] §5.7 (Proposition 7) into theorems with a
  precise proviso.
- **Part B.** Cryptanalysis of GPI, the good-preimage indistinguishability assumption of [UA] §3
  item 3.

Notation is that of [UA] §1: `F = GF(256)`, `(N, M, V) = (119, 45, 74)`, public map `P`, oil space
`𝒪`, `L_v`, `Good`, `Bad`, `δ`, the sampler `D = D_sk` (`derive_preimage`), its ideal version `D*`.
`J(s)` is the `M × N` matrix of the differential `DP_s = P'(s, ·)`; `K_s = ker J(s)`.

**Status labels.** *Proved*: a complete paper proof is given here. *Heuristic*: proved up to a
stated genericity hypothesis, which was checked on toy parameters. *Estimate*: a cost figure from
a standard model. *Conjecture*: no proof; the basis is stated. Nothing here is mechanized in Lean.
The literature was not re-retrieved in this session; citations are from memory and the reference
list says where the recollection is less certain.

Scripts (pure Python, no dependencies): `scripts/uov-open-structure/mq_estimates.py` (cost
figures of §B.5) and `scripts/uov-open-structure/bad_oracle_toy.py` (§B.1, §B.3 on toy
parameters).

## 0. Summary

**Part A (meta-reductions).** A1 and A2 are for *key-preserving* black-box reductions: every run
of the adversary is on the public key of the reduction's own instance. A3 needs no such
restriction, but allows only one run.

| # | Statement | Status |
|---|---|---|
| A1 | No key-preserving reduction from the UOV problem or OW to **OMPR** or **CT-UF** (chosen targets), with any amount of rewinding: `ε_R ≤ k·Adv^{uov}(M₁) + Adv^{uov}(M₂)`, `k` the number of adversary runs. The same from det-FDH or spec EUF/SUF-CMA: OMPR is not key-preservingly reducible to any hash-target assumption. Uses only that the oracle must be answered at a target the reduction did not choose. Determinism plays no role | proved |
| A2 | No key-preserving *fully* black-box reduction (one that must also serve unbounded adversaries) from UOV/OW to **any** of OMPR, A-OMPI, CT-UF, CT-UF^open, with rewinding: `ε_R ≤ Adv^{uov}(M_⊥) + k·Adv^{dpred}`, and `Adv^{dpred} ≤ q_v·2^{−256} + 2^{−258} + κ` in the ROM. Uses determinism of `D`: its answers are unique given `pk`, unpredictable, and checkable by an unbounded adversary | proved; `κ` (two seeds with one key) is heuristic |
| A3 | For A-OMPI (and OMPR with `n = q + 1`), single-run reductions lose at least `q_T`: `ε_R ≤ 1/q_T + Adv^{uov}(M) + Δ_R`, where `Δ_R` is the reduction's sensitivity to *which* valid preimage it is given; `Δ_R = 0` for reductions that only use validity. [UA] T2's loss `q_T` is optimal in this class | proved |
| A4 | What is not covered: reductions that change the key (A1, A2); rewinding and `Δ_R ≠ 0` reductions in A3 (the proviso is real, a preimage is one of `≈ 2^{592}`); reductions that use a second assumption (GPI) and so need not serve unbounded adversaries | obstacles stated |

Reading: the reason OMPR does not reduce to UOV is the *chosen-target* oracle (A1), not anything
subtle. For index-only games, reductions to UOV **plus GPI** exist ([UA] T2, T4), their loss
`q_T` is optimal (A3), and GPI cannot be dropped by a fully black-box reduction (A2).

**Part B (GPI).**

| # | Statement | Status |
|---|---|---|
| B1 | `Adv^{gpi}(A; q) = (1 − (1−δ)^q)·|Pr[A = 1 ∣ some sample bad] − Pr[A = 1 ∣ all good]|`. GPI is average-case detection of bad points from `pk`; the samples carry no other information | proved |
| B2 | `Bad` is the zero set of `f(s) = det(J(s)·O′)`, a form of degree 45, invariant under `𝒪`; `f = Σ_T c_T·det J(s)_T` with `c` the Plücker vector of `𝒪` (`≈ 2^{110}` unknowns). `rank J(s) < 45` is a public certificate of badness, of density `≈ 2^{−592}` | proved (density heuristic) |
| B3 | Key recovery ⇒ GPI break (`Adv = 1 − (1−δ)^q`). Conversely an exact badness oracle, or a *certifying* (no false positives) detector that catches ≥ 30% of the bad points, gives the oil space with `≈ 2^{36}` calls and `≈ 2^{54}` field operations. A witness-finding detector gives it with one call | first: proved; second: heuristic (two genericity hypotheses, verified on toy parameters); third: by [Péb24a] |
| B4 | Kipnis–Shamir, reconciliation, intersection and rectangular MinRank give no badness test cheaper than key recovery. Dedicated systems ("an oil vector in `K_s`") are underdetermined for one sample, and cost `≥ 2^{262}` bit operations when completed to a determined system | estimate |
| B5 | Conjecture: for uov-Ip `(119, 45, 256)`, GPI has the security of key recovery, `≈ 2^{194}` multiplications (`2^{201}` bit operations) by our intersection-attack estimate, above the direct forgery attack (`≈ 2^{151}`) | conjecture |
| B6 | GPI is not implied by public-key indistinguishability in any way we can see: the reduction cannot sample `Good`. Exact relation: `Adv^{gpi} ≤ Adv^{jpr} + Adv^{pkind}`, `Adv^{jpr} ≤ Adv^{gpi} + Adv^{pkind}` for the joint assumption JPR | proved (trivial) |
| B7 | Open: two-sided, low-advantage distinguishers; quantum attacks | — |

---

# Part A. Meta-reductions

## A.1 Model

- **Base problem** `Π`: the UOV problem or OW ([UA] §3 items 1, 2). An instance is `(pk, t)`.
  Where stated, also det-FDH or spec EUF/SUF-CMA, in which the reduction has the game's signing
  oracle and random oracle.
- **Game** `G`: OMPR(n, q), A-OMPI(q_T, Q), CT-UF, CT-UF^open ([UA] §3 items 7, 9, 10, 11), `K = 1`.
- **Reduction.** A probabilistic oracle machine `R`. On an instance of `Π` it may start up to `k`
  runs of an adversary for `G`, playing `G`'s challenger in each: it supplies a public key and
  the targets, and answers the oracle queries. It may interleave and rewind the runs at will. It
  outputs a candidate solution. `T_R` is its running time, `q_v` the number of its SHAKE256
  queries. SHAKE256 (inside `KeyGen` and `D`) is a random oracle that every party can query and
  nobody programs.
- **Adversaries** are deterministic machines with a random function hard-wired (written `f`,
  `h`); their answers are functions of what they were given. So rewinding an adversary and
  repeating its input repeats its behaviour. They may be computationally unbounded.
- **Key-preserving**: in every run, `R` supplies the `pk` of its own instance. This is the
  "parameter-invariant" class of [BMV08]; see §A.5 for what lies outside.
- `ε_R(A) = Pr[R^A(pk, t) solves Π]`, over the key, `t`, the coins of `R`, and `A`'s random
  functions. A reduction is useful only if `ε_R(A)` is noticeable for every `A` that wins `G`
  with probability close to 1. A *meta-reduction* is an efficient machine that solves `Π` by
  running `R` and playing `A` itself.

## A.2 Theorem A1: chosen-target oracles

**Adversary `A₁ = A_{f,h}`** for OMPR(n, q), `q ≥ 1`, `n ≥ q + 1`. On input `(pk, t_1..t_n)`:
1. `u := f(pk, t_1..t_n)`, a uniform element of `F^M`. Query `D(u)`; let the answer be `s`.
2. If `P(s) ≠ u`, stop and output `⊥`.
3. For `i ≤ q + 1` let `s_i := h(pk, t_i)`, a uniform preimage of `t_i` (found by exhaustive
   search; `⊥` if none). Output `(s_i, i)_{i ≤ q+1}`.

`A₁` makes one query. Against the real oracle it wins whenever `G_sk ≠ ∅` (then every target has
a preimage, [UA] Lemma C). Only step 3 is inefficient.

**Theorem A1.** Let `R` be a key-preserving reduction from the UOV problem to OMPR(n, q) with at
most `k` adversary runs. There are machines `M₁`, `M₂`, each running `R` once plus `k`
evaluations of `P`, with

    ε_R(A₁) ≤ k·Adv^{uov}(M₁) + Adv^{uov}(M₂).

So one of them solves the UOV problem with probability `≥ ε_R(A₁)/(k + 1)`.

*Proof.* Let `E` be the event that, in the execution of `R^{A₁}`, some run of `A₁` receives a
valid answer in step 2. Until the first time this happens every run of `A₁` consists of one
uniform query followed by `⊥`.

- `M₂(pk, t)` runs `R(pk, t)` and plays each adversary run as: query a fresh uniform `u` (the same
  `u` for a repeated input), then output `⊥`. Outside `E` this is exactly `R^{A₁}`. So
  `Pr[R^{A₁} solves ∧ ¬E] ≤ Adv^{uov}(M₂)`.
- `M₁(pk, t*)` draws `t₀ ← U(F^M)` and `j ← U([k])`, runs `R(pk, t₀)`, and plays the adversary as
  `M₂` does, except that the query for the `j`-th *distinct* adversary input is `t*`. If `R`
  answers that query with `s` and `P(s) = t*`, it outputs `s`. It gives up if any other query is
  answered validly first.
  - `t*` is uniform and independent of everything else, as `f`'s value is. So up to the first
    valid answer the view of `R` is as in `R^{A₁}`, and independent of `j`.
  - Under `E`, the first valid answer belongs to one of at most `k` distinct inputs. It is the
    `j`-th with probability `1/k`. Hence `Adv^{uov}(M₁) ≥ Pr[E]/k`.
- `ε_R(A₁) ≤ Pr[E] + Pr[solves ∧ ¬E]`. ∎

**Variants** (same proof).
- **OW.** Let `f` output `P(r)` for uniform `r ∈ F^N` instead of a uniform target. `M₁` embeds its
  OW challenge there, and gives `R` an instance `(pk, P(r₀))` of its own.
- **CT-UF.** `A₁` queries `Sign(u)`, then outputs a brute-forced forgery on a fresh `Com(x*)`.
- **From hash-target assumptions.** Let the base problem be det-FDH EUF-CMA ([UA] §3 item 6). `R`
  now has the game's `H` and `Sign` oracles (`q_H`, `q_S` queries). `M₁` picks `m* ← {0,1}^{256}`
  and uses `u := H(m*)`; `M₁`, `M₂` forward `R`'s oracle queries. `R` asks `H` or `Sign` at `m*`
  with probability `≤ (q_H + q_S)·2^{−256}`. Otherwise `(m*, s)` is a forgery. So

      ε_R(A₁) ≤ k·(Adv^{euf}_{det}(M₁) + (q_H + q_S)·2^{−256}) + Adv^{euf}_{det}(M₂).

  The same holds from A-OMPI (equivalent to det-FDH, [UA] T1) and from spec EUF/SUF-CMA (use
  `u := H(m* ‖ salt*)`). This makes [UA] §5.1's remark "what OMPR adds is the chosen-target
  oracle" a theorem for key-preserving reductions.

**What A1 uses.** Only that `G`'s oracle must be answered at a point the reduction did not choose,
and that a valid answer there is by itself a solution of the base problem. It uses no property of
UOV preimage sampling: not determinism, not the law of `D`, not uniqueness. It does not apply to
A-OMPI, to OMPR adversaries that only query listed targets, or to CT-UF^open when the reduction
programs Com: there the reduction chooses every target that is queried, and can know preimages.
For those games, reductions to UOV *plus GPI* exist, with loss `q_T` ([UA] T2, T4).

**Remark (list-only OMPR).** If all queries are on listed targets, then at least one of the `q + 1`
output indices was never queried. Guessing it costs `n`. So list-only OMPR(n, q) follows from GPI
and the UOV problem with loss `n`, exactly as in [UA] T2. The [BMV08]-style sketch of [UA] §5.7,
whose adversary queries a subset of the listed targets, therefore cannot give a separation from
UOV; it gives the tightness bound A3. The separation comes from off-list queries.

## A.3 Theorem A2: unique oracle answers (uses determinism)

`D_sk` is a function, and `sk` is a function of the 32-byte seed. Call a seed `σ` *consistent with
`pk`* if `KeyGen(σ)` has public key `pk`. Let `κ = Pr[some seed other than the real one is
consistent with pk]`.
- `κ` is negligible heuristically: SHAKE256 outputs `pk_seed ‖ O` do not collide, and two oil
  matrices giving the same `P3` for the same `(P1, P2)` would be two oil spaces of one key. We do
  not prove a bound.

**The D-prediction problem.** `Adv^{dpred}(B) = Pr[B(pk) = (y, s) with s = D_σ(y) for a seed σ
consistent with pk]`.

**Lemma A2.1.** In the model of [UA] §1 (SHAKE256 a random oracle, key-average bound on `δ`), for
`B` with `q_v` SHAKE256 queries, `Adv^{dpred}(B) ≤ q_v·2^{−256} + 2^{−258} + κ`.

*Proof.* Outside `κ` only the real seed counts. By [UA] Lemma D, up to `q_v·2^{−256} + E[δ^{255}]`
the value `D(y)` is uniform on `S^G_y`, which has `|G_sk| = (1 − δ)·256^{74}` elements, and is
independent of `B`'s view. So `B` hits it with probability `≤ 2·256^{−74}` if `δ ≤ 1/2`. By
[UA] §1, `Pr[δ > 1/2] ≤ 2^{37}·E[δ^{37}] ≤ 2^{37}·(255^{−37} + 256^{−37}/255) ≤ 2^{−258.7}`, and
`E[δ^{255}] ≤ 2^{−295}`. ∎

**Adversary `A₂`** (for A-OMPI(Q + 1, Q); unbounded, also in its SHAKE256 queries).
1. Find all seeds consistent with `pk`. Request `Q + 1` targets `y_1..y_{Q+1}`.
2. For `i = 1..Q`: query index `i`; if the answer is not `D_σ(y_i)` for some consistent `σ`, stop
   and output `⊥`.
3. Output `(Q + 1, D_σ(y_{Q+1}))` for the first consistent `σ`.

Against the real oracle `A₂` never stops in step 2, and wins unless `D_σ` fails. The same
adversary works for the other games: for OMPR it uses listed targets only; for CT-UF and
CT-UF^open it uses targets `Com(x_i)` and opens them.

**Theorem A2.** Let `R` be a key-preserving reduction from the UOV problem (or OW) to any of the
four games, with at most `k` adversary runs, rewinding allowed. Then

    ε_R(A₂) ≤ Adv^{uov}(M_⊥) + k·Adv^{dpred}(M_p) ≤ Adv^{uov}(M_⊥) + k·(q_v·2^{−256} + 2^{−258} + κ).

`M_⊥` and `M_p` run `R` once and do nothing else.

*Proof.* Let `C` be the event that in some run the *first* answer of `R` passes the check of
step 2.
- Outside `C`, every run of `A₂` is: request targets, query index 1, output `⊥`. `M_⊥` runs `R`
  and plays that. So `Pr[solves ∧ ¬C] ≤ Adv^{uov}(M_⊥)`.
- `M_p` plays the same, picks one of the at most `k` distinct first answers at random and outputs
  it with its target. Up to the first passing answer its simulation is exact. So
  `Adv^{dpred}(M_p) ≥ Pr[C]/k`. ∎

**What A2 uses, and what it means.**
- It uses three properties of the sampler: `D` is *deterministic*; its value is *determined by
  `pk`* (up to `κ`); and it is *unpredictable* without the seed. Together they make `D` a
  unique-answer oracle, the analogue of unique signatures in [Cor02, KK12, BJLS16]. The
  difference is that uniqueness is not publicly checkable here. Only an unbounded adversary can
  check it, so the meta-reduction does not need to rewind; it only needs to notice that the
  reduction cannot produce the unique answer.
- So determinism does change the picture, contrary to the wording of [UA] P7: it makes a
  separation *easier*. With a randomized sampler every good preimage is a possible answer and
  `A₂` is not available. (An unbounded adversary could still test that all answers are *good*;
  a reduction then has to avoid `Bad` in every answer, which is [UA] Prop. 4.1.)
- A2 is a statement about *fully* black-box reductions in the sense of [RTV04], which must work
  for every adversary, efficient or not. It says nothing about a proof whose simulation is only
  computationally faithful. [UA] T2 is such a proof: its simulated answers are uniform preimages,
  not `D`-values, `A₂` aborts on them, and the proof pays for that with the GPI term. A2 shows
  that some such term is unavoidable: **no fully black-box key-preserving proof of any of these
  games from the UOV problem alone exists, unless the UOV problem is easy.**
- `A₂` is useless as an attack. It is not a GPI distinguisher: in [UA] T2's hop it aborts in both
  worlds.

## A.4 Theorem A3: the loss `q_T` is optimal for index-only games

This is the rewinding meta-reduction sketched in [UA] §5.7, in the form of [Cor02]. The adversary
is the "natural" one: it checks only validity and returns a fresh preimage.

**Adversary `A₃ = A_{f,h}`** for A-OMPI(Q + 1, Q).
1. Request `Q + 1` targets `y_1..y_{Q+1}`. Let `i* := f(pk, y_1..y_{Q+1})`, uniform in `[Q + 1]`.
2. Query the indices `i ≠ i*` in increasing order. Stop with `⊥` at the first answer `s_i` with
   `P(s_i) ≠ y_i`.
3. Output `(i*, h(pk, y_{i*}))`, with `h(pk, y)` uniform on the preimages of `y` under `pk`
   (`⊥` if there are none).

**Class.** `R` is *simple*: one adversary run, no rewinding. It need not be key-preserving; `pk`
above is whatever key `R` supplies, and `A₃` and the proof never use its structure. Write `ω` for the
instance and all coins of `R`. Then `R`'s targets are a function of `ω`, and its answers a
function of `ω` and `i*`. Let `𝒢(ω) = {i : in the run with i* = i all Q answers are valid}`.
For `i ∈ 𝒢(ω)` with `|𝒢(ω)| ≥ 2`, let `s′(ω, i)` be the answer `R` gives to the query `i` in the
run with `i* = i′`, for the least `i′ ≠ i` for which that answer exists and is valid.

**Forgery sensitivity.** With `E₃ = {i* ∈ 𝒢(ω), |𝒢(ω)| ≥ 2}`,

    Δ_R = Pr[R solves when given (i*, h(pk, y_{i*})) ∧ E₃] − Pr[R solves when given (i*, s′(ω, i*)) ∧ E₃].

`R` is *forgery-agnostic* if its success depends on the forgery only through its validity; then
`Δ_R = 0`. Every reduction that embeds its instance in a target and outputs (a known function of)
the forgery is forgery-agnostic, e.g. the one of [UA] T2.

**Theorem A3.** For every simple `R` from the UOV problem (or OW) to A-OMPI(Q + 1, Q) there is `M`
with running time `≤ (Q + 1)·T_R` and

    ε_R(A₃) ≤ Adv^{uov}(M) + 1/(Q + 1) + Δ_R.

*Proof.* `M(pk, t)` runs `R(pk, t)` with coins of its choice, draws `i*` uniformly, and plays `A₃`.
- If some answer is invalid, it outputs `⊥` as `A₃` does, and returns `R`'s output. Exact.
- Otherwise `i* ∈ 𝒢(ω)`. For each `i′ ≠ i*` in increasing order, `M` rewinds `R` to the point
  after the targets and plays `A₃` with missing index `i′`, until the query `i*` is answered or an
  answer is invalid. If the answer to `i*` is valid, it is `s′(ω, i*)`; `M` resumes the main run
  with the forgery `(i*, s′)` and returns `R`'s output.
- `M` finds no `s′` only if no `i′ ≠ i*` is in `𝒢(ω)`, since a run with `i′ ∈ 𝒢(ω)` answers the
  query `i*` validly. `i*` is uniform and independent of `ω`, so
  `Pr[i* ∈ 𝒢(ω) ∧ |𝒢(ω)| = 1] ≤ 1/(Q + 1)`.
- On `E₃` the run of `R` inside `M` differs from `R^{A₃}` only in the forgery. That is `Δ_R`. ∎

**Consequences.**
- For forgery-agnostic simple reductions, `ε_R ≤ 1/q_T + Adv^{uov}(M)` with `q_T = Q + 1`: they
  lose at least `q_T`. The reduction of [UA] T2 succeeds against `A₃` with probability
  `≈ 1/q_T` (its uniform answers pass a validity check), so the bound is attained. **T2's factor
  `q_T` is optimal in this class.** We expect the same for T4's `q_f + q_S + 1` (CT-UF^open with a
  programmed Com), but did not write that out.
- By [UA] T1(c), an A-OMPI adversary is an OMPR adversary, so A3 holds for OMPR with `n = q + 1`
  as well.
- **The proviso is `Δ_R`, and it is real for UOV.** A target has about `2^{592}` preimages. `s′` is one that `R` could compute itself; `h(pk, y)` is one that it could not. If
  `R` knows a preimage `s_i` of each of its targets, the forgery gives it a *collision*
  `P(s_i) = P(h(pk, y_i))`, and nothing known says that collisions of `P` do not help to invert
  `P` elsewhere (this is the multicollision point of [BBBMR26] App. A). For one-more problems
  with unique preimages (RSA, DL) `Δ_R = 0` always, which is why [BMV08] needs no such proviso.
- `1/(Q + 1)` cannot be improved in this class, by T2. So for index-only games a full separation
  is not available by this route; A2 gives one, for fully black-box reductions.

## A.5 What is not covered

- **Reductions that change the key.** `R` may run the adversary on `pk′ ≠ pk`.
  - If `R` knows a trapdoor for `pk′`, it answers every query honestly and learns nothing it
    could not compute. To be useful, `pk′` must be related to `pk`.
  - The known relation is isomorphism, `pk′ = U ∘ P ∘ T` with `U`, `T` linear and invertible. A1
    extends to reductions that *output* `(U, T)` with each key (the analogue of algebraic
    reductions, [PV05]): `M₁` asks for a preimage of `U(t*)` under `pk′` and maps the answer `s`
    to `T(s)`. Without `(U, T)` the meta-reduction would have to find the isomorphism itself. A2
    does not extend: `pk′` has no seed, so `A₂` is not defined on it.
  - A3 is not affected: it holds for every single-run reduction.
  - No other self-reducibility of UOV keys or targets is known. In particular there is no random
    self-reduction of targets under one key, which is why A1 loses the factor `k`.
- **Rewinding in A3.** A3 is for one run. A1 and A2 allow rewinding.
- **Reductions with a second assumption.** [UA] T2–T5 are of this kind (GPI). They are consistent
  with A1 (their games are index-only) and with A2 (they are not fully black-box to UOV alone),
  and A3 bounds their loss.
- **Non-black-box reductions.** As for every meta-reduction result.

So [UA] P7 becomes: OMPR and CT-UF are separated from the UOV problem, OW, and all EUF/SUF-CMA
notions for key-preserving reductions (A1). OMPR should remain an assumption of its own.

---

# Part B. GPI

## B.1 What GPI asks

**Lemma B1 (proved).** For every `A` and `q`,

    Adv^{gpi}(A; q) = (1 − (1 − δ)^q)·| Pr[A = 1 ∣ s ← U(F^N)^q, some s_i bad] − Pr[A = 1 ∣ s ← U(Good)^q] |.

*Proof.* `U(F^N)^q` conditioned on "all good" is `U(Good)^q`, and that event has probability
`(1 − δ)^q`. ∎

- So `Adv^{gpi}(q) ≤ 1 − (1 − δ)^q ≤ qδ`; for `q = 1` it is at most `δ ≈ 2^{−8}`.
- Uniform points can be generated by anyone. The samples are therefore only test inputs. **GPI is
  the problem of noticing a bad point among random points, given `pk`.** Many samples do not help
  beyond providing more test inputs: no two share a vinegar part (probability `q²·256^{−74}`), and
  they lie on no common low-dimensional space.
- The `Good` world is the law of real signatures: `(y, D(y))` for uniform `y` is a uniform good
  point ([UA] Corollary §2). So GPI says that signatures of the vinegar-retry signer on random
  targets look uniform. Every EUF-CMA argument for that signer needs this in some form; [SSH11]
  pointed out the non-uniformity and avoided it by changing the signer.

**Lemma B2 (proved; structure of `Bad`).** Let `O′` be the `N × M` matrix whose columns are a basis
of `𝒪`.
1. `L_{vin(s)} = J(s)·O′` up to the choice of basis. So `s` is bad iff `f(s) := det(J(s)·O′) = 0`,
   iff `K_s ∩ 𝒪 ≠ 0`.
2. `f` is a form of degree `M = 45` with `f(s + o) = f(s)` for `o ∈ 𝒪` and `f(λs) = λ^{45}f(s)`.
   So `Bad + 𝒪 = Bad`, and the derivative of `f` along every oil direction is zero:
   `∇f(s) ∈ 𝒪^⊥` for all `s`.
3. (Cauchy–Binet) `f(s) = Σ_{T ⊂ [N], |T| = M} c_T·det J(s)_T`, where `J(s)_T` is the `M × M`
   submatrix on columns `T` and `c_T = det O′_T` are the Plücker coordinates of `𝒪`.
4. `Bad = ⋃_{o ∈ 𝒪∖0} ker J(o)`: `s` is bad iff `J(o)s = 0` for some oil vector `o`.
5. If `rank J(s) < M` then `s` is bad.

*Proof.* (1) The `j`-th column of `J(s)·O′` is `P'(s, o_j)`, and `P'(s, o) = P'((v, 0), o)` because
the polar form vanishes on `𝒪 × 𝒪`; this is the definition of `L_v`. (2) follows, with degree `M`
because `J` is linear in `s`. (3) is Cauchy–Binet. (4) `J(s)o = P'(s, o) = J(o)s`. (5)
`rank(J(s)·O′) ≤ rank J(s)`. ∎

- The toy script checks (1) from the public polar matrices on 4000 points per key.
- (3) shows the shape of the problem. The minors `det J(s)_T` are public. `Bad` is the kernel of a
  *hidden linear functional* on them, in a space of dimension up to `binom(119, 45) ≈ 2^{110}`.
  Good samples give inequations `f(s_i) ≠ 0`, which linearization cannot use.
- (5) is a public, efficiently checkable certificate, so `Adv^{gpi}` is not zero. Since
  `J(s)s = 2P(s) = 0`, `J(s)` acts on a space of dimension 118; for a random `45 × 118` matrix
  rank loss has probability `≈ 256^{−74} = 2^{−592}` (heuristic).

## B.2 Key recovery breaks GPI (proved)

Given `𝒪`, badness is a rank computation. So a key-recovery algorithm with success `p` gives
`Adv^{gpi}(q) ≥ p·(1 − (1 − δ)^q)`, e.g. `0.63·p` at `q = 256`. One oil vector is enough, since it
gives `𝒪` in polynomial time [Péb24a] (argument as we recall it: `𝒪 ⊂ ker J(o)`, which has
dimension 74, and there `𝒪` is an oil space of dimension `45 > 74/2`, the regime that
Kipnis–Shamir breaks in polynomial time [KS98]).

## B.3 Deciding badness reliably is as hard as key recovery (heuristic)

**Proposition B3.** Let `B` be an oracle for the indicator of `Bad`. There is an algorithm that
outputs `𝒪` with about `V·⌈(N−1)/2⌉·q³ ≈ 2^{36.1}` calls to `B` and about `2^{54}` field
operations, under the hypotheses (H1), (H2) below. It does not use `pk`.

*Algorithm.*
1. Pick `s₀ ∈ F^N` and standard basis vectors `e_a, e_b, e_c`. Query `B` on the `q³ = 2^{24}`
   points of `A = s₀ + ⟨e_a, e_b, e_c⟩`. About `2^{16}` are bad.
2. Solve the linear system "`g` vanishes on the bad points of `A`" for a polynomial `g` of degree
   `≤ 45` in three variables (`binom(48, 3) = 17296` coefficients).
   **(H1)** The solution space is spanned by `f|_A`.
3. The coefficients of the linear monomials of `g` are `c·∂_a f(s₀), c·∂_b f(s₀), c·∂_c f(s₀)`
   for an unknown `c ≠ 0`. Repeat with the same `s₀` and `e_a` and the remaining directions, two
   at a time (59 spaces in all), and divide by the `e_a`-coefficient. This gives `∇f(s₀)` up to a
   scalar.
4. Repeat for further base points until the gradients span a space of dimension `V = 74`.
   **(H2)** The gradients of `f` span `𝒪^⊥`. Output their common kernel.

*Proof of correctness given (H1), (H2).* `f|_A` has degree `≤ 45 < q`, so it is among the
solutions of step 2 and its coefficients are those of the Taylor expansion at `s₀`. By Lemma
B2(2) every gradient lies in `𝒪^⊥`, which has dimension 74. ∎

*Status of the hypotheses.*
- (H1) is a counting heuristic: `≈ 65536` conditions on 17296 unknowns. We cannot prove it at
  these sizes (Bézout and Lang–Weil bounds are too weak for degree 45 over `F_256`).
- (H2) fails only if `f` does not depend on all vinegar directions.
- `bad_oracle_toy.py` runs the algorithm over `F_16` for `(N, M) = (8, 3), (11, 4), (12, 5)`. It
  recovered the oil space in every run, with `5`–`9` base points for `V = 5..7`.

**Certifying detectors.** The algorithm only uses points flagged as bad. So it works with a
detector that never flags a good point and flags each bad point with probability `a`, if
`a·2^{16}` exceeds 17296 (`a ≥ 0.3`; smaller `a` with 4-dimensional spaces, `2^{32}` calls each),
and if (H1) holds for the flagged points. The script confirms this for `a = 1/2`. Such a detector
has `Adv^{gpi}(q) = a·(1 − (1−δ)^q)`.

**Witness-finding detectors.** A detector that outputs an oil vector in `K_s` for a bad `s` gives
the key from one success (§B.2).

**What this does and does not show.**
- Any attack on GPI that works by *certifying* badness (finding a witness, or any other
  certificate that is never wrong and covers a constant fraction of `Bad`) is a key-recovery
  attack, with overhead `≤ 2^{36}` calls. All algebraic attacks we know are of this kind.
- It does not cover distinguishers with false positives. A false-positive rate above `≈ 2^{−36}`
  per point puts wrong equations into step 2. Resampling subsets of the flagged points should
  tolerate rates up to `≈ 2^{−22}`; we did not test this. A distinguisher with a small two-sided
  advantage is outside the reduction: `Bad` has no known random self-reduction (only
  `s ↦ λs` and translation by the unknown `𝒪`), so a weak average-case detector cannot be
  amplified at a given point. This is the main gap (§B.7).

## B.4 Known structural attacks as badness tests

For a bad `s`, the witness is an oil vector `o ∈ K_s`, unique up to scalars except with conditional
probability `≈ q^{−3}`.

- **Reconciliation [DYCCC08]: find `o ∈ K_s` with `P(o) = 0`.** This is 45 quadrics on a space of
  dimension 74. It is underdetermined: for *every* `s` the solutions form a cone of dimension
  `≥ 29`. A solution says nothing unless it is an oil vector, and the oil line adds `q` points to
  about `q^{29}`. The same excess `V − M = 29` is why reconciliation does not find oil vectors of
  uov-Ip in the first place [Beu21].
  - We looked for a local property that singles out the oil point on the cone and found none.
    The differential of `P|_{K_s}` at any point `c` of the cone kills `c` and `s` (as
    `J(c)s = J(s)c = 0`, `J(c)c = 0`), and nothing more at the oil point, because
    `K_s ∩ 𝒪` is only a line.
- **Kipnis–Shamir [KS98, KPG99].** It finds `𝒪` as an invariant subspace, with probability
  `q^{−(N−2M)} = 2^{−232}` per trial. Knowing `s` does not change the trial.
- **Intersection attack [Beu21].** It finds `x ∈ M_1𝒪 ∩ M_2𝒪` (`M_i` the polar matrices), a space
  of dimension `3M − N = 16`, from `3M − 2 = 133` quadrics in `2N − 3M = 103` unknowns. It is the
  best key recovery we know for these parameters. A bad `s` adds the constraint `o ∈ K_s` on an
  oil vector, but its oil line is not in the 16-dimensional space the attack searches, so it
  costs new variables: system (b) below.
- **Rectangular MinRank [Beu21].** It needs `(M_1x | … | M_Mx)` to have low rank for `x` in a
  secret subspace. For UOV and `x ∈ 𝒪` the columns lie in `𝒪^⊥`, of dimension `74 ≥ 45`, so
  there is no rank defect. The analogous object for badness is `J(s)` itself: its rank does not
  drop at bad points (Lemma B2(5) is the only exception).
- **Singular points [Péb24b].** The points `x ∈ 𝒪` with `rank J(x) < M` are singular points of
  `{P = 0}`; they are the oil vectors with `M_a x = 0` for some `a ≠ 0`. Badness is the transposed
  condition `J(s)o = 0`. A bad `s` is not a singular point of anything public that we could find.
- **Dedicated determined systems.** Add further oil vectors until the system has more equations
  than unknowns (all pairs of oil vectors satisfy `P'(o, o′) = 0`):

  | System | unknowns | equations | cost (bit ops) |
  |---|---|---|---|
  | (a) `o ∈ K_s` | 73 | 45 | underdetermined, always solvable |
  | (b) `o ∈ K_s` and an intersection pair | 176 | 268 | `2^{262}` |
  | (c) three samples, `o_i ∈ K_{s_i}` (all three must be bad) | 219 | 270 | `2^{402}` |
  | (d) two bad samples and one free oil vector | 220 | 270 | `2^{403}` |
  | intersection attack (key recovery) | 103 | 133 | `2^{201}` |

  Two samples with one oil vector each give 146 unknowns and 135 equations, still
  underdetermined. (c) also needs a triple of bad samples (`≈ 2^{24}` triples to try).

So every route we know to a badness test goes through an oil vector, and the cheapest way to an oil
vector ignores `s`.

## B.5 Concrete estimates for uov-Ip `(N, M, q) = (119, 45, 256)`

Model (`mq_estimates.py`): hybrid XL with a Wiedemann solver, semi-regular systems,
`q^k·3·binom(n−k+D, D)²·binom(n−k+2, 2)` multiplications, `2·8² + 8 = 136` bit operations per
multiplication. The bilinear structure of the systems is ignored. For `(112, 44)` the script gives
`2^{165.7}` for the intersection attack, which matches the figure we remember from the round-1
UOV specification (`≈ 2^{166}`); we could not check the round-3 tables.

The first row applies no variable reduction. With Thomae–Wolf preprocessing (and the guesses of
Furue–Nakamura–Takagi), which the best forgery attack uses, the same model gives `2^{140.3}`
multiplications (`ompr-shift-algebra.md` §4.1, `scripts/ompr-shift-algebra/c1_experiments.py`),
and with the class attack of `ompr-cryptanalysis-2.md` §3.1 (44 homogeneous quadrics, then
scaling) `2^{138.5}`;
for `(112, 44)` it gives `2^{145.6}` bit operations, close to the direct-attack figure we
remember from the UOV specification. Use the third row as the forgery cost.

| Attack | Goal | multiplications | bit operations |
|---|---|---|---|
| direct, 45 equations in 45 unknowns (no variable-reduction trick) | forgery | `2^{144}` | `2^{151}` |
| direct, after Thomae–Wolf variable reduction (one equation removed; `ompr-shift-algebra.md` §4.1) | forgery | `2^{140.3}` | `2^{147.4}` |
| class attack P1 with Thomae–Wolf (`ompr-cryptanalysis-2.md` §3.1) | forgery | `2^{138.5}` | `2^{145.6}` |
| intersection | key | `2^{194}` | `2^{201}` |
| Kipnis–Shamir | key | `2^{253}` | `2^{260}` |
| best dedicated badness system (b) | GPI | `2^{255}` | `2^{262}` |
| rank certificate, Lemma B2(5) | GPI | advantage `≈ q·2^{−592}` | |

**Conjecture B5.** For uov-Ip-pkc keys, every GPI(q) distinguisher with running time `T` has
advantage at most about `T/T_KR + q·2^{−592}`, where `T_KR` is the cost of key recovery
(`≈ 2^{201}` bit operations by the estimate above).

*Basis.* (i) §B.2: GPI is no harder than key recovery. (ii) §B.3: certifying attacks are
key-recovery attacks. (iii) §B.4: the known structural attacks give nothing cheaper. (iv) A direct
(forgery) attack does not help: a preimage of a target carries no information on `𝒪`.

*Caveats.* GPI has had no outside cryptanalysis. (ii) does not cover low-advantage statistical
distinguishers. The cost model is the usual heuristic one. Quantum attacks were not analysed.

*Consequence for [UA].* Under B5 the GPI terms in T2–T5 are not the weakest link: they are bounded
by key recovery, which is harder than forgery at these parameters. The multiplied term
`q_T·Adv^{gpi}` in T2's second bound stays meaningful only for `q_T·T ≪ 2^{201}`; the first bound
(`Adv^{gpi}(q_T)` un-multiplied) has no such limit.

## B.6 Relation to known assumptions

- **Public-key indistinguishability** (`pkind`): `pk` is hard to tell from a uniformly random
  quadratic map. As we recall, this is the "OV problem" in the security argument of MAYO [Beu21b].
  Its best known attacks are the key-recovery attacks.
- **GPI does not follow from `pkind` by any argument we can find.** A reduction would receive `pk`
  or a random map, and would have to produce `U(Good)` samples for the distinguisher. It cannot:
  it has no `sk`, and for a random map `Good` is not defined. GPI is about a set defined by the
  trapdoor; `pkind` is about the map alone.
- **Exact relation (proved, trivial).** Let JPR(q) be: `(pk, s_1..s_q)` with `s_i ← U(Good_sk)` is
  hard to tell from `(R, s_1..s_q)` with `R` a random quadratic map and `s_i` uniform. Since
  `(pk, uniform)` versus `(R, uniform)` is `pkind`,

      Adv^{gpi}(q) ≤ Adv^{jpr}(q) + Adv^{pkind},        Adv^{jpr}(q) ≤ Adv^{gpi}(q) + Adv^{pkind}.

  So given `pkind`, GPI is *equivalent* to "a key together with signatures on random targets is
  pseudorandom". That is the natural strong form of the UOV assumption, and it is what
  simulation-based arguments for the specified signer implicitly use.
- **Key recovery.** §B.2 and §B.3: key-recovery hardness is necessary for GPI, and sufficient
  against certifying attackers. We have no reduction from key recovery (or from the UOV problem)
  to GPI against arbitrary distinguishers.
- **Partial information.** A GPI(1) distinguisher with advantage `ε` is a predicate `A(pk, s)` with
  `Pr[A = 1 ∣ bad] − Pr[A = 1 ∣ good] = ε/δ`. So it is correlated with the predicate
  "`f(s) = 0`", i.e. with a function of `𝒪` (Lemma B2(3): of its Plücker vector). §B.3 turns this
  into `𝒪` only when the correlation is one-sided and strong.

## B.7 Obstacles and open problems

- **Two-sided, weak distinguishers.** Is there a public statistic of `s` whose law differs
  between bad and good points by more than `2^{−592}`? We found none, and §B.3 cannot exclude
  one. *Update* (`ompr-cryptanalysis.md` §2.3, Lemma F): for a linear form `w·s` the difference
  is 0 unless `w ∈ 𝒪^⊥`, and then about `2^{−292}` (root mean square over the key, uniform
  `P2`); seeing it takes `2^{600}` samples. On toy keys this statistic recovers the oil space
  from 2 to 5 times `q^V/δ` samples. Statistics of higher degree: `ompr-cryptanalysis-2.md` §2. A
  statistic of the vinegar fixed before the key block has a difference of at most `2^{−288}`
  (root mean square, any degree; proved); every linear one at most `2^{−140}` for almost all
  keys (proved, fourth moment); the best of degree `d`, heuristically,
  `2^{−292}·√(11·binom(74+d, d))`. Statistics of the whole point at chosen targets stay open. A worst-case to average-case reduction for badness would close the gap; the lack of
  public symmetries of `Bad` is the obstacle.
- **(H1)** of §B.3 at the real parameters: prove that `f|_A` is determined by its `F_256`-points
  on a random 3-space, or replace the interpolation.
- **Dedicated algebraic attacks.** The systems of §B.4 are the obvious ones. A modelling that
  uses `K_s` inside the intersection attack without new variables would be a real improvement;
  we see none.
- **Quantum.** `ompr-cryptanalysis-2.md` §4: Kipnis–Shamir with Grover, `≈ 2^{144}` gates at
  depth `2^{130}`, is the cheapest quantum key recovery we know. GPI against quantum
  distinguishers was not analysed beyond that.
- **Fixed keys.** All of this is for keys with `δ(sk)` near `δ_unif`; see [UA] §9.

## References

Citations are from memory. Items marked (†) are the ones whose details we are least sure of; they
are used only where the text says "as we recall".

- [UA] `lean/docs/security/uov-assumptions.md`, and the references there: [BMV08], [SSH11],
  [BBBMR26], [Beu21], [UOV-R3].
- [Cor02] J.-S. Coron, *Optimal security proofs for PSS and other signature schemes*,
  EUROCRYPT 2002.
- [PV05] P. Paillier, D. Vergnaud, *Discrete-log-based signatures may not be equivalent to
  discrete log*, ASIACRYPT 2005.
- [KK12] S. Kakvi, E. Kiltz, *Optimal security proofs for full domain hash, revisited*,
  EUROCRYPT 2012.
- [FF13] M. Fischlin, N. Fleischhacker, *Limitations of the meta-reduction technique: the case of
  Schnorr signatures*, EUROCRYPT 2013. (Background on reduction classes; no result of it is
  used.)
- [BJLS16] C. Bader, T. Jager, Y. Li, S. Schäge, *On the impossibility of tight cryptographic
  reductions*, EUROCRYPT 2016.
- [RTV04] O. Reingold, L. Trevisan, S. Vadhan, *Notions of reducibility between cryptographic
  primitives*, TCC 2004.
- [KS98] A. Kipnis, A. Shamir, *Cryptanalysis of the oil and vinegar signature scheme*,
  CRYPTO 1998.
- [KPG99] A. Kipnis, J. Patarin, L. Goubin, *Unbalanced oil and vinegar signature schemes*,
  EUROCRYPT 1999.
- [DYCCC08] J. Ding, B.-Y. Yang, C.-H. O. Chen, M.-S. Chen, C.-M. Cheng, *New
  differential-algebraic attacks and reparametrization of Rainbow*, ACNS 2008.
- [Beu21b] W. Beullens, *MAYO: practical post-quantum signatures from oil-and-vinegar maps*,
  SAC 2021. (†: the name and exact form of its distinguishing assumption.)
- [Péb24a] P. Pébereau, *One vector to rule them all: key recovery from one vector in UOV
  schemes*, PQCrypto 2024 (ePrint 2023/1131). (†: parameter range of the polynomial-time claim.)
- [Péb24b] P. Pébereau, *Singular points of UOV and VOX*, ePrint 2024/219. (†)
