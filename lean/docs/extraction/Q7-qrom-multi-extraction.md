# Q7: QROM extraction from many proofs, mid-run programming, and the quantum protocol theorems

Status: **[paper]**, with **[Lean]** for the linear-algebra and counting steps
(`lean/VoleMole/Seed/QMulti.lean`, no `sorry`, no `axiom`; check with
`cd lean && lake env lean VoleMole/Seed/QMulti.lean`). This continues README §L9 after Q2
(single-proof QROM extraction) and Q5 (QROM simulation-extractability). Notation, counts, oracle
names and lemma names follow Q2 and Q1. `ε_multi` is kept symbolic. Its current values are Q1's
Thms 5.1 and 5.2; Q6 (`Q6-cipher-binding.md`, in progress) may improve them.

## 0. Summary

**Theorem M (§2): multi-proof extraction.** A quantum adversary outputs `n` proofs, possibly for
different statements and different relations. They may share chains, trees and leaf commitments.
The extractor runs the game once with compressed oracles. It runs the verifier on all `n`
outputs, then applies Q1's `Ext` to at most `nτ` hidden-leaf commitments. It recovers witnesses
for **all** accepted outputs simultaneously:

    Pr[∃ j: V accepts o_j ∧ E fails on o_j]  ≤  (Σ^{(n)})² + ε_multi(Q_E, Q₄) + n·ε_rec + ε_Sim^{(n)}.

`Σ^{(n)}` is Q2's `Σ`, with the verifier's queries on all `n` outputs added to the counts. So
`Σ^{(n)} ≤ Σ^{(1)}(q) + (n−1)·κ`, where `κ ≈ 2√2·7·2^{−64} ≈ 2^{−59.7}` is one verification's
weight. In the leading-term model this gives

    (Σ^{(n)})² ≈ 8(5q + 7n)²·2^{−128} = (200q² + 560qn + 392n²)·2^{−128}     [Lean: main_term_multi_eq].

The `q²` Grover term is **not** multiplied by `n`. The cost of `n` is `O(qn + n²)·2^{−128}`, plus
`n·2^{−128}` for recording. It also enters through `ε_multi`: each verification adds cipher work.
Lemma K (§2.5) brings that work down from about `2^{17}` block queries to at most `2L−1 = 4607` key
fetches per proof.

**Mid-run extraction (§3).**
- A DFMS-style mid-run measurement of PomFRIT's `E₁` is well-defined and almost commutes with later
  queries. Its cost per later query is `4√(2ρ)`, where `ρ` is the density of values that change
  `E₁` (Cor. S.2). This covers *classical* points only.
- PomFRIT's reductions need `E₁` at **superposition** `H_T` queries. There a measurement is the
  wrong tool. The right tool is **database-controlled programming** (Lemma S): answer
  `H_T(x) := G(x) ⊕ E₁(x; D)` coherently, controlled on the compressed database `D` of the proof
  oracles.
- Lemma S shows that this world equals `V·ψ_R̃`, where `V` is a database-controlled relabelling of
  `H_T`'s cells, and `‖ψ_R̃ − ψ_R‖ ≤ δ_stab := Σ_{proof-oracle queries} 4√(2ρ_stab)`. Here `ρ_stab`
  is the density of values that change the committed data of a chain already named in a filled
  `H_T` cell.
- For VOLEitH, `δ_stab ≈ 2^{−74.8}` at `q = 2^{30}` and `2^{−44.8}` at `q = 2^{50}`. Programming
  is therefore essentially free. No mid-run measurement, no rewinding and no measure-and-reprogram
  are needed.

**PomFRIT in the QROM (§4)**, for `n = ℓ+1` forgeries:

    U1-Q:  Adv^{omuf} ≤ Adv^{ompr-RO}_{UOV}(B; ℓ) + (Σ_*^{(n)})² + ε_multi + n·ε_rec + 2δ_stab + n·2^{−357} + ε_DS (+ε_Sim)
    U2-Q:  Adv^{omuf} ≤ Adv^{ompr⊕τ-RO}_{UOV}(B'; ℓ) + (Σ^{(n)})²  + ε_multi + n·ε_rec + 2δ_stab + n·2^{−357} + ε_DS (+ε_Sim)

- `Σ_*` is `Σ` with H₂³ density `2^{57}·2^{−128}` in place of `max(d,1)·2^{−128}`. This is
  Lemma P-Q, the QROM form of PomFRIT's Lemma P (largest-width prefix group). Its term is
  `≈ 8·Q₂₃²·2^{−71}`. That is `2^{−8}` at `Q₂₃ = 2^{30}` and `2^{−28}` at `Q₂₃ = 2^{20}` H₂³
  queries [Lean: `shift_term_at_2_30`, `shift_term_at_2_20`].
- The classical 71-bit margin becomes 35.5 bits. This is tight for the reduction: a Grover search
  over the grinding counter achieves it (§4.3).
- U2-Q has no such term. It is stated under the QROM τ-shift assumption, with the shift set salted
  into the oracle input, `G(x, S)`.
- `A-OMPR-RO` and `A-OMPR⊕τ-RO` are the natural QROM forms of the paper's assumptions. Classically
  they are equivalent to them by lazy sampling.

**Ratatouille balance and Moussaka one-more unforgeability in the QROM (§5, §6).** Both
reductions extract only at the end. With Theorem M they lift directly, with
`ε_ext → ε_ext^{Q,(n)}`. Moussaka needs no quantum-random-oracle assumption on UOV: its CT-UF game
has a classical signing oracle and a concrete `Com`. Ratatouille needs UF-Tag with quantum access
to `Tag` (its §10 already said so).

**Numbers** (`λ = 128`, `d = 9` unless stated, cipher queries `q_E = 2^{30}`):

| | `q = 2^{30}` | `q = 2^{50}` hash, `q_E = 2^{30}` |
|---|---|---|
| Theorem M, `n = 1` | `2^{−60.4}` | `2^{−20.4}` |
| Theorem M, `n = 2^{20}` (Lemma K) | `2^{−60.4}` (Σ²) `+ 2^{−62.9}` (`ε_multi^{H₄}`) | `2^{−20.4}` |
| Theorem M, `n = 2^{20}`, no Lemma K | `ε_multi^{H₄} ≈ 2^{−41.8}` | same |
| PomFRIT U2-Q (`d = 2`) | `2^{−61.5} + ε_multi` | `2^{−21.5}` |
| PomFRIT U1-Q | `2^{−8}` (if all `2^{30}` queries go to H₂³) | `2^{−22.5}` with `q₂₃ ≤ 2^{20}` |
| `2δ_stab` (PomFRIT) | `2^{−73.8}` | `2^{−43.8}` |
| Ratatouille / Moussaka extraction part | `2^{−60.4} + ε_multi` | `2^{−20.4}` |

At `q_E ≥ 2^{40}` the `ε_multi` column is vacuous with Q1's bounds. That cap is unchanged from Q2.

**Confidence.**
- Theorem M: high. It is Q2's argument with one property for all chains, and Q5 §8.1 already used
  this pattern.
- Lemma S: high for the operator algebra (in Lean) and the hybrid. Medium-high for the
  instantiation counts (§3.4), which reuse Q2 §5.4.
- U1-Q and U2-Q: medium-high. The assumption formulations are new.
- Ratatouille and Moussaka: high, given their stated assumptions.

---

## 1. Setting

As in Q2 §2 and Q5 §1. All hashes are quantum random oracles, simulated by DFMS compressed
oracles. AES is Q1's key-level compressed ideal cipher, or Q4's `S*` for efficiency. Queries are
non-parallel, with a fixed oracle schedule. Q2 §3's exact reductions are always applied:
- `iv` goes into the H₂¹' label (§3.1);
- `l` goes into the H₂³' label (§3.2).

**Outputs.** The adversary (or a combined algorithm, e.g. a reduction running honest parties
plus the adversary) produces outputs `o_j = (R_j, x_j, b_j, π_j)` for `j ≤ n`, where:
- `R_j` is a relation from a fixed finite set `ℛ` (the repo's five relations);
- `x_j` is a statement and `b_j` are binders.

The outputs may be chosen adaptively. Some may be verified **mid-run**, as when an Issuer verifies
a request before answering it. `n` is an upper bound on their number.

**Counts.** `q_o` counts the adversary's queries to oracle `o`. Analysis counts include the
verifier's queries on all `n` outputs, Q2 §3's extra queries, and any honest parties' classical
queries:

    Q₂₁ = q₂₁ + n,  Q₂₂ = q₂₂ + n,  Q₂₃ = q₂₃ + n,  Q_c = q_c + 2Q₂₃ + n,
    Q₁ = q₁ + n(τ+1),  Q₀ = q₀ + 2n,  Q₄ = q₄ + 2Q₂₁ + n,  Q_E = q_E + n·K_V,

where `K_V ≤ 4607` is the verifier's number of distinct cipher keys (Lemma K). Honest provers add
their own counts the same way. Each honest proof adds `≈ 2^8` H₂³ grinding queries and `≤ 4607`
key fetches.

**Relation-wise maxima.**
- `ε̂_KOS := max_R ε_KOS(R) ≤ 2^{−153.5}`;
- `ε̂_QS := max_R ε_QS(R) ≈ 2^{−128}(1+2^{−36.8})`;
- `d̂ := max_R max(d_R, 1) = 9`;
- `M̂ := min` over the combined-slot relations of `M_R` (only in negligible terms).

---

## 2. Theorem M: multi-proof extraction

### 2.1 The extractor `E^{(n)}`

1. Run the whole game once, answering every oracle query (adversary, honest parties, Issuer-side
   verifications) with the compressed oracles. Run `V_{R_j}` on each output, mid-run or at the end,
   as the game prescribes. All of `V`'s queries are classical.
2. After the last oracle query of the game, for each `j` with `V` accepting, read `Δ_j`, `iv_j`
   and the hidden-leaf commitments `com_{j,i,Δ_{j,i}}`. Apply `Ext_{(iv_j, twk_i)}(com_{j,i,Δ_{j,i}})`
   for every `i < τ`. If several `(j, i)` give the same `(ι, t)`, measure once and reuse the
   outcome.
3. For each `j`, form the candidates `w_j^{(i)} = u_{j,i}[0..ℓ_j) ⊕ c_{j,i} ⊕ d_j` from the
   extracted keys and the opened seeds, and output the first one with `R_j(x_j, w_j^{(i)})`.

### 2.2 One bad property for all chains and all relations

**Typing chains by relation.** By `lean/docs/security/domain-separation.md` (correction to L0 O3), for the
shipped relations the H₂¹, H₂² and H₃ inputs have pairwise distinct lengths across relations. So a
raw H₂¹ string parses for at most one relation. Define:
- `rel(c)` for an H₂¹' cell `c = (x₁, iv)`: the unique `R` whose H₂¹ length `x₁` has, or "junk";
- `rel` of an H₂² cell likewise;
- `rel` of an H₂³' cell: that of the H₂² cell whose output is its 56-byte prefix. Under `¬COL` there
  is at most one such cell.

`H_comb` cells carry the relation's `dst`. H₁, H₄, H₅ and the cipher are shared across relations,
by design.

**The property.**

    P_⋆(D) := COL ∨ ∃c: B₁^{rel(c)}(c) ∨ ∃(c,x₂): B₂^{rel(c)} ∨ B_l^{rel(c)} ∨ ∃(c,x₂,x₃,l) consistent: B₃^{rel(c)},

- `B^R_•` is Q2 §5.3's component with `R`'s parameters (`ℓ_R`, `d_R`, the constraint system,
  `inst` decoded with `R`'s encoding).
- Junk chains satisfy no component (`A := ∅`).
- `COL` is global: one collision anywhere.

**Non-neutral counts.** Q2 §5.4's case analysis applies cell by cell. Each H₂¹', H₂², H_comb or
H₂³' cell belongs to one relation. So its count is Q2's count for that relation, bounded by the
maximum over relations. The H₁, H₂⁰ and cipher counts were already global in Q2, summing over
all chains. One thing must be checked: a single cell can feed chains of several relations, and
the counts still hold.
- An **H₁** cell value is non-neutral only if it equals one of: a `com` field of any chain (`≤ Q₂₁`
  values), an `h`-block (`≤ 17Q₁`), or another output (`≤ Q₁`).
- A **cipher** cell value is non-neutral only if it is aligned with a target of some chain
  (`≤ Q₂₁·L`).
- An **H₂⁰** cell value is non-neutral only if it equals a μ field (`≤ Q₂₁ + Q₂₂`) or another
  output.

The relation of a chain whose μ preimage is defined later is fixed by its H₂¹ length, not by μ.
The late μ preimage only defines `inst(c)`, which is (N-H₂⁰). So:

    ρ₂₁ ≤ ε̂_KOS + (Q₂₁+Q₂₂)2^{−1088},  ρ₂₂ ≤ ε̂_QS + (Q₂₂+Q₂₃+Q_c)2^{−448},  ρ_c ≤ 2^{−128} + Q₂₃2^{−128M̂},
    ρ₂₃ ≤ d̂·2^{−128},  ρ₁ ≤ (Q₂₁+18Q₁)2^{−256},  ρ₀ ≤ (Q₂₁+Q₂₂+Q₀)2^{−256},  ρ_E ≤ Q₂₁·L·p.

**Confidence: high.** These are Q2's counts. The only new fact is typing by length, which the
domain-separation note establishes.

### 2.3 Lemma F^{(n)}: each accepted output that the extractor fails on lands in `P_⋆`

Define the following events on the final measured database:
- **Rec^{(n)}**: every classical query of every verification (mid-run or final) and of every
  honest party is recorded. For hash queries, `D(x) = y`. For each opened leaf of each accepted
  output, the verifier's key is in the key database and aligned.
- **Bad_end**: two distinct database keys agree on an adjacent pair `{x₀(iv, twk), x₁(iv, twk)}`
  for some `iv` in the H₄ database (or, in the free-iv version, for any `iv`) and some leaf tweak
  `twk`. This is Q1 Thm 5.2's `Bad`, respectively Thm 5.1's `Z(D) ≠ ∅`. It is **one** event for all
  outputs.

**Lemma F^{(n)}.** If `V_{R_j}` accepts `o_j`, `E^{(n)}` fails on `o_j`, Rec^{(n)} holds and
`¬Bad_end`, then `D ∈ P_⋆`.

*Proof.* This is Q2 Lemma F, applied to output `j` with its verifier's records. The steps are: the
tree, the opened leaves (equal to the committed seeds because of `¬Bad_end ⊇ ¬MULTI_end`), the
checks, consistency, `Δ_j ∈ A`, the statement, and `E` fails iff `¬Ext_D(c_j, x₂,j)`. That gives
`B₃^{R_j}(c_j, x₂,j, x₃,j, l_j)`. Two points are new.
- **Mid-run verification.** Q2 used Rec only for queries at the end. A record made mid-run
  persists exactly in the purified oracle: every later purified query is diagonal in the value
  basis (Q5 Lemma R). So the final compressed measurement keeps it with probability
  `≥ 1 − 2^{1−n_o}` per hash record and `≥ 1 − 2p` per cipher check.
- **Sharing.** Nothing in the argument depends on other outputs.
  - Two outputs on the same chain (same `chall₁`) give two `x₂`'s or the same one. Two outputs
    with the same `x₂` and different counters (PomFRIT F3) give two H₂³' cells. They yield the
    same or different `B₃` witnesses of the **same** property `P_⋆`.
  - A tree or leaf commitment reused across chains or across relations is reused data inside
    `D`. Each chain's committed data is computed from `D` independently.
  - Identical outputs (replays) are one witness of `P_⋆`.

  So sharing never adds terms. ∎

### 2.4 Order of the `Ext` measurements and the joint event

- All `nτ` `Ext` measurements are diagonal in the database basis, so they commute **exactly** with
  each other (Q1 §3, (I1)), and with every hash query, since they act only on cipher registers.
- `E^{(n)}` applies them after the game's last oracle query. So no `Ext` is ever moved across a
  cipher query, and their joint outcome is the marginal of one computational-basis measurement of
  `D` at the end. Repeating an identical `(ι, t)` gives the identical outcome, which justifies the
  deduplication in §2.1.
- Measuring all of `D` at the end is therefore w.l.o.g. for the analysis (Q2 §6.1). The **joint**
  event "every accepted output yields a witness" is a single event of that one measurement. Its
  complement is the union in Lemma F^{(n)}.
- **Interleaved implementations.** If an implementation runs `Ext` for `o_j` before later
  verifications, Q1 P1 charges `δ` per later cipher query. A fetch (Lemma K) is one query. That
  costs at most `n²·τ·K_V·δ ≤ 2^{−68}` for `n = 2^{20}`, and it is avoidable.
- Remark S.3 (§3.3) shows `δ` can be halved to `4√(2p)`.

### 2.5 Lemma K: a classical party's cipher work counts per key, not per block

**Lemma K.** Let a classical party (the verifier, an honest prover, the extractor) evaluate the
cipher at several points under one key `k`, with points that are fixed once `k` is known. Replace
those evaluations by one **fetch** `F_k (Σ_σ |σ⟩⟨σ| ⊗ U_σ) F_k`, where `U_σ` computes all the
needed values `σ(x_1), …, σ(x_m)` into the party's registers. Then:
- (a) the party's classical output distribution is unchanged, exactly;
- (b) in Lemma T and in Lemma S, the fetch is one query to cell `k`;
- (c) in Q1's database bound it adds at most one key;
- (d) in Q1 Thms 5.1 and 5.2 (full-value reduction) it is two full-value queries;
- (e) in Q4 Thm C it is one cipher query.

*Proof.*
- (a): all three worlds (real, purified, compressed) are perfectly indistinguishable for every
  algorithm (Q1 P0), and in the real world the two implementations compute the same function.
- (b): Lemma T step 5 (Q2 §4) and Lemma S step 3 use only that the operator between the two `F_k`
  is controlled on `D_k`'s value basis and acts on other registers.
- (c): Lemma 2.1's proof uses only "controlled on the key, acting on one register".
- (d): fetch `σ_k`, evaluate all points, un-fetch, exactly as Q1 §2 does for one point.
- (e): Q4's `S*` implements `E_k = A_{F(k)}∘ρ_k`, and a fetch reads `F(k)` once. ∎

**Count for VOLEitH.** The verifier derives each GGM node key and each opened leaf key once. Each
needs only blocks at fixed points: two children, or the commitment plus the leaf PRG. So
`K_V ≤ 2L − 1 = 4607 ≈ 2^{12.2}` [Lean: `fetch_keys`], instead of the `≈ 2^{17}`–`2^{18}` block
queries counted in Q5 §1.1. The same holds for an honest prover (its root expansion included).
Remark: the same applies to Q5's simulator `Sim`, whose `c_E` would drop from `2^{18}` to about
`2^{12.2}`. That would move Q5's vacuity threshold from `Q_S ≈ 2^{20}` to `Q_S ≈ 2^{25}`.

**Confidence: high.** It is a re-implementation of a classical computation.

### 2.6 The theorem

**Theorem M.** For every quantum adversary with the counts of §1 and the extractor `E^{(n)}` of
§2.1:

    Pr[∃ j ≤ n: V_{R_j} accepts o_j ∧ ¬R_j(x_j, E^{(n)}(o_j))]  ≤  (Σ^{(n)})² + ε_multi^{(n)} + n·ε_rec + ε_Sim^{(n)},

    Σ^{(n)} := 2√2·[ Q₂₁√(ε̂_KOS + (Q₂₁+Q₂₂)2^{−1088}) + Q₂₂√(ε̂_QS + (Q₂₂+Q₂₃+Q_c)2^{−448})
                   + Q_c√(2^{−128} + Q₂₃2^{−128M̂}) + Q₂₃√(d̂·2^{−128})
                   + Q₁√((Q₂₁+18Q₁)2^{−256}) + Q₀√((Q₂₁+Q₂₂+Q₀)2^{−256}) + Q_E√(Q₂₁·L·p) ],

    ε_multi^{(n)} := min{ (32/9)·Q_E³/(N−1),  ε_multi^{H₄}(2Q_E + Q₄ + 1) + 2n·2^{−128} }   (Q1 Thms 5.1, 5.2; Q2 §6.3),
    ε_rec ≈ 2^{−128}  (Q2 §6.2, per output),     ε_Sim^{(n)} ≤ 2^{−172} + nτ·Q_E·δ  (Q4 Thm C; 0 with S^IC).

The `+2n·2^{−128}` reads the `n` accepted `iv`s back from the H₄ database (DFMS eq. (8)).

*Proof.*
1. **Reduction to one database event.** The simulation is perfect (Q2 §6.1), and all `Ext`
   measurements are marginals of the final measurement of `D` (§2.4). So by Lemma F^{(n)},
   `Pr[∃j: accept_j ∧ fail_j] ≤ Pr[D ∈ P_⋆] + Pr[¬Rec^{(n)}] + Pr[Bad_end]`.
2. **Lemma T on the whole game** (Q2 §4; **[Lean]** `QROM.telescope`, and `telescope_with_neutral`
   for steps that are not queries). Every query of every party is a step. By §2.2,
   `√Pr[D ∈ P_⋆] ≤ Σ^{(n)}`.
3. **Recording.** Take a union over the `n` verifications' records, as in Q2 §6.2:
   `Pr[¬Rec^{(n)}] ≤ n·ε_rec`. Honest parties' records are not needed in Lemma F^{(n)}.
4. **Agreement.** `Pr[Bad_end] ≤ ε_multi^{(n)}`, by Q1 Thms 5.1 and 5.2 applied to the whole game,
   which is one algorithm with `Q_E` cipher queries (Lemma K) and `Q₄` H₄ queries. `Bad_end` does
   not depend on `n` except through the counts and the readback.
5. **Efficient cipher simulation.** With `S*` instead of `S^IC`, add `ε_Sim` with `L = nτ` `Ext`
   calls (Q4 Thm C). By Q4 Thm B, every bound except `ε_multi^{H₄}` already holds for `S*` without
   the `L·q·δ` term. ∎

### 2.7 Shape of the bound

Let `κ` be the contribution of one verification to the bracket of `Σ`:

    κ := 2√2·[ √ε̂_KOS + √ε̂_QS + 3·2^{−64} + √d̂·2^{−64} + (τ+3)·√(Q·2^{−256}) + K_V·√(Q₂₁Lp) ]  ≈  2√2·7·2^{−64}  ≈  2^{−59.7}.

The verifier's H₂³' query costs `√9 = 3`, plus `2` for its two H_comb queries from Q2 §3.2. Its
own H_comb query and its H₂² query cost `1` each. So `Σ^{(n)} ≤ Σ^{(1)}(q) + (n−1)κ`, and

    (Σ^{(n)})² ≤ (Σ^{(1)})² + 2(n−1)κ·Σ^{(1)} + (n−1)²κ².

In the leading-term model (all `q` on H₂³) this is `8(5q+7n)²·2^{−128}` [Lean:
`main_term_multi_eq`]. The cross term `2nκΣ ≈ 560·qn·2^{−128}` is the "`n·(small)`" the brief asks
for, with small `= O(q·2^{−128})`. The `n²` term is that of `n` classical queries, as if the
adversary had made them. Classical queries enjoy no advantage in Lemma T: a mixed-state version
gives the same increment, `4√(2ρ)·√Pr + 8ρ`.

| `q` | `n` | `(Σ^{(n)})²` | added vs `n = 1` | `Q_E` (Lemma K, `q_E = 2^{30}`) | `ε_multi^{H₄}` | `ε_multi^{free}` | `ε_Sim` |
|---|---|---|---|---|---|---|---|
| `2^{30}` | 1 | `2^{−60.4}` | — | `2^{30.0}` | `2^{−70.3}` | `2^{−36.2}` | `2^{−90.4}` |
| `2^{30}` | `2^{10}` | `2^{−60.4}` | `2^{−78.9}` | `2^{30.0}` | `2^{−70.3}` | `2^{−36.2}` | `2^{−80.4}` |
| `2^{30}` | `2^{20}` | `2^{−60.4}` | `2^{−68.9}` | `2^{32.5}` | `2^{−62.9}` | `2^{−28.8}` | `2^{−68.0}` |
| `2^{30}` | `2^{30}` | `2^{−57.8}` | `2^{−58.1}` | `2^{42.2}` | n/a (`θ > 1/2`) | vacuous | `2^{−48.2}` |
| `2^{50}` | `2^{20}` | `2^{−20.4}` | `2^{−48.9}` | `2^{32.5}` | `2^{−62.9}` | `2^{−28.8}` | `2^{−68.0}` |

- Without Lemma K (`2^{17}` blocks per verification), `n = 2^{20}` gives `Q_E = 2^{37}`,
  `ε_multi^{H₄} ≈ 2^{−41.8}` and `ε_multi^{free} ≈ 2^{−15.1}`.
- `n·ε_rec ≈ n·2^{−127}`.
- **Where `n` hurts:** only through `ε_multi`, because each verification touches about `2^{12.2}`
  keys. With Q1's key-level bounds, `n·K_V` must stay below about `2^{36}`. Q6's improvement would
  lift this.

(Numbers: `scratchpad/q7/nums.py`. **[Lean]**: `main_term_multi_at_2_30_n_2_20`,
`main_term_multi_at_n_eq_q`, `multi_free_fetch_at_n_2_20`, `multi_free_blocks_at_n_2_20`.)

---

## 3. Mid-run extraction and database-controlled programming

### 3.1 What PomFRIT needs, and why a measurement is the wrong tool

Classically, PomFRIT's reductions (pomfrit.md §6) answer a fresh `H_T` query `x` with
`t_j ⊕ E₁(x)`. Here `E₁(x)` is the prefix of the largest-width group of alive trees of the chain
named by `x`'s `chal1`, with `x`'s `d_pre`. In the reduced world of Q2 §3.1, every ingredient of
`E₁` is a deterministic function of the compressed database `D_o` of the *proof* oracles:
- the H₂¹' cell with output `chal1`, whose label carries `x₁` and `iv`;
- its H₁ preimages `com → h → com_{i,·}`;
- the aligned keys (canonical: the least) and their permutations, for ConvertToVOLE.

Write `E₁(x; D_o)`, and `S(x; D_o)` for the set of alive-tree prefixes (≤ 17 values). `E₁` reads
no H₄ cell, because `iv` is in the H₂¹' label. If the reduction did not use Q2 §3.1, a fresh `iv`
value would change alignments with probability `≈ Q_E·Q₂₁L·2^{−128}` per H₄ query, which would be
fatal.

Two obstacles were identified in pomfrit.md §7.
1. `H_T` is queried in superposition over `x`. Measuring `E₁(x)` for a superposition of `x`
   disturbs the query, and the reduction must program *all* `x` at once.
2. The classical reduction's `x ↦ t_{j(x)}` (a fresh target per query) has no direct quantum
   analogue.

The resolution:
- (2) is an assumption-level question: use targets given by a quantum-accessible random oracle,
  §4.1.
- (1) disappears once `E₁` is applied **coherently**, as a control, rather than measured. The
  answer to a superposition query is computed by a unitary controlled on the basis state of
  `D_o`. Lemma S bounds the error.

### 3.2 Lemma S: database-controlled relabelling of a target oracle

**Setting.** Partition the oracles into the *target* oracle `T` (here `H_T`), with compressed
database `D_T`, and the others, with database `D_o`. Let `{Γ_D}` be unitaries on `D_T` (plus
possibly an auxiliary register), indexed by basis databases `D` of `D_o`, such that:
- (Γ1) each `Γ_D` permutes the computational basis of `D_T` and fixes `|⊥…⊥⟩`;
- (Γ2) each `Γ_D` maps the span of basis states with at most `m` non-`⊥` cells into itself, for
  every `m`.

Put `V := Σ_D |D⟩⟨D| ⊗ Γ_D`. **World R** is the real game with compressed oracles. **World S** is
the same, except that every `T`-query `cO_T` is replaced by `V cO_T V†`.

**Non-neutral density.** For an oracle `o ≠ T`, a cell `y` of `o`, a database `D_{o,−y}` on the
other cells of `o`'s family, and a basis state `β` of `D_T`, let

    NN(y, D_{o,−y}, β) := { v : Γ_{D[y↦⊥]}^{-1} Γ_{D[y↦v]} β ≠ β },
    ρ_o^{stab}(s) := max_{y, |D_o| ≤ s−1, β with ≤ Q_T(s) non-⊥ cells} |NN|/|Y_o|.

Here `Q_T(s)` is the number of `T`-queries before step `s`. For the cipher, use Q1's measure on
`Sym(X)`.

**Lemma S.** Let `ψ_R`, `ψ_S` be the final states, and let `ψ_R̃` be world R with every non-`T`
query `U_o` replaced by `V† U_o V`. Then:
- (a) `ψ_S = V ψ_R̃` exactly;
- (b) `‖ψ_R̃ − ψ_R‖ ≤ δ_stab := Σ_{s: non-T query} 4√(2ρ_{o(s)}^{stab}(s))`.

So for any measurement `M` on registers other than `D_T` that commutes with `V` (for example, any
computational-basis measurement of the algorithm's registers and of `D_o`, including all `Ext`):

    |Pr_S[M = m] − Pr_R[M = m]| ≤ 2δ_stab.

For an event that also reads `D_T`, `Pr_S[E] = Pr_R̃[V†EV]`.

*Proof.*
1. **(a), conjugation.** Initially `D_T = |⊥…⊥⟩`, so `V ψ_init = ψ_init` by (Γ1). `V` acts on oracle
   registers only, so it commutes with the algorithm's unitaries. World S's step sequence is
   `…, V cO_T V†, …, U_o, …`. Writing `U_o = V (V† U_o V) V†` gives `ψ_S = V ψ_R̃` by induction
   (**[Lean]** `conj_run`).
2. **(b), hybrid.** Replace the non-`T` queries one at a time, from the last to the first. Two
   neighbouring hybrids differ only at one query `s`, applied to the *real* state `ψ^R_{s−1}`, and
   agree on everything after it (unitaries). So `‖ψ_R̃ − ψ_R‖ ≤ Σ_s ‖(U_o − V†U_oV)ψ^R_{s−1}‖`
   (**[Lean]** `hybrid_le`). This equals `Σ_s ‖[V, U_o]ψ^R_{s−1}‖` (**[Lean]**
   `conj_defect_norm`).
3. **Local commutator.** `cO_o = Σ_y |y⟩⟨y| ⊗ cO_y` is block-diagonal in `(y, D_{o,−y})`, and so is
   `V`, which is controlled on `D_o` and does not change it (DFMS Cor. 2.2). Fix a block, and
   restrict to the subspace `H_m` of `D_T`-states with `≤ m = Q_T(s)` non-`⊥` cells. It contains
   `ψ^R_{s−1}` and is invariant under everything below, by (Γ2).
   - Put `W := Γ_{D[y↦⊥]}^{-1}V`. Since `Γ_{D[y↦⊥]}` is constant on the block and acts on `D_T`,
     `‖[cO_y, V]‖ = ‖[cO_y, W]‖`.
   - `W = |⊥⟩⟨⊥| ⊗ 1 + Σ_v |v⟩⟨v| ⊗ Γ'_v`, with `Γ'_v := Γ_{D[y↦⊥]}^{-1}Γ_{D[y↦v]}`. Write
     `cO_y = F O F`. `O` is controlled on the cell's value and acts on the algorithm's output
     register, so `[O, W] = 0`. By **[Lean]** `QROM.conj_commutator_le`,
     `‖[cO_y, W]‖ ≤ 2‖[F, W]‖`.
   - `F = 1 − 2|w⟩⟨w|` with `w = (|⊥⟩ − |u⟩)/√2`. So `[F, W] = −2[P, Z]` with `P = |w⟩⟨w| ⊗ 1` and
     `Z := W − 1` (**[Lean]** `swap_comm`).
   - `[P, Z] = PZ(1−P) − (1−P)ZP` (**[Lean]** `comm_offdiag`). The two terms map into orthogonal
     subspaces, so `‖[P,Z]‖ ≤ max(‖ZP‖, ‖Z†P‖)` (**[Lean]** `offdiag_norm_le`).
4. **Density.** `Z|⊥⟩ = 0`. So for `χ ∈ Im P`, `χ = |w⟩⊗φ`, we get `Zχ = −Z(|u⟩⊗φ)/√2`. Expand
   `φ = Σ_β |β⟩ ⊗ φ_β`. Then `Z(|u⟩⊗φ) = Σ_v u_v |v⟩ ⊗ Σ_{β: v∈NN(β)} φ_β ⊗ (Γ'_vβ − β)`.
   - `Γ'_v` permutes basis states, so the inner vector has norm `≤ 2‖φ|_{\{β: v∈NN(β)\}}‖`.
   - Hence `‖Z(|u⟩⊗φ)‖² ≤ 4 Σ_v |u_v|² Σ_{β: v∈NN(β)} ‖φ_β‖² = 4 Σ_β ‖φ_β‖² μ(NN(β)) ≤ 4ρ‖φ‖²`
     (**[Lean]** `density_swap_le`).
   - So `‖ZP‖ ≤ √(2ρ)`. `Z† = W† − 1` has the same non-neutral sets, since a permutation fixes `β`
     iff its inverse does. So `‖Z†P‖ ≤ √(2ρ)`.
   - Together: `‖[F,W]‖ ≤ 2√(2ρ)` and `‖[cO_y, V]‖ ≤ 4√(2ρ)` on `H_m`.
5. **Measurement.** `M` commutes with `V`, and `V` is unitary, so the outcome distributions under
   `ψ_S = Vψ_R̃` and `ψ_R̃` coincide. Then use `|‖Πa‖² − ‖Πb‖²| ≤ 2‖a − b‖` for unit vectors. ∎

**Remarks.**
- **Non-monotone, two-sided.** As in Lemma T, a removal (a cell forgetting a value that mattered)
  is counted in `NN` exactly like an insertion, because `NN` is defined relative to `⊥`.
- **Only filled target cells matter.** `NN(β)` counts a value only if it changes `Γ` on the
  *actual* `D_T` basis state `β`. A new H₂¹' cell creates a chain, and so changes `E₁(x)` for
  infinitely many `x`, but none of them is filled. This is why `ρ^{stab}` is small. A crude bound
  `‖Γ'_v − 1‖ ≤ 2` without `β` would make every H₂¹' value non-neutral.
- **Relation to literature.** The proof is Lemma T's local-commutator computation (CFHL Lemma 5.6;
  DFMS Lemma 3.3; Q1 Lemma 3.1), applied to a database-controlled unitary instead of a projector.
  I did not find this "coherent online programming" statement in DFMS, GHHM or DFM20. GHHM's
  adaptive reprogramming is the closest relative: it programs at points chosen by the reduction,
  with fresh values, and pays `√(q·p_max)`. Here the *value* is programmed (a shift by a database
  function) at *every* point, and the cost is the database's stability.

### 3.3 Corollary S.2: DFMS-style mid-run measurement, and a sharper `δ`

A projective measurement `{Σ^o}` diagonal in `D_o`, purified as `M = Σ_o Σ^o ⊗ X^o` (DFMS eq. (12)),
is a `V` of Lemma S with `Γ_D := X^{o(D)}` on an outcome register. (Γ1) and (Γ2) hold trivially.

**Corollary S.2.** `‖[cO_y, M]‖ ≤ 4√(2ρ)`, where `ρ` is the density of values of cell `y` that change
the outcome `o(D)`, relative to `⊥`.

- **Application to `E₁` at a classical point `x`.** Measuring `E₁(x; D_o)` mid-run (DFMS-style
  online extraction) is possible. It almost commutes with each later query, at cost
  `4√(2ρ_stab)`, with `ρ_stab` from §3.4 (one filled point). This is enough wherever the point is
  classical, e.g. for the verifier's `H_T` query.
- **Remark S.3 (Q1's δ).** For Q1's `Ext_ι(t)`, the outcome `∅ / k / multi` changes under a value
  `σ` of cell `k` only if `σ` is aligned with `t`. Then `ρ = p`, and Cor. S.2 gives
  `‖[cO_k, M]‖ ≤ 4√(2p)`, half of Q1 Lemma 3.2's `δ = 8√(2p)`. Q1's four-group decomposition adds
  four single-projector commutators. The block argument above bounds the whole outcome register
  at once. This halves `ε_Sim`'s `L·q·δ` term (Q4 Thm C). **Confidence: medium-high.** The argument
  is the same as Lemma S, but I have not cross-checked it against Q1's proof line by line.

### 3.4 Instantiation: `ρ_stab` for committed-data controls

Let `Γ_D` be controlled by a function `f(x; D_o)` of the committed data of the chain named by `x`
(i.e. by `E₁` or by `S`). This is the XOR form, `Γ_D = ⊕_x shift by f(x; D_o)` on non-`⊥` cells
of `H_T` (§4.3), or the salted form, a cell permutation (§4.4). Both satisfy (Γ1) and (Γ2). A shift
`S_a` on a cell fixes `|⊥⟩` and the uniform vector, and so commutes with DFMS's `F`. That is why
the reduction can implement world S by querying a *standard* oracle `G` (§4.3).

A value of a non-`H_T` cell is non-neutral only if it changes the committed data of some chain
named by a *filled* `H_T` cell. Using Q2 §5.4's counts, restricted to those chains:
- **H₂¹' cell:** the value equals the `chal1` of a filled `H_T` cell (this also covers collisions
  that would change the canonical chain). `ρ ≤ Q_T·2^{−704}`, using the lower bound `|chal1| ≥ 704`
  from pomfrit.md §1; it is 1088 in the code.
- **H₁ cell:** `ρ ≤ (Q₂₁ + 18Q₁)·2^{−256}`, as (N-H₁).
- **Cipher key cell:** the value is aligned with a target of a named chain. `ρ ≤ Q₂₁·L·p`, by
  Q1 (F1). Seed expansion after `chal1` is covered here exactly as in Q2 (N-E).
- **H₄, H₂⁰, H₂², H₂³', H_comb, H₃, H₅, XOF_seed, H_ref:** `ρ = 0`. `E₁` and `S` read none of
  these cells. In particular, `iv` is in the H₂¹' label.

Hence

    δ_stab ≤ 4·[ Q₂₁·√(2Q_T·2^{−704}) + Q₁·√(2(Q₂₁+18Q₁)·2^{−256}) + K_E·√(2Q₂₁·L·p) ],

where `K_E` is the number of cipher queries (fetches). The reduction's own `E₁` evaluations read
the database coherently. They are not queries and do not appear. Numerically, with all counts
equal to `q`:
- `2δ_stab ≈ 2^{−73.8}` at `q = 2^{30}`;
- `2δ_stab ≈ 2^{−43.8}` at `q = 2^{50}`, where the cipher part dominates (**[Lean]**
  `stab_cipher_at_2_50` for its square).

The classical Lemma P term `Q_T·q₁·2^{−704}` ("`H_T` queried before the chain exists") is
contained in the first summand.

**Confidence: medium-high.** These are Q2's counts on a subset of chains. The step "E₁ reads no
H₄ cell" relies on Q2 §3.1's reduction being applied by the reduction itself, which it can do
(§4.3).

### 3.5 Alternatives considered

- **Extract at the end, then reprogram `H_T` at the `ℓ+1` forgery points** (measure-and-reprogram,
  DFM20). Each programmed point costs a multiplicative `O(q²)`, so `ℓ+1` points cost
  `(2q+1)^{2(ℓ+1)}`. That is useless.
- **GHHM adaptive reprogramming** of `H_T` at the queried points. GHHM reprograms at points the
  reduction chooses, to fresh *independent* values. Here the needed value `t ⊕ E₁(x)` depends on
  the adversary's database. Lemma S is what one gets by doing that dependence coherently.
- **A small-range target function** `x ↦ t_{j(x)}` (Zhandry 2012). This is needed only to reach
  the *n-target* A-OMPR from the RO form (§4.1, Remark). It is not part of the main theorems.

So the answer to the brief's question is: online extraction in DFMS style works for classical
points (Cor. S.2). For PomFRIT's superposition `H_T` queries the right object is coherent
database-controlled programming (Lemma S). It costs `2δ_stab`, which is negligible.

---

## 4. PomFRIT one-more unforgeability in the QROM

### 4.1 Assumptions

Notation as in pomfrit.md §3: `P = P_pk`, `SPre = derive_preimage(sk, ·)` on **arbitrary** targets,
deterministic.

- **(A-OMPR-RO).** `A` gets `pk`, quantum access to a random oracle `G : {0,1}* → GF(256)^{45}`,
  and ≤ ℓ classical `SPre` calls. It wins with `ℓ+1` pairs `(x_i, s_i)` with distinct `x_i` and
  `P(s_i) = G(x_i)`.
- **(A-OMPR⊕τ-RO).** The same, with `G : {0,1}* × Sets_{≤τ}(GF(256)^{45}) → GF(256)^{45}`. It wins
  with `ℓ+1` tuples `(x_i, S_i, δ_i, s_i)`, distinct `x_i`, `|S_i| ≤ τ`, `δ_i ∈ S_i` and
  `P(s_i) = G(x_i, S_i) ⊕ δ_i`. The shift set is salted into the oracle input. This is the QROM
  version of "submit the shifts before receiving `h`".

**Relation to pomfrit.md's assumptions.**
- In the classical ROM, (A-OMPR-RO) ⇔ (A-OMPR) and (A-OMPR⊕τ-RO) ⇔ (A-OMPR⊕τ) by lazy
  sampling: each fresh `G` query is a target request, and in the τ-version the request carries
  its shift list `S`. The reduction is exact, except that targets must be pairwise distinct
  (`q²·2^{−361}`).
- `τ = 1` (`S = {0}`) is (A-OMPR-RO).
- With quantum `G`, these are new assumptions. They are the natural analogues, in the same way that
  Ratatouille's §10 states UF-Tag with quantum `Tag`, and that salted hash-and-sign UOV is analysed
  in the QROM.
- *Remark (from the n-target form).* `B` can simulate `G(x) := t_{j(x)}` with `j` a
  `2q`-wise-independent function into `[n_t]` (Zhandry's small-range distributions, CRYPTO 2012).
  A forgery pair sharing an index is then a `G`-collision.
  - The loss is `O(q³/n_t)` for the small-range switch, plus `O(q³·2^{−360})` for collisions.
  - The constant in `O(q³/n_t)` is from Zhandry's theorem and was not re-derived here.
  - This needs `n_t ≫ q³` targets, so it is inefficient at interesting `q`. I state the theorems
    under the RO forms. **Confidence in this remark: medium.**

### 4.2 Lemma P-Q: the largest-width group in the QROM

For a PomFRIT chain `c` and an attached `x₂` (which carries `d_pre = d[0..M)`), let `g*(c, x₂)` be
pomfrit.md's group of largest width. It is computed from the committed data in `D`, so it is a
function of `D`. Let `ρ_{g*}` be its prefix. Replace Q2's extractor predicate by

    Ext*_D(c, x₂) :⇔ ∃ i ∈ g*(c,x₂): R_PomFRIT(inst(c), w^{(i)}),     B₃* := Δ ∈ A ∧ ¬Ext*_D.

Write `P_*` for `P_⋆` with `B₃` replaced by `B₃*` on PomFRIT chains.

**Lemma P-Q.** Fix the H₂³' cell `(x₃, l)` of a PomFRIT chain, with `D_{−x}` satisfying
`¬B₁, ¬B₂, ¬B_l`. Then `|{Δ : B₃*}| ≤ 2^{57}`. So in Theorem M, PomFRIT's H₂³ density is
`ρ₂₃* ≤ 2^{57}·2^{−128} = 2^{−71}`, and

    Pr[∃ accepted PomFRIT output j with no R-candidate of prefix ρ_{g*}]  ≤  (Σ_*^{(n)})² + ε_multi^{(n)} + n·ε_rec (+ε_Sim),

where `Σ_*^{(n)}` is `Σ^{(n)}` with `Q₂₃√(d̂·2^{−128})` replaced by `Q₂₃√(2^{−71})` for PomFRIT's H₂³
cells. The leading term is `≈ 8(Q₂₃+n)²·2^{−71}`.

*Proof.* With the chain's data fixed by `D_{−x}`, pomfrit.md Lemma P steps 3–6 are deterministic
and apply verbatim:
- either `|A| ≤ max(d,1) = 2`;
- or `u*` is a bit vector held by a free tree. Then either its prefix group `G(u*) = g*` (so
  `Ext*` holds), or `G(u*) ≠ g*`, every tree outside `G(u*)` is fixed, and `|A| ≤ 2^{57}`
  (**[Lean]** `PomFRIT.fixed_outside_prefixGroup`, `PomFRIT.minority_card_le`).

The count is a number of 128-bit strings (Q2 §8.2). Lemma F^{(n)} goes through with `Ext*`: if `E`
outputs no candidate in `g*`, then `¬Ext*_D`. Lemma T then gives the bound. ∎

**Comparison.** Classically the term is `(Q₃ + n)·2^{−71}` (pomfrit.md Lemma P). In the QROM it is
squared and amplitude-summed: `8Q₂₃²·2^{−71}`.

### 4.3 Theorem U1-Q (standard assumption, RO form)

**Theorem U1-Q.** Consider a quantum adversary `A` against Def. 2.5 with the counts of
pomfrit.md §1, where `Q_T` counts `H_T` queries and `n = ℓ+1`. There is a quantum `B` such that

    Adv^{omuf}_{PomFRIT}(A) ≤ Adv^{ompr-RO}_{UOV}(B; ℓ) + (Σ_*^{(n)})² + ε_multi^{(n)} + n·ε_rec
                              + 2δ_stab + n·2^{−357} + ε_DS (+ ε_Sim).

- `B` runs `A` once.
- `B` makes `Q_T + 2n` queries to `G` and `≤ ℓ` `SPre` calls.
- `B` evaluates `E₁` coherently once per `H_T` query. Each evaluation costs `O(q·L)` database
  lookups and `≤ 17` ConvertToVOLE computations.

*Proof.*
- **`B`'s simulation (world S).** `B` simulates every proof oracle with compressed oracles,
  including Q2 §3.1's split `H₂¹ = H₂¹'(·, H₄(·))`, and the cipher with `S*`. It forwards Issuer
  queries to `SPre`.
  - On an `H_T` query `|x, y⟩` under `dig(pk)`, it computes `E₁(x; D_o)` into an ancilla
    (controlled on its database), queries `G` at `x`, XORs, and uncomputes. So
    `|x, y⟩ ↦ |x, y ⊕ G(x) ⊕ E₁(x; D_o)⟩`. `E₁ = ⊥` is read as 0.
  - Other key digests get `G(x)` directly.
  - Against a compressed `G` this is `V cO_G V†`, with `Γ_D` the XOR shift by `E₁(·; D)` on
    non-`⊥` cells (§3.4). Since `S_a` commutes with `F`, it equals the standard-oracle step.
- **Lemma S.** World S is `Vψ_R̃`, and `‖ψ_R̃ − ψ_R‖ ≤ δ_stab`. World R is the real game, up to
  the exact Q2 §3 reductions and (DS) for independence of `H_T` from the proof oracles.
- **Good event.** Let `x_i` be the verifier's `H_T` input on forgery `i`, and `h_i` its answer.
  Define `Good` on the final measurement of world R:
  - (i) for every `i`, some extracted candidate of `o_i` with prefix `ρ_{g*}(c_i, d_pre,i)`
    satisfies `R(pk, h_i; ·)`;
  - (ii) `D_T(x_i) = h_i` for all `i` (recording).

  By Lemma P-Q, `Pr_R[win ∧ ¬(i)] ≤ (Σ_*^{(n)})² + ε_multi + n·ε_rec`. By Q5 Lemma R,
  `Pr_R[¬(ii)] ≤ n·2^{1−360}`.
- **Transport.** `win ∧ Good` is an event on the algorithm registers, `D_o` and `D_T`. So
  `Pr_R[win ∧ Good] ≤ Pr_R̃[win ∧ Good] + 2δ_stab`. In `ψ_S = Vψ_R̃`, the cell `D_T(x_i)` is
  shifted by `E₁(x_i; D_o^{final})`, and nothing else readable changes. Also,
  `E₁(x_i; D_o^{final}) = ρ_{g*}(c_i, d_pre,i)`: by `¬COL` the `chal1` of `x_i` names `c_i`, and
  `d_pre` is the same field of the proof. So in world S, `win ∧ Good` means:
  - the verifier accepted every `o_i`, with distinct `msg_i` and hence distinct `x_i`;
  - every `o_i` has an extracted `(r_i, s_i)` with `r_i = E₁(x_i; D_o^{final})` and
    `P(s_i) = h_i ⊕ r_i`;
  - the final `G`-cell is `G(x_i) = h_i ⊕ E₁(x_i; D_o^{final})`.

  Hence `P(s_i) = G(x_i)`.
- **`B`'s output.** At the end, `B` queries `G(x_i)` classically. It agrees with the final
  compressed cell except with probability `2·2^{−360}` per point (DFMS eq. (8)). `B` outputs, for
  each `i`, an extracted candidate `(r, s)` with `P(s) = G(x_i)`. To find it, `B` tests the ≤ 17
  candidates; it does not even need to compute `g*`. These are `ℓ+1` preimages at distinct
  points after `ℓ` `SPre` calls.

Summing the error terms gives the bound. ∎

### 4.4 Theorem U2-Q (τ-shift, RO form)

**Theorem U2-Q.** Under the same conditions, with Theorem M's `Σ^{(n)}` for PomFRIT (`d = 2`, so
H₂³ weight `√2 + 2`):

    Adv^{omuf}_{PomFRIT}(A) ≤ Adv^{ompr⊕17-RO}_{UOV}(B'; ℓ) + (Σ^{(n)})² + ε_multi^{(n)} + n·ε_rec
                              + 2δ_stab + n·2^{−357} + ε_DS (+ ε_Sim).

*Proof.* As for U1-Q, with these changes.
- **Programming.** `B'` answers `H_T(x) := G(x, S(x; D_o))`, where `S` is the set of alive-tree
  prefixes, canonically encoded (≤ 17 values; `∅` if the chain or its trees are undefined).
  - Analysis: in the compressed `G`, cell `(x, ∅)` plays world R's `H_T(x)`. `Γ_D` swaps cells
    `(x, ∅) ↔ (x, S(x; D))` for all `x`. This is a basis permutation that fixes `|⊥…⊥⟩` and
    preserves the number of non-`⊥` cells, so (Γ1) and (Γ2) hold.
  - In world R only `(x, ∅)`-cells are ever filled. So `NN` counts exactly the values that change
    `S(x; ·)` at a filled `x`. These are §3.4's counts, so `δ_stab` is unchanged.
- **Good event.**
  - (i) is plain extraction success (Theorem M). Every known tree is alive, so the extracted
    prefix `r_i` lies in `S(x_i; D_o^{final})` automatically, and no Shift event arises.
  - (ii) is recording of `(x_i, ∅)` in world R. After transport it becomes the statement that
    `G(x_i, S(x_i; D_o^{final})) = h_i`.
- **`B'`'s output.** `B'` computes `S_i := S(x_i; D_o^{final})` by applying `Ext` to all `L` leaf
  commitments of `o_i`'s chain. These are diagonal measurements, so add `nL` to the `Ext` count in
  `ε_Sim`. `B'` then outputs `(x_i, S_i, r_i, s_i)`. ∎

### 4.5 Numbers and reading

- **Leading terms.**
  - U2-Q: `8(3.41q + 5.4n)²·2^{−128}`, i.e. `2^{−61.5}` at `q = 2^{30}` and `2^{−21.5}` at
    `q = 2^{50}`, plus `ε_multi`.
  - U1-Q adds `8(Q₂₃ + n)²·2^{−71}`: `2^{−28}` at `Q₂₃ = 2^{20}`, `2^{−18}` at `2^{25}`, `2^{−8}` at
    `2^{30}`.
  - With separate budgets, `q₂₃ ≤ 2^{20}` and all other hash queries `≤ 2^{50}`, U1-Q's `Σ_*²` is
    `≈ 2^{−22.5}`.
- **Tightness of U1-Q's term for this reduction.** The adversary commits seven 7-bit trees plus the
  8-bit tree (width 57, prefix `r_A`) and nine 7-bit trees (width 63, prefix `r_B`).
  - It queries `h = H_T(x)` and spends **one** Issuer query on `h ⊕ r_A`.
  - It then Grover-searches the counter for `Δ` in the minority accepting set
    (`|A| ≈ 2^{57}·Pr[open]`). That succeeds with probability `≈ 4q²·2^{57−128}` (`2^{−9}` at
    `q = 2^{30}`).
  - The forgery is honest, so not a break. But `B`'s programmed `E₁ = r_B` makes it useless to `B`.

  So `2^{−71}` per H₂³ query classically becomes `≈ q²·2^{−71}` quantumly, and U1-Q is
  reduction-tight up to the constant 2. As classically (pomfrit.md §6.3), we believe this is a
  reduction artifact. Pinning `r` to π₁ (pomfrit.md G1) would remove it.
- **What U1-Q and U2-Q do not need:** ZK, SE, or any mid-run measurement. Everything the reduction
  learns, it learns at the end.

**Confidence: medium-high.** The extraction and Lemma S parts reuse proven pieces. The assumption
forms are new, and the Lemma P-Q transport through `Γ` (the "Good (ii)" bookkeeping) is the most
delicate step. I checked it twice but it is paper only.

---

## 5. Ratatouille balance in the QROM

**Model** (ratatouille.md §2, §10).
- Proof oracles as in §1.
- KP800 and therefore `Com` and `Tag`: following ratatouille.md §10's stated modelling gap, `Com`
  and `Tag` are treated as independent quantum random oracles (heuristic). No quantum tool exists
  for an invertible random permutation with structured inputs.
- Signing is a classical oracle.

**(UF-Tag-Q).** UF-Tag (ratatouille.md §2.3) against a quantum adversary with quantum access to
`Tag`. Lemma 2.1's lazy-sampling reduction to A-OMPI does not lift, so UF-Tag-Q is the assumption
(ratatouille.md §10 already says so). Its RO form relates to A-OMPI as in §4.1's remark.

**Theorem R-Q.** Assume keys are separated. For every quantum adversary in BAL, with all
honest-client activity included in the counts, and with `n = N_I + N_S` (accepted issuance and
spend requests, issuance and spend relations together, `d̂ = 9`):

    Adv^{bal}_Q ≤ (Σ^{(n)})² + ε_multi^{(n)} + n·ε_rec + ε_Sim^{(n)} + Adv^{uf-tag-Q}(B) + (32/9)·q_K³·(2^{−256} + 2^{−360}) + ε_DS.

*Proof.* This is ratatouille.md Theorem 1's proof, unchanged except for the following.
- `B` runs the game with compressed oracles and runs honest clients itself, classically, knowing
  their witnesses. The Issuer verifies mid-run. `B` forwards signing calls to its classical
  `Sign` oracle and routes `Tag` queries to its quantum `Tag`.
- **No mid-run extraction.** The signing oracle's answers do not depend on extracted witnesses.
  At the end, `B` runs `E^{(n)}` on every accepted request. Mid-run verifications are covered by
  Lemma F^{(n)}.
  - (E1) is Theorem M, for all `n` proofs at once.
  - (E2) binding: with `Com` and `Tag` as QROs, Lemma T with `COL`, `ρ(s) ≤ s/|Y|`, gives
    `≤ (2√2·Σ_s√(s/|Y|))² ≤ (32/9)q_K³/|Y|` for `|Y| = 2^{256}` and `2^{360}`.
  - (E3) is a UF-Tag-Q forgery.
  - (E4) aborts are as classically.
- The accounting (Lean `Ratatouille.balance_le`) is deterministic and unchanged. ∎

**Numbers.** The extraction part is `2^{−60.4} + ε_multi` at `q = 2^{30}` and `2^{−20.4}` at
`q = 2^{50}`, `q_E = 2^{30}`. Honest proofs add `≈ 2^8` H₂³ queries and `≤ 4607` fetches each, so
`n` honest spends behave like `2^8·n` adversarial H₂³ queries. Binding is `2^{−164}` at
`q_K = 2^{30}` and `2^{−104}` at `2^{50}`.

**Confidence: high,** given UF-Tag-Q and the KP800-as-QRO heuristic (both from ratatouille.md).

---

## 6. Moussaka one-more unforgeability in the QROM

**Model** (moussaka.md §3).
- `Com` is concrete Keccak-p[800,12] with standard-model binding.
- CT-UF is a game with a classical signing oracle on arbitrary targets and no hash oracle.
- SHAKE256 key digests are a QRO (`ε_dig`).

**Theorem MO-Q.** For every quantum `A` in OMUF, with `n` = accepted issuance plus accepted
redemption proofs (both relations jointly, `d̂ = 9`):

    Adv^{omuf}_Q(A) ≤ (Σ^{(n)})² + ε_multi^{(n)} + n·ε_rec + ε_Sim^{(n)} + ε_dig^Q + Adv^{bind}_{Com}(B₁) + K·Adv^{ct-uf}_{UOV,Com,1}(B₂),

with `ε_dig^Q ≤ (32/9)·q_{256}³·2^{−256}` (Lemma T with `COL`). `B₁` and `B₂` are quantum
algorithms that run `A` once, then `E^{(n)}`. `B₂` makes as many `Sign` queries as `A` makes
accepted `Issue` queries.

*Proof.* This is moussaka.md Theorem 1's proof.
- `B₂`'s simulation (forward `Issue` to `Sign`) needs no extraction during the run (moussaka.md
  §8).
- Steps 2–4 use the extracted witnesses of all accepted proofs. Theorem M supplies them jointly.
  This replaces the classical `ε_ext^{iss} + ε_ext^{red}` with **one** `Σ^{(n)}` over both
  relations.
- `ε_dig` is needed for L4's statement binding, as classically.
- The Lean lemmas `selector_one_hot` and `exists_unsigned_of_card_lt` are deterministic and
  unchanged. ∎

**Remarks.**
- **No quantum-random-oracle assumption on UOV.** CT-UF has a classical oracle and a concrete
  `Com`, so `Adv^{ct-uf}` is a plain post-quantum assumption against quantum `B₂`. Only moussaka.md
  Lemma U, the heuristic link to one-more-UOV, would need a quantum random permutation.
- Theorem 3 (context binding via SE) would need Q5. That is out of scope here.

**Confidence: high,** given the stated assumptions.

---

## 7. Where `ε_multi` enters

| Theorem | `ε_multi` term | Cipher count that drives it |
|---|---|---|
| M | `ε_multi^{(n)} = min{ε^{free}(Q_E), ε^{H₄}(2Q_E+Q₄+1) + 2n·2^{−128}}` | `Q_E = q_E + n·K_V` (+ honest provers' fetches) |
| U1-Q, U2-Q | same, `n = ℓ+1` | `+ B'`'s `nL` `Ext`s enter `ε_Sim` only, not `ε_multi` |
| R-Q | same, `n = N_I + N_S` | `+ 4607` per honest proof |
| MO-Q | same, `n = n_iss + n_red` | `+ 4607` per verification |

- In every case `ε_multi` is the event `Bad_end` (two database keys agreeing on a leaf pair at an
  accepted `iv`). It is **one** event for all outputs: Q1's bounds hold "simultaneously for all
  commitments and all ι".
- `n` enters only through the counts and the readback term.
- A point-level bound from Q6 plugs in unchanged, as long as it bounds this same event for an
  algorithm with `Q_E` (fetch-counted) cipher queries.
- The PomFRIT reductions' coherent `E₁` evaluations make no cipher queries. They read `D_o`.

---

## 8. Lean (`lean/VoleMole/Seed/QMulti.lean`)

No `sorry`, no `axiom`. `#print axioms` shows only `propext`, `Classical.choice` and `Quot.sound`.

| Statement | Lean |
|---|---|
| Hybrid over oracle steps: `‖φ_T − ψ_T‖ ≤ Σ_s ‖(A_s − B_s)ψ_s‖` | `hybrid_le` |
| Conjugated run: `ψ_S = V ψ_R̃` | `conj_run` |
| Defect is a commutator: `‖(U − V⁻¹UV)ψ‖ = ‖(VU − UV)ψ‖` | `conj_defect_norm` |
| `[P,Z] = PZ(1−P) − (1−P)ZP`; `[1−2P, W] = −2[P, W−1]` | `comm_offdiag`, `swap_comm` |
| Orthogonal off-diagonal blocks cost their maximum | `offdiag_norm_le` |
| Density swap `Σ_v w_v Σ_{β∋v} a_β ≤ ρ Σ a_β` | `density_swap_le` |
| `8(5q+7n)² = 200q² + 560qn + 392n²` (·2^{−128}); values | `main_term_multi_eq`, `main_term_multi_at_2_30_n_2_20`, `main_term_multi_at_n_eq_q` |
| Lemma P-Q term `8Q₂₃²·2^{−71}` at `2^{30}`, `2^{20}` | `shift_term_at_2_30`, `shift_term_at_2_20` |
| `2L − 1 = 4607`; free `multi` with and without Lemma K | `fetch_keys`, `multi_free_fetch_at_n_2_20`, `multi_free_blocks_at_n_2_20` |
| Squared cipher part of `δ_stab` at `2^{50}` | `stab_cipher_at_2_50` |

Reused unchanged:
- `QROM.telescope` and `QSimExt.telescope_with_neutral` (Lemma T);
- `QROM.conj_commutator_le` (Lemma S step 3);
- `QROM.card_B3_le` (H₂³ count);
- `PomFRIT.minority_card_le` and `fixed_outside_prefixGroup` (Lemma P-Q);
- the protocol accounting lemmas.

Not in Lean: the quantum probability steps (block decomposition, the final-measurement arguments
and the union bounds), as in Q2 and Q5.

---

## 9. Gaps and confidence

| Step | Status | Confidence |
|---|---|---|
| §2.2 one property for all chains, relations typed by H₂¹ length | proof; uses domain-separation.md's length fact | high |
| Lemma F^{(n)}, sharing, mid-run verification | proof (Q2 Lemma F + Q5 Lemma R) | high |
| §2.4 `Ext` order and joint event | exact commutation (Q1 (I1)) | high |
| Lemma K (fetch per key) | proof | high |
| Theorem M | assembly | high |
| Lemma S (a) and (b) | proof; algebra in Lean | high |
| Cor. S.2, Remark S.3 (`δ → 4√(2p)`) | proof sketch via Lemma S | medium-high |
| §3.4 `ρ_stab` counts | Q2's counts on named chains | medium-high |
| Lemma P-Q | Lemma P's deterministic core (Lean) + Lemma T | high |
| U1-Q, U2-Q | proof; new RO-form assumptions; transport bookkeeping | medium-high |
| (A-OMPR) ⇒ (A-OMPR-RO) via small-range | remark only, constant not checked, inefficient | medium |
| R-Q, MO-Q | direct lift | high (given their assumptions) |

**Gaps, stated plainly.**
1. **`ε_multi`** is still Q1's key-level bound. Every theorem here is vacuous at `q_E ≳ 2^{40}`, or
   at `q_E + n·4607 ≳ 2^{37}` for the H₄ version. Q6's work would remove this.
2. **QROM assumptions.**
   - A-OMPR-RO and A-OMPR⊕τ-RO (PomFRIT) and UF-Tag-Q (Ratatouille) are quantum-oracle
     assumptions. Their classical forms are the protocols' stated assumptions.
   - I found no tight reduction from the `n`-target forms.
   - Ratatouille's KP800-as-QRO is a heuristic inherited from ratatouille.md.
3. **U1-Q's `8Q₂₃²·2^{−71}`** limits the standard-assumption result to about `2^{30}` H₂³ queries.
   It is reduction-tight (§4.5), so a better bound needs a different reduction or a protocol change
   (pomfrit.md G1).
4. **Efficiency of the PomFRIT reductions.** Coherent `E₁` costs `O(q·L)` database work per `H_T`
   query, which is polynomial but quadratic in `q` overall. With Q4's `S*` the cipher part is
   efficient. Hash databases use DFMS's sparse representation (App. B).
5. **Non-parallel queries only,** as in Q2 and Q5.
6. **SE/ZK-dependent properties** (Ratatouille N2a, Moussaka Thm 3, PomFRIT blindness) are not
   covered here. See Q5 and `lean/docs/zk-qrom.md`.
7. **Literature.** I did not find coherent database-controlled programming (Lemma S) stated in
   DFMS22, DFM20, GHHM21 or CFHL21. It may exist elsewhere, e.g. in work on QROM blind signatures
   or one-more problems. No papers were downloaded for this task. Citations are those already
   verified in Q2 and Q5, plus Zhandry 2012, which is cited from memory for the small-range
   remark.

## References

- [CFHL21] Chung, Fehr, Huang, Liao, *On the Compressed-Oracle Technique, and Post-Quantum
  Security of Proofs of Sequential Work*, EUROCRYPT 2021, arXiv 2010.11658. Lemma 5.6 (telescoping).
- [DFMS22] Don, Fehr, Majenz, Schaffner, *Online-Extractability in the Quantum Random-Oracle
  Model*, EUROCRYPT 2022, arXiv 2103.03085. §2.2, eq. (8), eq. (12), Cor. 2.2, Lemma 3.3, Thm 4.3,
  App. B.
- [DFM20] Don, Fehr, Majenz, *The Measure-and-Reprogram Technique 2.0*, CRYPTO 2020. Only as the
  rejected alternative of §3.5.
- [GHHM21] Grilo, Hövelmanns, Hülsing, Majenz, *Tight Adaptive Reprogramming in the QROM*,
  ASIACRYPT 2021, arXiv 2010.15103. Contrast in §3.2 and §3.5.
- [Zha12] Zhandry, *Secure Identity-Based Encryption in the Quantum Random Oracle Model*,
  CRYPTO 2012. Small-range distributions; §4.1 remark only, cited from memory.
- [Zha19] Zhandry, *How to Record Quantum Queries*, CRYPTO 2019.
- Repo: `lean/docs/extraction/Q1-quantum-ideal-cipher.md`, `Q2-qrom-fiat-shamir.md`,
  `Q4-efficient-cipher-simulation.md`, `Q5-qrom-simulation-extractability.md`;
  `lean/docs/security/pomfrit.md`, `ratatouille.md`, `moussaka.md`, `domain-separation.md`;
  `lean/VoleMole/Seed/{QROM,QSimExt,QMulti}.lean`, `lean/VoleMole/Protocols/PomFRIT.lean`.
