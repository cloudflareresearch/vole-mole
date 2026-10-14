# Q5: simulation-extractability against quantum adversaries

Status: **[paper]**, with **[Lean]** for the bookkeeping (`lean/VoleMole/Seed/QSimExt.lean`, no
`sorry`, no `axiom`; check with `cd lean && lake env lean VoleMole/Seed/QSimExt.lean`). This is
README §L9, "Simulation-extractability in the QROM", which Q2 §11 gap 3 left open. It lifts L8 to
quantum adversaries. Hashes are quantum random oracles, and AES is a quantum ideal cipher with Q1's
key-level compressed oracle. Notation, counts and lemma names follow Q2 and Q1. `L8` means
`L8-simulation-extractability.md`.

## 0. Verdict

**What is proved (Theorem Q5, §3).** In the strong-SE game, a quantum adversary gets simulated
proofs for statements of its choice. A straight-line extractor in Q2's style recovers a witness
from every fresh accepting `(x, b₁, b₂, π)`. It runs the game once with compressed oracles,
answers the simulator's programmed H₂³ points from a classical table, and applies Q1's `Ext` to the
outputs' hidden-leaf commitments after the verifier. The bound is

    Pr[A wins strong SE]  ≤  Σ_SE² + ε_bind^C(T') + ε_rec' (+ ε_Sim),

- `Σ_SE` is Q2's `Σ`, evaluated on the whole game (adversary, simulator, and the verifier on the
  outputs).
- `ε_bind^C(T')` is Q1's `multi`-type event, on a tweak set enlarged to every GGM tweak. It is
  needed only for strong SE; weak SE uses Q2's leaf-tweak set.
- `ε_rec'` (recording) and `ε_Sim` (efficient cipher simulation, Q4) are negligible.

The new ingredients:

1. **Programming is free in the bookkeeping (Lemma P).** The reprogrammed H₂³ can be implemented
   exactly: compressed off the programmed set `Prog`, and a classical table on `Prog`. This is
   GHHM's "reset the register" implementation of reprogramming, in bypass form. Once `B₃` excludes
   programmed points, a programming step never moves amplitude into the bad property. So Lemma T
   charges it 0, and no reprogramming loss enters SE. The GHHM loss belongs to the ZK hop (§9),
   not to the SE game.
2. **The simulator's own chains cost nothing (Lemma G).** With the punctured simulator `Sim°`,
   every tree of a simulated chain has a dead hidden leaf, so `|A| ≤ 1` with no KOS or QuickSilver
   hypothesis. Guarding `B₁`, `B₂` and `B_l` by "some tree is known" makes the simulator's H₂¹, H₂²
   and H_comb queries cost only collision terms.
3. **Case (P) is closed by recording, not by abort checks (Lemma F', case P).** Every classical
   query of the simulator stays exactly recorded in the purified oracle. So a fresh accepted
   output on a programmed point gives a `COL` in the database, or two keys agreeing on a GGM pair
   at the simulator's `iv`, or it equals the simulated triple.

**Numbers at λ = 128, q = 2^30, Q_S = 2^30.**
- `Σ_SE² ≈ 2^{−60.4}` with `Sim°`, the same as Q2's main term, and `2^{−59.4}` with the
  unpunctured `Sim` (**[Lean]** `main_term_punctured_at_2_30`, `main_term_unpunctured_at_2_30`).
- **`ε_bind^C` is vacuous, and so the whole theorem is vacuous at these parameters.** Each
  simulated proof makes `c_E ≈ 2^{17}`–`2^{18}` cipher queries: the GGM co-path, the leaf
  commitments and the leaf VOLE PRGs. So the database sees `Q_E ≈ 2^{48}` cipher queries. Q1's key-level
  `multi` bounds are vacuous beyond about `2^{37}`:
  - the free-iv bound is `≈ 2^{17.8}` (**[Lean]** `multi_free_vacuous_at_2_48`);
  - the H₄ bound is inapplicable, since `θ > 1/2` (**[Lean]** `theta_gt_half_at_2_48`).
- **The step that fails is exactly Q1/Q4's open `multi` lemma, now driven by the simulator's
  classical cipher queries.** At `q = 2^30` the theorem gives:
  - `≈ 2^{−59}` for `Q_S ≤ 2^{12}` (strong SE);
  - `≈ 2^{−60}` for `Q_S ≤ 2^{14}` (weak SE: `ε_bind^C(T) ≈ 2^{−63.4}` there);
  - a vacuous bound for `Q_S ≳ 2^{20}`.

  §3.1 has the table, and §12 has the precise missing lemma.

**No classical-L8 term survives as a loss.**
- `ε_prog` is 0: there is no abort, and the simulator overwrites.
- `ε_hk` is 0: Lemma G charges simulated chains generically, so even the unpunctured `Sim` is
  covered.
- `ε_H` becomes Lemma D, `≈ 8Q_E²·2^{−256}` per hidden leaf.
- `ε_eq` becomes `COL` plus `ε_bind^C`.

**Literature.** I found no paper that combines compressed-oracle online extraction with a
reprogramming simulator to get SE in the QROM. The closest ones:
- Unruh's EUROCRYPT 2015 transform has simulation-sound online extractability, but the extractor
  inverts an oracle that the simulator never programs;
- DFMS22 does online extraction without simulation;
- Majenz–Sharma 2026 do Fischlin in the QROM, with ZK via GHHM and extraction via a compressed
  oracle, proved separately.

I could not locate a paper titled "Fiat–Shamir in the QROM: simulation-sound extractability"
(§2).

---

## 1. Game, oracles, simulator

### 1.1 The game `SE^Q`

This is L8 §2 with quantum access.
- `A` gets superposition access to every hash (H₁, H₂⁰/H₂⁴, H₂¹, H₂², H_comb, H₂³, H₃, H₄, H₅) and
  forward and inverse superposition access to `E`.
- `A` makes classical calls `Prove(x, b₁, b₂)`. Each returns `π ← Sim(x, b₁, b₂)` and records
  `(x, b, π)` in `S`. The statement `x` may be false and may be chosen adaptively.
- `A` outputs `n_out` triples.
- `A` wins **strong SE** if some output `∉ S` is accepted by `V` and `R(x, E(…))` fails. It wins
  **weak SE** if additionally `(x, b)` differs from every simulated `(x_s, b_s)`.

The queries are non-parallel, with a fixed oracle schedule (as in Q2 §2). The counts:
- `q_o` is `A`'s count for oracle `o`, and `q = Σ_o q_o`;
- `Q_S = q_S` is the number of `Prove` calls;
- `c_o` is the simulator's per-proof count on oracle `o`;
- `c_E` is the simulator's per-proof cipher count: about 4.6·10³ GGM blocks, plus
  `2304·(2 + ⌈ℓ̂/128⌉)` leaf blocks, with `ℓ̂ ≲ 7.3·10³`. This is estimated from the proof sizes
  in `docs/perf.md` (Ratatouille spend is the largest), so `c_E ≤ 2^{18}`.

### 1.2 How the extractor runs the game

The challenger (= the extractor `E`) simulates **every** oracle for **everyone**: `A`, `Sim`, and
`V` on the outputs.
- Hashes use DFMS compressed oracles.
- The cipher uses Q1's key-level compressed oracle, or Q4's `S*` when efficiency matters.
- **H₂³ is reprogrammable.** `E` keeps a classical table `T` of programmed points `Prog`. A query
  at `x₃ ∈ Prog` returns `T[x₃]`, and a query at `x₃ ∉ Prog` goes to the compressed H₂³. A
  superposition query does this controlled on `x₃`.
- `Sim` sends `(x₃, y)` pairs to `E`, which writes them into `T`, overwriting any earlier entry.

`E` uses no coins of `Sim` and no trapdoor. It only measures its own databases at the end. This is
the standard QROM arrangement for online-extractable NIZKs, where extractor and simulator share
the oracle simulation (Unruh 2015).

After the run, `E` runs `V` on each output and reads off Δ, `iv` and the hidden-leaf commitments.
It applies `Ext_{(iv, twk_i)}` (Q1 §3) to each of them, at most `τ` per output. Then it forms the
candidates `u_i ⊕ c_i ⊕ d` and outputs the first one that satisfies R (Q2 §6.1, unchanged).

### 1.3 Simulators

- **`Sim°` (punctured; L8 §3.3, lean/docs/zk.md H7).** It samples the grinding outcome, makes the co-path
  seeds uniform, and makes each hidden-leaf commitment `ρ_{s,i}` a uniform 2λ-bit string. It
  computes everything else as `V` would, through the shared oracles. Then it programs
  `H₂³(chall₂_s ‖ qs_check_s ‖ ã_s ‖ c) := Δ_c` for `c ≤ ctr_s`, with `Δ_{ctr_s} = Δ_s ∈ Good` and
  `Δ_c ∈ Goodᶜ` for `c < ctr_s`. **It never aborts:** in the QROM "already defined" cannot be
  checked, so it overwrites.
- **`Sim` (lean/docs/zk.md §5).** The same, except that the tree is honest from a uniform `seed*`. This adds
  cipher queries under the hidden keys.

The proof uses only these properties of the simulator:
- **(S1')** It programs only H₂³, at points whose prefix is its own `chall₂_s`. §8.3 covers
  simulators that also program H₂¹, H₂² or H₄ with fresh uniform values.
- **(S2)** Exactly one programmed value per proof lies in `Good`.
- **(S3')** Every other oracle use is a **classical** query to the shared oracles.
- **(S5)** Its proofs are accepted.

(S3') is what makes the simulator's queries visible in the databases. For `Sim°` they are a
subset of what `V(π_s)` would query, so this matches L8's "public log" idea.

---

## 2. Literature: what exists and what is used

| Result | Used for | Notes |
|---|---|---|
| Zhandry 2019; DFMS22 §2.2, eq. (8), Cor. 2.2, Lemma 3.3 (arXiv 2103.03085) | compressed oracle; recording; block decomposition; local commutator | as in Q2 |
| CFHL21 Lemma 5.6 (arXiv 2010.11658) | telescoping | Q2 Lemma T step 1 |
| Q2 Lemma T | the transition-capacity bound | reused, with neutral steps (Lemma P) |
| Q1 Lemma 3.1, (F1), (F2), P3, Thms 5.1/5.2 | cipher commutator, densities, recording, `multi` | Thm 5.2 used with an enlarged tweak set |
| GHHM21, *Tight adaptive reprogramming in the QROM* (ASIACRYPT 2021; arXiv 2010.15103), §5.1 and Thm 1/Prop. 2 | §5.1: reprogramming in the superposition oracle "discards the contents of register `F_x` and replaces them with a fresh `|φ₀⟩`". Lemma P is the compressed, bypass form of this. Thm 1, `(3/2)Σ_r√(q̂_r p_max^{(r)})`, is the reprogramming loss | used only in §9 (the ZK hop), not in the SE bound |
| Unruh, *NIZK proofs in the QROM*, EUROCRYPT 2015 | structural precedent: simulation-sound online extractability, where the extractor's oracle (inverted) is disjoint from the simulator's programmed oracle | **from memory**: the PDF was not retrievable here, so no theorem numbers are given. Our analogue: the extractor's bad property reads H₂³ only via `B₃`, from which programmed points are excluded |
| Majenz–Sharma, *Security of the Fischlin transform in the QROM*, arXiv 2602.17307 | precedent for "ZK via GHHM plus extraction via compressed oracle" | read: they prove the two properties separately and state no SE |
| Chiesa–Manohar–Spooner TCC 2019 | QROM PoK for Micali/BCS | no SE (per abstract); not retrieved |
| Gao 2015, quantum union bound | proposed route for the open lemma (§12) | not used in the proof |

**Not found.** The brief mentions "Don–Fehr–Majenz, *Fiat–Shamir in the QROM: simulation-sound
extractability*". I found no such paper. DFMS22 has no simulation section (the full text was
searched for "simulat"; every hit concerns the RO simulator). The SE statements for FS-type
NIZKs in the QROM that I found are Unruh's (a different transform) and classical-ROM ones
(Chiesa–Fenzi; eprint 2024/1549 for Micali/BCS). Treat "QROM SE for FS with a compressed-oracle
extractor" as not in the literature, as far as I could check.

---

## 3. Main theorem

Write `Σ_Q2(Q₂₁, Q₂₂, Q_c, Q₂₃, Q₁, Q₀, Q_E)` for the bracket of Q2 Theorem 7.1, so `Σ = 2√2·[…]`.
Split each count into `Q_o = Q_o^A + Q_o^S`:
- `Q_o^A` is `A`'s queries plus `V`'s on the `n_out` outputs, including Q2 §3's reductions:
  - `Q₂₁^A = q₂₁ + n_out`, `Q₂₂^A = q₂₂ + n_out`, `Q₂₃^A = q₂₃ + n_out`;
  - `Q_c^A = q_c + 2q₂₃ + n_out`;
  - `Q₁^A = q₁ + n_out(τ+1)`, `Q₀^A = q₀ + 2n_out`.
- `Q_o^S = q_S·c_o` is the simulator's:
  - `Q₂₃^S = 0`, since programming is not a query;
  - `Q₂₁^S = Q₂₂^S = Q_c^S = q_S`;
  - `Q₁^S = q_S(τ+1)`, `Q₀^S = q_S`, `Q₄^S = 3q_S` (Q2 §3.1);
  - `Q_E^S = q_S·c_E`.

**Theorem Q5.** For every quantum `A` in `SE^Q` with the counts above, and `E` as in §1.2:

    Pr[A wins strong SE]  ≤  Σ_SE² + ε_bind^C(T') + ε_rec' (+ ε_Sim),
    Pr[A wins weak SE]    ≤  Σ_SE² + ε_bind^C(T)  + ε_rec' (+ ε_Sim),

where, for **`Sim°`**:

    Σ_SE := 2√2·[ Q₂₁^A·√(ε_KOS + (Q₂₁+Q₂₂)2^{−1088}) + Q₂₂^A·√(ε_QS + (Q₂₂+Q₂₃+Q_c)2^{−448})
                 + Q_c^A·√(2^{−128} + Q₂₃·2^{−128M}) + Q₂₃^A·√(max(d,1)·2^{−128})
                 + Q₂₁^S·√((Q₂₁+Q₂₂)2^{−1088}) + Q₂₂^S·√((Q₂₂+Q₂₃+Q_c)2^{−448})
                 + Q_c^S·√(Q₂₃·2^{−128M})
                 + Q₁·√((Q₂₁+18Q₁)2^{−256}) + Q₀·√((Q₂₁+Q₂₂+Q₀)2^{−256}) + Q_E·√(Q₂₁·L·p) ]
             + 3q_S·ε_G,       ε_G := τ·(√(Q_E·2^{−256}) + 2√2·c_E·√p)   (Lemma G).

For the unpunctured **`Sim`**, move the three `S` terms into the `A` terms (`Q₂₁^A += q_S`,
`Q₂₂^A += q_S`, `Q_c^A += q_S`) and drop `ε_G`.

The remaining terms:
- `ε_bind^C(T') := Pr[Bad_{T'}]` (§7.2), where `T'` is the set of all GGM node and leaf tweaks,
  `|T'| = 2303 + 17 = 2320`:

      ε_bind^C(T') ≤ min{ (32/9)·Q_E³/(N−1),  ε_multi^{H₄}(q_{H₄}; |T'|) },
      q_{H₄} := 2Q_E + Q₄ + 2Q₂₁ + 1,

  with `ε_multi^{H₄}(q; |T|) = (e q²√(10|T|p) + 4e q√(10|T|/N)·θ + qθ^{2^{31}})² + 2^{−127}`
  (Q1 Thm 5.2; linear in `|T|` to leading order), valid for `θ = 2e√30·q^{3/2}/√N ≤ 1/2`.
  `ε_bind^C(T)` is the same with Q2's leaf-tweak set, `|T| = 17`.
- `ε_rec' := n_out·ε_rec^{Q2} + q_S(τ+6)·2^{−255} + q_S·2^{13}·2p`. This is recording of `V`'s
  queries on the outputs, as in Q2 §6.2, and of `Sim`'s queries (Lemma R).
- `ε_Sim ≤ 2^{−172} + τ·n_out·Q_E·δ` with Q4's `S*` (Q4 Thm C), `δ = 8√(2p)`.

The bound holds for all `n_out` outputs simultaneously.

### 3.1 Numbers (λ = 128, `d = 9`, `L = 2304`, `M = 45`, `c_E = 2^{18}`, `q = 2^{30}` on every oracle)

| `Q_S` | `Q_E` | `q_{H₄}` | `θ` | `Σ_SE²` (`Sim°`) | `ε_bind^C(T)` (weak) | `ε_bind^C(T')` (strong) | total, strong |
|---|---|---|---|---|---|---|---|
| 0 (Q2) | `2^{30}` | `2^{32.3}` | `2^{−10.6}` | `2^{−60.4}` | `2^{−70.3}` | `2^{−63.2}` | `2^{−60.2}` |
| `2^{12}` | `2^{31.0}` | `2^{32.8}` | `2^{−9.9}` | `2^{−60.4}` | `2^{−67.9}` | `2^{−60.8}` | `2^{−59.6}` |
| `2^{14}` | `2^{32.3}` | `2^{33.7}` | `2^{−8.6}` | `2^{−60.4}` | `2^{−63.4}` | `2^{−56.3}` | `2^{−56.2}` |
| `2^{16}` | `2^{34.1}` | `2^{35.2}` | `2^{−6.3}` | `2^{−60.4}` | `2^{−55.9}` | `2^{−48.8}` | `2^{−48.8}` |
| `2^{18}` | `2^{36.0}` | `2^{37.1}` | `2^{−3.5}` | `2^{−60.4}` | `2^{−46.6}` | `2^{−39.5}` | `2^{−39.5}` |
| `2^{20}` | `2^{38.0}` | `2^{39.0}` | `2^{−0.6}` | `2^{−60.4}` | n/a; free `2^{−12.2}` | n/a; free `2^{−12.2}` | `2^{−12.2}` |
| **`2^{30}`** | `2^{48.0}` | `2^{49.0}` | `2^{14.4}` | `2^{−60.4}` (`Sim`: `2^{−59.4}`) | **vacuous** (free `2^{17.8}`) | **vacuous** | **vacuous** |

The `T'` column uses the leading terms scaled by `|T'|/|T| = 2320/17 ≈ 2^{7.1}`. The other terms
at `Q_S = 2^{30}`:
- the cipher-alignment part of `Σ_SE²` is `2^{−114.8}`;
- `3q_S ε_G` adds `< 2^{−97}` to `Σ_SE²`;
- Lemma D is `2^{−157}` per hidden leaf;
- `ε_rec' ≈ n_out·2^{−128}`;
- `ε_Sim ≈ 2^{−72.4}`.

(These were computed by a short script; the Lean file checks the main term, the dead-leaf bound,
the free-`multi` vacuity and `θ > 1/2`.)

**Reading.** Apart from `ε_bind^C`, simulated proofs are free: `Σ_SE²` stays at Q2's `2^{−60.4}`.
The whole price of SE is that each simulated proof touches about `2^{18}` cipher keys' worth of
queries, and Q1's key-level `multi` bounds grow like `Q_E³/N` (free) or `q⁵/N²` with
`q ≲ 2^{37}` (H₄). §12 states the lemma that would remove this.

---

## 4. Lemma P: programming under compressed oracles

**Lemma P1 (exact implementation).** The game's H₂³ is `H` overwritten on `Prog` by `T`, with each
overwrite at the moment `Sim` programs. The following is perfectly indistinguishable from it, for
the joint state of `A`, `Sim`, `V` and every other oracle:
- run a compressed oracle for `H`;
- route queries at `x₃ ∈ Prog` to the classical table;
- never touch the frozen cell `D_{x₃}` again.

*Proof.* Purify `H` as `⊗_x |φ₀⟩_{F_x}`. GHHM §5.1 implements "reprogram `x` to a fresh value" by
moving `F_x` into a discarded register and inserting a fresh `|φ₀⟩`. Programming to the
simulator's classical `y` is a fresh register measured at `y`, or equivalently the classical value
`y` itself. In the bypass implementation the old `F_x` stays in place but is never acted on again,
because every later query at `x` is controlled to use `T`. That is the same as discarding it. The
compressed form is obtained by conjugating with `F^{⊗}` (Q2 §2), which commutes with routing,
since routing is controlled on the classical register `T` and the query input. ∎

**Lemma P2 (programming is neutral).** Let `P(D, T)` be any database property that reads `T` only
through `Prog(T)`, and such that `Prog ⊆ Prog'` implies `P(D, T') → P(D, T)`. Let `G` be the
programming step `|D, T⟩ ↦ |D, T'⟩`, which writes into a fresh table slot. Then
`P·G·(1 − P) = 0`. So in Lemma T a programming step has transition bound 0, and it does not
increase `‖PΨ‖`.

*Proof.* `G` is a relabelling of basis states, and a basis state can be bad after `G` only if it
was bad before. **[Lean]** `relabel_neutral`, `neutral_le`, `telescope_with_neutral`. ∎

**Why GHHM's cost does not appear.** GHHM bounds the distinguishability of "programmed" from
"not programmed". The SE game is *defined* with the programming simulator, and Theorem Q5 bounds a
probability in that game. Nothing is compared to an unprogrammed world, so no reprogramming loss
arises. A loss arises only when an application swaps real proofs for simulated ones (§9).

**What this needs from `P`.** `P` must not *reward* programming. `B₃` (Δ accepted and `E` fails)
is the only component of Q2's `P` that reads H₂³. Lemma P2 applies once `B₃` is restricted to
`x₃ ∉ Prog` (§5). We must then show separately that a fresh output never sits on a programmed
point. That is Lemma F' case (P), and it is the quantum form of L8's case (P).

---

## 5. The bad property `P'`

All definitions are those of Q2 §5, in the reduced world of Q2 §3, with three changes.
1. **Programmed points excluded.** `B₃(c, x₂, x₃, l)` is required only for `x₃ ∉ Prog`. Cells
   `(x₃, l)` with `x₃ ∈ Prog` are frozen, and `P'` ignores them.
2. **Guards.** Let `known(c)` be the set of trees of `c` with no dead leaf, in the current
   database (Q2 §5.2). Then:
   - `B₁'(c) := known(c) ≠ ∅ ∧ B₁(c)`;
   - `B₂'(c,x₂) := known(c) ≠ ∅ ∧ B₂(c,x₂)`;
   - `B_l'(c,x₂) := known(c) ≠ ∅ ∧ B_l(c,x₂)`.
3. **No time.** As in Q2, chains, trees, committed data, alive and dead are functions of the
   current database.

So `P' := COL ∨ ∃c B₁'(c) ∨ ∃(c,x₂) [B₂' ∨ B_l'] ∨ ∃(c,x₂,x₃∉Prog,l) consistent: B₃`.

### 5.1 Non-neutral counts for queries (worst case over `D_{−x}`)

Each count is Q2 §5.4's, with these changes.
- **(N-H₂¹'), (N-H₂²), (N-H_comb).** Unchanged, with `B·` replaced by `B·'`. The guard
  `known(c)` is a function of `D_{−x}`, because the cell does not affect alive status. So the
  bounds are Q2's, or the collision part alone when `known(c) = ∅`.
- **(N-H₂³'), cell `(x₃, l)` with `x₃ ∉ Prog`.** If the label is inconsistent, or `B₁'`, `B₂'`
  or `B_l'` holds, every value is neutral. Otherwise:
  - if `known(c) = ∅`, every tree has a dead leaf. A dead leaf must be hidden on `A`, so every tree
    is fixed and `|A| ≤ 1`;
  - if `known(c) ≠ ∅`, then `¬B₁ ∧ ¬B₂ ∧ ¬B_l` and Q2's L6 argument give `≤ max(d,1)`.

  **[Lean]** `card_B3_le_guarded`, `card_acc_le_one_of_all_fixed`. So `ρ₂₃ ≤ max(d,1)·2^{−128}`,
  as in Q2.

  For `x₃ ∈ Prog` the query does not act on `D` (table lookup), so the transition is 0.
- **(N-E).** Unchanged: `NN ⊆` the values aligned with some chain target, so
  `ρ_E ≤ Q₂₁·L·p`. A non-aligned key value changes no alive status. So it changes neither
  `known(c)` nor any guard, `A` or `Ext_D`. **This count is the quantum dead-leaf argument for
  simulated hidden leaves:** reviving `ρ_{s,i}` needs an aligned value (Lemma D).
- **(N-H₁), (N-H₂⁰), (N-H₄, N-H₃, N-H₅).** Unchanged.

### 5.2 Lemma G (the punctured simulator's own queries)

**Lemma G.** Run Lemma T on `P'`. Consider a query step of `Sim°` on its own chain `c_s`: its
H₂¹' query, its H₂² query, or its H_comb query. The transition amplitude is at most

    2√2·√(collision part of ρ_o) + ε_G,     ε_G := τ·(√(Q_E·2^{−256}) + 2√2·c_E·√p).

*Proof.* Let `G` be the diagonal projector "no key in the database is aligned with any `ρ_{s,i}`
at `(iv_s, twk_i)`". On `G`, every tree of `c_s` has a dead leaf (its hidden leaf), so
`known(c_s) = ∅`. Then `B₁'(c_s)`, `B₂'(c_s, ·)` and `B_l'(c_s, ·)` are false whatever value the
cell takes. `G` reads only cipher registers, so it commutes with the hash query and with `P'`.
Hence

    ‖P' cO (1−P') Ψ‖ ≤ ‖P' cO (1−P') G Ψ‖ + ‖(1−G) Ψ‖.

The first term is Q2's block bound restricted to `D_{−x} ∈ G`, which leaves only the collision
part.

For the second term:
- `ρ_{s,i}` is `Sim°`'s fresh uniform 256-bit string, sampled within the same `Prove` call. It is
  held in a classical register, so the branches for different values are orthogonal.
- At sampling time, `E_ρ‖Π_{alive(ρ)}Ψ‖² ≤ #keys·2^{−256} ≤ Q_E·2^{−256}`, because each key has
  one `f_ι` value.
- Each of the `≤ c_E` cipher queries `Sim°` makes before its H₂¹, H₂² or H_comb query raises the
  aligned amplitude by at most `2√(2p)` (Q1 Lemma 3.1, with the fibre of a fixed target, (F1)).
- Take a union over the `τ` trees, in amplitude. ∎

The adversary's own queries on `c_s` all come *after* the `Prove` call. Its H₂² queries (a new
instance, a new `b₂`) and its H₂³ queries (a new `ctr` or `ã`) are covered by the worst-case counts
of §5.1, with the guard false or true. If the adversary revives a hidden leaf, `known(c_s)` becomes
non-empty. That transition is (N-E): it costs alignment density only, whatever `chall₁_s` is.

For the unpunctured `Sim`, `known(c_s) ≠ ∅`, because the hidden keys are in the database. Its
three queries are then charged at full `ρ` (`ε_KOS`, `ε_QS`, `2^{−128}`), which is the
substitution stated in Theorem Q5. No other change is needed.
- L3 holds for `c_s`: its committed data, including the uniform `c_mult` and the honest tree, is
  fixed in `D_{−x}` at `Sim`'s H₂¹ query.
- L4 holds: `w* = u* + d`, with the uniform `d`, is fixed at `Sim`'s H₂² query.
- L6 gives a witness candidate or `|A| ≤ d`.

**This removes classical L8's `ε_hk`.** L8 needed the hidden leaves dead only because it did not
charge L3/L4 to the simulator's chains (L8 §9.3). The same remark applies classically.

---

## 6. Lemma D: simulated hidden leaves are dead

**Lemma D.** Let `ρ` be `Sim°`'s uniform hidden-leaf commitment, sampled at time `t₀`, and let `ι`
be classical and fixed (for example `(iv_s, twk_i)`). Let `Q_E^{>t₀}` be the number of cipher queries
after `t₀`. Then

    Pr[the final measured key database has a key k with σ_k(x₀(ι)) ‖ σ_k(x₁(ι)) = ρ]
        ≤ ( √(Q_E·2^{−256}) + 2√2·Q_E^{>t₀}·√p )²  ≈ 8Q_E²·2^{−256}.

*Proof.* Let `P_ρ` be the diagonal projector "some key is aligned with `ρ` at `ι`".
- At `t₀`, `E_ρ‖P_ρΨ_{t₀}‖² ≤ (#keys)·2^{−256}`, because `ρ` is independent of `Ψ_{t₀}` and each
  key has a single `f_ι` value.
- By Q1 (F1), the fibre of a fixed `ρ` has density `p` if `ρ₀ ≠ ρ₁`, and 0 otherwise (nothing
  opens `ρ₀ = ρ₁`). So each later cipher query moves at most `2√(2p)` into `P_ρ`, by Q1
  Lemma 3.1. Inverse queries are included.
- Other steps commute with `P_ρ`: hash queries, programming, `Ext`, adversary unitaries.
- Telescope, then use Minkowski over `ρ`. ∎

At `Q_E = 2^{48}` this is `≤ 2^{−156}` per leaf (**[Lean]** `dead_leaf_at_2_48`), and `2^{−122.9}`
over the `τ·Q_S` hidden leaves. This is "Q1's dead-leaf bound applied to uniform strings", in the
form Thm 4.2(a) has with `q₂ = Q_E`.
- Copying `ρ` into a tree with a different `iv` changes `ι`. Inside the proof, alignment with
  every chain's targets under its own `iv` is counted by (N-E).
- A key found for `ρ` under a new `iv` makes that leaf *alive*, so `Ext` returns the key. That is
  harmless. Being dead matters only for pinning the simulator's own chain (Lemma G, §5.1).

---

## 7. From "a fresh output is accepted and `E` fails" to `D ∈ P'`

### 7.1 Lemma R (recording)

Every classical query of `V` on the outputs and of `Sim` is recorded in the final measured
database, except with probability `ε_rec'`.

*Proof.* For a hash query with answer `y`, the purified register is projected onto `|y⟩`. Every
later purified query is diagonal in the value basis, so the register stays `|y⟩` exactly. The
final compressed measurement gives `y` with probability `|⟨y|F|y⟩|² ≥ 1 − 2^{1−n}`.

For a cipher check of `(k, ι, t)`, the purified `D_k` is projected onto `Im Π_{ι,t}`. Every later
purified forward or inverse query is diagonal in `σ`, so it stays in `Im Π`. On `Im Π`, the
operator `ΠF` has smallest singular value `1 − ‖Πu‖² = 1 − p`, so the final measurement keeps the
alignment with probability `≥ 1 − 2p` (Q1 P3).

Take a union bound over the final-measurement events: `V`'s as in Q2 §6.2, plus `q_S(τ+6)` hash
records and `≤ q_S·2^{13}` cipher records of `Sim`. ∎

This is stronger than Q2 needed. **Records made mid-run persist exactly**, so the simulator's
cells can be used at the end with no "forgetting" transition.

### 7.2 The event `Bad_{T'}`

`Bad_{T'}`: some `iv` in the H₄ database and some `twk ∈ T'` have two distinct database keys `k ≠ k'`
with `σ_k, σ_{k'}` agreeing on `{x₀(iv, twk), x₁(iv, twk)}`. This is Q1 Thm 5.2's `Bad` with
`T ↦ T'`, so Pr[Bad_{T'}] is bounded as in §3. The bound covers any algorithm that makes `Q_E`
cipher queries and `Q₄` H₄ queries. The programmed H₂³ is part of that algorithm: it is simulated
from randomness independent of `(Π, H₄)`.
- `MULTI_end` of Q2 Lemma F implies `Bad_T`, with leaf tweaks.
- The co-path argument below implies `Bad_{T'}`. GGM nodes expand by
  `expand_chunk<…, 2, TREE_PRG>(iv, node, …)` with tweak = node index (`faest/vector_com.inc:687-688,
  713-714`). So the two children sit at the adjacent pair `x₀, x₀ ⊞ e₀`. The leaf tweaks are
  `vec_index + 2303` (`:754`). Hence `|T'| ≤ 2303 + 17`.

### 7.3 Lemma F' (the case analysis)

**Lemma F'.** Suppose an output `o = (x, b, π) ∉ S` is accepted, `E` fails on it, and Rec and
`¬Bad_{T'}` hold. Then `D ∈ P'`. (For weak SE, `(x, b) ∉ {(x_s, b_s)}`, and `¬Bad_T` suffices.)

*Proof.* Let `y` be `V`'s H₂³ input on `o`. Assume `¬COL` (otherwise we are done).

**Case (P): `y ∈ Prog`.** `V`'s H₂³ answer is `T[y]`, the value of the last programming at `y`,
by some `s` at counter `c`.
- If `c < ctr_s`, then `T[y] ∈ Goodᶜ`, and `V` rejects (S2; L8 §1). Contradiction.
- So `y = y_s` and `Δ = Δ_s`.
- **Tracing the chain.** `y` fixes `chall₂`, `qs_check`, `ã` and `ctr`. `V`'s H₂² cell `x₂` and
  `Sim_s`'s H₂² cell `x₂_s` are both in `D` (Rec) with output `chall₂_s`. With `¬COL`,
  `x₂ = x₂_s`, so `chall₁`, `ũ`, `h_V`, `[μ_inst]`, `b₂` and `d` are equal.
- The same argument applies in turn:
  - to the H₂¹' cells: `x₁ = x₁_s` and `iv = iv_s`, so `μ`, `com`, `c`, `c_mult`, `iv_pre` and `b₁`
    are equal;
  - to H₂⁰/H₂⁴: `enc(x) = enc(x_s)`, and the modes cannot be confused (L8 Lemma 5.1);
  - to H₁: the leaf-commitment families are equal, so the τ hidden-leaf entries of the opening are
    equal.
- **Co-path seeds.** If some co-path seed differs, descend the subtree, comparing `V`'s keys (in
  `D` by Rec) with `Sim_s`'s keys (in `D` by Rec, Lemma R).
  - Take the deepest node or leaf where the keys differ, `k' ≠ k`.
  - Its two output blocks agree: the children are equal by maximality, or the leaf commitment is
    equal by family equality.
  - These blocks sit at `x₀(iv_s, twk), x₁(iv_s, twk)` with `twk ∈ T'`, and `iv_s` is in the H₄
    database (`V`'s H₄ query, Rec). That is `Bad_{T'}`. Contradiction.
- Hence `π = π_s` in every field (the padding is zero), so `o = (x_s, b_s, π_s) ∈ S`.
  Contradiction.

For weak SE, the chain trace alone gives `(x, b) = (x_s, b_s)`. Contradiction, with no cipher
event used. If the point was programmed by several proofs, the last one is traced, and `o` equals
that proof.

**Case (non-P): `y ∉ Prog`.** This is Q2 Lemma F verbatim:
- the tree;
- the opened leaves are alive with the committed seed equal to `V`'s seed, by `¬MULTI_end ⊆ ¬Bad_T`;
- the checks, consistency and `Δ ∈ A`;
- the statement;
- `E` fails iff `¬Ext_D(c, x₂)`.

So `B₃(c, x₂, y, l)` holds with `y ∉ Prog`. This covers every remaining case of L8:
- **(α), the same `(com, chall₁)` as a simulated proof.** `c` is the cell `(x₁_s, iv_s)` created
  by `Sim_s`. With `Sim°`, `known(c) = ∅` unless a hidden leaf was revived (charged in (N-E)).
  - A new `ctr` or `ã` with `chall₂_s` kept, a new `b₂`, and the **delayed-instance** reuse with a
    new instance (a new `x₂` from the adversary's own H₂² query, classically "a new chain from
    chall₂ on") all give `B₃` at a fresh, unprogrammed H₂³ cell. Its count is `≤ 1` (§5.1).
  - So each of the adversary's H₂³ queries contributes at most `2√2·2^{−64}`. This is the quantum
    form of "the forger needs a fresh answer equal to `Δ_s`".
- **(β), fresh chains,** including trees copied from simulated proofs (dead hidden leaves, fixed
  on `A`), changed binders and cross-mode reuse. This is Q2's generic count, `max(d,1)`, and the
  witness comes from a known tree that the adversary committed itself.
- **The same `(com, chall₁)` with every tree copied and `b₁` changed.** This is a new H₂¹' cell
  with `known = ∅`, so the count is `≤ 1`.

∎

---

## 8. Proof of Theorem Q5

1. **Perfect simulation.** The compressed oracles, Q1's key-level cipher and Lemma P1's
   bypass-programmed H₂³ are perfectly indistinguishable from the game's oracles (Q2 §2, Q1 P0,
   Lemma P1). The reductions of Q2 §3 are exact here too: `l` goes into H₂³' only for
   `x₃ ∉ Prog`, and programmed points bypass. `E`'s measurements are diagonal, so measuring all of
   `D` at the end is w.l.o.g. (Q2 §6.1).
2. **Reduction to the database.** By Lemma F' and Lemma R,
   `Pr[win] ≤ Pr[D ∈ P'] + ε_rec' + Pr[Bad_{T'}]` (or `Bad_T` for weak SE).
3. **Lemma T with neutral steps.** The steps of the whole game are:
   - `A`'s queries, `Sim`'s classical queries and `V`'s classical queries;
   - programming steps, which are neutral (Lemma P2);
   - other unitaries and measurements, which act on algorithm registers and classical registers
     other than `T`, and commute with `P'`.

   So `‖P'Ψ_end‖ ≤ Σ_s (transition bound of step s)` (**[Lean]** `telescope_with_neutral`). The
   per-step bounds are §5.1 for every query, and Lemma G for `Sim°`'s H₂¹', H₂² and H_comb queries.
   Grouping by oracle and by party gives `Σ_SE`.
4. `Pr[Bad_{T'}] ≤ ε_bind^C(T')`, by Q1 Thms 5.1 and 5.2 with `T ↦ T'` (§7.2).
5. With Q4's `S*` instead of `S^IC`, add `ε_Sim`. Every event above is an event of the joint
   classical output (Q1 §6, Q4 Thm C). ∎

### 8.1 Simultaneity

As in Q2 and L8 §9.1, `P'` is a single property and Lemma F' applies to each output. So one bound
covers all `n_out` outputs. `n_out` enters only through `V`'s queries on the outputs.

### 8.2 What the extractor does not need

It needs no rewinding, no mid-run extraction, no simulator coins and no trapdoor. The programmed
table is part of the oracle simulation. With `Sim°` the database contains only what `A` queried
plus what `V(π_s)` would query, which is L8's public log. With `Sim` it also contains the hidden
keys, and the proof is unaffected (§5.2).

### 8.3 Simulators that program more

Suppose a QROM simulator (for example GHHM-style, in a future `lean/docs/zk-qrom.md`) also programs H₂¹
at its own `(x₁_s, iv_s)`, or H₂² at its own `x₂_s`, or H₄, with **fresh uniform values
independent of the point**. Each such step replaces the effective value of one cell by a uniform
classical `r`. Its transition amplitude into `P'` is then at most `√(E_r[r non-neutral]) ≤ √ρ_o`,
with `ρ_o` as in §5.1, because the branches over `r` are orthogonal. So it is charged like one
query (with `1` instead of `2√2`), and the theorem holds with these counts added.

Programming whose *value* determines its *point*, as with H₂³ here, must instead be excluded as in
§5. Then the corresponding case must be closed by recording, as in Lemma F' (P). I did not check a
simulator that programs H₁ or the cipher. Neither is needed.

---

## 9. The reprogramming cost belongs to the ZK hop

Applications that swap honest proofs for simulated ones (L8 §8) pay the quantum ZK distance. That
includes GHHM's reprogramming term (GHHM Thm 1):

    (3/2)·Σ_{r=1}^{R} √(q̂_r·p_max^{(r)})    (the dominant part, for q̂_r p_max < 1).

Here `R` is the number of programmed points (`q_S` if only the accepted counter is reprogrammed,
`≈ 2^8 q_S` if every grinding attempt is), and `p_max` is the maximal probability of the H₂³
position given the distinguisher's view.

*Observation for `lean/docs/zk-qrom.md`, unverified.* The position's entropy comes from the prover's secret
`rho` (128 bits) through `H₃`, so `p_max ≈ 2^{−128}` may be the right value when the distinguisher
knows `w`. Then the term is `≈ 1.5·q_S·√(q·2^{−128}) ≈ 2^{−18.4}` at `q = q_S = 2^{30}` with
`R = q_S`, which is far larger than the SE terms. This is not part of Theorem Q5, and I did not
analyse it further.

---

## 10. Dependence on the label-rows fix

**SE does not depend on it.**
- `P'` reads no H₅ cell.
- The proof never uses that `c_mult`, `ũ` or `ã` are distributed like honest ones. L3, L4 and L6
  are applied to whatever committed data the database holds.
- The simulator's uniform `c_mult` is just more committed data.

The fix matters for SE only through:
- `c_E`: dedicated label rows lengthen the VOLE a little, which raises `c_E` slightly (still
  `≤ 2^{18}`);
- the PoK lemmas L3, L4 and L7, which must cover the new rows. That is Q2's and L3/L4's concern.

---

## 11. Lean (`lean/VoleMole/Seed/QSimExt.lean`)

| Note | Lean |
|---|---|
| A neutral step does not increase `‖P·‖` | `neutral_le` |
| Lemma T with neutral (programming) steps | `telescope_with_neutral` (wraps `QROM.telescope`) |
| Programming is neutral when the bad property is monotone in `Prog` | `relabel_neutral` |
| No known tree ⇒ `≤ 1` accepted answer, with no KOS/QS hypotheses | `card_acc_le_one_of_all_fixed` |
| Guarded H₂³ count `≤ max d 1` | `card_B3_le_guarded` (uses `QROM.card_B3_le`) |
| Main term at `q = 2^{30}` (`Sim°` / `Sim`) | `main_term_punctured_at_2_30`, `main_term_unpunctured_at_2_30` |
| Lemma D at `Q_E = 2^{48}` | `dead_leaf_at_2_48` |
| `multi` bounds fail at `Q_S = 2^{30}` | `multi_free_vacuous_at_2_48`, `theta_gt_half_at_2_48` |

Not formalized: the quantum steps (Lemma P1, Lemma G's decomposition, Lemma D's telescoping, Lemma
R), Lemma F' and the union bounds.

---

## 12. Gaps and confidence

| Step | Status | Confidence |
|---|---|---|
| Lemma P1 (bypass = GHHM reset) | proof given | high |
| Lemma P2 (programming neutral once `B₃` excludes `Prog`) | proof; Lean core | high |
| §5.1 counts with guards and `Prog` exclusion | proofs; Lean for the H₂³ count | high (inherits Q2) |
| Lemma G (`Sim°` chains pinned; freshness decomposition) | proof | medium-high: the step that uses a state-dependent (not worst-case) bound inside Lemma T is new, though elementary |
| Unpunctured `Sim` covered, no `ε_hk` | argument in §5.2 | medium-high: it rests on L3/L4 applying to the simulator's chain with uniform `c_mult`, `ũ`, `d`, which they do as stated |
| Lemma D | proof | high |
| Lemma R (exact persistence of classical records) | proof | high |
| Lemma F' case (P) via `COL` + `Bad_{T'}` | proof | high; tweak set read from code |
| Lemma F' case (non-P) | Q2 Lemma F verbatim | as Q2 (high) |
| `ε_bind^C(T')` via Q1 Thm 5.2 with `T ↦ T'` | imported | medium (as Q2: Q1 Thm 5.2 is long; linear scaling in `|T|` read off its proof) |
| Numbers | script plus Lean spot checks | high, given `c_E ≤ 2^{18}`. **`c_E` is an estimate** from proof sizes, not counted in code |
| §9 GHHM observation | heuristic | low; not part of the theorem |

**Gaps, stated plainly.**

1. **The theorem is vacuous at `Q_S = 2^{30}`.** The only failing term is the AES key-level binding
   `ε_bind^C`. Each simulated proof makes about `2^{18}` classical cipher queries, and Q1/Q4's
   `multi` bounds grow like `Q_E³/N`, or are valid only for `q ≲ 2^{37}`. The true value is
   presumably tiny:
   - the simulator's keys are fresh and uniform, so pairs of them agreeing anywhere occur with
     probability about `(q_S·2^{12})²/N ≈ 2^{−44}`;
   - the adversary must then still hit such a point through `iv = H₄(·)`, which costs another
     `q²/N`.

   The amplitude-additive telescoping charges each classical query as if it were coherent.
   **Precise missing lemma (M):** Q1 Thm 5.2 with `Q_A` quantum and `Q_C` *classical* cipher
   queries, where the classical ones are to keys sampled uniformly within a `Prove` call, with
   `θ` depending on `Q_A` only and an additive `O(Q_C²·|T'|·q₄²/N²)`-type term. Possible routes:
   - Gao's quantum union bound, for the classical-randomness events ("a simulator key was already
     touched");
   - a mixed classical/quantum agreement-level recursion.

   Neither is done here. With (M), or with Q4's open point-level lemma, the bound at
   `q = Q_S = 2^{30}` would be `≈ 2^{−60}`.
2. **Strong vs weak SE.** Weak SE (statement or binder differs) needs only `Bad_T`, the same event
   as Q2. Strong SE needs `Bad_{T'}`, because the co-path seeds of a simulated proof could be
   replaced. This is the only use of the GGM node tweaks, and it costs `≈ 2^{7.1}` more. The
   protocols need only weak SE (L8 §8).
3. **Efficiency.** As in Q2/Q4: `ε_Sim` with `S*`. The `L·q·δ` term counts the simulator's cipher
   queries, giving `≈ 2^{−72}`.
4. **Inherited from Q2.** These are: non-parallel queries only; the `q²` Grover-inherent loss (so
   meaningful only for `q ≲ 2^{50}`); and Chiesa–Manohar–Spooner not consulted.
5. **Simulator scope.** Only H₂³ programming is analysed in full. Fresh-value programming of H₂¹,
   H₂² or H₄ is handled by §8.3. `lean/docs/zk-qrom.md` is absent, so the exact quantum ZK simulator is not
   known to me. Whatever it is, Theorem Q5 needs only (S1')–(S5) and §8.3.
6. **Literature.** The Unruh 2015 attribution is from memory. The paper named in the brief
   ("DFM, simulation-sound extractability") was not found. GHHM and Majenz–Sharma were read.

## References

- [GHHM21] A. B. Grilo, K. Hövelmanns, A. Hülsing, C. Majenz, *Tight adaptive reprogramming in the
  QROM*, ASIACRYPT 2021; arXiv 2010.15103. §5.1 (superposition-oracle reprogramming), Thm 1,
  Prop. 2, Thm 6, Thm 3 (FS signatures).
- [DFMS22] J. Don, S. Fehr, C. Majenz, C. Schaffner, *Online-Extractability in the Quantum
  Random-Oracle Model*, EUROCRYPT 2022; arXiv 2103.03085. §2.2, eq. (8), Cor. 2.2, Lemma 3.3.
- [CFHL21] K.-M. Chung, S. Fehr, Y.-H. Huang, T.-N. Liao, EUROCRYPT 2021; arXiv 2010.11658. Lemma 5.6.
- [Zha19] M. Zhandry, *How to Record Quantum Queries*, CRYPTO 2019.
- [Unr15] D. Unruh, *Non-interactive zero-knowledge proofs in the quantum random oracle model*,
  EUROCRYPT 2015 (simulation-sound online extractability; cited from memory).
- [MS26] C. Majenz, J. Sharma, *Security of the Fischlin Transform in Quantum Random Oracle Model*,
  arXiv 2602.17307 (ZK via GHHM, Appendix D; extraction via compressed oracle).
- [CMS19] A. Chiesa, P. Manohar, N. Spooner, TCC 2019; ePrint 2019/834 (not retrieved).
- [Gao15] J. Gao, *Quantum union bounds for sequential projective measurements*, Phys. Rev. A 92
  (2015) (route for lemma (M); not used).
- Repo: `lean/docs/extraction/L8-simulation-extractability.md`, `Q1-quantum-ideal-cipher.md`,
  `Q2-qrom-fiat-shamir.md`, `Q4-efficient-cipher-simulation.md`, `lean/docs/zk.md` §5–6;
  `lean/VoleMole/Seed/{QROM,SimExt,QSimExt}.lean`; `subprojects/faest-arch-opt/vector_com.inc`.
