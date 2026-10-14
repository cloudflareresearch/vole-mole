# L8: Simulation-extractability

This note proves Lemma L8 of `lean/docs/extraction/README.md`. The README's straight-line extractor `E` still
works when the prover also gets simulated proofs, provided it is run on the right query log. The
notion proved is **strong** simulation-extractability: extraction succeeds from every accepting
triple (statement, binders, proof) that differs from all simulated triples. Weak SE, where the
statement or a binder must differ, follows. Lean is used only for the combinatorial core, in
`lean/VoleMole/Seed/SimExt.lean`.

Model, notation, parameters and lemma names follow `lean/docs/extraction/README.md`. The simulator is the
one from `lean/docs/zk.md` §5. Citations `faest/<file>:<line>` refer to the patched faest-arch-opt in
`subprojects/faest-arch-opt`, with patches 0001–0005; those into `src/` and the patched faest files
refer to branch `voleith-label-rows` (commit `d5def9c`).

Contents:
- §0 Verdict
- §1 The transcript, as implemented
- §2 The SE game and the extractor's log
- §3 The simulator
- §4 Main theorem
- §5 Lemmas
- §6 Proof of the theorem
- §7 The specific malleability questions
- §8 What each protocol needs, and the effect of lean/docs/zk.md's (PU) finding
- §9 Remarks
- §10 Lean

## 0. Verdict

- **Strong SE holds, unconditionally in `w`.** The SE game feeds the adversary simulated proofs
  for statements it chooses adaptively, including false statements. The simulator never uses a
  witness, so lean/docs/zk.md's prefix-unpredictability condition (PU) plays no role in the theorem itself.
  (PU matters only when a reduction swaps real proofs for simulated ones; see §8.) On branch
  `voleith-label-rows` the gate labels come from dedicated VOLE rows and (PU) is gone (lean/docs/zk.md);
  the SE theorem is unaffected either way.
- **The error** is the README's PoK bound for the combined system, plus four terms that are
  negligible at λ = 128. The largest of these is a multi-key AES-128 term,
  `ε_hk ≤ 138·q_S·N_E·2^{−127}`: the adversary guesses one of the simulator's unopened GGM keys.
  With the punctured simulator variant `Sim°` (§3.3) this term is 0, but the ZK distance gains
  lean/docs/zk.md's `ε_hide`.
- **No malleability attack was found.** Every byte of the proof is either hashed into a challenge
  or uniquely determined by hashed data (Lemma 5.1). So the following all fail except with
  probability `2^{−λ}` per H₂³ query:
  - changing the grinding counter;
  - changing a binder;
  - changing the instance in delayed-instance mode while keeping a simulated `(com, chall₁)`;
  - reusing the simulated Δ.
  In delayed mode, reusing a simulated `(com, chall₁)` with a new instance is a new chain from
  chall₂ on. Every tree of the simulated commitment has a dead leaf at `Δ_s`, so that chain
  accepts only `chall₃ = Δ_s`.
- **What the protocols need.** The protocols need:
  - straight-line *simultaneous* extraction from many adversarial proofs (the PoK theorem
    already gives this, §9.1);
  - weak SE w.r.t. statements, for observed or relayed honest proofs: Moussaka redeem and
    Ratatouille spend, and to a lesser extent the two issuance proofs.

  No protocol uses a binder except PomFRIT. No protocol reveals a first-phase message π₁ on its
  own, or completes one π₁ twice. PomFRIT's unforgeability needs no simulated proofs at all. Its
  blindness needs ZK against the Issuer, which lean/docs/zk.md shows fails. SE cannot repair that (§8).

## 1. The transcript, as implemented

Proof fields (`faest/faest_sig.hpp:39-66`, contiguous and with no gaps):

| Field | Bound by |
|---|---|
| corrections `c_1..c_{τ−1}` | H₂¹ input (`src/voleith.hpp:228`, `:418`) |
| `c_mult` | H₂¹ input (`voleith.hpp:229`, `:419`); padding also checked (`faest/faest_sig.hpp:135-150`) |
| `ũ` (KOS response, 4λ bits) | H₂² input, all bytes (`faest/kos_vole_check.hpp:104-108`) |
| `d` (witness correction, `WITNESS_BYTES`) | H₂² input (`voleith.hpp:300`, `:465`) |
| `ã_1..ã_{d−1}` (`qs_proof`) | H₂³ input (`voleith.hpp:492`) |
| `veccom_open` | τ hidden-leaf commitments, then co-path seeds, then zero padding. Checked (`faest/vector_com.inc:896-926`) and used to rebuild `com` |
| Δ (`delta`, 128 bits) | must equal the H₂³ output (`voleith.hpp:497`); top `w_grind = 8` bits zero (`faest/faest_sig.hpp:128-134`) |
| `iv_pre` | H₄ and H₂¹ inputs (`voleith.hpp:391, 420`) |
| `ctr` (4 bytes) | H₂³ input (`voleith.hpp:493`) |

The challenges:

```
mu     = H₂⁰(enc(x) ‖ DST ‖ 0x08)              non-delayed
       = H₂⁴(DST ‖ 0x0C)                       delayed (PomFRIT)          voleith.hpp:125-140
iv     = H₄(iv_pre ‖ mu ‖ 0x04)                                            :388-394
com    = H₁(h_0 ‖ … ‖ h_16 ‖ 0x01),  h_i = H₁(com_{i,0} ‖ … ‖ com_{i,N_i−1} ‖ 0x01)
                                                       faest/vole_commit.inc:29-80
chall₁ = H₂¹(mu ‖ com ‖ c ‖ c_mult ‖ iv_pre ‖ b₁ ‖ 0x09)                    voleith.hpp:413-423
chall₂ = H₂²(chall₁ ‖ ũ ‖ h_V ‖ [mu(x)] ‖ b₂ ‖ d ‖ 0x0A)                    :452-467
chall₃ = H₂³(chall₂ ‖ qs_check ‖ ã ‖ ctr ‖ 0x0B)                            :487-495
```

- `h_V` and `qs_check` are recomputed by `V` from Q, Δ and the proof.
- `[mu(x)]` is present exactly in delayed mode. The mode is a fixed property of each relation:
  PomFRIT always passes `nullptr` (`src/pomfrit/pomfrit.cpp:167, 229`), and the others call
  `voleith_prove`/`voleith_verify`.
- Lengths: `|chall₁| ≥ 5λ+64` bits (`faest/constants.hpp:291, 306`),
  `|chall₂| = 3λ+64` (`:275`), `|mu| = |com| = |h_i| = 2λ` (`voleith.hpp:128`,
  `faest/constants.hpp:467`).

**Parsing is unique.** Every H₂ʲ input has fixed-length fields, except one variable-length binder
in each of H₂¹ and H₂². In H₂¹, `b₁` is last before the domain byte. In H₂², `b₂` is followed by
the fixed-length `d`. So each input determines its fields, including the binders.

Statements are identified with their encodings `enc(x)`. These are injective:
- the fields are fixed-length (`src/moussaka/issue.hpp:170-173`, `src/ratatouille/issue.hpp:157-161`,
  `src/ratatouille/spend.hpp:327-333`, `src/pomfrit/redeem.hpp:114-117`);
- the Moussaka anchor list is length-prefixed (`src/moussaka/redeem.hpp:188-205`);
- a UOV key enters as its SHAKE256 digest (`src/uov/public_key.hpp:31-32`), so two keys with the
  same digest count as the same statement. Distinct keys with equal digests would be a SHAKE256
  collision.

**Leaf commitments** (`aes_ctr`): `com_{i,j} = E_k(iv ⊞ c₀(t)) ‖ E_k(iv ⊞ c₁(t))` with
`c_b(t) = (b,0,0,t)` (32-bit lanes), `t = i + L − 1` and `k = sd_{i,j}`
(`faest/vector_com.inc:754, 1071-1085`). Write `δ = (1,0,0,0)`, so that
`iv ⊞ c₁(t) = (iv ⊞ c₀(t)) ⊞ δ`.

**Opening and grinding.**
- `open` fails iff the number of co-path nodes `#hidden − 2τ + 1` exceeds `T_open = 105`
  (`faest/vector_com.inc:818`).
- `verify` fails iff it needs more co-path nodes than `OPEN_SIZE` holds (`:905`).
- `OPEN_SIZE = τ·hash_len + T_open·λ/8` (`faest/vector_com.hpp:121-122`).
- So **the prover's opening condition and the verifier's are the same predicate on Δ**. Let
  `Good` be the set of Δ with zero top bits that satisfy it. `V` rejects every proof whose
  Δ ∉ Good.

## 2. The SE game and the extractor's log

**Game `SE_A` (one relation R, in its fixed mode).**
- `A` gets the oracles (all random oracles, and `E`/`E⁻¹`).
- `A` also gets a proving oracle `Prove(x, b₁, b₂)`. It returns `π ← Sim(x, b₁, b₂)` and records
  `(x, b₁, b₂, π)` in the list `S`. The statement `x` is arbitrary: it may be false, and it may
  be chosen adaptively.
- `A` finally outputs any number `n_out ≥ 1` of triples `(x, b, π)` with `b = (b₁, b₂)`.

**The log `L`** given to `E` is the time-ordered list of:
1. every query of `A`;
2. for each `Prove` answer, every query made by `V(x_s, b_s, π_s)`, placed at the time of the
   answer;
3. every query made by `V` on each output triple, placed at the end.

`H₂³` answers at programmed points appear in `L` with the programmed value.

So `E` uses only the *public* transcript of the `Prove` oracle, not the simulator's coins. Item 2
supplies the cipher and H₁ queries that make the opened leaves of simulated proofs alive. It
cannot supply the simulator's private queries under unopened keys, and must not: §5.2 needs those
leaves to be dead.

**Winning.** Let `Bad(x, b, π)` be the event that `V(x, b, π)` accepts and
`R(x, E(x, b, π, L))` fails.
- Strong SE: `A` wins if some output with `(x, b, π) ∉ S` satisfies `Bad`.
- Weak SE: `A` wins if some output whose `(x, b)` differs from every simulated `(x_s, b_s)`
  satisfies `Bad`.

Strong SE implies weak SE.

**Counts.**
- `q`: the number of `A`'s queries. `Q_A`: the number of its H₂³ queries.
- `q_S`: the number of `Prove` calls.
- `N`: the total number of queries in `L`. `N_E ≤ N`: its cipher queries. `q₄`: its H₄ outputs.
- `c_V`: the cost of one verification, so `N ≤ q + (q_S + n_out)·c_V`.
- `q₁`, `q₂`: the H₂¹ and H₂² queries made by `A` and by `V` on the outputs.
- `p := 1/(2^{128} − N_E − M) ≤ 2^{−127}`, where `M` is the largest number of simulator cipher
  entries under one key (a few thousand). Assume `N_E + M ≤ 2^{127}`.

## 3. The simulator

### 3.1 `Sim` (lean/docs/zk.md §5), one-shot

`Sim(x, b₁, b₂)` runs lean/docs/zk.md's `Sim₁` and then `Sim₂(x, b₂)` with no adversary step in between.
In brief:
- **Commitment.** Sample `seed*` and `iv_pre`. Compute `mu` and `iv` honestly. Run
  `crt_vole_commit(seed*, iv)` honestly, so the tree, `com` and the corrections are real.
  Replace `c_mult` by a uniform value.
- **chall₁ and first-phase messages.** Compute `chall₁` honestly. Make `ũ` and `d` uniform.
- **Grinding.** Sample the grinding outcome: `ctr` geometric, `Δ_s ← Good`, and failing values
  `Δ_c ← Goodᶜ` for `c < ctr`.
- **Opening and chall₂.** Open at `Δ_s`. Compute `h_V` the way `V` does, and `chall₂` honestly.
- **QuickSilver.** Make `ã` uniform. Compute `qs_check` the way `V` does.
- **Programming.** Program `H₂³(chall₂ ‖ qs_check ‖ ã ‖ c ‖ 0x0B) := Δ_c` for `c < ctr`, and
  `:= Δ_s` for `c = ctr`. Abort if any of these points is already defined.

### 3.2 The properties of `Sim` that the proof uses

The proof uses only these properties, so it covers any simulator that has them.

- **(S1) Programming.** `Sim` programs only H₂³, and only at points whose prefix is its own
  `chall₂_s`. The cipher `E` is never programmed. All of `Sim`'s other queries go to the real
  oracles. (If a simulator also programmed H₂¹ at points containing `com_s`, H₂² at points
  starting with `chall₁_s`, or H₄ at `(iv_pre_s ‖ mu_s)` with a uniform value, the proof would go
  through unchanged: such points are only ever reached through the chains of §5.4 (α).)
- **(S2) Exactly one accepting programmed value.** Among the programmed values for proof `s`,
  exactly one lies in `Good`: Δ_s, at `y_s = (chall₂_s ‖ qs_check_s ‖ ã_s ‖ ctr_s ‖ 0x0B)`. The
  others lie in `Goodᶜ` and are rejected by `V` (§1).
- **(S3) Hidden keys.** Let `K_s` be the set of hidden GGM nodes of proof `s`: the root `seed*`,
  every ancestor of a hidden leaf, and the τ hidden leaves. Then:
  - `|K_s| = #hidden ≤ T_open + 2τ − 1 = 138`;
  - `V` on `π_s` never queries `E` under a key in `K_s`, because it expands only co-path subtrees;
  - from `A`'s view, the keys in `K_s` are uniform among the values not yet excluded, until some
    query in `L` uses one of them. (In the ideal-cipher model a key is only an index. Revealed
    co-path seeds are outputs under hidden keys and reveal nothing about those keys.)
- **(S4) Hidden-leaf commitments.** The hidden-leaf commitment
  `ρ_{s,i} := com_{s,i,Δ_{s,i}} = E_{k}(iv_s ⊞ c₀(t)) ‖ E_{k}(iv_s ⊞ c₁(t))` uses a hidden key
  `k ∈ K_s`. While no query in `L` uses a key in `K_s`, the pair `ρ_{s,i}` is uniform over
  `≥ (2^{128} − M)²` pairs and independent of every entry of `L`.
- **(S5) Completeness.** `V(x_s, b_s, π_s)` accepts (lean/docs/zk.md H3).

### 3.3 Variant `Sim°` (punctured)

`Sim°` is the same as `Sim`, except that it samples the grinding outcome first. It never computes
the hidden paths: co-path seeds are uniform, and `ρ_{s,i}` is a uniform 2λ-bit string. This is the
simulated form of lean/docs/zk.md's hybrid H7, so its distance from `Sim` is lean/docs/zk.md's `ε_hide` (hybrids
H4/H8).

`Sim°` has (S1), (S2) and (S5). It has (S3) with `K_s = ∅` and (S4) unconditionally. So all
statements below hold for `Sim°` with `ε_hk = 0`.

## 4. Main theorem

Write `ε_ext(N; q₁, q₂, Q)` for the README's PoK bound with per-oracle query counts:

```
ε_ext(N; q₁, q₂, Q) = Q·max(d,1)·2^{−λ} + q₁·ε_KOS + q₂·(ε_QS + 2^{−128}) + ε_bind(N) + ε_dead(N)
```

The README writes this with `Q` in place of `q₁` and `q₂`; see §9.2.

**Theorem L8.** For every `A` in `SE_A` with the simulator `Sim`,

```
Pr[A wins strong SE] ≤ ε_ext(N; q₁, q₂, Q_A + n_out) + ε_prog + ε_hk + ε_H + ε_eq,
```

where

```
ε_prog ≤ 4·q_S·N·2^{−254}                      (programming aborts)                 Lemma 5.5
ε_hk   ≤ 138·q_S·N_E·2^{−127}                  (some query in L uses a hidden key)  Lemma 5.2
ε_H    ≤ q_S·τ·(9 + 4τ·q₄)·N_E·2^{−254}        (a hidden-leaf commitment is hit)    Lemma 5.3
ε_eq   ≤ N²·2^{−253}                           (collisions; uniqueness of the opening) Lemma 5.1
```

- The bound covers all `n_out` outputs simultaneously.
- `E` is the README's extractor run on `L`, and it does not depend on `A`.
- The simulator's own H₂¹ and H₂² queries are **not** counted in `q₁` and `q₂`: the chains
  through them are handled by Lemma 5.4 without L3 or L4.

With `Sim°`, `ε_hk = 0`.

**Magnitudes** (λ = 128, τ = 17). The PoK part is dominated by
`(Q_A+1)·max(d,1)·2^{−128} + q₁ε_KOS + q₂ε_QS`. Of the new terms:
- `ε_hk` is the largest. For `q_S = 2^{30}` and `N_E = 2^{64}` it is about `2^{−26}`.
- `ε_prog`, `ε_H` and `ε_eq` are below `2^{−100}` for `N, q₄ ≤ 2^{64}`.

`ε_hk` is the standard multi-key loss of AES-128 keys, the same kind of term as lean/docs/zk.md's
`ε_hide`. Using `Sim°` moves it into the ZK hop.

## 5. Lemmas

Throughout, "the chain of an output" means the chain `V` recomputes from it: `y` (the H₂³ input),
then `chall₂`, then `chall₁`, then `com`. For a query input `z`, the *first query* to `z` is its
earliest occurrence in `L`.

### Lemma 5.1 (the transcript binds everything)

Suppose no collision occurs among the outputs in `L` of H₂⁰/H₂⁴, H₁, H₂¹ or H₂², and no
cross-key two-block coincidence occurs in `E`. (The latter means: `k ≠ k'` with `E_k(a) = E_{k'}(a)`
and `E_k(a') = E_{k'}(a')` for two inputs `a, a'`.) The probability that either fails is at most
`ε_eq`.

Then, if two accepted triples `(x, b, π)` and `(x', b', π')` have the same H₂³ input `y`, they
are equal.

*Proof.* `y` has fixed-length fields (§1). So it fixes `chall₂`, `qs_check`, `ã` and `ctr`, and Δ
equals the H₂³ output at `y` in both proofs (`voleith.hpp:497`).

Equal `chall₂` and no H₂² collision give equal H₂² inputs. By unique parsing, `chall₁`, `ũ`, `b₂`
and `d` are equal, and so is `mu(x)` in delayed mode.

Equal `chall₁` give equal H₂¹ inputs. So `mu`, `com`, `c`, `c_mult`, `iv_pre` and `b₁` are equal.

Equal `mu = mu(x)`, sitting in H₂¹ (non-delayed) or H₂² (delayed), and no H₂⁰ collision give
`enc(x) = enc(x')`. The H₂⁰/H₂⁴ domain bytes 0x08 and 0x0C differ (`voleith.hpp:136-137`), so
the two modes cannot be confused either.

Equal `com` and no H₁ collision give equal `h_i`, and hence equal leaf-commitment families. The
opening's first τ entries are the family's entries at the positions Δ_i (`vector_com.inc:966-970`),
so they are equal.

The co-path positions are a function of Δ (`:896-916`). Suppose a co-path seed differed between
`π` and `π'`, say `n ≠ n'` at the same position.
- Expand both subtrees with `E` (as `V` does).
- At each level, either both children agree, which is a cross-key two-block coincidence between
  keys `n` and `n'` at the two child inputs, or some child differs, in which case descend into it.
- At a leaf, different keys with equal commitments `E_k(iv⊞c₀) ‖ E_k(iv⊞c₁)` are again such a
  coincidence.

So the co-path seeds are equal. The padding is zero in both (`:918-926`), so `π = π'`.

*Bound.* The output collisions cost at most `N²·2^{−2λ}`, since the outputs are at least 2λ bits.
For a coincidence, the entry that completes it has a uniform free coordinate, which must hit a
fixed value with probability ≤ p. The first of the two needed entries has probability ≤ p as
well. Taking a union over ≤ N_E² ordered pairs of entries gives `N_E²·p²`. In total,
`ε_eq ≤ N²·2^{−256} + N_E²·2^{−254} ≤ N²·2^{−253}`.

This also absorbs the out-of-order events: a fresh H₂¹ or H₂² output equals the prefix of an
earlier query, at most `N²·2^{−(2λ)}`. ∎

### Lemma 5.2 (hidden keys stay hidden)

Let `HK` be the event that some cipher query in `L` (by `A`, or by `V` on an output) uses a key in
some `K_s`. Then `Pr[HK] ≤ 138·q_S·N_E·p = ε_hk`.

*Proof.* By (S3), `V` on simulated proofs never uses a hidden key. Consider any other query, and
condition on no earlier query having used a hidden key. Each of the ≤ 138 keys in each `K_s` is
then uniform over at least `2^{128} − N_E − M` values. Take a union bound over queries and keys. ∎

### Lemma 5.3 (simulated hidden leaves are pinned)

Let `ρ = ρ_{s,i}`. Let `Hit(ρ)` be the event that `L` contains cipher entries `(k, a, ρ₀)` and
`(k, a⊞δ, ρ₁)` with `a ⊟ c₀(t) ∈ IV` for some leaf tweak `t` (τ choices). Here `IV` is the set of
H₄ outputs in `L`.

Then `Pr[¬HK ∧ Hit(ρ)] ≤ (9 + 4τ·q₄)·N_E·p²`. A union bound over the `q_S·τ` commitments gives
`ε_H`.

*Proof.* Assume ¬HK. Then every entry of `L` is under a key outside `K_s`. By (S4), ρ is uniform
over ≥ `(2^{128}−M)²` pairs, independent of all entries of `L`.

Each entry of `L` is created by a forward query, which chooses the input and draws the output
uniformly from ≥ `2^{128} − N_E` values. Or it is created by an inverse query, which chooses the
output and draws the input. Call the drawn value the entry's *free coordinate*.

Let `F` be the earlier and `S` the later of the two entries in `Hit(ρ)`. Given `F` (which fixes
`k` and the role of `F`), `S` is either the entry at position `(k, a_F ⊞ δ)` or the one at
`(k, a_F ⊟ δ)`, and its value must be `ρ_{b}` for the known `b`. There are two ways to create it:
- a forward query at that position, whose output hits `ρ_b` with probability ≤ p;
- an inverse query at `(k, ρ_b)`, whose input hits the position with probability ≤ p.

So `Pr[S completes | F] ≤ 2p`, conditioned on everything before `S`.

- **(i) `F` exists before ρ is sampled.** Then ρ must hit `F`'s output, with probability
  ≤ `2p` per `F`. Together with `S`, this gives `≤ 4N_E·p²`. If `S` is also earlier, ρ must hit
  one of ≤ `N_E` existing consecutive pairs, giving `≤ N_E·p²`.
- **(ii) `F` comes later and is a forward query.** Its output must hit `ρ₀` or `ρ₁`, with
  probability ≤ 2p. Together with `S`, this gives `≤ 4N_E·p²`.
- **(iii) `F` comes later and is an inverse query at `(k, ρ_b)`.** This is free, but its input
  `a_F` is uniform. The condition `a ⊟ c₀(t) ∈ IV` concerns `a = a_F` or `a = a_F ⊟ δ`.
  - If the needed H₄ output exists before `F`, then `a_F` hits one of ≤ `τ·q₄` values, with
    probability ≤ `τq₄p`.
  - Otherwise some later H₄ output (uniform, ≤ 2^{−128} ≤ p per value) hits one of τ values, with
    probability ≤ `τq₄p` over all H₄ queries.

  `S`'s draw is a different draw, so each bad event is bounded conditionally on the past, in
  either order. Together with `S`, and summing over `F`, this gives `≤ 2τq₄N_E·p·2p`.

Summing the cases gives `(5 + 4 + 4τq₄)·N_E·p²`. ∎

**Consequence (pinning).** Suppose ¬HK and ¬Hit(ρ_{s,i}) hold. Suppose further that an accepted
output's family for tree `i'`, under that output's `iv`, contains `ρ_{s,i}` at position `j`. Then
`Δ_{i'} = j`. Otherwise `V` derives a key for leaf `(i', j)` and evaluates its commitment
`E_k(iv⊞c₀(t')) ‖ E_k(iv⊞c₁(t'))`. Here `iv = H₄(iv_pre ‖ mu)` is in `IV` because `V` queries
H₄. Since the commitment equals `ρ_{s,i}`, this gives `Hit(ρ_{s,i})`.

The same argument shows that `ρ_{s,i}` is dead in the sense of L1 in every chain: being alive
would also need such entries. So a tree containing a simulated hidden-leaf commitment, at any
position and copied from any simulated proof, is *pinned*: it is fixed on the chain's accepting
set. This is Claim 4 (i) for copied trees; Lean `isFixed_of_pinned`.

### Lemma 5.4 (chain classification)

Fix an accepted output, its H₂³ input `y` and its chain. Assume the events of Lemmas 5.1–5.3 and
5.5 do not occur. Exactly one of the following holds.

- **(P) `y` is a programmed point of some `Prove` answer `s`.**
- **(α) `y` is not programmed, and the first H₂¹ query with output `chall₁` is `V(π_s)`'s replay
  of `Sim_s`'s H₂¹ query, for some `s`.** That is, the H₂¹ input equals `Sim_s`'s, so
  `com = com_s`.
- **(β) Otherwise.** Then the first H₂¹ query with output `chall₁` and the first H₂² query with
  output `chall₂` are both queries of `A`, or of `V` on an output. Neither is a replay of a
  simulator query.

*Proof of (β).* Suppose the first H₂² query for `chall₂` were a replay of `Sim_s`'s H₂² query.
Its input would start with `chall₁_s`. Then, with no H₂¹ output collision, the H₂¹ query for
`chall₁` would be `Sim_s`'s, which puts us in case (α). ∎

### Lemma 5.5 (programming never aborts)

`Pr[some Sim aborts] ≤ ε_prog`.

*Proof.* The programmed points for `s` start with `chall₂_s`. This is the output of `Sim_s`'s H₂²
query, whose input starts with `chall₁_s`, the output of an H₂¹ query whose input contains
`com_s = H₁(… h_{s,i} …)`, where `h_{s,i} = H₁(… ρ_{s,i} …)`.

Before `Sim_s` runs, `A` has no information about `ρ_{s,i}` (fresh `seed*`, (S4)). So each H₁
input of `Sim_s` was queried before with probability ≤ `N·p²`. Given that it was not, `h_{s,i}`
and then `com_s` are fresh uniform 2λ-bit values, then `chall₁_s` (≥ 5λ+64 bits), then `chall₂_s`
(3λ+64 bits). Each step's input was previously queried with probability ≤ `N·2^{−2λ}`.

So `Pr[abort_s] ≤ N·(p² + 3·2^{−2λ}) ≤ 4N·2^{−254}`. This also covers collisions with the
programmed points of other proofs, which are in `L`. It matches lean/docs/zk.md's `ε_prog`, plus the
freshness of `Sim`'s H₂² input. ∎

## 6. Proof of the theorem

Discard the events of Lemmas 5.1, 5.2, 5.3 and 5.5, which cost `ε_eq + ε_hk + ε_H + ε_prog`.
Also discard the L1, L2, L3 and L4 failure events of the README for the chains of type (β), which
cost `ε_bind(N) + ε_dead(N) + q₁ε_KOS + q₂(ε_QS + 2^{−128})`.

*Why L1–L4 transfer to (β) chains.*
- L1 and L2 concern only H₁, H₄ and `E` on the entries of `L`.
- Under ¬HK, every entry of `L` is under a key outside all `K_s`. So the simulator's private
  cipher entries are independent of `L`, and L1's and L2's arguments, which reason only about
  entries of `L`, apply to the combined system with `q → N`.
- Simulated hidden-leaf commitments are covered directly by Lemma 5.3.
- In case (β), `chall₁` and `chall₂` are fresh outputs of unprogrammed random-oracle queries of
  `A` or `V`. The committed data is fixed before `chall₁`, including any trees copied from
  simulated proofs, fixed earlier by `Sim`. `d` is in the H₂² input. That is all L3 and L4 use.

Now take an accepted output with `(x, b, π) ∉ S`.

**Case (P).** Suppose `y` is a programmed point of `s`.
- If its programmed value is a failing value `Δ_c ∈ Goodᶜ`, then `V` rejects (S2, §1).
  Contradiction.
- Otherwise `y = y_s` and Δ = Δ_s. Both `(x, b, π)` and `(x_s, b_s, π_s)` are accepted with H₂³
  input `y_s`, so Lemma 5.1 gives `(x, b, π) = (x_s, b_s, π_s) ∈ S`. Contradiction.

So for a fresh output (P) never occurs. In particular, **a programmed chall₃ can be reused only by
the identical simulated triple.**

**Case (α).** Here `com = com_s`. Since there are no H₁ collisions, the output's leaf-commitment
families are `Sim_s`'s, and every tree `i` contains `ρ_{s,i}` at `Δ_{s,i}`.
- By pinning (Lemma 5.3), acceptance forces `Δ_i = Δ_{s,i}` for all `i`. So the decoded 120
  bits equal those of `Δ_s`.
- The top 8 bits are zero in both (`faest_sig.hpp:128-134`), so Δ = Δ_s. In Lean, all pinned
  gives at most one accepted challenge: `card_le_one_of_all_pinned`,
  `admissible_card_le_one_of_all_pinned`.
- Since `y` is unprogrammed, Δ is the answer to the first H₂³ query at `y`, made by `A` or by `V`
  on an output. That answer is uniform and independent of `Δ_s`, which is fixed by `y` through
  the chain before the query. So it equals `Δ_s` with probability `2^{−λ}`.

**Case (β).** The README's per-chain argument applies to this chain:
- The trees copied from simulated proofs, from one proof or from several, are pinned, hence
  fixed. Lean `claim4Hyp_of_pinned` discharges `Claim4Hyp.unknown_fixed` for them.
- By L5/L6 (`extraction_cases`), either some known tree's candidate satisfies every uncombined
  constraint, so `E` succeeds by L7, or `|A_chain| ≤ max(d,1)`.
- A free tree is never a copied one (`free_tree_is_fresh`): the witness comes from a tree `A`
  committed itself.
- In the second case, the uniform answer at `y` lands in `A_chain` with probability
  `≤ max(d,1)·2^{−λ}`.

**Union.** Assign each H₂³ query of `A`, or of `V` on an output, to the chain its input
determines. Each query is charged at most `max(d,1)·2^{−λ}`, which covers both (α) and (β), so
the total is `(Q_A + n_out)·max(d,1)·2^{−λ}`. Off the discarded events, every accepted fresh
output is in case (β) with a successful extraction. This holds for all outputs at once. ∎

**Partial and mixed reuse, in more detail.**
- A tree copied with a different `iv` (a new `iv_pre` or `mu`) keeps the simulator's leaf
  commitments, but those were computed under `iv_s`. So its opened leaves are dead under the new
  `iv`, unless `A` finds keys, which L2 bounds.
- A tree with two or more dead leaves never opens (L2), so `A_chain = ∅` for such chains.
- Trees copied from several simulated proofs share one chain `iv`. Distinct proofs have distinct
  `iv` (fresh `iv_pre`), so trees copied from all but one `iv` class die completely.
- Moving a copied tree to another index changes its tweak `t`. Lemma 5.3 already takes a union
  over all τ tweaks.

## 7. The specific malleability questions

**Delayed instance (PomFRIT): reusing a simulated `(com, chall₁)` with a new instance `x'`.**
- The H₂¹ input contains `mu_null = H₂⁴(DST)`, not `x`, so `chall₁ = chall₁_s` (the same H₂¹
  point).
- The H₂² input contains `mu(x')` (`voleith.hpp:287-290, 460-463`), so `chall₂ ≠ chall₂_s`,
  barring an H₂⁰ or H₂² collision. **It is a new chain from chall₂ on**, of type (α).
- Every tree of `com_s` is pinned at `Δ_s`, so the forger needs a fresh H₂³ answer equal to
  `Δ_s`: probability `2^{−λ}` per query. **This is not a malleability attack.** Extraction
  succeeds vacuously, because acceptance is negligible.

What makes delayed binding safe for SE is that **the commitment, not the instance, fixes the only
acceptable Δ** once the hidden leaves are dead. An honest prover can complete its own π₁ for any
instance because it knows all the seeds. An adversary holding only `π_s` cannot.

For PomFRIT the instance `h = H(pk, chall₁, ũ, d_pre, msg)` (`pomfrit.cpp:96-111`) changes with
`msg`, so the same analysis covers re-targeting a signature to a new message.

**Grinding counter.** Changing `ctr` changes `y`. The new point is either:
- a failing programmed point (`c < ctr_s`), whose value `Δ_c ∉ Good` is rejected; or
- unprogrammed, in which case (α) requires the answer `Δ_s` (`2^{−λ}`).

Re-randomizing by grinding therefore needs about `2^λ` work. The verifier does not check that
`ctr` is minimal (lean/docs/zk.md §7.3), and SE does not need it to.

**Binders.**
- Changing `b₁` changes the H₂¹ input. If `com_s` is kept, the chain is (β) with every tree
  pinned, so `|A_chain| ≤ 1` and the forger succeeds with probability `2^{−λ}` per query.
- Changing `b₂` gives a new H₂² input, and the chain is (α).
- Both binders are uniquely parsed (§1).
- PomFRIT's binders are `b₁ = refresher_com` and `b₂ = refresher`, with `refresher_com = H(refresher)`
  checked by `verify` (`pomfrit.cpp:221-236`). So a signature cannot be re-randomized through
  them either.

**The programmed H₂³ points.** Reusing the point `y_s` reproduces the simulated triple exactly
(Lemma 5.1). Reusing the value `Δ_s` with any other `y` is a fresh draw (`2^{−λ}`). The failing
programmed values are rejected (S2).

**Cross-mode and cross-relation reuse.** The H₂⁰ and H₂⁴ domains are disjoint, and every relation
has its own `DST` in `mu`. A proof checked in a different mode or relation therefore has a
different `mu` in H₂¹ (and in H₄), which makes it a (β) chain with every tree pinned, or with
trees that are dead under the new `iv`.

**What SE does not prevent.** Replaying the identical `(x, b, π)`. The protocols handle this with
nullifiers (`README.md:122-128`).

**Two completions of one π₁.** lean/docs/zk.md's two-phase ZK game, and any oracle that completes a π₁ more
than once, are not needed:
- no API reveals π₁ alone (PomFRIT's client sends only `t = h ⊕ r`, `pomfrit.cpp:173-176`);
- no API completes one π₁ twice (`PendingBlindSignature` is consumed, `pomfrit.cpp:194-215`).

Two completions would reveal two Δ's for one commitment. That would open almost every seed and
break ZK outright, so such an oracle cannot be simulated in the first place.

**Concrete attacks: none found.** One caveat is the `detail::issue_request_with_seed` test hook.
With a repeated seed, `pk` and `msg` it reproduces π₁. Two Issuer responses would then give two
completions. This is a ZK/blindness issue, not an SE issue (lean/docs/zk.md §7.2).

## 8. What each protocol needs, and the effect of lean/docs/zk.md's (PU) finding

**Status after patch 0005.** The (PU) discussion below describes the unpatched code (`main`), where
the CRT gate-label offset is `u` on the first λ witness rows, i.e. `d ⊕ w[0..λ)`. On branch
`voleith-label-rows` all five relations set `CRT_DEDICATED_LABEL_ROWS`: the offset is `u₀` on λ
dedicated rows with cross-tree corrections but no `d`, so it is uniform given the view, and lean/docs/zk.md's
`ε_ZK` has a `Pred_R`-free label term. Then the real-to-simulated hop is valid for every
adversary, including the PomFRIT Issuer, and the "No" for PomFRIT blindness below no longer applies
to the proof system. The SE theorem and its error are unchanged: `Sim` was already honest on the
commitment, and extraction never uses the labels.

The SE theorem does not need (PU), because `Sim` uses no witness. (PU) enters when a reduction
replaces honest real proofs by simulated ones. That hop costs lean/docs/zk.md's `ε_ZK`, which contains
`(Q₅ + n_mult·Q_V)·Pred_R`.

| Protocol | Proofs the adversary sees | Notion needed | Provided? |
|---|---|---|---|
| PomFRIT one-more unforgeability (Algorithm 2) | None. The signer returns only a UOV preimage (`pomfrit.cpp:188-190`); the adversary makes every proof | Straight-line simultaneous PoK for ℓ+1 outputs | Yes (README theorem; §9.1). SE not needed |
| PomFRIT blindness | Final signatures, to the adversarial Issuer | ZK against the Issuer | **No.** (PU) fails because the Issuer knows `t = h ⊕ r` (lean/docs/zk.md §4). SE cannot help |
| PomFRIT, signatures shown to third parties (not in the paper's games) | Honest signatures | Strong SE w.r.t. `(pk, h)`, `refresher_com`, `refresher` | Yes. The real-to-simulated hop is valid against parties without `t` (`Pred = 2^{−128}`), but not for an adversary colluding with the Issuer |
| Moussaka issue (`issue.hpp:211-223`) and Ratatouille issue (`issue.hpp:203-215`) | Honest requests, if observed or relayed | Weak SE w.r.t. statement `(t, ctx_iss)` / `(c, t_init, ctx_iss)`. No binders | Yes, given the hop: (PU) holds computationally (lean/docs/zk.md, Keccak one-wayness) |
| Moussaka redeem (`redeem.hpp:291-309`) | Honest redemptions, possibly for statements chosen by the adversary (the origin picks `anchors`, `ctx_red` and `challenge_digest`, `moussaka.cpp:184-220`) | Weak SE w.r.t. statements, with adaptively chosen statements, so that a token cannot be redirected to another origin or challenge | Yes. `nf` and everything else is in the statement. Replays are left to the nullifier store |
| Ratatouille spend (`spend.hpp:411-434`) | Honest spends | Weak SE w.r.t. `(pk, nf, d, c_next, ctx_iss)`, so that `c_next` and `d` cannot be changed | Yes, as above |

**Summary.**
- No protocol needs more than weak SE w.r.t. statements, plus simultaneous extraction. Strong SE
  is a bonus: it covers anyone who keys on proof bytes.
- Binders matter only for PomFRIT, and there they are covered.
- The only unmet need is **ZK against the PomFRIT Issuer**. That is a (PU) failure of the CRT-mask
  construction (lean/docs/zk.md), not an extraction issue.
- For the Keccak relations, SE-based reductions in the presence of honest proofs pay `ε_ZK`,
  including lean/docs/zk.md's `Adv^{ow}_{Com}` term.

## 9. Remarks

### 9.1 Simultaneous extraction

Every bad event in the README's argument and in §6 is attached to a chain or a query, not to an
output. So one union bound covers any number of outputs. This is what PomFRIT's one-more reduction
and the token schemes' one-more reductions need. No factor `n_out` appears beyond the `+n_out`
verifier H₂³ queries.

### 9.2 The README's bound

The README charges `Q·(ε_KOS + ε_QS)`, with `Q` counting H₂³ queries. But a prover can make many
H₂¹ queries, look for a bad `chall₁` (the KOS bad event is checkable by the prover), and then
spend a single H₂³ query on that chain. So the union for L3 has to be over H₂¹ queries, and the
union for L4 over H₂² queries: `q₁·ε_KOS + q₂·(ε_QS + 2^{−128})`. The README's form is correct
when `Q` counts all H₂¹, H₂² and H₂³ queries. Theorem L8 is stated with per-oracle counts.

### 9.3 The extractor needs no trapdoor

`E` runs on `A`'s queries plus the public transcript of the `Prove` oracle (§2). It never sees
`Sim`'s seeds or coins. Feeding it `Sim`'s private queries would be wrong for lean/docs/zk.md's `Sim`:
- the hidden leaves would become alive and the simulated trees "known";
- the (α) argument would be lost;
- the uniform `ũ` and `c_mult` do not match those seeds.

## 10. Lean

`lean/VoleMole/Seed/SimExt.lean` has no `sorry` and no `axiom`. Check it with
`cd lean && lake env lean VoleMole/Seed/SimExt.lean`.

| Note | Lean |
|---|---|
| A pinned (copied) tree is fixed | `isFixed_of_pinned` |
| All trees pinned ⇒ `A ⊆ {Δ_s}`, `|A| ≤ 1` (case (α), and (β) with every tree copied) | `subset_singleton_of_all_pinned`, `card_le_one_of_all_pinned` |
| Per-H₂³-query form: at most one admissible output is accepted | `admissible_card_le_one_of_all_pinned` |
| Mixed chains satisfy the base theorem's `Claim4Hyp` | `claim4Hyp_of_pinned` |
| A free tree is fresh, known, and holds `u*` | `free_tree_is_fresh` |

Not formalized: the probabilistic lemmas 5.1–5.3 and 5.5, and the union bound.
