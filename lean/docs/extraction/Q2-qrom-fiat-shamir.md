# Q2: the QROM Fiat–Shamir lift (straight-line extraction against quantum provers)

Status: **[paper]**, with **[Lean]** for the linear-algebra and counting steps
(`lean/VoleMole/Seed/QROM.lean`) and reuse of the classical Lean results unchanged (§9). This is
README §L9, item Q2. AES is modelled as a quantum ideal cipher with Q1's key-level compressed
oracle. That is the repo's design (the `aes_ctr` leaf commitment stays). SHAKE leaf hashing
appears only in Remark 6.4.

## 0. Summary

**What is proved.** Theorem 7.1 gives an explicit bound on `Pr[V accepts ∧ E fails]` for every
quantum prover `P*` in the QROM plus the quantum ideal-cipher model (QICM). Here `E` is a
straight-line extractor. It runs `P*` once with all oracles simulated by compressed oracles. After
`V` has run, it applies Q1's extraction measurement to the hidden-leaf commitments, at most τ = 17
times. Then it computes the candidates `w^{(i)} = u_i ⊕ c_i ⊕ d` and outputs the first one that
satisfies R. `E` does no rewinding, no reprogramming and no measure-and-reprogram, and it extracts
nothing mid-run.

**Shape of the bound** (λ = 128, `N = 2^128`, `p = 1/(N(N−1))`):

    Pr[V accepts ∧ E fails]  ≤  Σ² + ε_multi + ε_rec (+ ε_Sim),
    Σ = 2√2·( Q₂₁√ε_KOS + Q₂₂√ε_QS + Q_c·2^{−64} + Q₂₃·√max(d,1)·2^{−64} ) + (collision terms),

where `Q_o` counts queries to oracle `o` (with `Q_c = q_c + 2q₂₃ + 1` for the relations with a
chall₂-combination). For `d = 9` the leading term is at most `200·q²·2^{−128}`.

**Numbers.** At `q = 2^64` the bound is vacuous (`≈ 200`). This is inherent: a Grover search over
the grinding counter reaches success `Ω(q²·d·2^{−128})` (§8). The q² part gives `2^{−20.4}` at
`q = 2^50` and `2^{−40.4}` at `q = 2^40`. The AES-specific term `ε_multi` (two touched keys open
the same leaf commitment, Q1 §5) gives `≈ 2^{−70}` at `q_E = 2^{30}` and `2^{−6.2}` at
`q_E = 2^{40}`, and is vacuous beyond. So with the key-level ideal cipher, the theorem is
meaningful for `q_E ≲ 2^{37}` cipher queries and `q ≲ 2^{55}` hash queries.

**Main new ingredient: Lemma T (§4).** It is a two-sided transition-capacity bound. It combines
CFHL's telescoping (Chung–Fehr–Huang–Liao, EUROCRYPT 2021, Lemma 5.6) with DFMS's *local*
commutator (Don–Fehr–Majenz–Schaffner, EUROCRYPT 2022, Lemma 3.3), or Q1's Lemma 3.1 for the
cipher. Its consequence: the bad database property need **not** be monotone. A query that
*removes* a database entry (the compressed oracle "forgetting" a key, or the prover expanding a
seed after chall₁) is bounded by the same `2√(2ρ)` as a query that adds one. This is the obstacle
that stops the FAEST spec §10.11 method (Lemma 10.44, from AHJ+23) from giving *knowledge*. Its
predicates need local witnesses, i.e. monotonicity, and "the extractor fails" is not monotone.

**Charging per oracle.** As the coordinator asked, ε_KOS is charged per H₂¹ query and ε_QS per H₂²
query. The `2^{−128}` of the chall₂-combination is charged per **H_comb** query. That includes 2
per H₂³ query, from the reduction in §3.2. In the QROM the combination vector `l` is a separate
oracle cell, so this is where it must be charged (§5.4, §10).

---

## 1. The interactive protocol behind the proof

### 1.1 The code (FS form)

Line numbers refer to `src/voleith.hpp` on branch `voleith-label-rows` (commit `d5def9c`), and `faest-arch-opt` means the patched read-only
copy in `subprojects/` (patches 0001–0005). These are the FAEST v3 parameters used by the repo: λ = 128, τ = 17, `w_grind = 8`,
`n_Δ = 120`, a `one_tree` BAVC with `L = 2304` leaves, the `aes_ctr` leaf commitment, and the CRT
VOLE.

| step | prover (`voleith_vole_gen`, `voleith_prove_commit`) | verifier (`voleith_vole_reconstruct`, `voleith_verify_commit`) |
|---|---|---|
| μ | `hash_mu`: `μ = H₂⁰(inst ‖ DST)`, or the constant `H₂⁴(DST)` when the instance is delayed (118–140) | same (386) |
| seed | `(r, iv_pre) = H₃(w_prefix ‖ μ ‖ ρ)` (186–201) | — |
| iv | `iv = H₄(iv_pre ‖ μ)` (205–211) | 388–394 |
| msg₁ | `crt_vole_commit` → `com` (= `vole_commit_check`), `c_1..c_16`, `c_mult` (220–221). Leaf `(i,j)`: `com_{i,j} = E_{k}(x_{0,i}) ‖ E_k(x_{1,i})`, `x_{c,i} = iv ⊞ (c,0,0,twk_i)` (Q1 §0; faest-arch-opt `vector_com.inc:1071-1085`). `h_i = H₁(com_{i,·})`, `com = H₁(h)` | `crt_vole_reconstruct` (406–410) recomputes the same quantities from the opening |
| chall₁ | `H₂¹(μ ‖ com ‖ c ‖ c_mult ‖ iv_pre ‖ chal1_binder)`, 136 bytes (223–233; `kos_vole_check.hpp:20`) | 413–423 |
| msg₂ | `ũ` (4λ bits), `h_V` (`kos_vole_check_sender`, 240), corrections `d` (244–250, 293–299) | `h_V` is **recomputed** from `Q`, Δ and `ũ` (`kos_vole_check_receiver`, 457; faest-arch-opt `kos_vole_check.hpp:139-178`) |
| chall₂ | `H₂²(chall₁ ‖ ũ ‖ h_V ‖ [μ_inst] ‖ chal2_binder ‖ d)`, 56 bytes (284–301; `constants.hpp:275`) | 452–468 |
| comb. | `l = H_comb(chall₂ ‖ dst)` inside `Relation::constraints` (`uov/circuit.hpp:59-71`; PomFRIT redeem, Moussaka redeem, Ratatouille spend) | same (482) |
| msg₃ | QuickSilver `ã` (`qs_proof`) and the prover's `qs_check` (303–312) | `qs_check` is **recomputed** from `Q`, Δ (485) |
| chall₃ | grinding: `Δ = H₂³(chall₂ ‖ qs_check ‖ ã ‖ ctr)` with the top 8 bits zero (314–333; faest-arch-opt `vector_com.inc:982-1060`) | `check_format` checks the zero bits (380; `faest_sig.hpp:126-133`). Accept iff `proof.delta() = H₂³(chall₂' ‖ qs_check' ‖ ã ‖ ctr)` (487–497) |
| msg₄ | the BAVC opening for Δ (`grind_and_open`) | the opening is consumed in `crt_vole_reconstruct` |

Two features matter below.
- The verifier's KOS and QuickSilver checks are **implicit**. The verifier recomputes the
  messages `h_V` and `qs_check` that the honest prover would have hashed, and accepts iff the hash
  chain reproduces Δ. So "check passes at Δ" means exactly "the verifier's recomputed hash input
  equals the input recorded in the chain".
- **Delayed instance binding.** With `instance == nullptr` in `voleith_vole_gen` (180, 287–290,
  460–463), μ in H₂¹ and H₄ is the instance-independent `H₂⁴(DST)`. The instance enters **only**
  through `μ_inst = H₂⁰(inst ‖ DST)` at a fixed offset of the H₂² input. In the non-delayed mode it
  enters through μ in the H₂¹ input. Binders are plain fields of the H₂¹ and H₂² inputs. They only
  separate chains.

### 1.2 The public-coin IP

The 7-round public-coin protocol whose FS transform is the code:
- `P → V`: msg₁ = (μ, com, c, c_mult, iv_pre, binder₁). This includes all leaf commitments
  `com_{i,j}` and `h`, which are the H₁-preimages; FAEST's IP⁺ (spec §10.11.6) makes them
  explicit.
- `V → P`: chall₁ ∈ {0,1}^{1088}.
- `P → V`: msg₂ = (ũ, h_V, [μ_inst], binder₂, d).
- `V → P`: chall₂ ∈ {0,1}^{448}, and `l ∈ F^M` for the three relations with a combined slot.
- `P → V`: msg₃ = (qs_check, ã).
- `V → P`: chall₃ = Δ ∈ {0,1}^{128}. It is rejected unless the 8 grinding bits are zero; the prover
  may resample by changing `ctr`.
- `P → V`: msg₄ = the opening.

The verifier accepts iff:
- the opening is consistent with the leaf commitments;
- the KOS check passes, i.e. the recomputed `h_V` equals msg₂'s;
- the QuickSilver check passes, i.e. the recomputed `qs_check` equals msg₃'s.

In the FS transform, chall₁ = H₂¹(msg₁), chall₂ = H₂²(chall₁ ‖ msg₂), `l = H_comb(chall₂ ‖ dst)` and
chall₃ = H₂³(chall₂ ‖ msg₃ ‖ ctr). The leaf commitments are not sent. They are bound through H₁ and
the cipher, and the prover's *knowledge* of them is the extraction problem.

### 1.3 Round-by-round knowledge soundness (the classical states)

With the leaf commitments explicit, define for a partial transcript and committed data `K` (the
extracted seeds of the alive leaves; §5.2):

| round | doomed/extractable state before the round | transition to non-doomed | error |
|---|---|---|---|
| chall₁ | data `K` fixed | chall₁ is KOS-bad for `K` (L3) | ε_KOS ≤ 2^{−153.5} |
| chall₂ | not KOS-bad; canonical `u*` (L4 §5) | `B₂(⊥)`: some uncombined constraint fails at `w* = u*+d` yet the χ-part of the top coefficient vanishes | ε_QS ≈ 2^{−128}(1+2^{−36.8}) |
| `l` | not `B₂(⊥)` | `B_l`: `Σ_k χ_k f_k(w*; l) = 0` | 2^{−128} |
| chall₃ | none of the above | Δ ∈ A and the extractor fails; by L6 that is ≤ max(d,1) strings | max(d,1)·2^{−128} |
| commitment rounds | — | a late H₁ preimage, a late key aligned with a target, an H₂⁰ preimage | ≤ (#targets)·2^{−256} |

The final row depends on how the commitments are modelled. That is exactly what the QROM lift has
to handle (§5). The A in the chall₃ row consists of zero-grinding strings only, which is why the
error is `max(d,1)·2^{−λ}` and not `·2^{−n_Δ}` (§8.2).

---

## 2. Model

- **Oracles.** `H₁` (256-bit output), `H₂⁰`/`H₂⁴` (256), `H₂¹` (1088), `H₂²` (448), `H_comb`
  (`128·M`, `M = 45`), `H₂³` (128), `H₃`, `H₄` (128). These are independent quantum random oracles,
  by domain separation (L0). The cipher `E` is a uniform `π : K → Sym({0,1}^128)` with forward and
  inverse quantum queries (Q1 §0).
- **Compressed oracles.** Every hash uses DFMS's compressed oracle (DFMS §2.2). Its cell `D_x` has
  basis `{|y⟩ : y ∈ {0,1}^n} ∪ {|⊥⟩}`, and a query is `cO = Σ_x |x⟩⟨x| ⊗ F_x CNOT F_x`. The cipher
  uses Q1's key-level compressed oracle (Q1 §2). Its cell `D_k` has basis `{|σ⟩ : σ ∈ Sym} ∪ {|⊥⟩}`,
  and `cO_k = F_k O_k F_k` with `O_k` controlled on `σ`. Both are perfectly indistinguishable from
  the real oracles (Zhandry 2019; Q1 P0).
- **Database basis.** A basis state of all oracle registers is a database `D` (a partial function
  per oracle). `|D|` is its number of non-⊥ cells. After `s` queries the joint state is supported
  on `|D| ≤ s` (Zhandry; Q1 Lemma 2.1, `run_mem_junta`).
- **Query counts.** `P*` makes `q₁, q₀, q₂₁, q₂₂, q_c, q₂₃, q₄, q_E` queries to `H₁`, `H₂⁰`, `H₂¹`,
  `H₂²`, `H_comb`, `H₂³`, `H₄` and the cipher (forward plus inverse). `q` is the total. Grinding
  attempts count in `q₂₃`. The queries are non-parallel, with a fixed oracle schedule, which is
  w.l.o.g. for counting per oracle.
- **Notation.** `ε_KOS` is from L3, `ε_QS = ε_QS(n)` from L4, `d` is QS_DEGREE, and `L = 2304`.

---

## 3. Two exact reductions (analysis only)

### 3.1 Putting iv into the H₂¹ cell

Let `H₂¹' : (x₁, iv) ↦ {0,1}^{1088}` be a fresh random oracle and define
`H̃₂¹(x₁) := H₂¹'(x₁, H₄(x₄(x₁)))`, where `x₄(x₁) = iv_pre ‖ μ` is parsed from `x₁`.

**Claim.** `(H̃₂¹, H₄)` is distributed exactly as `(H₂¹, H₄)`.

*Proof.* Given `H₄`, the map `x₁ ↦ (x₁, H₄(x₄(x₁)))` is injective. So `H̃₂¹` is a uniformly
random function independent of `H₄`. ∎

One quantum `H̃₂¹` query costs one `H₂¹'` query and two `H₄` queries (compute and uncompute `iv`).
So `P*` and `V` in the real world are exactly `P*'` and `V'` in this world. This is the quantum
form of L0–L2's normalization N1 ("query H₄ just before H₂¹"). Its effect: **a chain's iv is part
of its H₂¹' cell label.** No H₄ cell enters the bad property, so the "free iv" problems of L2 and
Q1 §5 never arise for the chain bookkeeping. `ε_multi` is the exception, handled in §6.3.

### 3.2 Putting `l` into the H₂³ cell (relations with a combined slot)

Likewise `H̃₂³(x₃) := H₂³'(x₃, H_comb(chall₂(x₃) ‖ dst))` is exact, at the cost of two `H_comb`
queries per `H₂³` query. **Effect:** each H₂³' cell carries the `l` it was answered under.

Without this, a Δ already assigned while the `l` cell is empty can become accepted when `l` is
filled. Lemma T would then charge `(#attached H₂³ entries)·2^{−128}` per `H_comb` query, which
gives a `q³·2^{−128}` term.

**Analysis counts:**
- `Q₂₁ = q₂₁ + 1`, `Q₂₂ = q₂₂ + 1`, `Q₂₃ = q₂₃ + 1`;
- `Q_c = q_c + 2q₂₃ + 1`, or 0 without a combined slot;
- `Q₁ = q₁ + τ + 1`, `Q₀ = q₀ + 2`;
- `Q_E = q_E + q_{E,V}`, where `q_{E,V}` is the verifier's cipher queries;
- `T` is the total, at most `q + 2q₂₁ + 2q₂₃ + q_V`.

The `+1`s and `q_V` are the verifier's queries.

---

## 4. Lemma T: two-sided transition capacity

**Setting.** Let `P` be a projector diagonal in the database basis (a "database property"). Run a
`T`-query algorithm against the compressed oracles from `|init⟩ ⊗ |⊥…⊥⟩`, with arbitrary unitaries
on the algorithm's registers between queries. Any classical query, including the verifier's, is a
unitary query followed by a measurement of the output register, which can be deferred. Let `Ψ_s`
be the state after `s` queries.

**Neutral values.** For a cell `x` of oracle `o` (range `Y_o`) and a database `D_{−x}` on the other
cells, let

    NN(x, D_{−x}) := { r ∈ Y_o : P(D[x↦r]) ≠ P(D[x↦⊥]) },     ρ_o(s) := max_{x, |D_{−x}| ≤ s−1} |NN(x, D_{−x})| / |Y_o|.

These are the *non-neutral* values: those whose effect on `P` differs from leaving the cell empty.

**Lemma T.** If the `s`-th query goes to oracle `o(s)`, then

    √Pr[measuring D at the end gives D ∈ P]  =  ‖P Ψ_T‖  ≤  Σ_{s=1}^{T} 2√2·√ρ_{o(s)}(s).

*Proof.*
1. **Telescoping.** `P` commutes with the unitaries between queries, and `‖P cO P v‖ ≤ ‖P v‖`. So
   `‖PΨ_s‖ ≤ ‖P cO (1−P) Ψ_{s−1}‖ + ‖PΨ_{s−1}‖`, and `PΨ_0 = 0` because `P(∅) = 0`. This is CFHL
   Lemma 5.6, and **[Lean]** `telescope`.
2. **Block decomposition.** `Ψ_{s−1}` is supported on `|D| ≤ s−1`, and `1−P` preserves that
   support. `cO` is block-diagonal in `(x, D_{−x})`: it is controlled on the query input `x`, acts
   on `D_x` only, and leaves `D_{−x}` alone. So `‖P cO (1−P)Ψ_{s−1}‖ ≤ max_{x,|D_{−x}|≤s−1}
   ‖Π_{S₁} cO_x Π_{S₀}‖·‖Ψ_{s−1}‖`, where `S₁ := {r ∈ Ȳ : D[x↦r] ∈ P}` and `S₀ := Ȳ ∖ S₁` (DFMS
   Cor. 2.2).
3. **The side without ⊥.** Exactly one of `S₁, S₀` contains `⊥`. Call the other one `S`. Then
   `S ⊆ NN(x, D_{−x})`: if `⊥ ∉ S₁`, every `r ∈ S₁` differs from `⊥`, and symmetrically. So
   `Π_S|⊥⟩ = 0` and `μ(S) := |S|/|Y_o| ≤ ρ_o(s)`.
4. **Transition ≤ commutator.** The block operator is either `Π_S cO_x (1−Π_S)` (insertion) or
   `(1−Π_S) cO_x Π_S` (removal). Both have norm `≤ ‖[cO_x, Π_S]‖`. **[Lean]**
   `proj_mul_mul_compl_le`, `compl_mul_mul_proj_le`.
5. **Local commutator.** `cO_x = F O F` with `O` controlled on the value basis of `D_x`, so
   `[O, Π_S] = 0`. Hence `‖[cO_x, Π_S]‖ ≤ 2‖[F, Π_S]‖` (**[Lean]** `conj_commutator_le`). Also
   `‖[F, Π_S]‖ = √(2μ − μ²) ≤ √(2μ)`.
   - For a random oracle this is DFMS Lemma 3.3: `‖[O^x, Π^x]‖ ≤ 2·2^{−n/2}√(2Γ_x)` with
     `Γ_x/2^n = μ(S)`.
   - For the cipher it is Q1 Lemma 3.1. Q1 states it for one target's fibre, but the proof uses
     only that `Π` is diagonal with `Π|⊥⟩ = 0` and `⟨u|Π|u⟩ = μ`: with `w = (|⊥⟩−|u⟩)/√2` and
     `a = Πw`, we get `‖a‖² = μ/2`, `⟨w|a⟩ = μ/2` and `[F,Π] = −2(|w⟩⟨a| − |a⟩⟨w|)`. So it holds
     for every relation `S ⊆ Sym`, for forward and inverse queries alike. ∎

**Remarks.**
- Step 3 is where monotonicity disappears. CFHL Thm 5.17 and AHJ+23 Lemma 1 (= spec Lemma 10.44)
  need "`⊥` has no more value than any `r`" (CFHL Def. 5.10(2)), i.e. `⊥ ∈ S₁ ⇒ S₀ = ∅`. Lemma T
  only needs the non-⊥ side to be small, whichever side that is.
- Constants. `2√2 < √10` (CFHL Thm 5.17), so Lemma T is also slightly sharper in the monotone
  case.
- Novelty. As far as I found, this combination is not stated in the literature. It is a direct
  consequence of CFHL Lemma 5.6 and DFMS Lemma 3.3. **Confidence: high.** The algebra is in Lean,
  and the `‖[F,Π]‖` computation is DFMS's and Q1's.

---

## 5. The bad property P

All definitions are deterministic functions of a basis database `D` in the reduced world of §3.
Fix the relation, so every hash input parses uniquely (L0 §2.5 O4).

### 5.1 Chains

A *chain* `c` is a non-⊥ `H₂¹'` cell `(x₁, iv) ↦ chall₁`. Its other parts:
- **Tree.** `com` is a field of `x₁`. `h` is the H₁-preimage of `com` in `D`, and `com_{i,·}` the
  H₁-preimage of `h_i`, chosen canonically (the least in a fixed order) if there are several. They
  are undefined if missing.
- **Targets.** `t_{c,i,j} := com_{i,j}`, at the points `x_{b,i}(iv)` with the chain's own iv.
- **Statement.** `inst(c)` is the H₂⁰-preimage of μ: of `x₁`'s μ in non-delayed mode, of `x₂`'s
  `μ_inst` in delayed mode.
- **Stage 2.** An H₂² cell `x₂ ↦ chall₂` whose 136-byte prefix equals `chall₁` *attaches* to `c`.
- **Stage 2'.** The `H_comb` cell `(chall₂ ‖ dst) ↦ l`.
- **Stage 3.** An H₂³' cell `(x₃, l') ↦ Δ` whose 56-byte prefix equals `chall₂`. It is
  *consistent* if `l' = D_comb(chall₂ ‖ dst) ≠ ⊥`.

### 5.2 Committed data (quantum Definition B)

Leaf `(i,j)` of `c` is **alive** iff some key `k` in the key database has
`σ_k(x_{0,i}(iv)) ‖ σ_k(x_{1,i}(iv)) = t_{c,i,j}`, i.e. Q1's `Ext ∈ K ∪ {multi}`. Its **committed
seed** is the least such key. Otherwise the leaf is **dead**, and leaves with undefined targets are
dead too. The following are deterministic functions of `D`:
- the committed per-tree data (`u^{(i)}`, `V_i` via ConvertToVOLE of the committed seeds, using the
  values `σ_k` held in `D`);
- `S`, `r(Δ')` and `A_V` (L3 §1, L4 §5);
- the canonical `u*` and `w* = u* + d` (L4 §5);
- `known(c)`, the trees with no dead leaf.

This is the key-level form of L0–L2's Definition B (one block recorded, the other a cipher value),
as Q1 §3 states. A key in the database carries its whole permutation, so "recorded block" is not
needed. The **canonical** choice of seed replaces L1's uniqueness. Two keys aligned with one target
are *not* part of `P` (§6.3).

**Accepting set.** For a chain, an attached `x₂` and a consistent `(x₃, l)`, let `A(c,x₂,x₃,l)` be
the set of `Δ ∈ {0,1}^{128}` such that:
- the top 8 bits of Δ are zero, and the opening for the decoded Δ' exists (`T_open`);
- every dead leaf is hidden (`Δ_i = j`);
- the KOS check computed from the committed data gives `x₂`'s `h_V`;
- the QuickSilver check computed from the committed data, `inst(c)`, `chall₂` and `l` gives
  `x₃`'s `qs_check`.

If `inst(c)` is undefined, set `A := ∅` and let `B₂`, `B_l` and `B₃` below be false. A later
H₂⁰ answer that defines `inst(c)` is then a non-neutral value counted in (N-H₂⁰).

**Extractor predicate.** `Ext_D(c, x₂)` holds iff some tree `i ∈ known(c)` has a candidate
`u^{(i)} + d` (with `d` from `x₂`) that satisfies R(inst(c), ·). For `Δ ∈ A`, the hidden leaf of a
known tree is alive, so this is what `E` computes. It does not depend on Δ (§9).

### 5.3 The property

`P(D) := COL ∨ ∃c: B₁(c) ∨ ∃(c,x₂): B₂(c,x₂) ∨ B_l(c,x₂) ∨ ∃(c,x₂,x₃,l) consistent: B₃`.

The components:
- **COL.** Two distinct non-⊥ cells with equal outputs in `H₁`, in `H₂⁰`, in `H₂¹'` or in `H₂²`.
- **B₁(c).** `chall₁` is KOS-bad for `c`'s committed data, in L3's sense: some triple in `S` has
  `δ_Q ≠ 0` and `H_c(δ_Q) = −δ_D` (L3 §5).
- **B₂(c,x₂).** `¬B₁(c)`, `inst(c)` is defined, some uncombined constraint fails at `w*`, and
  `Σ_{k≠k₀} χ_k g_k = 0 ∧ (χ_{k₀} = 0 ∨ a = 0)`. Here `g_k = f_k(w*)` for `k ≠ k₀`, `a = (a_m(w*))`,
  and `χ = χ(chall₂)` (L4 §3–6). This says the top coefficient vanishes for *every* `l`. Without a
  combined slot it is just `Σ_k χ_k f_k(w*) = 0`.
- **B_l(c,x₂).** `l` is defined, some uncombined constraint fails, and
  `Σ_k χ_k f_k(w*; l) = 0`.
- **B₃(c,x₂,x₃,l).** `Δ = D(x₃,l) ∈ A(c,x₂,x₃,l)` and `¬Ext_D(c,x₂)`.

### 5.4 Non-neutral counts, cell by cell

For each oracle, `NN` is bounded for every `(x, D_{−x})` with `|D_{−x}| ≤ T`. If `D[x↦⊥] ∈ P` by a
component that the cell cannot influence, every value is neutral. The cases below therefore assume
the opposite where needed.

**(N-H₂¹') Cell `(x₁, iv)`, value `r = chall₁`.**
- The cell only creates chain `c`. Other chains are untouched unless `r` collides (COL).
- Non-neutral values:
  - `r` equal to another chain's `chall₁` (COL);
  - `r` equal to the prefix of an existing H₂² input (attachment);
  - `r` with `B₁(c)`.
- `c`'s committed data is a function of `D_{−x}`: the tree, the keys and `iv` in the label. So L3
  applies with fixed data: `Pr_r[B₁] ≤ ε_KOS`. This is precisely where L3's hypothesis "data fixed
  before chall₁" is used, with no notion of time.
- So `ρ₂₁ ≤ ε_KOS + (Q₂₁+Q₂₂)·2^{−1088}`.

**(N-H₂²) Cell `x₂`, value `r = chall₂`.**
- If `B₁(c)` holds, all values are neutral.
- Otherwise the non-neutral values are:
  - COL (≤ Q₂₂ values);
  - `r` equal to the prefix of an existing H₂³' input (≤ Q₂₃) or the `chall₂` part of an existing
    `H_comb` input (≤ Q_c, the "pre-queried `l`" of L4);
  - `r` with `B₂`.
- `w*`, the statement, `g` and `a` are fixed by `D_{−x}` (L4 §5).
- `Pr_r[B₂] ≤ ε_QS` by L4's Proposition 2. If `g ≠ 0`, apply it to the nonzero vector
  `(g_k)_{k≠k₀}` padded with 0 at `k₀`. If `g = 0`, the failing constraint is in `a ≠ 0`, and
  `χ_{k₀} = 0` is the event for the unit vector `e_{k₀}`.
- So `ρ₂₂ ≤ ε_QS + (Q₂₂ + Q₂₃ + Q_c)·2^{−448}`.

**(N-H_comb) Cell `chall₂ ‖ dst`, value `l`.**
- Assume `¬B₂(⊥)`. Then either `Σ_{k≠k₀}χ_k g_k ≠ 0` with `χ_{k₀}a = 0`, so the top coefficient is
  a nonzero constant and `B_l` is impossible; or `χ_{k₀}a ≠ 0`, so the top coefficient is a
  non-constant affine function of `l` and `Pr_l[B_l] = 2^{−128}` (`card_combination_eq_zero`).
- The value also makes attached H₂³' cells with label `l' = l` consistent, which is at most `Q₂₃`
  values.
- So `ρ_c ≤ 2^{−128} + Q₂₃·2^{−128M}`.

**(N-H₂³') Cell `(x₃, l)`, value `Δ`.**
- If the label is inconsistent, or the chain has `B₁`, `B₂` or `B_l`, all values are neutral. Δ is
  never an input to another oracle.
- Otherwise the hypotheses of L6 hold for this chain:
  - `Claim4Hyp` from L3 and L1 on the committed data: `claim4Hyp_of_kosGood`, with `known` the
    trees with no dead leaf and `unknown_fixed` because dead leaves are hidden on `A`;
  - Claim 3's dichotomy and `hbits` from L4 (`claim3_of_circuit`), valid for this `l` by `¬B_l`.
- So `card_B3_le` (**[Lean]**, which wraps `accepting_card_le`) gives `|NN| ≤ max(d,1)`, and
  `ρ₂₃ ≤ max(d,1)·2^{−128}`.

**(N-H₁) Cell `x`, value `r`.** `r` is non-neutral only if it equals one of the following:
- a `com` field of a chain (≤ Q₂₁);
- an `h`-block of a length-545 H₁ input (≤ 17Q₁);
- another H₁ output (COL, ≤ Q₁).

Any other `r` links nowhere, so `D[x↦r]` and `D[x↦⊥]` give the same trees. Hence
`ρ₁ ≤ (Q₂₁ + 18Q₁)·2^{−256}`. This covers L1's Hit₁ (late tree completion) as a transition, without
any time ordering.

**(N-H₂⁰) Cell `x`, value `r`.** `r` is non-neutral only if it equals a μ field of an `H₂¹'` label
or an H₂² input, or another H₂⁰ output. So `ρ₀ ≤ (Q₂₁+Q₂₂+Q₀)·2^{−256}`. This is L4's (H-stmt) as a
transition.

**(N-E) Key cell `k`, value `σ`.**
- If `σ` is aligned with no target of any chain, `k` is no chain's committed seed. Its permutation
  enters no committed data, no `A` and no `Ext_D`. So `D[k↦σ]` behaves as `D[k↦⊥]`.
- Hence `NN ⊆ {σ : ∃ target t at points (x₀,x₁) with σ(x₀)‖σ(x₁) = t}`, and by Q1 (F1),
  `ρ_E ≤ (#targets)·p ≤ Q₂₁·L·p`.
- This single count covers three things:
  - *late keys* (L2's Post: a dead leaf revived after chall₁);
  - *forgetting* (an aligned key's cell returning to ⊥ or to an unaligned value: the removal side of
    Lemma T);
  - *seed expansion after chall₁*: a ConvertToVOLE, GGM or opening query to an aligned key `k` is a
    query to cell `k`, and it can change `k`'s status only with amplitude `≤ 2√(2ρ_E)`.

  This is the sketch's flagged subtlety ("committed data is fixed per chain before chall₁, but the
  prover may expand seeds after chall₁"). It reduces to the local commutator.

**(N-H₄, N-H₃).** `P` reads no `H₄` or `H₃` cell. `ρ = 0`.

---

## 6. From "V accepts and E fails" to `D ∈ P`

### 6.1 The extractor

`E(x, P*)` works as follows.
1. Run `P*`, answering hash queries with compressed oracles and cipher queries with Q1's
   simulator. Then run `V` on the output (inst, π, binders) with the same oracles, as classical
   queries.
2. From `V`'s recomputation, read Δ, `iv` and the hidden commitments `com_{i,Δ_i}`. For each
   `i < τ` apply `Ext_{(iv, twk_i)}(com_{i,Δ_i})` (Q1 §3).
3. For each returned key, compute the candidate `w^{(i)} = u_i[0..ℓ) ⊕ c_i ⊕ d`. ConvertToVOLE uses
   the opened seeds and the extracted seed, evaluating the cipher through the simulator.
4. Output the first candidate with R(inst, w^{(i)}).

The simulation is perfect (§2), so `Pr[V accepts]` is the real-world value. The reductions of §3
change only the H₂¹ and H₂³ simulation. The reduced state on `P*`'s registers and the key database
is identical, because both worlds purify the same distribution of random functions. So `E`'s output
distribution is the one analysed below.

All `Ext` measurements are diagonal in the database basis. Their joint outcome is the marginal of
a full computational-basis measurement of `D` at the end. Measuring all of `D` is therefore
w.l.o.g. for the analysis.

### 6.2 Lemma F

Define two events on the final measured database:
- **Rec.** Every classical query of `V` is recorded:
  - `D(x) = y` for its hash queries;
  - for each opened leaf, `V`'s key `s'` is in the key database with `σ_{s'}(x_{b,i}) = c'_b` for
    `b = 0, 1`.
- **MULTI_end.** Some leaf of the accepted chain has two distinct aligned keys.

**Lemma F.** `V accepts ∧ E fails ∧ Rec ∧ ¬MULTI_end ⇒ D ∈ P`.

*Proof.* Let `c` be `V`'s `H₂¹'` cell. If COL holds, we are done. Otherwise:
1. **Tree.** `V`'s H₁ queries are recorded, so `c`'s tree is `V`'s tree (L1.4).
2. **Opened leaves and seeds.** `V`'s keys for the opened leaves are recorded and aligned, so those
   leaves are alive. By `¬MULTI_end` the committed seeds equal `V`'s seeds `s'` (L2(b)). The dead
   leaves are therefore hidden.
3. **Checks.** `V`'s recomputed `h_V` and `qs_check` equal the committed-data values, which are
   exactly the fields of `V`'s recorded `x₂` and `x₃`.
4. **Consistency.** `V`'s `l` is recorded, so `(x₃, l)` is consistent.
5. **Δ ∈ A.** Δ is recorded, has zero grinding bits (`check_format`), and the opening succeeded.
   So `Δ ∈ A`.
6. **Statement.** `inst(c)` is `V`'s instance, since H₂⁰ is recorded and there is no COL.
7. **Extractor.** By `¬MULTI_end`, `Ext` returns the committed seed of every alive hidden leaf. So
   `E` fails iff `¬Ext_D(c, x₂)`.

Hence `B₃`. ∎

**Pr[¬Rec] ≤ ε_rec.** After a classical query with answer `y`, cell `D_x` is `F|y⟩`, since no
measurement on `D` precedes it. Measuring gives `y` with probability `≥ 1 − 2^{−n}` (DFMS eq. (8)).
For keys, Q1 P3 gives `≤ 2p` per checked key. So

    ε_rec ≤ 2^{−128} (H₂³') + 2^{−447} + (τ+3)·2^{−256} + 2Lp  ≈  2^{−128}.

The evaluations in `E`'s step 3 agree with the measured `σ_k` except with probability `2p` per key
(Q1 P2/(I4)). This is absorbed into `ε_rec` (`2τp`).

### 6.3 ε_multi (AES-specific)

`MULTI_end` implies that two keys agree on `{z, z ⊞ e₀}` with `z = x₀(iv, twk_i)`, where `iv` is
the accepted chain's iv. That iv is an `H₄` output recorded by `V`. This is Q1's `multi` event:

    ε_multi ≤ min{ ε_multi^free, ε_multi^{H₄} }.

- **Free iv.** Lemma T, applied to `Z(D_E) ≠ ∅` with Q1 (F2), gives
  `ρ_E(s) ≤ s/(N−1)`. So `ε_multi^free ≤ (2√2·Σ_{s<Q_E}√(s/(N−1)))² ≤ (32/9)·Q_E³/(N−1)`. That is
  `≈ 3.6·Q_E³·2^{−128}`, a tenth of Q1 Thm 5.1's `(320/9)` (no full-value reduction, `2√2` instead
  of `√10`).
- **Using H₄.** Q1 Thm 5.2, with `q₄ := q₄ + 2q₂₁ + 1` because §3.1 adds H₄ queries:
  `≈ 1.8·10⁷·(2Q_E + q₄ + 2q₂₁ + 1)⁵·2^{−256} + 2^{−127}`, valid while Q1's `θ ≤ 1/2`, i.e.
  `≲ 2^{37}`.

**Why `multi` is not in P.** Putting "two keys aligned with a target" into `P` would make the
`H₂¹'` transition non-neutral for *every* `r` whenever the label's iv hits an agreement point.
`ρ₂₁` would then be 1. With canonical seeds the run-time bookkeeping never needs uniqueness, and
`multi` is paid once, at the end. This is the "intrinsic to key-level reasoning" weakness of Q1 §9.
It is the term that limits the theorem to `q_E ≲ 2^{37}`–`2^{40}`.

**Remark 6.4 (not the repo's design).** With faest-arch-opt's `leaf_hash::shake` the leaf
commitment is a random-oracle output, and `multi` becomes a 256-bit output collision,
`O(q³·2^{−256})`. Lemma T and §5 apply verbatim with `ρ_E` replaced by `Q₂₁·L·2^{−256}`. No ideal
cipher and no permutation simulation are needed. The maintainer rejected this switch (README §L9).

---

## 7. Main theorem

**Theorem 7.1.** For every quantum prover `P*` with the query counts of §2 and analysis counts of
§3, and the extractor `E` of §6.1:

    Pr[V accepts ∧ E fails]  ≤  Σ² + ε_multi + ε_rec (+ ε_Sim),

    Σ := 2√2·[ Q₂₁·√(ε_KOS + (Q₂₁+Q₂₂)·2^{−1088})
             + Q₂₂·√(ε_QS + (Q₂₂+Q₂₃+Q_c)·2^{−448})
             + Q_c·√(2^{−128} + Q₂₃·2^{−128M})
             + Q₂₃·√(max(d,1)·2^{−128})
             + Q₁·√((Q₂₁+18Q₁)·2^{−256})
             + Q₀·√((Q₂₁+Q₂₂+Q₀)·2^{−256})
             + Q_E·√(Q₂₁·L·p) ],

with `ε_multi` from §6.3, `ε_rec ≈ 2^{−128}` from §6.2, and `ε_Sim` the cipher-simulation error
when `E` is to be efficient (§10).

*Proof.*
1. By §6.1 and Lemma F, `Pr[accept ∧ E fails] ≤ Pr[D ∈ P] + Pr[¬Rec] + Pr[MULTI_end]`.
2. By Lemma T, `√Pr[D ∈ P] ≤ Σ_s 2√2·√ρ_{o(s)}(s)`.
3. §5.4 bounds `ρ_o(s)` for every oracle by the bracketed quantity of `o`, using `s ≤ T` and
   database sizes `≤` the respective counts. Group the queries by oracle. ∎

Without a combined slot (Moussaka issue, Ratatouille issue) the `Q_c` term is absent and
`Q_c = 0` elsewhere.

### 7.1 Numbers (λ = 128)

Inputs: `ε_KOS ≤ 2^{−153.5}` (L3 §6, all relations), `ε_QS ≤ 2^{−128}(1+2^{−36.8})` (L4 §7),
`d ∈ {2, 9}`, `L = 2304`, `M = 45`. Per-query coefficients of `2√2·2^{−64}` in Σ:

| oracle | coefficient | note |
|---|---|---|
| H₂³ | `√max(d,1) + 2` = 5 (`d = 9`), 3.41 (PomFRIT); 3 without a combined slot | `+2`: the two `H_comb` queries of §3.2 |
| H₂² | ≈ 1 | `√ε_QS·2^{64}` |
| H_comb | 1 | |
| H₂¹ | `2^{−12.75}` | `√ε_KOS·2^{64}` |
| H₁, H₂⁰, cipher | ≤ `2^{−30}` up to `q = 2^{64}` | collision and alignment terms |

With all `q` queries on the worst oracle, the leading part is
`Σ² ≤ 8·(5q·2^{−64})² = 200·q²·2^{−128}` (**[Lean]** `main_term_eq`).

| `q` (and `q_E = q`) | `200q²/2^{128}` | `ε_multi` (min of §6.3) | collision terms | total |
|---|---|---|---|---|
| `2^{30}` | `2^{−60.4}` | `≈ 2^{−70.3}` (Q1 Thm 5.2 with `q₄ ↦ q₄+2q₂₁+1`, `q₄ = q₂₁ = 2^{30}`) | `< 2^{−130}` | `≈ 2^{−60.4}` |
| `2^{40}` | `2^{−40.4}` | `2^{−6.2}` (free; the H₄ bound is not applicable) | | `≈ 2^{−6.2}` |
| `2^{50}` | `2^{−20.4}` (**[Lean]** `main_term_at_2_50`) | vacuous | | vacuous |
| `2^{60}` | `2^{−0.36}` | vacuous | | vacuous |
| `2^{64}` | `200` (**[Lean]** `main_term_at_2_64`) | vacuous | | vacuous |

Separate budgets matter. For example, with `q_E ≤ 2^{30}` cipher queries and `q ≤ 2^{50}` hash
queries the bound is `≈ 2^{−20.4}`. At `q = 2^{64}`:
- the KOS term alone is `8q²ε_KOS ≤ 2^{−22}` (**[Lean]** `kos_term_at_2_64`);
- the H₁ term is `8·19·q³·2^{−256} ≈ 2^{−56.7}`;
- the cipher alignment term is `8Q_E²Q₂₁Lp ≈ 2^{−49.8}`.

So the vacuity at `2^{64}` comes entirely from the challenge-round Grover terms and from `multi`.

---

## 8. The q² loss and grinding

### 8.1 The q² loss is inherent

A cheating prover can commit to a non-witness and arrange the QuickSilver check polynomial to have
`d` roots, chosen as lifts `e(Δ')` of zero-grinding challenges. It then accepts iff Δ hits one of
`d` strings out of `2^{128}`. Grover over `ctr` with `q₂₃` H₂³ queries succeeds with probability
`≈ sin²((2q₂₃+1)·√(d·2^{−128})) ≈ 4q²d·2^{−128}`. Theorem 7.1's H₂³ term is `8(√d+2)²q²·2^{−128}`,
within a factor `2(1+2/√d)² ≈ 5.6` for `d = 9`. The H₂² term is likewise matched by Grover over
chall₂. So no QROM bound can avoid `Ω(q²·2^{−128})`. At `q = 2^{64}` every such bound is `Ω(1)`,
including FAEST's own spec Lemma 10.49 for EM, `10(τ+1)Q³2^{−2λ} + 10Q²d·2^{−λ}`, which is `90` at
`Q = 2^{64}`, `d = 9`. NIST level 1 is defined relative to AES-128 key search, which is itself a
`2^{64}`-query Grover problem. The meaningful reading is "`≤ 2^{−k}` for `q ≤ 2^{(120.4−k)/2}`".
(The attack's construction of roots in the image of `e` is plausible but not checked in detail.)

### 8.2 Grinding

`A` contains only strings with 8 zero bits. So in the H₂³ transition `|NN| ≤ max(d,1)` counts
strings in `{0,1}^{128}`, and the density is `d·2^{−λ}`, not `d·2^{−n_Δ} = d·2^{−120}`. A quantum
adversary gains nothing from grinding. Grover over `ctr` has amplitude `√(d·2^{−128})` per query
whether or not the zero bits are required, because the bits are part of the target set.

This is exactly FAEST's accounting: spec §2 "Optimization 2" ("any forger must perform the same
`2^{w_grind}` expected hash evaluations per attempt") and spec Lemma 10.48 (`ε₃ = d_zk·2^{−λ}`). The
honest prover's `2^8` grinding work is not counted against security. Every adversarial attempt is
one H₂³ query in `Q₂₃`. The reduced `n_Δ = 120` only enters `ε_KOS` through `|S| ≤ 2^{120}`, which
helps.

---

## 9. What is reused from the classical Lean development, and how

Lemma T and §5.4 work on **one basis database at a time**. Every deterministic statement about
committed data is therefore used unchanged, with the database supplying the data. In
(N-H₂³'), for a fixed `D_{−x}` with `¬B₁, ¬B₂, ¬B_l` and a consistent label, instantiate as
follows:
- `ι` is the τ trees, `B i` the challenge blocks, and `e` the CRT lift (injective);
- `A` is `A(c,x₂,x₃,l)`, decoded;
- `known` is the trees with no dead leaf in `D`;
- `u i j` is bit `j` of the committed `u^{(i)}`, i.e. ConvertToVOLE of the canonical seeds;
- `Q` is the verifier's key rows from the committed data;
- `uStar` is the canonical `u*`;
- `sat` is "every uncombined constraint holds", which implies R by L7;
- `dzk = d`, `Z` is the zero-grinding strings, `δ` is decoding, and `acc = (∈ A)`.

The hypotheses then come from these sources:
- `Claim4Hyp` (`tree_form`, `consistent`, `unknown_fixed`, `lift_inj`) from L3's
  `claim4Hyp_of_kosGood` (`Seed/KOS.lean`) on `¬B₁`;
- `hclaim3` and `hbits` from L4's `claim3_of_circuit` (`Seed/QuickSilver.lean`) on `¬B₂ ∧ ¬B_l`;
- `hclaim1` by definition of `acc`.

`accepting_card_le` (`SeedExtraction.lean`) yields "some known tree's candidate satisfies `sat`, or
`#{x ∈ Z | acc x} ≤ max d 1`". `card_B3_le` (`Seed/QROM.lean`) restates this as
`#{Δ ∈ Z : Δ ∈ A ∧ ¬Ext} ≤ max d 1`, the non-neutral count. It also uses the observation that
`Ext` does not depend on Δ. `extraction_cases` and `free_tree_holds_witness` enter through
`accepting_card_le`.

So nothing in the classical Lean files changes. The quantum part only changes *which database*
they are applied to, and the probability step that consumes their output: Lemma T instead of a
union bound.

---

## 10. Interface assumed from Q1

Used (all from `Q1-quantum-ideal-cipher.md`):
- **(Q1-a)** Key-level purification and compression are perfect (Q1 §1–2, P0). The support is on
  `≤ s` keys after `s` queries (Lemma 2.1, `run_mem_junta`).
- **(Q1-b)** Local commutator: `‖[cO_k, Π_S]‖ ≤ 2√(2μ(S))` for every relation `S ⊆ Sym(X)`, for
  forward and inverse queries. Q1 Lemma 3.1 proves it for one target's fibre. The same proof, which
  uses only diagonality, `Π|⊥⟩ = 0` and `⟨u|Π|u⟩ = μ`, gives every `S`; it is re-derived in §4,
  step 5.
- **(Q1-c)** Counting facts (F1) `μ(fibre) = p` and (F2) `Pr_σ[agreement with σ' on an adjacent
  pair] ≤ 1/(N−1)`.
- **(Q1-d)** Recording and validity: P3, the `2p` in `ε_rec`, and P2/(I4).
- **(Q1-e)** `ε_multi^{H₄}`: Thm 5.2 as stated, with the H₄ count adjusted.

**Not used:**
- Q1's global commutator `δ = 8√(2p)`;
- Theorem 4.2 (`ε_dead^Q` and persistence);
- the "Ext at Θ's time" definition (I2).

`E` extracts only at the end, so no `Ext` is ever commuted past a query. Dead leaves, late keys,
persistence and forgetting are all handled by (N-E) through (Q1-b). The quantum "alive" of §5.2 is
evaluated on the current database, so no time is needed. Q1 (I2)'s "alive at Θ's time" is the
special case `D_{−x}` at the moment `x = Θ`'s cell is filled.

**Efficient simulation.** The bound is proved with Q1's information-theoretic `S^IC`. An
**efficient** `E` needs a cipher simulator that:
1. answers `P*`'s and `V`'s forward and inverse queries;
2. supports at most τ classical `Ext` queries **after** the run;
3. evaluates the cipher under extracted keys.

It must be `ε_Sim`-close to `S^IC` on the joint classical output (`P*`'s output, `V`'s verdict, the
`Ext` outcomes, `E`'s evaluations), in the sense of Q1 §6. Then Theorem 7.1 holds with `+ε_Sim`.
The lift does **not** need mid-run extraction or commutation of `Sim`'s `Ext` with queries. Lemma T
is applied in the `S^IC` model only. Q4 is handling `ε_Sim`. Q3 notes that statistical options
cost `≳ q·2^{−64}` (Carolan–Majenz), which would dominate `200q²·2^{−128}` for `q < 2^{64}`.

---

## 11. Gaps and confidence

| step | status | confidence |
|---|---|---|
| §1 protocol and FS mapping (code read, line refs) | done | high |
| §3 reductions (iv into H₂¹', `l` into H₂³') | exact | high |
| Lemma T | proof given; algebra in Lean; `‖[F,Π]‖` from DFMS/Q1 | high |
| §5.4 non-neutral counts | proofs given; H₂³ case in Lean via `accepting_card_le` | high for the hashes; medium-high for (N-E), which rests on (Q1-b) generalized |
| Lemma F | proof given | high |
| use of L3, L4 with data from `D_{−x}` | their "fixed before the challenge" hypotheses hold by construction | high, given L3 and L4 |
| ε_multi | imported (Q1 Thm 5.2) or re-derived (free iv, Lemma T) | medium (Q1's Thm 5.2 is long); free-iv bound high |
| efficient extractor | **open** (ε_Sim, Q4) | — |
| tightness (§8.1) | heuristic attack | medium |

**Gaps, stated plainly.**
1. **AES key-level `multi`.** This is the dominant weakness. With the key-level QICM the theorem
   says nothing beyond `q_E ≈ 2^{37}`–`2^{40}` cipher queries, far below the Grover-inherent
   `q ≈ 2^{60}`. A point-level compressed ideal cipher (Q1 §9.2 fallback) or the SHAKE leaf hash
   (Remark 6.4) would remove it.
2. **Efficiency of `E`**, as in §10.
3. **Simulation-extractability (L8) in the QROM is not covered.** Simulated proofs require
   reprogramming H₂³ (and H₂¹, H₂²) at points that are only computationally unpredictable. The
   spec's §10.11.3 tools (GHHM21 adaptive reprogramming, "quantum guesses") would have to be
   combined with Lemma T. That is a separate task.
4. **Non-parallel queries only.** Parallel queries would follow CFHL's `k`-parallel versions, but
   they are not done.
5. **Literature.** I did not obtain Chiesa–Manohar–Spooner 2019 (ePrint 2019/834; access blocked).
   Their Lemma 8 is a commutator bound that DFMS compare to theirs, and their BCS knowledge
   argument may contain an equivalent of Lemma T. ePrint 2023/1256 states that QROM *knowledge*
   for BCS from special soundness was open as of 2023. Neither DFM20's multi-round
   measure-and-reprogram (a `(2q+1)^{6}` multiplicative loss for three challenges) nor DFMS Thm 5.4
   (single challenge, then DFM20) gives a useful multi-round bound.

## References

- [CFHL21] K.-M. Chung, S. Fehr, Y.-H. Huang, T.-N. Liao, *On the Compressed-Oracle Technique, and
  Post-Quantum Security of Proofs of Sequential Work*, EUROCRYPT 2021; arXiv 2010.11658. Def. 5.5,
  Lemma 5.6, Def. 5.10, Thms 5.17, 5.23.
- [DFMS22] J. Don, S. Fehr, C. Majenz, C. Schaffner, *Online-Extractability in the Quantum
  Random-Oracle Model*, EUROCRYPT 2022, LNCS 13277; arXiv 2103.03085. §2.2 and eq. (8), Cor. 2.2,
  Lemma 3.3, Thm 3.1, Thm 4.3, Cor. 4.8, Thm 5.4.
- [DFM20] J. Don, S. Fehr, C. Majenz, *The Measure-and-Reprogram Technique 2.0: Multi-Round
  Fiat–Shamir and More*, CRYPTO 2020; arXiv 2003.05207. Not used; see gap 5.
- [CMS19] A. Chiesa, P. Manohar, N. Spooner, *Succinct Arguments in the Quantum Random Oracle
  Model*, TCC 2019; ePrint 2019/834. Round-by-round soundness gives QROM FS/BCS soundness with
  `O(q²)` loss. Not retrieved.
- [AHJ+23] Lemma 1, as quoted in the FAEST v3 spec, Lemma 10.44.
- FAEST v3.0 specification (1 Sep 2026), §2 (grinding), §10.9.4, §10.11.1–10.11.8 (Def. 10.39,
  Thm 10.46, Lemmas 10.48, 10.49). Local copy in the session scratchpad, reference only.
- [Zha19] M. Zhandry, *How to Record Quantum Queries*, CRYPTO 2019.
- Repo: `lean/docs/extraction/L0-L2-commitments.md`, `L3-kos.md`, `L4-quicksilver.md`,
  `Q1-quantum-ideal-cipher.md`, `Q3-aes-models.md`; `lean/VoleMole/SeedExtraction.lean`,
  `lean/VoleMole/Seed/{KOS,QuickSilver,QuantumCipher,QROM}.lean`.
