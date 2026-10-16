# L0–L2: oracle uses, committed data, binding, and dead leaves

This file proves Lemmas L0, L1 and L2 of `README.md` for the repo's five relations (FAEST-EM-128f
VOLEitH, λ = 128, τ = 17, n_Δ = 120, `one_tree` BAVC, `aes_ctr` leaf commitment). Every protocol
fact is checked against the code. `voleith.hpp` means `src/voleith.hpp`. A bare faest file name
means the patched copy in `subprojects/faest-arch-opt/`. Line numbers in `src/` and in the patched
faest files refer to branch `voleith-label-rows` (commit `d5def9c`), with faest-arch-opt patches 0001–0005 applied. Of the files used
here, the repo's patches change only `vole_commit.inc`, `constants.hpp` and `quicksilver.hpp`. In
`vole_commit.inc`, patch 0002 widens the H₅ output from 16 to 32 bits, and patch 0005 derives the
CRT gate labels from λ dedicated VOLE rows after the witness (`CRT_DEDICATED_LABEL_ROWS`, set by
all five relations). Patch 0005 changes which rows feed the H₅ labels and lengthens each
correction `c_i` by λ bits (`VOLE_CORRECTION_ROWS = ℓ + λ`), but no oracle's input layout or domain
tag. The results of this file are unaffected: L1 and L2 commit to the corrections whatever their
length, and seed extraction never uses the gate labels.

The AES part of L0 and the domain-tag table are machine-checked in
`lean/VoleMole/Seed/Commitments.lean` (no `sorry`, no `axiom`).

## 0. Summary

**L0 (proved).** In scope are all SHAKE128 calls reachable from `voleith_*` and from the
relations' constraint code. They fall into twelve domains, listed in §2.1. Any two domains differ
in their final byte, or (for the three H₁ shapes, which share final byte `0x01`) in their fixed
input length. So the input sets are pairwise disjoint. Prefix-freeness is neither true nor needed.
QuickSilver's χ and the KOS universal-hash keys are not hashes: they are read straight from the
bytes of chall₂ and chall₁. AES is used only through `aes_ctr_prg`, in four roles with tweak ranges
[0, 2302], [2303, 2319], {2³¹−1} and [2³¹, 2³¹+16]. For a fixed iv, the map
(counter, tweak) ↦ AES input is injective, so different roles never share an AES input block. This
holds for the verifier's dummy key-0 expansions too.

**L1 (proved), with the clarified definitions of §3.** Here q₁ is the number of H₁ queries, q₂ the
number of H₂¹ queries, q_E the number of cipher queries (forward plus inverse, counting the
verifier's and the extractor's), L = 2304 the number of GGM leaves, and p := 1/(2¹²⁸ − q_E):

    ε_bind = q₁²/2²⁵⁷ + q₁(q₂ + 17 q₁)/2²⁵⁶ + 10 q_E² p² + L q₂ p² (1 + 3 q_E² p)
           ≈ (18 q₁² + q₁q₂ + 10 q_E² + 2304 q₂) · 2⁻²⁵⁶.

**L2 (proved).** With the **corrected** definition of "alive" (§3.4, Definition B: one block of
the leaf commitment determined before chain Θ's H₂¹ query, the other matching as a cipher value):

    ε_dead = 8 L q₂ q_E p²  ≈  2^{14.2} · q₂ q_E · 2⁻²⁵⁶.

**Finding F1 (a stated bound is false).** With the README's literal definition (both blocks
determined by queries before Θ), L2 holds only with ε_dead^lit = 4 L q₂ p (1 + q_E² p) ≈
2^{13.2} q₂ · 2⁻¹²⁸ (§5.3). The bound "Claim 1 is q·2^{−2λ}" in `lean/docs/lean-correspondence.md` (and the
sketch's EM case) is **false** in the ideal-cipher model: an explicit attack (§5.4) makes the
lemma's bad event happen with probability ≈ q₂/2¹²⁸. The attack does not break extraction, because
the prover really knows the key. It shows that the definition is wrong, not the scheme.
Definition B repairs it. The extractor changes slightly: it accepts a key with one matching block
recorded in the query list and evaluates the cipher itself for the other block (§6).

**Other findings** (§2.5) are minor: the README's claim that the inputs are prefix-free is false
but unnecessary; the key-0 caveat in L0 is unnecessary; application-level hashes (outside L0's
scope) use DST prefixes and are not formally disjoint from the proof system's suffix-tagged
domains; a raw H₂¹ input string parses differently for different relations.

---

## 1. Code facts used (verified)

Parameter sets. All five relations are `parameter_set<s128, 17, OWF, aes_ctr, aes_ctr,
leaf_hash::aes_ctr, 8, {one_tree, 105}>` (`pomfrit/redeem.hpp:77-79`, `moussaka/issue.hpp:136-138`,
`moussaka/redeem.hpp:151-153`, `ratatouille/issue.hpp:122-124`, `ratatouille/spend.hpp:290-292`).
`leaf_hash::aes_ctr` is `prg_leaf_hash<aes_ctr_prg>` (`parameters.hpp:143-146`) and `prg::aes_ctr`
is `aes_ctr_prg` (`parameters.hpp:129-131`). λ ≤ 128 selects SHAKE128 (`hash.hpp:25-31`).

| Fact | Where |
| --- | --- |
| k_max = ⌊120/17⌋+1 = 8, one tree with k = 8 and sixteen with k = 7 | `constants.hpp:322-327` |
| L := COMMIT_LEAVES = 256 + 16·128 = 2304, COMMIT_NODES = 2L − 1, heap layout (children 2a+1, 2a+2) | `vector_com.hpp:116-119`, `vector_com.inc:834-847` |
| Leaf j of tree i sits at node L−1+pos(i,j). The map is injective (interleaved layout). | `vector_com.inc:629-640` |
| AES block c of PRG(k, iv, t) is E_k(iv ⊞ (c,0,0,t)), with ⊞ lane-wise addition mod 2³² | `prgs.hpp:197-206`, `avx2/block_impl.hpp:34-42` |
| GGM: node a (0 ≤ a ≤ L−2) expands to its children as PRG(v_a, iv, a), blocks 0, 1 | `vector_com.inc:39-77` (2 blocks, counters 0, 1), `:674-696` (tweak `node`, `tweak_increment`), `:699-727` |
| Prover's root v₀ = seed r from H₃ | `vector_com.inc:743`, `voleith.hpp:187-201` |
| Leaf commitment com_{i,j} = PRG(k, iv, i+L−1)[0..2λ) = E_k(x_{0,i}) ‖ E_k(x_{1,i}). The seed is sd = k itself. | `vector_com.inc:754,768`, `:1069-1085` (`keys_out = keys_in`, hash = 2 PRG blocks) |
| h_i = H₁(com_{i,0} ‖ … ‖ com_{i,N_i−1} ‖ 0x01), 32-byte output, natural leaf order | `vole_commit.inc:29-62`, `vector_com.inc:173` |
| com = H₁(h₀ ‖ … ‖ h₁₆ ‖ 0x01), 2λ = 256 bits | `vole_commit.inc:64-80`, `constants.hpp:467` |
| com is not in the proof. It enters only H₂¹. | `faest_sig.hpp:54-66`, `voleith.hpp:223-233,413-423` |
| iv = H₄(iv_pre ‖ mu ‖ 0x04). Both iv_pre and mu are in the H₂¹ input. | `voleith.hpp:205-211,388-394`, `:226,230`, `:416,420` |
| ConvertToVOLE: PRG(sd_{i,j}, iv, 2³¹+i). The verifier skips the hidden key. | `vole_commit.inc:103-126,165-181`, `small_vole.inc:145-181` (`:151-154`) |
| Mask top bits: PRG(r, iv, 2³¹−1), counter 0, one block | `vole_commit.inc:234-263` |
| Opening = the τ hidden-leaf commitments, then the co-path seeds, then zero padding (checked) | `vector_com.inc:823-850` (open), `:896-926` (verify) |
| Exactly one hidden leaf per tree, at index Δ_i read from 7 or 8 bits of Δ | `vector_com.inc:879-893` |
| Verifier: v₁, v₂ := 0 when not opened. Every node that was not opened is overwritten by its parent's expansion, top-down. Opened nodes are never overwritten. | `vector_com.inc:932-939`, `:665-672,690-692,716-718` |
| Verifier: the hidden leaf's key is set to 0 and hashed, then its commitment is replaced by the opened one | `vector_com.inc:951,968-970` |
| Verifier recomputes com from these leaf commitments, then chall₁ | `vole_commit.inc:151-157`, `voleith.hpp:406-423` |
| Acceptance: H₂³ output equals the proof's Δ, and Δ's top 8 bits are zero | `voleith.hpp:487-497`, `faest_sig.hpp:126-134` |

Terminology. A *chain* is an H₂¹ query. Its input parses uniquely, for the fixed relation, by
fixed offsets: mu (32 bytes) ‖ com (32) ‖ corrections ‖ c_mult (fixed lengths) ‖ iv_pre (16) ‖
chal1_binder ‖ 0x09. The binder is either empty or PomFRIT's 32-byte `refresher_com`
(`pomfrit.cpp:167,229`).

---

## 2. Lemma L0 — domain separation and oracle uses

### 2.1 SHAKE128 inventory

Every call below initializes `hash_state` (or `hash_state_x4`, which absorbs the same bytes per
lane) with SHAKE128 and squeezes a fixed number of bytes. For ℓ_w := witness bytes and
d := QuickSilver degree:

| # | Oracle | Input layout (bytes) | Final byte | Input length | Output | Code |
| --- | --- | --- | --- | --- | --- | --- |
| 1 | H₁ (leaf hash, k = 8) | com_{0,0} ‖ … ‖ com_{0,255} (32 each) ‖ tag | 0x01 | 8193 | 32 | `vole_commit.inc:29-62` |
| 2 | H₁ (leaf hash, k = 7) | com_{i,0} ‖ … ‖ com_{i,127} ‖ tag | 0x01 | 4097 | 32 | same |
| 3 | H₁ (com) | h₀ ‖ … ‖ h₁₆ (32 each) ‖ tag | 0x01 | 545 | 32 | `vole_commit.inc:64-80` |
| 4 | H₂⁰ (mu) | enc(instance) ‖ DST (7) ‖ tag | 0x08 | var. | 32 | `voleith.hpp:125-140` |
| 5 | H₂⁴ (mu, delayed) | DST (7) ‖ tag | 0x0C | 8 | 32 | same (`:136-137`) |
| 6 | H₃ | witness prefix ‖ mu ‖ rho (16) ‖ tag | 0x03 | fixed per relation | 32 | `voleith.hpp:186-201` |
| 7 | H₄ | iv_pre (16) ‖ mu (32) ‖ tag | 0x04 | 49 | 16 | `voleith.hpp:205-211,388-394` |
| 8 | H₅ (gate hash) | iv (16) ‖ e (u32 LE) ‖ label (16) ‖ tag | 0x05 | 37 | 4 | `vole_commit.inc:406-465` |
| 9 | H₂¹ | mu ‖ com ‖ c₁..c₁₆ ‖ c_mult ‖ iv_pre ‖ binder ‖ tag | 0x09 | var. | 136 | `voleith.hpp:223-233,413-423` |
| 10 | H₂² | chall₁ (136) ‖ ũ (64) ‖ h_V (64) ‖ [mu] ‖ binder ‖ d (ℓ_w) ‖ tag | 0x0A | var. | 56 | `voleith.hpp:235-243,284-302,452-467`, `kos_vole_check.hpp:104-108,132-138,173-177` |
| 11 | H₂³ | chall₂ (56) ‖ ã₀ (16) ‖ ã₁..ã_{d−1} ‖ ctr (u32 LE) ‖ tag | 0x0B | fixed per relation | 16 | `voleith.hpp:314-324,487-497`, `vector_com.inc:996-1026` |
| 12 | UOV combination l | chall₂ (56) ‖ combine-DST (7) | 0x30 (`'0'`) | 63 | M·16 | `uov/circuit.hpp:58-66`, callers `pomfrit/redeem.hpp:132`, `moussaka/redeem.hpp:259`, `ratatouille/spend.hpp:385` |

No other SHAKE call is reachable for these parameters:
- **QuickSilver χ** comes from bytes of chall₂ directly (`quicksilver.hpp:358-377`, called with
  `chal2.data()` at `voleith.hpp:306-308,480-482`). No hash is involved.
- **The KOS universal-hash keys** (four λ-bit keys, one 64-bit key and the 4×λ-bit combination
  matrix) come from bytes of chall₁ directly (`kos_vole_check.hpp:29-45,94-96`).
- **The BAVC** with `leaf_hash::aes_ctr` uses no SHAKE. The SHAKE "universal hash iv"
  (`vector_com.cpp:9-13`) belongs to `stat_binding_leaf_hash` only (`vector_com.hpp:229-238`). That
  hash is selected only by `leaf_hash::aes_ctr_stat_bind*` (`parameters.hpp:148-156`), which no
  relation here uses.
- `shake_prg_impl` (`hash.hpp:120-155`) belongs to the SHAKE PRG, which is unused.
- `faest.inc`'s hashes belong to FAEST signing, which `voleith.hpp` reimplements and does not call.
- The relations' Keccak constraints (`src/keccak/`) arithmetize Keccak-p[800]/[1600] as circuits.
  They are part of R, not oracle calls.

### 2.2 Disjointness

SHAKE128 is modelled as one random oracle `{0,1}* → {0,1}^∞`, of which each call reads a prefix.
SHAKE's padding is injective, which is what the sponge indifferentiability result needs. A family
of oracles obtained by restricting this oracle to **pairwise disjoint** input sets is a family of
independent random oracles. This needs only disjointness, not prefix-freeness: the inputs are byte
strings fed whole to the sponge, not blocks of an iterated construction. Each domain uses one fixed
output length per relation, so no domain reads two prefixes of one stream.

**Claim.** Domains 1–12 are pairwise disjoint.

*Proof.* Two strings with different final bytes are different. The final bytes 0x01, 0x08, 0x0C,
0x03, 0x04, 0x05, 0x09, 0x0A, 0x0B, 0x30 are pairwise distinct, which separates every pair except
those among domains 1–3. Those three share 0x01 and have fixed lengths 8193, 4097 and 545, which
are pairwise distinct. ∎ (Lean: `Domain.disjoint`, `domains_separated`.)

Unique parsing inside a domain, which the chain definitions use:
- H₂¹'s fixed fields come first at fixed offsets, and the variable binder comes last.
- H₂²'s optional mu is present exactly for the delayed-instance relation (PomFRIT), so it is fixed
  per relation. The variable binder is followed by the fixed-length d.
- H₂⁰'s instance encodings are fixed-length, except Moussaka redeem's, which is length-prefixed by
  the anchor count (`moussaka/redeem.hpp:188-204`). The trailing 7-byte DST tells the relations
  apart, and `dst.hpp:56-86` statically asserts that the DSTs are distinct.

**Independence of l and χ** (needed by L4). l = H₁₂(chall₂ ‖ dst) and χ = bytes(chall₂). Given
the history before the H₂² query, chall₂ is uniform on 448 bits. Except with probability
q/2⁴⁴⁸ (the point chall₂ ‖ dst was queried before chall₂ was known), the point is fresh, so l is
uniform and independent of chall₂ and of everything fixed before chall₂.

### 2.3 AES inventory

Every AES call is `aes_ctr_prg` (`prgs.hpp:174-206`). The relations themselves contain no AES
(`static_assert(!is_owf_with_aes_*)` in each relation header). Roles, for one proof with
iv = H₄(iv_pre ‖ mu):

| Role | Key | Tweak | Counters | Code |
| --- | --- | --- | --- | --- |
| GGM expansion of internal node a | v_a | a ∈ [0, L−2] = [0, 2302] (verifier: [1, 2302]) | 0, 1 | `vector_com.inc:688,713-714` |
| Leaf commitment, tree i | leaf seed | i + L − 1 ∈ [2303, 2319] | 0, 1 | `vector_com.inc:754,944,1078` |
| Mask top bits | root seed r | 2³¹ − 1 | 0 | `vole_commit.inc:241-251` |
| ConvertToVOLE, tree i | leaf seed | 2³¹ + i ∈ [2³¹, 2³¹+16] | 0 … COL_LEN−1 | `vole_commit.inc:106,168`, `small_vole.inc:153-180` |

**Claim.** For a fixed iv, AES input blocks from different roles, or from different
(tweak, counter) pairs within a role, are different.

*Proof.* The tweak ranges are pairwise disjoint, and all values are below 2³². The map
(c, t) ↦ iv ⊞ (c, 0, 0, t) is injective on [0, 2³²)², because lane-wise addition by iv is a
bijection and lanes 0 and 3 carry c and t. ∎ (Lean: `ctrInput_inj`, `roles_disjoint`,
`role_inputs_ne`.)

So two AES evaluations in one proof share a (key, input) pair only when they have the same key, the
same role and the same (tweak, counter): for example, two leaves of one tree with the same seed.
The verifier's dummy key 0 is used at nodes 1 and 2 (tweaks 1 and 2) and at each hidden leaf
(tweak i+L−1). These are distinct inputs too, so README L0's caveat "apart from the dummy key-0
expansions" can be dropped. Also needed below: the two blocks of a leaf commitment sit at x_{0,i}
and x_{1,i} = x_{0,i} ⊞ e₀, with e₀ = (1,0,0,0) (Lean: `leaf_second_block`).

### 2.4 Hash outputs used as AES inputs

Only iv = H₄(·) feeds AES. Nothing else couples the two idealizations.

### 2.5 Observations

- **O1. The README's "prefix-free" is inaccurate.** H₂⁰, H₂¹ and H₂² have variable-length fields
  (instance, binders), so the inputs are not prefix-free. Disjointness by final byte or length is
  what holds, and it is all that is needed (§2.2).
- **O2. Application hashes are outside L0's scope.** These are PomFRIT's
  `commit_to_refresher`, `hash_to_target` and the seed expansions (`pomfrit.cpp:76-84,97-110,
  151-160`), Moussaka's and Ratatouille's seed expansions (`moussaka.cpp:57-90`,
  `ratatouille.cpp:68-82`), and the SHAKE256 key digest (`uov.cpp:82-85`, a different function).
  The SHAKE128 ones are *prefix*-tagged with a DST, while the proof system's hashes are
  *suffix*-tagged. The two families are not formally disjoint. For example, a `hash_to_target`
  input with variable `msg` coincides with an H₂¹ input if mu begins with `POMFRIT_TARGET_DST` and
  the remaining bytes line up. For PomFRIT mu = H₂⁴(DST ‖ 0x0C) is a constant, so this would need a
  fixed 56-bit coincidence. This does not affect L1–L4: in the knowledge experiment every such query
  is a query of P*, and no step relies on independence between a proof-system oracle and an
  application oracle. A ROM proof of the application protocols should state it, though.
- **O3. Cross-relation parsing.** Correction and c_mult lengths depend on the relation, so one raw
  H₂¹ string can parse as a chain for two relations, with different field boundaries. Extraction
  fixes the relation, so this is harmless here. It is relevant only to a multi-relation
  simulation-extractability statement.

---

## 3. Model conventions and committed data

### 3.1 Ideal-cipher bookkeeping

E = (E_k)_k is a family of independent uniform permutations of {0,1}¹²⁸, lazily sampled. A query is
forward (k, x) or inverse (k, y). A query is **fresh** if its answer is not already fixed by an
earlier record (k, x, y). A fresh query adds one record, a **determination**. A determined pair is
one in the record list. "Determined before Θ" means recorded by a query that precedes Θ.

**Freshness bound.** At most q_E pairs are determined under any key. So the answer to a fresh
forward query equals any fixed y with probability at most p := 1/(2¹²⁸ − q_E). The same holds for a
fresh inverse query and any fixed x. Given the whole final transcript, an undetermined value
E_k(x) is uniform over at least 2¹²⁸ − q_E values, and values under distinct keys are independent.

### 3.2 Normalization

Replace P* by P° that:
- (N1) queries H₄(iv_pre ‖ mu ‖ 0x04) immediately before each H₂¹ query, with (mu, iv_pre) parsed
  from that query;
- (N2) after P* halts, runs the verifier on π and then the extractor's lookups (§6), as oracle
  queries.

Events are evaluated on P°'s query list. Then q₁, q₂, q_E count P°'s queries, so q_E ≤ q_{E,P*} +
q_{E,V} + q_{E,ext}. Here q_{E,V} = O(L·COL_LEN) is the verifier's cipher queries and
q_{E,ext} ≤ q_{E,P*} + q_{E,V}. Also q₂ ≤ q_{2,P*} + 1. N1 makes iv_Θ part of the history at Θ.

### 3.3 Chains and committed data

Fix a chain Θ: the **first** occurrence of an H₂¹ input. P* may query many H₂¹ inputs, and each
one is its own chain with its own time. Parse (mu, com, c₁..c₁₆, c_mult, iv_pre) from it and put
iv_Θ := H₄(iv_pre ‖ mu ‖ 0x04) and

    x^Θ_{c,i} := iv_Θ ⊞ (c, 0, 0, i + L − 1),   c ∈ {0,1}, i < τ.

*Committed data of Θ.*
- com^Θ is the com field.
- h^Θ = (h^Θ_i)_i is the input of the first H₁ query **before Θ** of length 545 with output com^Θ,
  if there is one.
- com^Θ_{i,·} is the input of the first H₁ query before Θ of length 32·N_i + 1 with output h^Θ_i,
  if there is one.

When a preimage is missing, the dependent objects are *undefined*, and their leaves are treated as
dead (they carry no target).

"Made before the H₂¹ query that produced chall₁" means: precedes the first occurrence Θ of the
H₂¹ input that the verifier, run on π, queries. By N2 that input is in the list.

### 3.4 Alive and dead

Write a := com^Θ_{i,j} = a₀ ‖ a₁ (two 128-bit halves). Leaf (i,j) of chain Θ:

- **Definition A** (README, literal). Alive iff some key k has both (k, x^Θ_{0,i}, a₀) and
  (k, x^Θ_{1,i}, a₁) determined before Θ.
- **Definition B** (corrected). Alive iff some key k has, for some c, (k, x^Θ_{c,i}, a_c)
  determined before Θ, and E_k(x^Θ_{1−c,i}) = a_{1−c} as a value of the ideal cipher (whether or not
  it is ever determined).

In both definitions, **dead** means not alive, and the key k is the leaf's *committed seed*
k^Θ_{i,j}. A-alive implies B-alive.

**Consistency with the iv actually used.** Alive is relative to the points x^Θ_{c,i}, that is, to
iv_Θ, which is fixed by Θ's input. A cipher record at the "same" counter and tweak under another
iv' is a different block and does not count. Conversely, any record whose block happens to equal
x^Θ_{c,i} does count, whatever iv it was "meant" for. If the verifier's H₂¹ query is Θ, then its iv
(computed from `proof.iv_pre()` and mu, `voleith.hpp:386-394`) is iv_Θ, because both iv_pre and mu
are inside Θ (`voleith.hpp:416,420`).

**Independence from chall₁.** Under A the alive set and seeds are a function of the transcript
τ_Θ before Θ. Under B they are a function of (τ_Θ, E). Given τ_Θ, chall₁ = H₂¹(Θ) is uniform and
independent of E and τ_Θ. So the alive set, the seeds, and u^{(i)}, V_i below (functions of seeds,
iv_Θ, c_i ∈ Θ and E) are independent of chall₁ given τ_Θ. L3 uses this.

For a tree with no dead leaf: u^{(i)} := u_i ⊕ c_i (c₀ := 0) and V_i are ConvertToVOLE of
(k^Θ_{i,j})_j under iv_Θ and tweak 2³¹+i (`vole_commit.inc:103-126`). The mask top bits
PRG(r, iv, 2³¹−1) are not committed tree data and play no role here.

### 3.5 The verifier's leaf seeds (GGM co-path)

**Lemma G.** Let T be the verifier's node array after `verify`, and Δ its decoded challenge.
- (i) An opened node keeps its opened value.
- (ii) A node a ≥ 3 that was not opened gets T[a] = block (a+1) mod 2 of PRG(T[⌊(a−1)/2⌋], iv,
  ⌊(a−1)/2⌋). Nodes 1 and 2 get 0 when they were not opened.
- (iii) Every leaf (i,j) with j ≠ Δ_i has an opened ancestor-or-self. So T at that leaf, written
  s'_{i,j}, is the GGM expansion of opened seeds only, never of a dummy.
- (iv) The verifier's commitment for that leaf is c'_{i,j} = E_{s'}(x_{0,i}) ‖ E_{s'}(x_{1,i}),
  computed by two forward queries. The hidden leaf's commitment is the opening's i-th 32-byte
  block.

*Proof.* (i) and (ii): the verifier writes children only where `seed_in_opening` is clear
(`vector_com.inc:665-672,690-692,716-718`). It processes parents in increasing index, and children
2a+1, 2a+2 have larger indices, so each parent is final before it is expanded (`:674-727`).
Nodes 1 and 2 are set at `:932-934`.

(iii): every node on a path from a hidden leaf to the root is marked `dont_reveal` (`:897-900`).
Take a leaf that is not hidden and its highest ancestor-or-self b that is not marked. b ≠ 0,
because the root is always marked (τ ≥ 1). b's parent is marked and has exactly one marked child,
so b is opened (`:903-913`). Every node from b down to the leaf is unmarked and, apart from b, not
opened, so (ii) applies to each of them.

(iv): `:942-964` and `:1069-1085`. The hidden key is zeroed and hashed, then replaced
(`:951,968-970`). ∎

Nothing below uses the internal GGM values: the leaf commitment binds a leaf's key directly. The
GGM structure only restricts which Δ admit an opening, which is part of L3's accepting set.

---

## 4. Counting lemmas (ideal cipher)

A **collision** is a triple ({k,k'}, z) with k ≠ k', E_k(z) and E_{k'}(z) both determined and
equal. N_coll is their number at the end.

**C1.** E[N_coll] ≤ q_E² p.

*Proof.* Each collision is created by a fresh determination D. Take D forward (κ, z): it creates a
collision with each κ' determined at z with probability at most p each, and there are at most q_E
such κ'. Take D inverse (κ, y): it returns z with probability at most p for each z, and creates
#{κ' : E_{κ'}(z) = y} collisions. In expectation that is at most p·#{(κ', z) : E_{κ'}(z) = y} ≤ p q_E.
Summing over at most q_E fresh queries gives q_E² p. ∎

Write n(z, y) := #{k : E_k(z) = y determined at the end}. Then (n − 1)⁺ ≤ C(n, 2) ≤ N_coll and
n² ≤ 1 + 3·C(n,2).

**C2 (double collisions).** Let Coll_E be the event that there are k ≠ k' and z such that
(a) E_k(z) = E_{k'}(z), both determined, and
(b) E_k(z') = E_{k'}(z') as cipher values for some z' ∈ {z ⊞ e₀, z ⊟ e₀}.
Then Pr[Coll_E] ≤ 10 q_E² p².

*Proof.* **Case I: both values in (b) are determined.** Let D be the last of the four
determinations. Before D, the pair already collides at the neighbour w of D's point.
- If D is forward (κ, z), it succeeds with probability at most p·#{κ̄ colliding with κ at z ± e₀}.
  An ordered collision (κ, κ̄, w) is charged by at most the two forward queries (κ, w ± e₀).
- If D is inverse (κ, y), then for a fixed ordered collision (κ, κ̄, w) and sign, only the inverse
  query at y = E_{κ̄}(w ± e₀) can succeed, with probability at most p.

So Pr ≤ p·(4 + 4)·E[N_coll] ≤ 8 q_E² p².

**Case II: one value in (b) is undetermined at the end.** Given the final transcript, each
(collision, neighbour) pair has probability at most p, so Pr ≤ 2p·E[N_coll] ≤ 2 q_E² p². ∎

**C3 (completions).** A *half-target* is a tuple (Θ, i, j, c) with com^Θ_{i,j} defined. Its point
is z = x^Θ_{c,i} and its value y = com^Θ_{i,j}[c]. Its partner point is z' = x^Θ_{1−c,i}, with
value y' = com^Θ_{i,j}[1−c]. There are at most 2 q₂ L half-targets. A determination D *completes*
the half-target if D fixes E_k(z) = y for a key k with E_k(z') = y' already determined.

- (a) If D runs over all determinations and the partner may have been determined at any time, then
  the probability that some D completes some half-target in a set 𝓗 is at most
  2p·E[Σ_{h∈𝓗} n(z'_h, y'_h)]. This requires 𝓗 ∩ {Θ before D} to be fixed by the history at D.
- (b) If we require both determinations to come after Θ, then
  Pr ≤ 2p·E[#post-Θ half-hits] ≤ 8 L q₂ q_E p². A *post-Θ half-hit* is a determination after Θ_h
  that fixes some key's value at z'_h to y'_h.

*Proof.* (a) Take D forward (k, z). The half-targets it can complete have point z and
E_k(z') = y' determined, and that set is history-determined. So the probability is at most p times
its size. Each pair (k, h) is charged to the unique fresh forward query (k, z_h). Take D inverse
(k, y): it must return z_h for some h with value y and E_k(z'_h) = y'_h. Each (k, h) is charged to
the unique fresh inverse query (k, y_h). Summing both cases, the charge is at most
2 Σ_h n(z'_h, y'_h) times p.

(b) The same charging, with n replaced by the number of keys whose partner value was determined
after Θ_h, gives 2p·E[#post-Θ half-hits]. A fresh forward determination at a point z half-hits in
expectation at most p·#{h : z_h = z, Θ_h earlier}, which is at most 2q₂L·p. A fresh inverse
determination (k, y) half-hits at most p·#{h : y_h = y}, which is at most 2q₂L·p. So
E[#half-hits] ≤ 4 q_E q₂ L p. ∎

---

## 5. Lemmas L1 and L2

Bad events, on P°'s execution:
- **Coll₁:** two distinct H₁ inputs (any of the three shapes) give equal outputs.
  Pr ≤ q₁²/2²⁵⁷.
- **Hit₁:** a fresh H₁ answer equals the com field of an earlier H₂¹ query, or a 32-byte block h
  of an earlier length-545 H₁ input. There are at most q₂ + 17q₁ targets at any time, so
  Pr ≤ q₁(q₂ + 17q₁)/2²⁵⁶.
- **Coll_E** as in C2. Pr ≤ 10 q_E² p².
- **Cross** (needed for Definition B only): for some Θ, i, j, keys k ≠ k' have (k, x^Θ_{c,i}, a_c)
  and (k', x^Θ_{1−c,i}, a_{1−c}) determined, the partners E_k(x^Θ_{1−c,i}) and E_{k'}(x^Θ_{c,i}) are
  undetermined at the end, and both equal the matching halves. Given the final transcript each
  configuration has probability at most p². Write n₀ := n(x^Θ_{0,i}, a₀) and n₁ := n(x^Θ_{1,i}, a₁).
  The number of configurations is at most Σ_{(Θ,i,j)} n₀n₁ ≤ ½ Σ_{(Θ,i,j)} (n₀² + n₁²) =
  ½ Σ_h n(z_h, y_h)² ≤ ½ · 2q₂L · (1 + 3N_coll), using n² ≤ 1 + 3·C(n,2) ≤ 1 + 3N_coll. With C1,
  Pr ≤ L q₂ p² (1 + 3 q_E² p).

Put ε_bind := Pr[Coll₁] + Pr[Hit₁] + Pr[Coll_E] + Pr[Cross], which is the formula in §0.

### 5.1 L1 (committed data and binding)

**Lemma L1.** Outside Coll₁ ∪ Hit₁ ∪ Coll_E ∪ Cross, for every chain Θ:

1. **Unique preimages.** com^Θ, h^Θ_i and com^Θ_{i,·}, when defined, are the unique H₁ preimages of
   their shape in the whole list.
2. **Unique seeds.** Each alive leaf (Definition A or B) has exactly one committed seed. Moreover
   no key other than k^Θ_{i,j} ever has both blocks determined (at any time, including by the
   verifier or the extractor) with values com^Θ_{i,j}.
3. **Well-defined data.** For each tree with no dead leaf, u^{(i)} and V_i are well defined.
4. **Linking.** Suppose V accepts π and its H₂¹ query is Θ. Then com^Θ, all h^Θ_i and all
   com^Θ_{i,j} are defined, and the verifier's recomputed values equal them: com' = com^Θ,
   h'_i = h^Θ_i, and c'_{i,j} = com^Θ_{i,j} for all (i, j). For j = Δ_i, c'_{i,j} is the opened
   hidden commitment.

*Proof.*

1. A second preimage is an H₁ collision.

2. Suppose keys k ≠ k' both have both blocks matching a := com^Θ_{i,j}, with k's blocks determined
   by the end (as for the verifier's key, or for Definition A). If k' has one determined block at
   point z, that block collides with k's at z, and the other point z ⊞ ±e₀ collides as cipher
   values. That is Coll_E. Under Definition B, a second committed seed k' has some block determined
   before Θ. If the two seeds share a determined point, that is again Coll_E. Otherwise each has
   exactly the opposite block determined, with the other undetermined at the end. That is Cross,
   or, if a partner is determined, a shared determined point and so Coll_E.

3. This follows from 2: ConvertToVOLE is a deterministic function of the seeds, iv_Θ and E, and
   c_i comes from Θ's input.

4. By N2, the verifier's H₁ queries are in the list. The verifier computed com' = H₁(h' ‖ 0x01).
   Let Q₀ be the first H₁ query with output com'.
   - If Q₀ came after Θ, it is fresh and hits the com field of the earlier Θ. That is Hit₁.
   - So Q₀ precedes Θ, and by Coll₁ its input is h' ‖ 0x01, so h^Θ = h'.
   - Likewise, the first H₁ query with output h'_i = h^Θ_i precedes Θ: otherwise it hits a block of
     the earlier length-545 query Q₀, which is Hit₁. By Coll₁ its input is c'_{i,·} ‖ 0x01, which
     has the right length.

   So com^Θ_{i,·} = c'_{i,·}. ∎

### 5.2 L2 (dead leaves are never opened), Definition B

**Lemma L2.** Except with probability ε_bind + ε_dead, where ε_dead := 8 L q₂ q_E p²: if V accepts
π, with H₂¹ query Θ, then

- (a) every B-dead leaf (i,j) of Θ is the hidden leaf of its tree (j = Δ_i). In particular a tree
  with two or more dead leaves never opens;
- (b) for every j ≠ Δ_i, the verifier's leaf seed s'_{i,j} equals the committed seed k^Θ_{i,j};
- (c) the extractor's lookup (§6) for the hidden leaf (i, Δ_i) returns a key iff that leaf is
  B-alive, and then it returns k^Θ_{i,Δ_i}.

*Proof.* Let **Post** be the event that for some Θ, (i,j) and key s, both (s, x^Θ_{c,i}) are
determined after Θ with values com^Θ_{i,j}[c]. By C3(b), Pr[Post] ≤ 8 L q₂ q_E p². The set of
half-targets is history-determined: it depends on Θ's input, on H₁ queries before Θ, and on iv_Θ,
which is known at Θ by N1. Assume none of the bad events and not Post.

(a) Let j ≠ Δ_i. By Lemma G(iv), the verifier queried E at (s', x^Θ_{c,i}), c = 0, 1, and got
c'_{i,j}. By L1.4 this equals com^Θ_{i,j}. So s' has both blocks determined and matching. If
neither block was determined before Θ, that is Post. So some block of s' was determined before Θ
with the matching value, and the other matches as a value. That makes the leaf B-alive with
witness s'.

(b) By L1.2, s' = k^Θ_{i,j}.

(c) The lookup evaluates E_k at the partner point, so a returned key has both blocks determined and
matching. If the leaf is B-dead, neither block of k was determined before Θ with the matching
value, so both matching determinations came after Θ. That is Post. If the leaf is B-alive with
seed k, the lookup finds k's pre-Θ record and confirms the partner value. By L1.2 no other key
passes. ∎

How the stated difficulties are handled:
- **Inverse queries** enter C1–C3 symmetrically with forward ones.
- **The choice of iv_pre after cipher queries** is covered: nothing assumes iv_Θ is fresh. Records
  count by block equality, and C3 charges every determination against every chain.
- **Many inputs under one key** are covered by the bound p = 1/(2¹²⁸ − q_E) per fresh answer.
- **The GGM co-path** is Lemma G. Opened internal nodes matter only through the leaf keys they
  expand to, and those are bound by the leaf commitments.
- **Many chains** give the factor q₂.

### 5.3 L2 with the README's literal Definition A

**Lemma L2-A.** The conclusions (a) and (b) of L2 hold for A-dead leaves except with probability
ε_bind + ε_dead^lit, where

    ε_dead^lit = 4 L q₂ p (1 + q_E² p).

*Proof.* Let **Comp** be the event that some A-dead leaf of some Θ has a key with both blocks
determined, matching, by the end. Deadness under A is fixed by the history at Θ. So C3(a) applies
with 𝓗 the set of half-targets of A-dead leaves, |𝓗| ≤ 2q₂L, giving

    Pr[Comp] ≤ 2p·E[Σ_h n] ≤ 2p · 2q₂L · (1 + E[N_coll]) ≤ 4 L q₂ p (1 + q_E² p).

Outside Comp, the verifier's key s' for j ≠ Δ_i (both blocks determined and matching) shows that
the leaf is A-alive. (b) follows from L1.2. ∎

For q₂ = 2⁶⁴ this is 2^{−50.8}, which exceeds the main term Q·d·2⁻¹²⁸ ≤ 2^{−60.8} at Q = 2⁶⁴.
Under Definition A, L2 would therefore dominate the knowledge error.

### 5.4 Finding F1: the q·2^{−2λ} bound fails under Definition A

**Attack.** P* runs the protocol honestly except in one tree.
1. Fix (mu, iv_pre), and so iv.
2. Pick a key k* and a leaf j₀ of tree i, and query E_{k*}(x_{0,i}) = y₀.
3. For r = 1, …, m, build a chain Θ_r whose leaf (i, j₀) has commitment y₀ ‖ c_r, with fresh
   random c_r. Give leaf j₀ seed k* in ConvertToVOLE. All other leaves are honest. Vary c_r so the
   H₂¹ inputs differ.
4. After all m chains, query E_{k*}(x_{1,i}).

With probability about m/2¹²⁸ the answer equals some c_r. Leaf (i, j₀) of Θ_r is then A-dead (only
one block was determined before Θ_r) but has a valid key. P* continues chain r honestly and grinds
chall₃ until Δ_i = sibling(j₀), so that leaf j₀ is opened directly as a co-path seed. Doing this in
all τ trees multiplies the success probability by τ.

So Pr[accept ∧ an A-dead leaf is opened] ≈ τ m / 2¹²⁸ with m ≤ q₂, which exceeds q·2⁻²⁵⁶ by far.
The lemma's event happens, yet extraction still succeeds, since P* knows k*.

**Correction.** Use Definition B, which counts leaf j₀ as alive with seed k*, and update the
extractor (§6). The README L1 and L2 and the `lean/docs/lean-correspondence.md` line "Claim 1 is q·2^{−2λ}" should
change accordingly.

Remarks:
- Under Definition A one can tighten L to about 2τ by using acceptance: a tree with three or more
  dead leaves needs two completions. That proof is not written here.
- The multi-chain factor q₂ is genuine in both definitions.

---

## 6. Interface to the extractor and to L3–L6

**Extractor step 2, corrected.**
1. For the hidden leaf (i, Δ_i) and its commitment a = a₀ ‖ a₁, with x_c := x^Θ_{c,i} where Θ is
   π's chain, so iv = iv_Θ: scan the record list for (k, x_c, a_c), for c ∈ {0,1}.
2. For each such k, query E_k(x_{1−c}) and accept k if it equals a_{1−c}.

This costs at most one cipher query per matching record. Records matching the hidden leaf are at
most n(x₀, a₀) + n(x₁, a₁).

By L2(c), outside the bad events tree i is **known** iff its hidden leaf is B-alive. On an accepting
chain every opened leaf is alive (L2(a)), so known ⟺ no dead leaf. That is the hypothesis `known`
of `free_tree_holds_witness` (`lean/VoleMole/SeedExtraction.lean`). For known trees the extractor's
seeds equal the committed seeds (L2(b), (c)), so its u_i is u^{(i)} ⊕ c_i, the committed vector.
For L3: the committed data is independent of chall₁ given τ_Θ (§3.4), and a tree with a dead leaf
(i, j_i) has, on the accepting set, Δ_i = j_i fixed and its other seeds fixed (L2(a), (b)).

**Totals (Definition B).**

    ε_bind + ε_dead ≤ q₁²/2²⁵⁷ + q₁(q₂+17q₁)/2²⁵⁶ + 10q_E²p² + Lq₂p²(1+3q_E²p) + 8Lq₂q_Ep².

For q₁, q₂, q_E ≤ 2⁶⁴ this is below 2⁻¹¹⁰. It is negligible next to the main term Q·d·2⁻¹²⁸ for
any realistic budget.

## 7. Not proved here, and scope

- The tighter, acceptance-based variant of L2-A (remark in §5.4).
- L0 covers only the proof system and the relations' constraint code. Application-level hashes
  are not proved disjoint (O2).
- The verifier's query count q_{E,V} is left symbolic: it depends on ℓ through COL_LEN.
- The counting lemmas C1–C3 and the binding argument are paper proofs. The Lean file checks only
  the AES input injectivity, the tweak-range disjointness and the domain-tag table. Since then the
  cipher part of binding is in Lean in the PRF view without inverse queries
  (`lean/VoleMole/ROM/CipherBind.lean`, `ROM/CipherGame.lean`; `lean/docs/probabilistic-plan.md`
  §2d): a C2-type double collision among the prover's cipher queries, `≤ 2·q_E²·2⁻²⁵⁶`, unique
  logged keys per leaf commitment (L1.2, Definition B extraction of §6), and the executable
  reconstruction's keys equal to the extracted ones unless a leaf whose key was never queried is
  opened. That residual is now bounded too (`ROM/CipherOpen.lean`, `ROM/Queried.lean`,
  `ROM/FreshGuess.lean`; plan §2e): an accepted proof opening a leaf whose key the prover never
  evaluated has probability `≤ (q₁+18)(17q₁+q₂₁)·2⁻²⁵⁶ + (q₂₁+1)q₂₂·2⁻¹⁰⁸⁸ + (q₂₂+1)q₂₃·2⁻⁴⁴⁸ +
  2⁻¹²⁸ + q₁·2⁻²⁵⁶`: either some leaf hash of the verifier was never queried by the prover (then
  `Hit₁` or its `H₂¹`, `H₂²` analogues up the chain, or the verifier's fresh `H₂³` answer is `Δ`:
  the "linking" half of L1.4, without the ordering), or the prover's `H₁` input contains the
  commitment of two cipher cells it never queried (a two-cell guess; the GGM derivation reads no
  leaf-commitment point). The rest of L1.4 and L2 is now in Lean too (`ROM/CipherChain.lean`,
  `ROM/CipherSame.lean`, `ROM/CipherFull.lean`; plan §2f), for a fixed statement: the data committed
  at the verifier's `H₂¹` input are read off the logs before its first query; without a hit (an
  `H₁`, `H₂¹`, `H₂²` answer equal to a field of an earlier input or to an earlier answer of its
  kind) the verifier's preimages were queried before `Θ` in order and are the first ones found (the
  ordering half of L1.4 and `Coll₁`); without Post (C3: a cipher query, first at both points of a
  key, whose blocks form a block of an earlier `H₁` input; `≤ 1024·q_E·q₁·2⁻²⁵⁶`) the keys found
  before `Θ` are the extractor's. L2 is used in the form of §5.2/§6: the accepting set excludes the
  `Δ` that open a committed dead leaf (the earlier formal hypothesis took the challenges on the
  committed chain with garbage keys at dead leaves, which a prover using the garbage key at a hidden
  dead leaf makes all of `chal3`; plan §2e F2). L2(c) is then deterministic, and L2(a) follows from
  Post and the opened-dead-leaf bound. The resulting soundness bounds for all five relations have
  no remaining hypothesis (`*_accept_le_full`); with adaptively chosen statements, plus the
  statement-binding term (`*_accept_le_adaptive`, plan §2g).
- **The permutation model of §3.1 is now in Lean too** (`ROM/PermModel.lean` … `ROM/PermAdapt.lean`;
  plan §2h): `E` a family of independent uniform permutations (drawn eagerly), the prover making
  forward and inverse queries, the extractor reading the records `(k, z, E_k(z))` of both kinds
  (§6), with N1 as a normalized prover (the `H₄` query of `iv` before each `H₂¹` query; N2 is not
  needed, the verifier and the extractor read the table). The per-fresh-value factor is exactly
  `p = 1/(2¹²⁸ − q_E)` (`q_E` the prover's queries; a record charged at index `n` has at most
  `n < q_E` protected inputs), except for the opened dead leaf whose leaf hash the prover queried,
  where the verifier's `2·2303` GGM points are protected too: `p' = 1/(2¹²⁸ − q_E − 4607)`. The
  terms: `Coll_E` and Cross `≤ 2·q_E²·p²` (the C2-type event, charged at the second key's first
  record, forward or inverse); the dead-leaf guess `≤ q₁·p'²`; C3(b)/Post `≤ q_E·4608·q₂₁·p²`
  (`2L·q₂₁·q_E·p²`, below the paper's `8L·q₂·q_E·p²`), for all five relations, fixed and
  adaptively chosen statements (`*_accept_le_perm`, `*_accept_le_adaptive_perm`). No PRP/PRF
  switching term. **Finding F3**: the Lean PRF-view Post of plan §2f (a record first at both
  points of a key whose values form a block of an earlier `H₁` input, at any points) is *not*
  small with inverse queries (query `E_κ⁻¹(t₀)` for a target block `(t₀, t₁)` and hope for
  `E_κ(E_κ⁻¹(t₀) ⊞ e₀) = t₁`: about `q_E·2⁻¹²⁸`); C3's half-targets must be tied to their points,
  `x^Θ_{c,i}` of the chain `Θ` whose committed commitment they are, as in §4. The point-tied Post
  (`PostP`) needs `iv_Θ` in the log at `Θ`, i.e. N1. Still paper: C1 (not needed), and the
  verifier's and extractor's own evaluations counted in `q_E` (they are table reads here).