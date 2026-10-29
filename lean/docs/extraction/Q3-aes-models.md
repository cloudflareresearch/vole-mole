# Q3: Models of AES for quantum extraction, and design alternatives

Status: **[paper, survey + measurements]**. This note supports README §L9. It does not prove
anything new. It compares the available ways to idealize AES for quantum straight-line extraction
of leaf seeds, checks what faest-arch-opt already offers, and measures the cost of the design
change.

**Bottom line.**
1. Best option: switch the five relations' parameter sets from `leaf_hash::aes_ctr` to
   `leaf_hash::shake`. This is a configuration change and needs no faest-arch-opt patch.
   - Every leaf commitment then becomes an ordinary random-oracle commitment, and seed extraction
     is DFMS online extraction in the QROM.
   - AES then needs **no idealization at all** for knowledge soundness. It only needs standard
     (post-quantum) PRF security, and only for zero-knowledge.
   - Proof size is unchanged. Proofs are no longer byte-compatible with FAEST-EM-128f's leaf hash,
     and the KATs must be regenerated.
   - Cost: about 2,300 extra Keccak-f[1600] calls per prove and per verify. On the test machine
     that was about +0.7 ms per prove and +0.5 ms per verify (§B4).
2. Second best: keep AES and work in the quantum ideal-cipher model (QICM) with key-level
   recording.
   - The analysis is sound.
   - Pitfall: an **efficient** extractor still has to simulate each touched key's permutation
     efficiently. That needs either a compressed permutation oracle, whose soundness loss is at
     least about q/2⁶⁴, or a computational qPRP hybrid (§A1).
3. Last: the seed PRG as a random oracle (`lean/docs/sketch.md`). As stated, on (k, iv, twk), it is
   unfaithful in a way that matters, because AES-CTR windows overlap (§A2). The block-level version
   (§A3) is a usable heuristic, but it cannot be derived from the QICM without a q³/2¹²⁸ loss.

Notation: N = 2¹²⁸ (block and key space), λ = 128, q = number of quantum oracle queries. All paper
references are listed in §References.

---

## Setting: how AES enters the repo's proofs

Line numbers into `src/` and into the patched faest files (`constants.hpp`) refer to branch
`voleith-label-rows` (commit `d5def9c`; merged to `main` as `64fd1a4`, with the opt-in flag `CRT_DEDICATED_LABEL_ROWS` replaced by the opt-out `REUSE_CRT_WITNESS`, which Moussaka and Ratatouille set; see `lean/docs/zk.md`, "Status on `main`"), with faest-arch-opt patches 0001–0005.

The relevant code and parameters:
- **Leaf commitment** (`leaf_hash::aes_ctr`, faest-arch-opt `vector_com.hpp:182-198`,
  `vector_com.inc:1069-1085`):
  - `com = AES_k(x₀) ‖ AES_k(x₁)`, where `x_c = iv ⊞ (c, 0, 0, twk)`;
  - `twk = i + COMMIT_LEAVES − 1` is **per tree, not per leaf** (`vector_com.inc:754`);
  - the output seed is the input key itself (`keys_out = keys_in`, `vector_com.inc:1082`).
  - The code comment says it is "based on assuming that a PRG is collision resistant"
    (`vector_com.hpp:182`).
- **GGM internal nodes:** `tree_prg = aes_ctr`.
- **ConvertToVOLE:** `vole_prg = aes_ctr`, tweak `2³¹ + i` (`vole_commit.inc:106,168`).
- **Prover-only mask high bits:** `PRG(seed, iv, 2³¹ − 1)` (`vole_commit.inc:241-251`).
- **All five relations** use exactly this configuration:
  - `src/pomfrit/redeem.hpp:76-79`
  - `src/moussaka/issue.hpp:135-138`
  - `src/moussaka/redeem.hpp:150-153`
  - `src/ratatouille/issue.hpp:121-124`
  - `src/ratatouille/spend.hpp:289-292`
- **Leaf counts:** for τ = 17 and Δ-bits = 120, `constants.hpp:322-327` gives MAX_K = 8,
  NUM_MAX_K = 1 and NUM_MIN_K = 16. So one tree has 256 leaves and sixteen have 128: **2,304
  leaves per proof**.

The obstacle: an extractor must output `k` given `com`, and nothing in the protocol routes `k`
through a random oracle.

---

## Part A: Models

### A1. Quantum ideal cipher with a compressed oracle on keys (README plan; Q1)

**Model.**
- E is uniform in `Func(K, Sym({0,1}¹²⁸))`.
- The adversary has forward and inverse quantum access `|k,x,y⟩ ↦ |k,x,y⊕π_k(x)⟩` (and with
  `π_k⁻¹`), with the key and the direction in superposition.
- Purification: `⊗_{k∈K} |u_Sym⟩_{R_k}`.

**Does key-level recording avoid permutation recording? For the analysis, yes.** The reason is
structural:
- A query is a unitary that is **diagonal in the permutation basis of the single register `R_k`**
  selected by the key.
- So the oracle is literally a random function `F : K → Y`, with the huge range Y = Sym(N). A
  query is "controlled on F(k), apply `V_{F(k)}` to (x, y)".
- Zhandry's compression `|u⟩ ↔ |⊥⟩`, applied per register, is an **exact** unitary change of basis
  (no soundness error). The key database (registers not in `|⊥⟩`) has at most q entries per
  branch, exactly as in [Zha19].
- This is the same structure that Carolan–Majenz use for their ideal-cipher extension:
  - a tensor product of per-key compressions;
  - queries controlled on the key act on one factor;
  - no dependence on |K| ([CM26, §4.6, Cor. 4.18]; see also [Car25, §3.3]).
- The README's two Q1 deliverables then go through without permutation recording:
  - **Unpredictability (Lemma-5 type):** for k ∉ D, register `R_k` is `|u_Sym⟩`, so
    `π_k(x₀) ‖ π_k(x₁)` is uniform over pairs of distinct values. So
    `Pr[out = (k, com) ∧ k ∉ D] ≤ (√p′ + √(1/(N(N−1))))²`, i.e. ≈ 2⁻²⁵⁶ for a single target, and
    ×(number of targets) for the 2,304 commitments.
  - **Commutator δ:** the extraction relation `R_com(k, π) = [π(x₀) ‖ π(x₁) = com]` has density
    `1/(N(N−1))` in Y. A DFMS-style commutator bound should give δ = O(2^{−λ}) per query.
    - DFMS prove their bound for `H : {0,1}^m → {0,1}^n` with XOR queries [DFMS22, Thm 4.3/5.x].
    - Re-deriving it for a generic range and "controlled-on-value" queries is needed. That is a
      routine generalization in the style of [CFHL21], but it has to be written.

**Pitfall 1 (main): efficiency of the simulation.**
- A straight-line extractor in the QROM must *run* the oracle simulation (DFMS's extractor is the
  compressed oracle plus a measurement).
- A database entry here is a vector in a space of dimension ≈ N!, i.e. ≈ 2¹³⁵ qubits. That is
  fine for an information-theoretic bound but not efficient.
- An extractor that is only "efficient up to the oracle simulation" is not enough for the
  reductions that L8 feeds (UOV / Keccak hardness).
- Two fixes:
  - (a) **Compress each touched key's permutation as well**, with a compressed permutation oracle
    supporting inverse queries:
    - Unruh [Unr21] (erratum; soundness conjectured);
    - MMW [MMW24] (single input-output predicates only);
    - Carolan [Car25] (sound up to about N^{1/12} queries);
    - Carolan–Majenz [CM26] (advantage ≤ 120q/√(N−q+1) + q(q+1)/(N−2q+1), the same in the ideal
      cipher model, claimed tight);
    - Kim [Kim26] (4q/√N).

    The loss is then **at least ≈ q·2⁻⁶⁴** for N = 2¹²⁸. No DFMS-style extraction or commutator
    theorem exists yet for these oracles.
  - (b) A **computational hybrid**:
    - replace the ideal cipher by `E′_k = P_{F(k)}`, where `{P_s}` is a strong quantum-secure PRP
    family ([Zha16]; or the 7-round Feistel of [Car25]) and `F : K → S` is a random function;
    - then compress F with the standard (small-range) compressed oracle.
    - This needs multi-instance strong-qPRP security, via small-range distributions [Zha12] plus
      a multi-key PRP. It also needs `Pr_s[P_s(x₀) ‖ P_s(x₁) = com] ≲ 2⁻²⁵⁶`, which holds for a
      PRP family composed with a pairwise-independent permutation.
    - The hybrid has no √N-type loss, but it is a new lemma.
- Either way, option (i) is **more** non-standard than it looks in the README.

**Pitfall 2: no classical "determined by queries".**
- The quantum extractor measures `R_com` on every database key. Keys touched only at other
  plaintexts (GGM, ConvertToVOLE, unrelated) give near-uniform outcomes, which is harmless.
- L1's definition of "alive" must be restated as "the extraction measurement at the time of the
  H₂¹ query returns a key" (Q2's job).

**Pitfall 3: binding becomes a quantum collision bound.**
- The uniqueness of the key for `com` (L1) is a 2λ-bit collision among database keys. Classically
  it is q²/2²⁵⁶; quantumly it is O(q³/2²⁵⁶) (BHT / [Zha15]).

**Pitfall 4: citation.** The README cites DFMS as CRYPTO 2022. It is **EUROCRYPT 2022**, LNCS
13277, pp. 677–706 [DFMS22].

**Concrete loss.**
- The database and unpredictability parts cost ≈ 2,304·q·2⁻¹²⁸ plus the δ-terms O(q·2⁻¹²⁸).
- Plus either ≈ 120·q·2⁻⁶⁴ (fix a) or Adv_sPRP (fix b).
- The QROM Fiat–Shamir term O(q²·2⁻¹²⁸) dominates for q ≤ 2⁶⁴ only under fix (b). Fix (a)'s
  q·2⁻⁶⁴ term is larger than q²·2⁻¹²⁸ everywhere below q = 2⁶⁴, although both become trivial at
  q ≈ 2⁶⁴.

**Faithfulness.**
- AES-128 is distinguishable from an ideal cipher in known-key and related-key settings:
  - the key-schedule structure;
  - Gilbert's full-10-round known-key distinguisher [Gil14];
  - bicliques at 2^{126.1} [BKR11].
- None of these gives what an attacker on extraction needs: a way to hit a *prescribed*
  `AES_k(x₀) ‖ AES_k(x₁)`, a preimage-type property in the key. The best preimage attacks on AES
  hashing modes with the key as the message reach only reduced rounds [Sas11].
- So the ICM is a standard, and here a reasonable, heuristic. It is still a heuristic about AES
  itself, used with **adversarially chosen keys**.

### A2. Seed PRG as a random oracle on (k, iv, twk) (`lean/docs/sketch.md`)

**Model.** `PRG(k, iv, twk; m) = RO_P(k, iv, twk)[0..m)`, forward only.

**Literature.**
- Quantum PRP/PRF switching costs Θ(q³/N): Zhandry's Ω(N^{1/3}) lower bound for random function
  versus random permutation [Zha15]. The bound is tight by BHT collision finding. Yuen's earlier
  bound was N^{1/5} [Yue14].

**Extraction.** Standard DFMS in the QROM, on the relation `RO_P(k, iv, twk)[0..2λ) = com`.
Loss O(q·2^{−λ}) per extracted value.

**Is it sound? Two separate issues.**
1. *Derivation from the ICM.*
   - Going ICM → RO_P costs the switching loss q³/2¹²⁸, which becomes trivial at q ≈ 2⁴³.
   - That destroys the **justification** of the model from the ICM. It does not by itself
     invalidate the model as an independent heuristic: SHAKE-as-RO is also trivially
     distinguishable from Keccak by anyone holding the code.
   - The test for a heuristic is whether the distinguishing feature can help an attacker *on this
     protocol*. Same-key collisions (which RO_P has and AES lacks) give the model adversary extra
     power, so their effect is conservative.
   - Moreover, the switching loss is **unnecessary**: key-level recording (A1) never compares
     outputs of the same key at many plaintexts.
2. *A defect specific to the (k, iv, twk) indexing.*
   - AES-CTR windows overlap: `PRG(k, iv, twk)` block c+1 equals `PRG(k, iv ⊞ (1,0,0,0), twk)`
     block c. This is a two-query **classical** distinguisher.
   - It is relevant to extraction: a real prover can obtain `com_{i,j}` from a PRG call with
     shifted iv or tweak. In RO_P that call is an independent oracle, and the `lean/docs/sketch.md`
     extractor, which searches for the exact `(k, iv, i+L−1)`, would miss it.
   - So the model excludes a natural real strategy. **Do not use the (k, iv, twk) form.** If an RO
     model of AES is wanted, use the block-level version A3.

### A3. Block-level random function: k ↦ AES_k(x) random for each x, permutation structure ignored

**Model.**
- `F : K × {0,1}¹²⁸ → {0,1}¹²⁸` is a random function with forward quantum access. Block c of
  `PRG(k, iv, twk)` is `F(k, iv ⊞ (c, 0, 0, twk))`.
- No inverse queries.

**Relation to the ICM.**
- For **one fixed plaintext x**, `k ↦ π_k(x)` under the ICM is *exactly* a uniform random function
  K → {0,1}¹²⁸, because the keys are independent.
- For two fixed plaintexts, `k ↦ (π_k(x₀), π_k(x₁))` is a random function into the pairs of
  distinct values. Its distance from a random function into {0,1}²⁵⁶ is a 2^{−128}-sparse search,
  so O(q²·2⁻¹²⁸) quantumly.
- Only the joint behaviour across *many* plaintexts under the same key costs q³/2¹²⁸.
- So "A3 restricted to the commitment plaintexts" follows from the ICM with small loss. The full A3
  (all plaintexts) does not.

**Extraction.**
- Standard compressed oracle on F, and efficient.
- The extraction relation involves **two** database points (k, x₀) and (k, x₁). DFMS is stated for
  single-input relations, so a two-point variant is needed. [CFHL21]-style database properties
  cover it; the expected loss is O(q·2^{−λ}).

**Faithfulness.**
- A real adversary holding k can invert AES, and A3 does not model that. Inverse access does not
  help to open a dead leaf in the ICM, since the plaintexts are fixed by `iv = H₄(·)`, but A3
  cannot express that argument.
- Same-key collisions exist in A3 and not in AES. That is conservative.
- No indifferentiability statement connects A3 to the ICM: a per-key permutation is not
  indifferentiable from a random function. Contrast the sponge, whose RO model is justified by
  (quantum) indifferentiability from a random permutation [ACMT25].

**Verdict.** A3 is a clean, efficient heuristic that is better founded than A2. It is still a
heuristic *about AES with adversarial keys*, and the ICM is preferable.

### A4. AES as a key-alternating (iterated Even–Mansour) cipher, or single-key EM

**Model.**
- `E_k(x) = k₁₀ ⊕ P₁₀(… P₁(x ⊕ k₀) …)`, with the real AES-128 key schedule (k₀ = k) and
  independent public random permutations Pᵢ, accessed forward and inverse in superposition.
- The single-key EM view is `P(x ⊕ k) ⊕ k`.

**Literature.**
- Post-quantum EM is proven only in the **Q1 setting**: quantum access to P, *classical* access to
  the keyed cipher with a secret key. Bound: `q_E·q_P² + q_P·q_E² ≈ 2^n` [ABKM22].
  - The bound is tight by the offline-Simon attack [BHNSS19].
  - Tweakable EM gets the same treatment [ABKMS24].
  - FX, LRW, XEX and modes are covered in [ABMS25].
- Q2 EM is broken by Simon's algorithm (Kuwakado–Morii).
- No post-quantum result covers multi-round key-alternating ciphers with a real key schedule.

**Is our use covered?** No.
- The adversary *chooses* the key, so we need extraction (a knowledge property), not
  pseudorandomness.
- Classically it is easy: since k₀ = k, every recorded forward query a to P₁ (or inverse-query
  output from P₁⁻¹) yields a candidate `k = a ⊕ x₀`, which the extractor can test.
- Quantumly this needs recording of **two-sided** queries to a random permutation, with a
  *two-point* relation on the database (both x₀ ⊕ k and x₁ ⊕ k):
  - MMW handle only single input-output predicates [MMW24];
  - Carolan's oracle has a small-list purification [Car25];
  - its soundness is at best O(q/√N) [CM26, Kim26];
  - no commutator or extraction theorem exists.

**Loss.** At least ≈ q·2⁻⁶⁴ per recorded permutation, plus an extraction theorem that still has
to be proven.

**Faithfulness.** This model is *worse* than the ICM. A single AES round (SB∘SR∘MC) is a tiny,
byte-structured, low-degree permutation, and modelling it as random is a larger leap than modelling
the whole cipher as ideal.

**Verdict.** Strictly dominated by A1.

### A5. Other literature

- **QICM one-wayness and collision resistance:**
  - Hosoyamada–Yasuda prove Davies–Meyer one-way in the QICM with inverse queries [HY18];
  - Cojocaru–Hhan–Liu–Yamakawa–Yun give *lifting theorems* for the QRPM and QICM, which turn
    classical few-query bounds into quantum bounds, including DM collision resistance [CHLYY25];
  - Carolan–Majenz give DM preimage `≤ 16384(q+1)²/2^n` with no |K| dependence [CM26, Thm 5.6].
  - Our dead-leaf event, "hit a fixed com under some key", is a DM-preimage-like search game. So
    the **unpredictability half** of Q1 could plausibly be obtained by lifting [CHLYY25] or from
    [CM26]. Lifting gives search bounds, **not online extraction**.
- **Key-level reasoning in the QICM** goes back at least to Jaeger–Song–Tessaro: double encryption
  and FX, with a reduction to list disjointness. They note that whether quantum random
  permutations can be lazily sampled was open, which blocked adaptive FX [JST21].
- **Quantum indifferentiability:**
  - Known for the sponge from a random permutation [ACMT25] (and for random functions,
    Czajkowski et al.).
  - Not known for any ideal-cipher-from-RO or RO-from-ideal-cipher construction that would fit
    AES-CTR. [Zha21] discusses why indifferentiability with quantum queries is delicate.

### A6. Comparison

| Model | Precise model | Quantum straight-line extraction of k | Main loss | Efficient simulator | Faithful to AES? |
|---|---|---|---|---|---|
| A1 QICM, key-level | `Func(K, Sym(N))`, forward and inverse | Yes for the analysis. Needs a generic-range DFMS commutator (routine, unwritten) | Key part ≈ 2,304·q·2⁻¹²⁸. **Simulation:** (a) ≥ 120q·2⁻⁶⁴ or (b) Adv_sPRP plus a new lemma | Not as stated. Needs (a) [CM26] or (b) a qPRP hybrid | Standard heuristic. Known-key distinguishers are irrelevant here |
| A2 PRG as RO on (k, iv, twk) | `RO_P(k, iv, twk)` | Yes (DFMS) | From the ICM: q³·2⁻¹²⁸ (trivial at 2⁴³) | Yes | **No**: CTR overlap is a 2-query classical distinguisher relevant to extraction |
| A3 block-level RF | `F(k, x)`, forward only | Yes (DFMS, two-point relation) | O(q·2⁻¹²⁸) inside the model. Not derivable from the ICM beyond 2 plaintexts | Yes | Ignores inversion. Conservative on collisions |
| A4 key-alternating or EM | Real key schedule, random Pᵢ, two-sided | Open (no two-sided multi-point extraction) | ≥ q·2⁻⁶⁴ plus an open theorem | Via [Car25]/[CM26] | Worse than the ICM |
| **(ii) SHAKE leaf** | SHAKE128 as a QRO. AES is a plain deterministic function | **Yes, standard DFMS** | O(2,304·q·2⁻¹²⁸) | Yes | Same assumption as every other hash in the proof |

---

## Part B: Design options in faest-arch-opt

### B1. Available variants (faest-arch-opt, patched copy)

`parameters.hpp:100-115` lists two PRGs (`aes_ctr`, `rijndael_fixed_key_ctr`) and six leaf
hashes:

| `leaf_hash` | Type | com | Output seed | Size |
|---|---|---|---|---|
| `aes_ctr` (**repo, FAEST-EM v2/v3**) | `prg_leaf_hash<aes_ctr_prg>` (`vector_com.hpp:182-198`) | `AES_k(x₀) ‖ AES_k(x₁)` | `k` | 2λ |
| `aes_ctr_stat_bind` (FAEST v2) | `stat_binding_leaf_hash<…, false>` (`vector_com.hpp:210-261`) | `PRG(k)[λ..4λ) ⊕ UH_h(sd)`, with h depending on the tweak | `sd = PRG(k)[0..λ)` | 3λ |
| `aes_ctr_stat_bind_same_hash` (FAEST v3) | the same, one h | the same | the same | 3λ |
| `rijndael_fixed_key_ctr[_stat_bind]` | fixed-key Rijndael | – | – | – |
| **`shake`** (FAEST v1, the template default) | `shake_leaf_hash` (`vector_com.hpp:263-279`, `vector_com.inc:1134-1149`) | `SHAKE128(k ‖ iv ‖ twk ‖ 0x00)[λ..3λ)` | `sd = SHAKE128(…)[0..λ)` | **2λ** |

Notes:
- The SHAKE input is 16 + 16 + 4 + 1 = 37 bytes, i.e. one Keccak-f[1600] absorb and a 48-byte
  squeeze (`hash.hpp:120-157`). The 4-way AVX2 or NEON batch is used.
- `parameter_set` takes `LEAF_HASH` as a free template parameter (`parameters.hpp:224-226`). Its
  default is `leaf_hash::shake`, and v1 uses it (`parameters.hpp:290-293`).
- **The repo can select it without patching faest-arch-opt.** In each of the five files, replace
  `faest::leaf_hash::aes_ctr` with `faest::leaf_hash::shake`.
- The `check` static_asserts then need adjusting, because `bavc_t` embeds `LEAF_HASH`:
  - `pomfrit/redeem.hpp:84,88`
  - `moussaka/issue.hpp:143,147`
  - `moussaka/redeem.hpp:158,162`
  - `ratatouille/issue.hpp:129,133`
  - `ratatouille/spend.hpp:297,301`

  Proposed: compare `bavc_t::OPEN_SIZE`, `COMMIT_LEAVES`, `tau_v` and `delta_bits_v`, and assert
  `leaf_hash_v == leaf_hash::shake`.
- Verified in the scratchpad (not in the repo): `one_tree_bavc<s128, 17, 120, aes_ctr,
  leaf_hash::shake, 3, 105>` compiles against the repo's libfaest. Commit → open → verify
  round-trips, all 2,304 leaf hashes agree, and `verify` returns true.
- faest-arch-opt's own `one_tree` + `shake` benchmark is under `#if 0` (`test/bench_leaf_hash.cpp:77`
  ff.). Upstream does not regularly test this combination, so run the repo's full test suite after
  switching.

### B2. With `shake`: what remains of AES in the extraction argument

I went through README L0–L8 asking where an AES *model* (as opposed to AES as a fixed function)
is used.

| Step | Uses an AES model today? | With `leaf_hash::shake` |
|---|---|---|
| L0 domain separation | AES block disjointness (ICM only) | Not needed for extraction. **New L0 item:** SHAKE128 inputs of 37 bytes ending in `0x00` must be disjoint from every other SHAKE128 use. Known so far: H₁ ends in `1`, H₂ʲ in `8+j`, H₃ in `3`, H₄ in `4`; `stat_bind`'s `SHAKE(iv ‖ 0)` is 17 bytes (`vector_com.cpp:6-14`). The L0 agent must check UOV `Combination` and the `src/*/` protocol hashes |
| L1 binding of alive leaves | Yes: uniqueness of k for com (an AES collision assumption, or the ICM) | RO collision on the 2λ-bit com part. Then `sd` is unique and `u_i` and `V_i` are deterministic functions of the seeds |
| L1/L2 "alive" | Yes: cipher queries that determine com | An H query `(k, iv, twk)` with `H(·)[λ..3λ) = com`, i.e. a DFMS extraction |
| L2 dead leaves | Yes: hitting com under an unqueried key, plus inverse queries | The verifier recomputes leaf keys from the co-path with **real** AES (a deterministic function), then SHAKE. Opening a dead leaf means a fresh QRO output hits a fixed 2λ-bit target: Zhandry Lemma 5 [Zha19]. Inverse queries are irrelevant |
| ConvertToVOLE, GGM | Evaluated through the oracle | Evaluated as real AES by E. No property needed: Claim 4 uses only the algebraic identity `Q = W_crt(V) + Σ u^{(i)} e_i`, which holds for every function PRG |
| Mask high bits | Prover-only, prover-chosen | Unchanged |
| L3/L4 (KOS, QS) | No | No |
| L5/L6 | No | No |
| L8 sim-ext | Simulated com uniform, i.e. a dead leaf | The same, in the QROM. **ZK** needs AES to be a PRF/PRG against quantum adversaries (secret key, classical outputs: the standard AES-128 assumption), for the GGM co-path and for `u` hiding. It is not idealized |

Conclusion: with `shake`, **knowledge soundness needs nothing about AES beyond determinism**. Every
idealization is the QROM for SHAKE, as for H₁ … H₅ already. The theorem then reads:
- QROM;
- AES-128 is a post-quantum PRF (for ZK only).

That is the strongest and most standard combination available.

### B3. `aes_ctr_stat_bind_same_hash`: does statistical binding help?

- `com = PRG(k)[λ..4λ) ⊕ UH_h(sd)` with `h = SHAKE(iv ‖ 0x00)` (`vector_com.inc:1087-1132`).
  - For a non-ground iv it is statistically binding to `sd`, with error ≈ 2^{2λ}/2^{3λ} per h.
  - This replaces the AES collision assumption in **L1** with a statistical argument.
- It does **not** help extraction. `sd` is only information-theoretically determined, and
  computing it from `com` still means inverting an AES-based map. That needs an AES idealization
  (A1/A3) or an inefficient extractor (soundness, not knowledge).
- It also costs 17·16 = 272 extra proof bytes (3λ hashes) and is slower than `aes_ctr` (§B4).
- Not recommended for this purpose.

### B4. Cost of switching to `shake`

The per-proof work is all 2,304 leaves for the prover and 2,304 − 17 = 2,287 for the verifier.

**Microbenchmarks.**
- Built in the scratchpad against `build/`'s libfaest and libxkcp with `-O3 -march=native`.
- Machine: Intel i7-4790 (Haswell, AVX2, no VAES/SHA-3 instructions). It was shared and loaded
  (load average ≈ 5), so the numbers are noisy at ±10%.

| | `aes_ctr` | `stat_bind_same_hash` | `shake` |
|---|---|---|---|
| leaf hash only, 2,304 leaves (best chunk width) | 50 µs (22 ns/leaf) | 84 µs | 520 µs (225 ns/leaf) |
| `one_tree_bavc` commit (tree + leaves) | 123–132 µs | 165 µs | 790–930 µs |
| `one_tree_bavc` verify | 140 µs | 183 µs | 655–740 µs |

So the switch adds **≈ +0.7 ms per prove and ≈ +0.5 ms per verify** on this machine.

For scale, in the same environment `build/tests/bench_pomfrit` (debugoptimized) gives:
- `FinalizeIssue` 0.87 ms CPU;
- `Verify` 1.24 ms CPU.

That makes the switch roughly +75% (prove) and +45% (verify) for PomFRIT on this host. The relative
cost is much smaller for the large relations: Ratatouille `spend_request` takes 1.45 ms on the M4
in `docs/perf.md`.
- **Estimate for Apple M4 Pro** (`docs/perf.md`): if Keccak scales like the rest of the code, about
  +0.15 ms prove and +0.12 ms verify. Then:
  - PomFRIT prove 0.19 → ≈ 0.34 ms, verify 0.37 → ≈ 0.49 ms;
  - Moussaka redeem (N=1) 0.77 → ≈ 0.92 ms;
  - Ratatouille spend 1.45 → ≈ 1.6 ms.
  - This is an extrapolation. Measure it with `meson test -C build-release --benchmark` after the
    switch.
- **Proof size: unchanged.** `hash_len = 2λ/8` for both (`vector_com.hpp:188,268`), so `OPEN_SIZE`
  is identical.
- **Wire format:**
  - Proof bytes change, so regenerate `tests/ihat/ihat_kat.txt` and
    `tests/act/act_kat.txt` (via `gen_*_kat.cpp`).
  - `tests/voleith/test_voleith.cpp` `FaestInterop` uses `faest::v3::faest_em_128_f` directly
    (`test_voleith.cpp:27-33`), so it is **unaffected** and still checks the shared code path
    against FAEST.
  - The header claim (`src/voleith.hpp:3-5`) already says, on branch `voleith-label-rows`, that
    proofs have FAEST's layout but are wire compatible with FAEST only for FAEST's own parameter
    sets: the relations' dedicated gate-label rows (patch 0005) lengthen the corrections. With the
    SHAKE switch it should also say that the leaf commitments use FAEST v1's SHAKE leaf hash.
    Proofs were already not FAEST signatures, and the README already says wire formats may change
    (`README.md:10`).
- **Optional further patch** (faest-arch-opt, not needed): a TurboSHAKE128 (12-round) leaf hash
  would roughly halve the Keccak cost, at the price of a nonstandard leaf hash and a subproject
  patch (see AGENTS.md on patch refresh).

---

## Part C: Recommendation

Ranking, from strongest and most standard guarantee per cost:

1. **(ii) Switch the five relations to `leaf_hash::shake`.**
   - *Guarantee:*
     - knowledge soundness in the plain QROM, with every oracle SHAKE;
     - seeds extracted by DFMS online extraction (EUROCRYPT 2022), error O(2,304·q·2⁻¹²⁸);
     - dead leaves by Zhandry's Lemma 5;
     - then the classical L3–L7 unchanged, plus Q2's round-by-round QROM lift;
     - no idealization of AES; ZK rests on the standard PRF assumption for AES-128.
   - *Cost:* ≈ 2,300 Keccak-f[1600] calls per side; +0.5–0.7 ms on Haswell, likely ≈ +0.1–0.15 ms
     on M4. No size change. KATs regenerated. No subproject patch.
   - *Concrete change:*
     - replace `faest::leaf_hash::aes_ctr` with `faest::leaf_hash::shake` at the five lines in §B1;
     - rewrite the ten `check` asserts;
     - update the `voleith.hpp:3-5` comment;
     - regenerate the KATs;
     - L0 must add the 37-byte `…‖0x00` SHAKE domain;
     - README §Model: the AES bullet becomes "AES is a fixed function (PRF for ZK only)", and Q1
       becomes unnecessary.
2. **(i) Keep AES and prove extraction in the QICM via key-level recording.**
   - Sound in outline, and it keeps the FAEST-EM leaf hash.
   - It still needs:
     - a generic-range DFMS commutator lemma;
     - an *efficient* simulation of touched keys' permutations: either [CM26]'s compressed
       ideal-cipher oracle, with loss ≥ 120q/2⁶⁴ and no extraction theorem yet, or a new
       multi-instance strong-qPRP hybrid.
   - It also rests on a heuristic about AES under adversarial keys.
   - Worth doing only if byte-compatibility with FAEST-EM leaf commitments or the ≈ 0.1–0.7 ms
     matters more than proof simplicity.
3. **(iii) Heuristic RO model of AES.**
   - If used, use the block-level A3 (forward-only random function on (k, block)), never A2's
     (k, iv, twk) form. A2 misses CTR-window overlaps that a real prover can exploit against the
     `lean/docs/sketch.md` extractor.
   - A3 is easy to work with, but it is not implied by the QICM except at the commitment plaintexts.
     Its full-strength derivation from the QICM costs q³/2¹²⁸.

A4 (key-alternating or EM) is dominated by (i) and is not recommended.

---

## References

- [ABKM22] G. Alagic, C. Bai, J. Katz, C. Majenz. *Post-Quantum Security of the Even-Mansour
  Cipher.* EUROCRYPT 2022. ePrint 2021/1601.
- [ABKMS24] G. Alagic, C. Bai, J. Katz, C. Majenz, P. Struck. *Post-Quantum Security of Tweakable
  Even-Mansour, and Applications.* EUROCRYPT 2024, LNCS 14651. ePrint 2022/1097.
- [ABMS25] G. Alagic, C. Bai, C. Majenz, K. Shi. *Post-Quantum Security of Block Cipher
  Constructions.* arXiv:2510.08725.
- [ACMT25] G. Alagic, J. Carolan, C. Majenz, S. Tokat. *The Sponge is Quantum Indifferentiable.*
  2025.
- [BHNSS19] X. Bonnetain, A. Hosoyamada, M. Naya-Plasencia, Y. Sasaki, A. Schrottenloher.
  *Quantum Attacks without Superposition Queries: the Offline Simon's Algorithm.* ASIACRYPT 2019.
- [BKR11] A. Bogdanov, D. Khovratovich, C. Rechberger. *Biclique Cryptanalysis of the Full AES.*
  ASIACRYPT 2011.
- [Car25] J. Carolan. *Compressed Permutation Oracles.* arXiv:2509.18586.
- [CFHL21] K.-M. Chung, S. Fehr, Y.-H. Huang, T.-N. Liao. *On the Compressed-Oracle Technique, and
  Post-Quantum Security of Proofs of Sequential Work.* EUROCRYPT 2021.
- [CHLYY25] A. Cojocaru, M. Hhan, Q. Liu, T. Yamakawa, A. Yun. *Quantum Lifting for Invertible
  Permutations and Ideal Ciphers.* arXiv:2504.18188.
- [CM26] J. Carolan, C. Majenz. *Compressed Permutation Oracles Revisited.* arXiv:2609.28469
  (Cor. 4.3, §4.6, Cor. 4.18, Thm. 5.6).
- [DFMS22] J. Don, S. Fehr, C. Majenz, C. Schaffner. *Online-Extractability in the Quantum
  Random-Oracle Model.* EUROCRYPT 2022, LNCS 13277, pp. 677–706. arXiv:2103.03085.
- [Gil14] H. Gilbert. *A Simplified Representation of AES.* ASIACRYPT 2014.
- [HY18] A. Hosoyamada, K. Yasuda. *Building Quantum-One-Way Functions from Block Ciphers:
  Davies-Meyer and Merkle-Damgård Constructions.* ASIACRYPT 2018. ePrint 2018/841.
- [JST21] J. Jaeger, F. Song, S. Tessaro. *Quantum Key-Length Extension.* TCC 2021. ePrint 2021/579.
- [Kim26] S. Kim. *Improved Soundness for Compressed Permutation Oracles and Tight Quantum Preimage
  and Collision Bounds for the Sponge.* ePrint 2026/2135.
- [MMW24] C. Majenz, G. Malavolta, M. Walter. *Permutation Superposition Oracles for Quantum Query
  Lower Bounds.* ePrint 2024/1140, arXiv:2407.09655.
- [Sas11] Y. Sasaki. *Meet-in-the-Middle Preimage Attacks on AES Hashing Modes and an Application
  to Whirlpool.* FSE 2011.
- [Unr21] D. Unruh. *Compressed Permutation Oracles (And the Collision-Resistance of Sponge/SHA3).*
  ePrint 2021/062 (with erratum).
- [Yue14] H. Yuen. *A Quantum Lower Bound for Distinguishing Random Functions from Random
  Permutations.* QIC 2014. arXiv:1310.2885.
- [Zha12] M. Zhandry. *How to Construct Quantum Random Functions.* FOCS 2012 (small-range
  distributions, oracle indistinguishability).
- [Zha15] M. Zhandry. *A Note on the Quantum Collision and Set Equality Problems.* QIC 15 (2015).
  arXiv:1312.1027.
- [Zha16] M. Zhandry. *A Note on Quantum-Secure PRPs.* ePrint 2016/1076, arXiv:1611.05564.
- [Zha19] M. Zhandry. *How to Record Quantum Queries, and Applications to Quantum
  Indifferentiability.* CRYPTO 2019.
- [Zha21] M. Zhandry. *Redeeming Reset Indifferentiability and Applications to Post-Quantum
  Security.* ASIACRYPT 2021.

Sources consulted online: eprint.iacr.org/2024/1140, eprint.iacr.org/2021/062,
eprint.iacr.org/2026/2135, arxiv.org/abs/2509.18586, arxiv.org/abs/2609.28469,
arxiv.org/abs/2504.18188, arxiv.org/abs/2510.08725, eprint.iacr.org/2021/1601,
eprint.iacr.org/2022/1097, eprint.iacr.org/2018/841, eprint.iacr.org/2021/579,
arxiv.org/abs/2103.03085, arxiv.org/abs/1310.2885, arxiv.org/abs/1611.05564. Bibliographic details
for [ACMT25], [Gil14], [BKR11], [Sas11], [BHNSS19], [CFHL21], [Zha12], [Zha19] and [Zha21] are from
memory and should be spot-checked. The [CM26] theorem numbers come from the arXiv HTML and should be
re-checked against the PDF.
