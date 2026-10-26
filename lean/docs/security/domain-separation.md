# Domain separation of every hash, XOF and permutation call in vole-mole

This file proves the domain-separation lemma that `lean/docs/security/pomfrit.md`, `lean/docs/security/moussaka.md`
and `lean/docs/security/ratatouille.md` cite as **Lemma DS**. It extends L0 of
`lean/docs/extraction/L0-L2-commitments.md` (§2.1–2.2), which covers only the proof system's twelve SHAKE128
domains. Here we add the application-level hashes and XOFs, pqov's SHAKE256 and AES uses, and the
Keccak-p[800,12] commitments.

The machine-checked part is `lean/VoleMole/Protocols/DomainSeparation.lean` (no `sorry`, no
`axiom`; `#print axioms` shows only `propext` and `Quot.sound`). It checks the full SHAKE128
tag/length/prefix table, proves the separation criterion sound, and exhibits concrete strings for
every overlap reported in §3.3. Every input length in §2 was also **measured**: we traced every
`Keccak_Hash*` call (via `-Wl,--wrap`) while running `examples/{pomfrit,moussaka,ratatouille}.cpp`,
and the traced lengths, first bytes, final bytes and output lengths match the tables exactly
(§2.4).

## 0. Summary

**Result.** Every SHAKE128 call in vole-mole falls into one of 25 input domains: 18 for the proof
system (per relation where lengths differ), 5 fixed-length application domains, PomFRIT's
`hash_to_target`, and PomFRIT's seed XOF. The first 23 are pairwise disjoint (Lean:
`clean_pairwise`). Disjointness comes from a final tag byte (proof system), a 7-byte DST prefix
(application) or the input length. The SHAKE256 calls (pk digest, pqov keygen, pqov vinegar) have
three distinct fixed lengths. The three Keccak-p[800,12] calls have distinct 7-byte DST prefixes.

**Finding F-DS1 (real overlap; no exploit found).** The PomFRIT `hash_to_target` domain
(`pomfrit.cpp:96-111`) ends in the caller's variable-length `msg`, with no length prefix and no
final tag. As a set, it **overlaps** the proof-system domains H₁ (all three shapes), H₃, H₂¹ and
H₂². Example: `"pomf\0h0" ‖ 0^4089 ‖ 0x01` is both a `hash_to_target` input (msg = 0^3812 ‖ 01)
and an H₁ leaf-hash input for a 128-leaf tree (§3.3). Each half can be reached by an adversary on
its own:
- any PomFRIT verifier hashes `TARGET_DST ‖ … ‖ msg` for any chosen msg;
- any VOLEitH verifier hashes an H₁ leaf string whose first 32 bytes are attacker-chosen (the opened
  hidden-leaf commitment when Δᵢ = 0, about 2⁷ grinding).

So **no** assignment of strings to oracles makes `hash_to_target` *formally* independent of those
four oracles. What is hard is a *meaningful* collision: one string used honestly in both roles
(§3.4). Its probability is

    ε_MC ≤ 2·q₁₂₈·q₂₅₆·2⁻²⁵⁶ + q_E·(q₁₂₈ + q₂₅₆)·2⁻²⁵⁴ + n₃·(n_T + q₁₂₈)·2⁻¹²⁸.

No exploit is known. The only consequence is a prefix relation between outputs: the 45-byte target
would be a prefix of chal₁ or chal₂, or would begin with a 32-byte H₁/H₃ output.

**Finding F-DS2 (overlap, harmless by secrecy).** PomFRIT's seed XOF (`pomfrit.cpp:150-161`) also
ends in `msg`. It overlaps H₁, H₂⁰ (PomFRIT and Ratatouille spend), H₃, H₂¹, H₂² and H₂³ as sets.
Every honest evaluation contains a fresh uniform 256-bit secret seed, so treating the XOF as an
independent oracle costs at most n_seed·Q·2⁻²⁵⁶.

**Proposed minimal fix (not implemented).** Append one final byte `APP_TAG = 0x20` to the inputs of
`hash_to_target` and of the PomFRIT seed XOF. The byte must lie outside the proof system's tag set
{0x01, 0x03, 0x04, 0x05, 0x08–0x0C} and differ from the combination hash's last byte 0x30. With the
fix, all 25 domains are pairwise disjoint (Lean: `fixed_pairwise`), and Lemma DS holds for every
oracle without exception (§7, §8).

**Other results.**
- **No XOF output-length reuse.** Every domain reads one fixed output length, the same for every
  relation. Multi-squeeze XOFs read consecutive, disjoint segments of one stream (§4).
- **Keccak-p[800,12]** is a different permutation from Keccak-f[1600], so it needs no separation
  from SHAKE. Model it as an independent ideal permutation. Its three uses then act as independent
  random oracles except with probability q_π·2⁻²²² + q_π²·2⁻⁴⁴⁰ (§5).
- **pqov** uses SHAKE256 (keygen, vinegar) and AES-128-CTR with a public key (expansion of the
  public map). The AES calls are extra queries to the one ideal cipher of L0 and must be counted in
  q_E. They need no separation (§6).
- **Correction to L0 §2.5 O3.** For the shipped relations the binders are fixed-length, so H₂¹, H₂²
  and H₃ have pairwise *distinct* lengths across relations, and H₂⁰ is told apart by its DST. A raw
  H₂¹ string therefore parses for at most one relation. H₁, H₄, H₅ and H₂³ (length 205 for four
  relations) are shared across relations by design (§3.5).

The citable statement is in §7.

---

## 1. Model and `hash_state` semantics

`faest::hash_state` (`subprojects/faest-arch-opt/hash.hpp:21-60`) wraps XKCP's `Keccak_HashInstance`:
- `init(s)` selects SHAKE128 (rate 1344, capacity 256, suffix 0x1F, `KeccakHash.h:61`) for λ ≤ 128.
  Otherwise it selects SHAKE256 (rate 1088). Every relation here has λ = 128. The only s256 use is
  the UOV pk digest (`uov.cpp:83`).
- `update(p, n)` absorbs n bytes. `update_byte(b)` is `update(&b, 1)`: an ordinary message byte with
  no special meaning. A "domain separator" byte is therefore simply the **last message byte**.
- `finalize(out, n)` calls `Keccak_HashFinal`, which appends SHAKE's suffix and pad10*1, then
  squeezes n bytes. Code that calls `Keccak_HashFinal` and then `Keccak_HashSqueeze` several times
  (the seed XOFs) reads consecutive segments of one output stream.
- `hash_state_x4` (H₅, grinding for H₂³) absorbs the same layout per lane. `update_1` feeds the same
  bytes to all four lanes, and `update_4` feeds per-lane data of equal length.

All calls are byte-aligned. So each call is SHAKE(M, ℓ) for a byte string M (the concatenation of
the updates) and a fixed ℓ. SHAKE's padding is injective on byte strings.

**Idealization.** SHAKE128 is one random oracle H: {0,1}* → {0,1}^∞. Each call reads a prefix of
the output. A *domain* is a set D_d of byte strings together with an injective encoding
enc_d: (fields) → D_d. The oracle O_d := H ∘ enc_d is H restricted to D_d. If the sets D_d are
pairwise disjoint, then the O_d (and H on the complement) are **perfectly independent** random
oracles, because they are restrictions of one random function to disjoint sets. Only disjointness
is needed, not prefix-freeness: inputs are whole strings, not blocks of an iterated construction.
SHAKE256 is a second random oracle. It is independent of SHAKE128 by the multi-rate padding
argument for sponges that share Keccak-f[1600] but have different rates (Bertoni–Daemen–Peeters–
Van Assche, *Cryptographic sponge functions*, multi-rate padding; *The Keccak reference* 3.0).
This is a standard assumption and is not re-proved here.

---

## 2. Inventory

Notation: ℓ_w is the witness bytes, M = 45 and N = 119 are the UOV dimensions (`uov.hpp:17-18`),
and D = SHAKE256(cpk) is a 32-byte pk digest. "Tag" is the final byte.

### 2.1 SHAKE128: proof system (all relations: `parameter_set<s128, 17, …>`)

Lengths per relation (measured; "–" means not used):

| Domain | Layout (bytes) | Final | PomFRIT | Mous. issue | Mous. redeem | Rata. issue | Rata. spend | Out | Code |
| --- | --- | --- | --- | --- | --- | --- | --- | --- | --- |
| H₁ leaves k=8 | com_{0,0..255} (32 each) ‖ 01 | 01 | 8193 | 8193 | 8193 | 8193 | 8193 | 32 | `vole_commit.inc:29-62` |
| H₁ leaves k=7 | com_{i,0..127} ‖ 01 | 01 | 4097 | 4097 | 4097 | 4097 | 4097 | 32 | same |
| H₁ com | h₀ ‖ … ‖ h₁₆ ‖ 01 | 01 | 545 | 545 | 545 | 545 | 545 | 32 | `vole_commit.inc:64-80` |
| H₂⁰ (mu) | enc(x) ‖ DST_R (7) ‖ 08 | 08 | 85 | 69 | 104+32k, 1≤k≤64 | 64 | 120 | 32 | `voleith.hpp:107-123` |
| H₂⁴ (mu, delayed) | DST_R ‖ 0C | 0C | 8 | – | – | – | – | 32 | `voleith.hpp:117-121` |
| H₃ | w_prefix ‖ mu ‖ rho (16) ‖ 03 | 03 | 94 | 305 | 392 | 289 | 896 | 32 | `voleith.hpp:169-184` |
| H₄ | iv_pre (16) ‖ mu ‖ 04 | 04 | 49 | 49 | 49 | 49 | 49 | 16 | `voleith.hpp:187-194,366-377` |
| H₅ (gate) | iv ‖ e (u32) ‖ label (16) ‖ 05 | 05 | 37 | 37 | 37 | 37 | 37 | 4 | `vole_commit.inc:372-431` |
| H₂¹ | mu ‖ com ‖ corr ‖ c_mult ‖ iv_pre ‖ binder₁ ‖ 09 | 09 | 3188 | 4645 | 6037 | 4389 | 14101 | 136 | `voleith.hpp:206-216,396-406` |
| H₂² | chal₁ (136) ‖ ũ (64) ‖ h_V (64) ‖ [mu] ‖ binder₂ ‖ d (ℓ_w) ‖ 0A | 0A | 493 | 521 | 608 | 505 | 1112 | 56 | `voleith.hpp:218-226,267-285,433-450`; `kos_vole_check.hpp:107,138,172-177` |
| H₂³ | chal₂ (56) ‖ ã₀ (16) ‖ ã₁.. ‖ ctr (u32) ‖ 0B | 0B | 93 | 205 | 205 | 205 | 205 | 16 | `voleith.hpp:297-307,470-480` |
| Comb. l | chal₂ (56) ‖ DST_comb (7) | 0x30 | 63 | – | 63 | – | 63 | 720 | `uov/circuit.hpp:59-66` |

Instance encodings `enc(x)` (`hash_instance`):

| Relation | enc(x) | Bytes | Code |
| --- | --- | --- | --- |
| PomFRIT redeem | D_pk ‖ h | 32 + 45 | `pomfrit/redeem.hpp:108-111` |
| Moussaka issue | t ‖ ctx_iss | 45 + 16 | `moussaka/issue.hpp:164-167` |
| Moussaka redeem | u32(64) ‖ u32(k) ‖ D₁..D_k ‖ nf ‖ ctx_iss ‖ ctx_red ‖ challenge_digest | 8 + 32k + 88 | `moussaka/redeem.hpp:182-200`; 1 ≤ k ≤ 64 by `moussaka.cpp:139-141` |
| Ratatouille issue | c ‖ ⟨t_init⟩_L ‖ ctx_iss | 32 + 8 + 16 | `ratatouille/issue.hpp:151-155` |
| Ratatouille spend | D_pk ‖ nf ‖ ⟨d⟩_L ‖ c' ‖ ctx_iss | 32 + 24 + 8 + 32 + 16 | `ratatouille/spend.hpp:321-327` |

Binders (all callers: `pomfrit.cpp:167,213,229,236`; `voleith_prove`/`voleith_verify` callers in
`moussaka/{issue,redeem}.hpp`, `ratatouille/{issue,spend}.hpp`):
- PomFRIT: binder₁ = refresher_com (32 bytes) and binder₂ = refresher (32 bytes). The `[mu]` field is
  present in H₂² (delayed instance).
- All other relations: both binders are empty, and `[mu]` is absent.

So **every proof-system domain has a fixed length per relation**, except H₂⁰ for Moussaka redeem,
which is length-prefixed by k. The combination DSTs are `"pomf\0l0"`, `"mous\0l0"` and
`"rata\0l0"` (callers `pomfrit/redeem.hpp:126`, `moussaka/redeem.hpp:253`,
`ratatouille/spend.hpp:379`).

Not hashes (see L0 §2.1): QuickSilver χ (bytes of chal₂), the KOS keys (bytes of chal₁), the BAVC
leaf hash (AES), the SHAKE PRG and `faest.inc`. The relations' in-circuit Keccak is an
arithmetization, not an oracle call.

### 2.2 SHAKE128: application level (prefix DST from `src/dst.hpp:33-55`; VERSION = 0)

| # | Oracle | Layout | Length | Out | Protocol step | Code |
| --- | --- | --- | --- | --- | --- | --- |
| A1 | PomFRIT refresher_com | `"pomf\0r0"` ‖ refresher (32) | 39 | 32 | client Sig1, verifier | `pomfrit.cpp:76-84`; calls `:166,225` |
| A2 | PomFRIT `hash_to_target` | `"pomf\0h0"` ‖ D_pk ‖ chal₁ (136) ‖ vole_check_proof (64) ‖ corr[0..45) ‖ **msg** | 284 + \|msg\| | 45 | client Sig1 line 5, verifier | `pomfrit.cpp:96-111`; calls `:170,234` |
| A3 | PomFRIT seed XOF | `"pomf\0s0"` ‖ seed (32) ‖ D_pk ‖ **msg** | 71 + \|msg\| | 16 ‖ 32 ‖ 45 (rho, refresher, r) | client Sig1 | `pomfrit.cpp:150-161` |
| A4 | Moussaka issue seed | `"mous\0s0"` ‖ seed (32) | 39 | 24 ‖ 16 ‖ 16 (nf, r, rho) | issue request | `moussaka.cpp:58-71` |
| A5 | Moussaka redeem seed | `"mous\0s1"` ‖ seed (32) | 39 | 16 (rho) | redeem request | `moussaka.cpp:74-86` |
| A6 | Ratatouille issue seed | `"rata\0s0"` ‖ seed (32) | 39 | 24 ‖ 16 ‖ 16 | issue request | `ratatouille.cpp:70-84`, call `:155` |
| A7 | Ratatouille spend seed | `"rata\0s1"` ‖ seed (32) | 39 | 24 ‖ 16 ‖ 16 | spend request | same, call `:242` |

Seeds are 32 bytes (`*/seeded.hpp`) from `random_bytes` (`src/random.cpp`: OS `getrandom`, no
hashing). The public API passes a fresh random seed. Only the `detail::*_with_seed` test entry
points let the caller choose it. All 18 DSTs are pairwise distinct (`static_assert`,
`dst.hpp:56-86`). Every application input begins with its DST at offset 0, so any two
application domains differ in their first 7 bytes.

Within-domain injectivity holds:
- A1 and A4–A7 are fixed-length.
- A2 and A3 have fixed fields, followed by one variable field (msg) at the end.
- The combination hash is fixed-length.

### 2.3 SHAKE256 and other primitives

| # | Oracle | Layout | Length | Out | Code |
| --- | --- | --- | --- | --- | --- |
| U1 | pk digest | cpk (46591) | 46591 | 32 | `uov.cpp:82-85` (every `PublicKey` construction) |
| U2 | pqov keygen | sk_seed (32) | 32 | 16 + 3330 (pk_seed ‖ O) | `pqov/src/ov_keypair.c:170-182` |
| U3 | pqov vinegar | target (45) ‖ sk_seed (32) ‖ `"pqov-derive-preimage"` (20) ‖ ctr (1) | 98 | 74 | `pqov/src/ov.c:226-238`, loop `:117-125` (ctr < 256 distinct) |

pqov is built with `_UTILS_BUILTIN_` and without `_HASH_SHAKE128_`, so `hash_ctx` is its built-in
SHAKE256 (`pqov/utils/utils_hash.h:16-45`, `utils_hash.c:52-88`). pqov's `ov_sign`/`ov_verify`
(H(M ‖ salt)) cannot be reached from the public API, because `include/vole_mole/uov.hpp` has no
sign or verify.

**AES-128.** There are two kinds of AES use:
- faest's `aes_ctr_prg`, in the four roles of L0 §2.3;
- pqov's AES-128-CTR "public inputs" PRNG with key pk_seed (public) and nonce 0, which expands P1
  and P2 (274 725 bytes, about 17 171 blocks per `PublicKey` construction): `ov_keypair.c:66-75,
  190-199`, `utils_prng.c`.

**Keccak-p[800,12]** (`src/keccak/keccak.cpp:54`, `include/vole_mole/keccak.hpp:25`). Each call is
one permutation call on a 100-byte state:

| # | Use | State layout (100 bytes) | Fixed bits | Output read | Code |
| --- | --- | --- | --- | --- | --- |
| K1 | Moussaka Com | `"mous\0c0"` ‖ r (16) ‖ 0⁹ ‖ ctx_iss ‖ ctx_red ‖ nf (24) ‖ 0¹² | 224 | first 45 (= UOV target) | `moussaka/commit.hpp:32-48`, `moussaka.cpp:89-95` |
| K2 | Ratatouille Com | `"rata\0c0"` ‖ r (16) ‖ 0⁹ ‖ ctx_iss ‖ ⟨t⟩_L ‖ nf ‖ 0²⁰ | 288 | first 32 | `ratatouille/commit.hpp:56-77`, `ratatouille.cpp:94-100`, `spend.hpp:236` |
| K3 | Ratatouille Tag | `"rata\0t0"` ‖ 0²⁵ ‖ c (32) ‖ ⟨x⟩_L ‖ 0²⁸ | 480 | first 45 (= UOV target) | `ratatouille/commit.hpp:79-93`, `ratatouille.cpp:102-107` |

The relations also evaluate K1–K3 inside the circuit. Those are statements about the same function,
not extra oracle calls.

### 2.4 Trace check

We relinked the three examples with `-Wl,--wrap` around the eight `Keccak_Hash*` entry points
(single and ×4). A copied `hash_state` is tracked by matching its snapshot. Every SHAKE call was
traced; none was left untracked. The traced (primitive, length, output length, 7-byte prefix,
final byte) classes are exactly the rows above:
- PomFRIT shows lengths 8, 37, 39, 49, 63, 85, 89 (seed XOF with an 18-byte msg), 93, 94,
  302 (target, 18-byte msg), 493, 545, 3188 (2932 before `64fd1a4`), 4097 and 8193.
- Moussaka shows 37, 39, 49, 63, 69, 200 (redeem H₂⁰ with k = 3), 205, 305, 392, 521, 545, 608,
  4097, 4645, 6037 and 8193.
- Ratatouille shows 37, 39, 49, 63, 64, 120, 205, 289, 505, 545, 896, 1112, 4097, 4389, 8193 and
  14101.
- SHAKE256 shows only length 46591. pqov's internal SHAKE256 does not go through XKCP and was
  checked from source.

PomFRIT's mu = H₂⁴(`"pomf\0p0"` ‖ 0C) is the constant
`1a4e66b84fdc6f79d37d3516bf9776606a656922e352711502f049207b7e3a49`. This value was computed from
`hash_mu` and independently with Python's `hashlib`.

---

## 3. Disjointness

### 3.1 Criterion

A domain is described by a known prefix, a known suffix and a set of lengths. Two domains are
disjoint if (i) their length sets are disjoint, (ii) their prefixes disagree at a common position,
or (iii) their suffixes disagree at a common position from the end. Each condition alone rules out
a common string (Lean: `sep_sound`). The proof-system domains use the suffix; for H₂⁰ the suffix is
DST_R ‖ 08, and for Moussaka redeem the prefix 40 00 00 00 (u32 LE of MAX_ANCHORS = 64) is used
too. The application domains use the DST prefix.

### 3.2 The 23 separated domains (Lean: `clean_pairwise`)

These are the 18 proof-system rows of §2.1 (H₂⁰ split per relation and the combination hash split
per protocol) and A1, A4–A7.
- **Proof system against proof system.** Final bytes 01, 08, 0C, 03, 04, 05, 09, 0A, 0B and 0x30 are
  pairwise distinct. The three H₁ shapes are told apart by length (8193, 4097, 545). The five H₂⁰
  domains are told apart by their DST suffix. The three combination domains are told apart by their
  DST. This is L0, refined.
- **Application against application.** Distinct 7-byte DST prefixes.
- **Proof system against fixed-length application (length 39).** No proof-system domain contains
  length 39. The nearest are H₅ at 37 and H₄ at 49, and H₂⁰ is at least 64. The combination
  domains have length 63. This covers the "application input ending in 0x01..0x0C" concern for A1
  and A4–A7: their last byte is a random refresher or seed byte, but their length differs from
  every proof-system length.

### 3.3 The two variable-length application domains (Lean: `target_sep`, `seed_sep`, `target_meets_*`, `seed_meets_*`)

**A2 (`hash_to_target`, length ≥ 284, prefix `"pomf\0h0"`, any final byte).** A2 is disjoint from:
- H₂⁰ for PomFRIT, Moussaka issue, Ratatouille issue and Ratatouille spend (lengths 85, 69, 64 and
  120, all below 284);
- H₂⁰ for Moussaka redeem (first byte 0x40 ≠ 0x70);
- H₂⁴, H₄, H₅, H₂³ (93, 205) and the combination domains (lengths);
- every application domain (prefix).

A2 is **not** disjoint from H₁ (8193, 4097, 545), H₃ (305, 392, 289, 896), H₂¹ or H₂². Concrete
common strings (each is also checked in Lean):

| Overlap | String x | As A2 | As the proof-system input |
| --- | --- | --- | --- |
| A2 ∩ H₁ (k=7) | `"pomf\0h0"` ‖ 0⁴⁰⁸⁹ ‖ 01 (4097 B) | D = 0³², chal₁ = 0¹³⁶, vcp = 0⁶⁴, corr = 0⁴⁵, msg = 0³⁸¹² ‖ 01 | com_{i,0} = `"pomf\0h0"` ‖ 0²⁵, com_{i,j≥1} = 0³² |
| A2 ∩ H₁ (k=8) | `"pomf\0h0"` ‖ 0⁸¹⁸⁵ ‖ 01 | msg = 0⁷⁹⁰⁸ ‖ 01 | tree-0 leaf string |
| A2 ∩ H₁ com | `"pomf\0h0"` ‖ 0⁵³⁷ ‖ 01 | msg = 0²⁶⁰ ‖ 01 | h₀ = `"pomf\0h0"` ‖ 0²⁵, h₁..₁₆ = 0³² |
| A2 ∩ H₃ (Mous. issue) | `"pomf\0h0"` ‖ 0²⁹⁷ ‖ 03 (305 B) | msg = 0²⁰ ‖ 03 | w = `"pomf\0h0"` ‖ 0²⁴⁹, mu = 0³², rho = 0¹⁶ |
| A2 ∩ H₂¹ (PomFRIT length) | `"pomf\0h0"` ‖ 0³¹⁸⁰ ‖ 09 (3188 B) | msg = 0²⁹⁰³ ‖ 09 | mu = `"pomf\0h0"` ‖ 0²⁵, rest 0 |
| A2 ∩ H₂² (PomFRIT length) | `"pomf\0h0"` ‖ 0⁴⁸⁵ ‖ 0A (493 B) | msg = 0²⁰⁸ ‖ 0A | chal₁ = `"pomf\0h0"` ‖ 0¹²⁹, rest 0 |

*Reachability of each half.* The **A2 half** is free: any PomFRIT verifier
(`pomfrit.cpp:219-237`) hashes `TARGET_DST ‖ D_pk ‖ chal₁ ‖ … ‖ msg` for a msg of the adversary's
choosing. That string can have any length ≥ 284 and any final byte.

The **H₁ half** is cheap. A VOLEitH verifier recomputes hᵢ over the leaf commitments of tree i in
natural order, after replacing the hidden leaf's commitment with the one supplied in the proof (L0
§1: `vector_com.inc:951,968-970`). When Δᵢ = 0, which costs about 2⁷ or 2⁸ H₂³ trials and is folded
into the grinding, com_{i,0} is the first 32 bytes of the H₁ input and is chosen by the adversary.
So a Moussaka issuer, say, can be made to hash a 4097-byte string that starts with
`"pomf\0h0"` and ends in 01.

For the PS halves of H₂¹, H₂² and H₁-com, the first 32 bytes are SHAKE outputs (mu, chal₁, h₀).
Reaching a 7-byte prefix there costs about 2⁵⁶ queries. For PomFRIT's own H₂¹ it is impossible,
because mu is the constant 1a4e… (§2.4).

**A3 (PomFRIT seed XOF, length ≥ 71, prefix `"pomf\0s0"`).** A3 is disjoint from:
- H₂⁰ for Moussaka issue (69), Ratatouille issue (64) and Moussaka redeem (prefix);
- H₂⁴, H₄, H₅ and the combination domains (lengths);
- every application domain (prefix).

It is **not** disjoint from H₁ (all three), H₂⁰ for PomFRIT (85) and Ratatouille spend (120), H₃,
H₂¹, H₂² or H₂³. Example: `"pomf\0s0"` ‖ 0⁷⁰ ‖ `"pomf\0p0"` ‖ 08 (85 B) is an A3 input (seed = D =
0³², msg = 0⁶ ‖ `"pomf\0p0"` ‖ 08) and an H₂⁰ input of the PomFRIT relation (D = `"pomf\0s0"` ‖ 0²⁵,
h = 0⁴⁵).

A2 and A3 are disjoint from each other (prefix; Lean: `target_seed_sep`).

### 3.4 Impact

**Formal independence fails for A2.** Fix any rule ρ that assigns each string of
A2 ∩ (H₁ ∪ H₃ ∪ H₂¹ ∪ H₂²) to one oracle. Then the adversary can make an honest party use one of
those strings in the *other* role and also query it itself. For a string with ρ = A2, a VOLEitH
verifier uses it as H₁ via the hidden leaf. For a string with ρ = H₁, a PomFRIT verifier uses it as
A2 via msg. In both cases the adversary's single SHAKE answer equals the honest party's value in a
role the ideal model would keep independent. So the standard reduction ("answer each raw query
x with O_{ρ(x)}(x)") is not identical-until-negligible, and **A2 cannot be listed as an
independent random oracle next to H₁, H₃, H₂¹ and H₂²** without the fix.

**A meaningful collision is hard.** Let MC_T be the event that some string is evaluated both as an
A2 input by an honest party (PomFRIT client or verifier, or a simulator acting for one) and as an
H₁, H₃, H₂¹ or H₂² input by an honest party (prover, verifier, extractor or simulator). Write:
- q₁₂₈ and q₂₅₆ for all SHAKE128 and SHAKE256 evaluations by anyone;
- q_E for all ideal-cipher queries, counting pqov's (§6);
- n_T for the number of honest A2 evaluations and n₃ for the number of honest H₃ evaluations.

Every honest A2 string has the form `"pomf\0h0"` ‖ D_pk ‖ C ‖ …, where D_pk is a SHAKE256 output
and C is the H₂¹ output of a PomFRIT proof.

- *H₂¹ of relation R.* The string starts with mu_R. For R = PomFRIT, mu is the constant 1a4e…, so
  the event is impossible. Otherwise mu_R is an H₂⁰ output and must equal `"pomf\0h0"` ‖ D[0..25).
  That fixes all 256 bits of mu given D, so the probability is ≤ q₁₂₈·q₂₅₆·2⁻²⁵⁶.
- *H₂².* chal₁[0..39) = `"pomf\0h0"` ‖ D, so the probability is ≤ q₁₂₈·q₂₅₆·2⁻³¹².
- *H₁ com.* h₀ = `"pomf\0h0"` ‖ D[0..25), so the probability is ≤ q₁₂₈·q₂₅₆·2⁻²⁵⁶.
- *H₁ leaves, tree i, hidden index j.* Each commitment that is not hidden is an ideal-cipher pair
  (E_k(z), E_k(z ⊞ e₀)). If j ≠ 0, com_{i,0} must equal `"pomf\0h0"` ‖ D[0..25). If j = 0,
  com_{i,2} must equal C[25..57). Each (cipher pair, SHAKE value) pair matches with probability
  ≤ ((2¹²⁸ − q_E)(2¹²⁸ − q_E − 1))⁻¹ ≤ 2⁻²⁵⁴. Total ≤ q_E·(q₁₂₈ + q₂₅₆)·2⁻²⁵⁴.
- *H₃.* Every honest H₃ input contains the prover's fresh 128-bit rho, and rho enters nothing else.
  The A2 strings that honest parties evaluate are fixed independently of rho, except through
  inverting H₃. So the probability is ≤ n₃·(n_T + q₁₂₈)·2⁻¹²⁸.

Hence Pr[MC_T] ≤ ε_MC, with ε_MC as in §0.

**Consequence if MC_T happened.** The outputs would be prefix-related: the 45-byte target would be
the first 45 bytes of chal₁ (136 B) or chal₂ (56 B), or the 32-byte h₀ or H₃ output (seed ‖ iv_pre)
would be the first 32 bytes of the target. We see no way to use this. Knowing the target does not
yield a UOV preimage, and h₀, chal₁ and chal₂ stay collision-resistant and unpredictable as
functions of their own inputs. But the PomFRIT proof cannot simply cite "independent ROs".

**How the protocol proofs can proceed without the fix.**
- *Moussaka and Ratatouille* use no variable-length application hash. Their oracles (A4–A7, the
  combination hash and the proof-system oracles) are all in the separated set. Lemma DS(a) applies
  unconditionally. This holds even when PomFRIT runs in the same system, because Lemma DS(a) is a
  statement about the restrictions of H to their own domains, whatever else H is evaluated on.
- *PomFRIT* may treat O_tgt as an independent random oracle in a game hop as long as the hop only:
  1. programs O_tgt at a string with a value that is uniform (or ε-close) on the 45 bytes read;
     the other roles then see a uniform prefix, which is consistent;
  2. reads the query list (extraction);
  3. relies on freshness of a string.

  It must not program O_tgt and a proof-system oracle to inconsistent values at one string. For
  strings used honestly, that conflict requires MC_T (probability ≤ ε_MC). The forgery reduction
  programs O_tgt at the forger's target queries. The ZK/blindness simulator programs H₂¹, H₂² and
  H₂³ at strings that contain its own fresh randomness (com, iv_pre, chal₁). So the conflict occurs
  only through MC_T. Each such hop must add ε_MC.

**A3 is harmless.** Assign the overlap strings to the proof-system oracles. An inconsistency then
requires a second evaluation (by anyone) of an honest A3 string, which needs the 256-bit seed:
probability ≤ n_seed·Q·2⁻²⁵⁶ (Q = all SHAKE128 evaluations).

### 3.5 Relation-level separation (correction to L0 O3)

The shipped binders are fixed-length (§2.1), so:
- H₂¹ lengths are pairwise distinct across the five relations: 3188, 4645, 6037, 4389 and 14101;
- H₂² lengths are pairwise distinct: 493, 521, 608, 505 and 1112;
- H₃ lengths are pairwise distinct: 94, 305, 392, 289 and 896;
- H₂⁰ is told apart by its DST suffix.

So one raw H₂¹ (or H₂², H₃, H₂⁰) string parses for **at most one** relation, and L0's O3 does not
arise for these parameters. H₁ (all lengths), H₄, H₅ and H₂³ are shared: H₂³ has length 205 for
Moussaka issue, Moussaka redeem, Ratatouille issue and Ratatouille spend. They bind the relation
only through mu (H₄ directly; H₂³ through chal₂ ← chal₁ ← mu). This is enough for the
single-relation statements cited here. A multi-relation simulation-extractability argument should
use the chain, not these oracles' domains. The `TODO` at `voleith.hpp:147-148` proposes
variable-length binders. If that happens, binders must be length-prefixed, or the per-relation
length separation above (and the relation-level parse) is lost.

---

## 4. XOF output-length reuse

SHAKE outputs are prefix-consistent, so a problem would need one input squeezed to two lengths.
- **Fixed length per domain, the same across relations.** H₁ 32, H₂⁰ and H₂⁴ 32, H₃ 32 (split as
  seed ‖ iv_pre), H₄ 16, H₅ 4, H₂¹ 136, H₂² 56, H₂³ 16, combination 720 (= M·16). A1 32, A2 45,
  A3 93 (rho 16 ‖ refresher 32 ‖ r 45), A4 56 (nf 24 ‖ r 16 ‖ rho 16), A5 16, A6 and A7 56. U1 32,
  U2 3346, U3 74. All were traced, except U2 and U3, which come from source.
- **Multi-squeeze XOFs** (A3–A7, `Keccak_HashFinal` then several `Keccak_HashSqueeze`) and split
  outputs (H₃, U2) read consecutive, disjoint segments of one stream. These segments are jointly
  uniform and independent.
- **No string lies in two separated domains** (§3.2). So no input is squeezed to two lengths,
  except within the A2 overlaps of §3.4. There the prefix relation is exactly the consequence
  already stated: the target is a prefix of chal₁ or chal₂, or the 32-byte H₁ or H₃ output is a
  prefix of the target.
- `hash_mu` is called twice per PomFRIT proof, on different inputs (H₂⁴, then H₂⁰). It is not one
  input read twice.

---

## 5. Keccak-p[800,12]

**Separation from SHAKE is not needed.** K1–K3 use a different permutation (width 800, 12 rounds)
from SHAKE (Keccak-f[1600], 24 rounds). No SHAKE call ever evaluates Keccak-p[800], and no
Keccak-p[800] call evaluates Keccak-f[1600]. The two primitives share only data flow: K1/K2
outputs enter H₂⁰ instance encodings, and K1/K3 outputs are UOV targets. Their inputs never
overlap. Model Keccak-p[800,12] as an **ideal permutation π, independent of Keccak-f[1600] and of
AES**. This is an assumption about a reduced-round permutation: Keccak-f[800] has 22 rounds.

**Separation among K1–K3.** Their 7-byte DST prefixes are distinct, so their input sets are
disjoint. Each Kᵢ fixes its DST and zero bytes and reads a truncation of length oᵢ:
- K1: 224 fixed bits, 440-bit unread tail;
- K2: 288 fixed bits, 544-bit unread tail;
- K3: 480 fixed bits, 440-bit unread tail.

**Random-oracle bound.** Simulate π lazily:
- A forward query at a K_i input enc_i(m) returns RO_i(m) ‖ (uniform tail), avoiding used outputs.
- Any other query is answered uniformly among unused values.

The simulation fails only in three cases:
- (a) a fresh inverse query returns a string in some Im(enc_i): probability
  ≤ q_π(2⁵⁷⁶ + 2⁵¹² + 2³²⁰)/(2⁸⁰⁰ − q_π) ≤ q_π·2⁻²²²;
- (b) a simulated full output collides with a used one: ≤ q_π²·2⁻⁴⁴¹;
- (c) an inverse query hits RO_i(m) ‖ tail before the forward query fixed the tail: ≤ q_π·2⁻⁴⁴⁰.

So F_i(m) := trunc_{oᵢ}(π(enc_i(m))) for i = 1, 2, 3 are **independent random oracles** (and
independent of π elsewhere), up to

    ε_π ≤ q_π·2⁻²²² + q_π²·2⁻⁴⁴⁰.

The protocol proofs need these consequences:
- collision resistance of the Com outputs: 2^{−128} birthday bound for K2's 256-bit output;
- hiding through r (128 bits): K1 and K2 are ROs on inputs with 128 bits of fresh r;
- programmability of K3, which acts as a hash-to-UOV-target.

This is a classical (ROM/ideal-permutation) statement. The QROM is not covered here.

---

## 6. SHAKE256, pqov and AES

- **SHAKE256 domains** U1 (46591 B), U2 (32 B) and U3 (98 B) have distinct fixed lengths, so they
  are pairwise disjoint. Each reads one fixed output length. U3's counter makes the up to 256
  attempts distinct. U2 and U3 contain the secret sk_seed. U1's input is public.
- **SHAKE256 against SHAKE128**: independent oracles by the multi-rate padding assumption (§1). Only
  D = U1(cpk) crosses into SHAKE128 inputs, as data.
- **AES.** There is one ideal cipher E. pqov's AES-128-CTR expansion of P1 and P2 is a set of
  additional queries E_{pk_seed}(0 ⊞ ctr) under a *public* key. These are about 17 171 queries per
  `PublicKey` construction (`uov.cpp:80`), and also at keygen. They need no separation from faest's
  roles:
  - L0's AES claims hold for every key, including adversarial ones;
  - an honest prover's GGM keys are uniform secrets, which equal a given pk_seed with probability
    ≤ 2⁻¹²⁸ per pair.

  They must, however, be **counted in q_E** wherever L1/L2's bounds are applied.

---

## 7. Lemma DS (citable form)

Model SHAKE128 and SHAKE256 as independent random oracles (multi-rate padding), AES-128 as one
ideal cipher E, and Keccak-p[800,12] as an ideal permutation π independent of both. Define the
oracles as the restrictions to the domains of §2 (each with its injective encoding and fixed output
length).

**(a) Unconditional (perfect, given the idealization).** The following **15 SHAKE128 oracles**
are mutually independent random oracles, and independent of SHAKE128 on every other input:
1. H₁ (the three shapes);
2. H₂⁰ (all five relations; the relation is part of the input via DST_R);
3. H₂⁴;
4. H₃;
5. H₄;
6. H₅;
7. H₂¹;
8. H₂²;
9. H₂³;
10. Comb (UOV combination; the protocol is part of the input via its DST);
11. A1 PomFRIT refresher_com;
12. A4 Moussaka issue seed XOF;
13. A5 Moussaka redeem seed XOF;
14. A6 Ratatouille issue seed XOF;
15. A7 Ratatouille spend seed XOF.

The **3 SHAKE256 oracles** U1 pk digest, U2 pqov keygen and U3 pqov vinegar are mutually
independent random oracles, and independent of the 15.

Per-relation refinement: H₂⁰, H₂¹, H₂² and H₃ restricted to a single relation are themselves
disjoint across relations (§3.5).

**(b) Up to ε_π.** The **3 Keccak-p[800,12] functions** K1 Moussaka Com, K2 Ratatouille Com and K3
Ratatouille Tag are independent random oracles, independent of everything in (a), except with
probability ε_π ≤ q_π·2⁻²²² + q_π²·2⁻⁴⁴⁰.

**(c) Up to n_seed·Q·2⁻²⁵⁶.** A3, the PomFRIT seed XOF, can be added to the list in (a), except
with probability n_seed·Q·2⁻²⁵⁶.
(Separately, the hop that the seed XOFs' outputs are uniform, given the adversary's own XOF
queries, is mechanized for the privacy games with the XOF an independent table: `lean/docs/zk.md`
§10.6. Part (c), the independence of A3 from the overlapping proof-system domains, stays on
paper.)

**(d) PomFRIT `hash_to_target`, as implemented: NOT covered by (a).** O_tgt is a random oracle, and
it is independent of the oracles in (a) at every string outside the overlap with
H₁ ∪ H₃ ∪ H₂¹ ∪ H₂² (§3.3). It may be used as an independent oracle only in the restricted way of
§3.4 (uniform programming, reading, freshness), at a cost of
ε_MC ≤ 2q₁₂₈q₂₅₆·2⁻²⁵⁶ + q_E(q₁₂₈ + q₂₅₆)·2⁻²⁵⁴ + n₃(n_T + q₁₂₈)·2⁻¹²⁸ per hop.

**With the fix of §8, (c) and (d) become unconditional.** All **23 random oracles** (17 SHAKE128 + 3
SHAKE256 + 3 Keccak-p[800,12] up to ε_π) are then independent of each other and of the ideal
cipher, which is a separate object. The AES roles inside one proof are separated by L0 §2.3. pqov's AES queries count
toward q_E.

---

## 8. Proposed fix (not implemented)

In `src/pomfrit/pomfrit.cpp`:
- in `hash_to_target`, add `hasher.update_byte(APP_TAG);` after `hasher.update(msg);` (line 108);
- in the seed XOF, add `xof.update_byte(APP_TAG);` after `xof.update(msg);` (line 156);
- define `APP_TAG = 0x20` in `src/dst.hpp`, with a comment that application hashes whose last field
  has variable length must end in `APP_TAG`, and that 0x00–0x0F and 0x30 are taken by the proof
  system.

Why this is enough:
- the final byte 0x20 differs from every proof-system tag and from the combination hash's 0x30, so
  both domains become disjoint from all proof-system domains by suffix (Lean: `fixed_pairwise`);
- the DST prefixes keep them apart from all application domains;
- within-domain parsing stays unique (msg = bytes [284, len−1) and [71, len−1)).

Cost:
- one byte per call;
- it changes the PomFRIT target derivation, a wire-format change that invalidates signatures made
  before the fix;
- it changes the seeded test vectors of `issue_request_with_seed`.

Alternative fixes:
- Hash msg to a fixed 32-byte digest first, giving a fixed A2 length of 316, which happens to be
  unused. This is fragile, because a later relation could take length 316.
- Tag every application hash uniformly. That is more invasive, and for the fixed-length ones it is
  unnecessary.

A **length prefix on msg alone does not fix this**: the final byte would still be msg's last byte.

---

## 9. Lean check

`lean/VoleMole/Protocols/DomainSeparation.lean` (check with
`cd lean && lake env lean VoleMole/Protocols/DomainSeparation.lean`):
- `Shape`, `sep` and `sep_sound`: the prefix/suffix/length criterion is sound;
- `clean_pairwise`: the 23 domains of §3.2 are pairwise separated;
- `target_sep` and `seed_sep`: A2 and A3 are separated from every domain except the listed
  exceptions;
- `target_seed_sep`: A2 and A3 are separated from each other;
- `target_meets_H1_leaves7/8`, `target_meets_H1_com`, `target_meets_H3`, `target_meets_H21` and
  `target_meets_H22`, plus `seed_meets_H20_pomfrit` and `seed_meets_H23`: explicit common strings,
  so the exceptions are real;
- `fixed_pairwise`: with `APP_TAG = 0x20` appended to A2 and A3, all 25 domains are pairwise
  separated.

The table entries (lengths, tags, DST bytes) are transcribed from §2 and were checked against the
trace of §2.4. Lean does not check that the C++ code computes these layouts.
