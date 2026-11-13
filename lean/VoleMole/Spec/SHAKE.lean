/-!
# SHAKE128 and SHAKE256 (FIPS 202), executable

A direct, computable transcription of Keccak-f[1600] and the SHAKE sponge, as used by the C++
through XKCP (`Keccak_HashInitialize_SHAKE128/256`, `Keccak_HashUpdate`, `Keccak_HashFinal`,
`Keccak_HashSqueeze`; e.g. `faest::hash_state`, `subprojects/faest-arch-opt/hash.hpp:25-31`).

* `keccakF1600`: the permutation on 25 lanes `a[x + 5y] : UInt64` (FIPS 202 §3.2, 24 rounds).
* `sponge rate dsByte input outLen`: pad10*1 with the domain byte (`0x1F` for SHAKE), absorb,
  squeeze `outLen` bytes. Squeezing in several calls (`Keccak_HashSqueeze` repeatedly) yields
  consecutive slices of one output stream, so `shake128 input n` with `n` the total length covers
  every multi-call squeeze.
* `shake128`, `shake256`, checked against the FIPS 202 known answers for the empty string and for
  a 200-byte `0xa3` message (`#guard`, evaluated by the interpreter at elaboration time).
-/

namespace VoleMole.Spec.SHAKE

/-- The 24 Keccak-f[1600] round constants (FIPS 202 §3.2.5). -/
def roundConstants : Array UInt64 := #[
  0x0000000000000001, 0x0000000000008082, 0x800000000000808A, 0x8000000080008000,
  0x000000000000808B, 0x0000000080000001, 0x8000000080008081, 0x8000000000008009,
  0x000000000000008A, 0x0000000000000088, 0x0000000080008009, 0x000000008000000A,
  0x000000008000808B, 0x800000000000008B, 0x8000000000008089, 0x8000000000008003,
  0x8000000000008002, 0x8000000000000080, 0x000000000000800A, 0x800000008000000A,
  0x8000000080008081, 0x8000000000008080, 0x0000000080000001, 0x8000000080008008]

/-- Rotation offsets `r[x + 5y]` (FIPS 202 §3.2.2). -/
def rotations : Array UInt64 := #[
  0, 1, 62, 28, 27,
  36, 44, 6, 55, 20,
  3, 10, 43, 25, 39,
  41, 45, 15, 21, 8,
  18, 2, 61, 56, 14]

/-- Rotate a lane left by `n < 64`. -/
def rotl (v n : UInt64) : UInt64 := if n = 0 then v else (v <<< n) ||| (v >>> (64 - n))

/-- One round of Keccak-f[1600]: θ, ρ, π, χ, ι. -/
def round (a : Array UInt64) (rc : UInt64) : Array UInt64 := Id.run do
  let get (i : Nat) : UInt64 := a.getD i 0
  -- θ
  let c : Array UInt64 := (Array.range 5).map fun x =>
    get x ^^^ get (x + 5) ^^^ get (x + 10) ^^^ get (x + 15) ^^^ get (x + 20)
  let d : Array UInt64 := (Array.range 5).map fun x =>
    c.getD ((x + 4) % 5) 0 ^^^ rotl (c.getD ((x + 1) % 5) 0) 1
  let a1 : Array UInt64 := (Array.range 25).map fun i => get i ^^^ d.getD (i % 5) 0
  -- ρ and π: B[y, 2x + 3y] = rot(A[x, y], r[x, y])
  let mut b : Array UInt64 := Array.replicate 25 0
  for x in [0:5] do
    for y in [0:5] do
      b := b.set! (y + 5 * ((2 * x + 3 * y) % 5))
        (rotl (a1.getD (x + 5 * y) 0) (rotations.getD (x + 5 * y) 0))
  -- χ
  let a2 : Array UInt64 := (Array.range 25).map fun i =>
    let x := i % 5
    let y := i / 5
    b.getD i 0 ^^^ (~~~(b.getD ((x + 1) % 5 + 5 * y) 0) &&& b.getD ((x + 2) % 5 + 5 * y) 0)
  -- ι
  return a2.set! 0 (a2.getD 0 0 ^^^ rc)

/-- Keccak-f[1600]. -/
def keccakF1600 (a : Array UInt64) : Array UInt64 := roundConstants.foldl round a

/-- XOR a block of `rate` bytes (little-endian lanes) into the state. -/
def xorBlock (a : Array UInt64) (block : ByteArray) : Array UInt64 := Id.run do
  let mut a := a
  for i in [0:block.size] do
    let lane := i / 8
    a := a.set! lane (a.getD lane 0 ^^^ ((block.get! i).toUInt64 <<< (8 * (i % 8)).toUInt64))
  return a

/-- The first `n` bytes of the state, lanes little-endian. -/
def stateBytes (a : Array UInt64) (n : Nat) : ByteArray := Id.run do
  let mut out := ByteArray.empty
  for i in [0:n] do
    out := out.push ((a.getD (i / 8) 0 >>> (8 * (i % 8)).toUInt64).toUInt8)
  return out

/-- Pad `input` with the domain byte and pad10*1 to a multiple of `rate`. -/
def pad (rate : Nat) (dsByte : UInt8) (input : ByteArray) : ByteArray := Id.run do
  let q := rate - input.size % rate
  let mut out := input
  for i in [0:q] do
    let b : UInt8 := (if i = 0 then dsByte else 0) ||| (if i + 1 = q then 0x80 else 0)
    out := out.push b
  return out

/-- The sponge: absorb `input` (with domain byte `dsByte`), squeeze `outLen` bytes. -/
def sponge (rate : Nat) (dsByte : UInt8) (input : ByteArray) (outLen : Nat) : ByteArray := Id.run do
  let padded := pad rate dsByte input
  let mut a : Array UInt64 := Array.replicate 25 0
  for k in [0:padded.size / rate] do
    a := keccakF1600 (xorBlock a (padded.extract (k * rate) (k * rate + rate)))
  let mut out := ByteArray.empty
  for _ in [0:outLen / rate + 1] do
    out := out ++ stateBytes a rate
    a := keccakF1600 a
  return out.extract 0 outLen

/-- SHAKE128 (rate 168 bytes). -/
def shake128 (input : ByteArray) (outLen : Nat) : ByteArray := sponge 168 0x1F input outLen

/-- SHAKE256 (rate 136 bytes). -/
def shake256 (input : ByteArray) (outLen : Nat) : ByteArray := sponge 136 0x1F input outLen

/-- Lowercase hex of a byte array. -/
def hex (b : ByteArray) : String :=
  String.join (b.toList.map fun x =>
    let h := Nat.toDigits 16 x.toNat
    String.ofList (if h.length = 1 then '0' :: h else h))

/-! ## Known answers (FIPS 202 / NIST CSRC examples) -/

#guard hex (shake128 .empty 32) =
  "7f9c2ba4e88f827d616045507605853ed73b8093f6efbc88eb1a6eacfa66ef26"

#guard hex (shake256 .empty 64) =
  "46b9dd2b0ba88d13233b3feb743eeb243fcd52ea62b81b82b50c27646ed5762f" ++
  "d75dc4ddd8c0f200cb05019d67b592f6fc821c49479ab48640292eacb3b7c4be"

-- 1600-bit message of 0xa3 bytes; first 32 bytes of the output (NIST example values).
#guard hex (shake128 (ByteArray.mk (Array.replicate 200 0xa3)) 32) =
  "131ab8d2b594946b9c81333f9bb6e0ce75c3b93104fa3469d3917457385da037"

#guard hex (shake256 (ByteArray.mk (Array.replicate 200 0xa3)) 32) =
  "cd8a920ed141aa0407a22d59288652e9d9f1a7ee0c1e7c1ca699424da84a904d"

-- Squeezing past one block (SHAKE128, 200 bytes of output from the empty input): the last 32
-- bytes, cross-checked with Python's hashlib.
#guard hex ((shake128 .empty 200).extract 168 200) =
  "767be1fda69419dfb927e9df07348b196691abaeb580b32def58538b8d23f877"

end VoleMole.Spec.SHAKE
