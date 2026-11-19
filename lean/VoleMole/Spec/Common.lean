import VoleMole.Arith.GF
import VoleMole.Arith.UOV
import VoleMole.Arith.Keccak.Ref
import VoleMole.Spec.SHAKE

/-!
# Shared helpers for the executable protocol specs (`VoleMole/Spec/*`)

* Byte strings are `List UInt8` (`Bytes`): the specs reason about concatenations and fixed-length
  fields, for which `List` lemmas (`List.append_inj`, `take`/`drop`) are the convenient tools.
* `shake128B` / `shake256B`: SHAKE on `Bytes`, with output length exactly `n` by construction
  (`length_shake128B`); the truncation is a no-op since `Spec.SHAKE.shake128` returns `n` bytes.
* `makeDst`: the 7-byte domain separation tags of `src/dst.hpp:22-30`.
* `UOVKey`: an expanded UOV public key as the specs see it: its digest (`PublicKeyAccess::digest`,
  SHAKE256-256 of the compressed key, `src/uov/uov.cpp:81-85`, treated as an opaque identifier)
  and its expanded map (`PublicKeyAccess::expanded`), evaluated concretely by
  `Arith.UOV.publicMap` (`UOVKey.eval`, i.e. `PublicKey::eval`, `uov.cpp:100-106`).
* `Signer`: UOV preimage derivation (`SecretKey::derive_preimage`, pqov `ov_derive_preimage`),
  kept abstract; `Signer.Correct` is the only property the specs use.
* `concat_inj` and friends: injectivity of concatenations of fixed-length fields (the
  "parses uniquely" facts behind every hash-input binding claim).
* A small parser for `key value` known-answer files (blank-line separated records).
-/

namespace VoleMole.Spec

open VoleMole.Arith

/-- Byte strings. -/
abbrev Bytes := List UInt8

/-- `b[off .. off + len)`. -/
def slice (b : Bytes) (off len : ℕ) : Bytes := (b.drop off).take len

/-- Byte-wise XOR (`t[i] = h[i] ^ r[i]`). -/
def xorBytes (a b : Bytes) : Bytes := List.zipWith (· ^^^ ·) a b

/-- SHAKE128 on byte lists, `n` bytes of output. -/
def shake128B (input : Bytes) (n : ℕ) : Bytes :=
  ((SHAKE.shake128 ⟨input.toArray⟩ n).toList ++ List.replicate n 0).take n

/-- SHAKE256 on byte lists, `n` bytes of output. -/
def shake256B (input : Bytes) (n : ℕ) : Bytes :=
  ((SHAKE.shake256 ⟨input.toArray⟩ n).toList ++ List.replicate n 0).take n

theorem length_shake128B (input : Bytes) (n : ℕ) : (shake128B input n).length = n := by
  simp [shake128B]

theorem length_shake256B (input : Bytes) (n : ℕ) : (shake256B input n).length = n := by
  simp [shake256B]

/-- `make_dst(protocol, version, purpose, index)` (`src/dst.hpp:22-30`). -/
def makeDst (protocol : String) (version : UInt8) (purpose index : Char) : Bytes :=
  (protocol.toList.take 4).map (fun c => c.toNat.toUInt8) ++
    [version, purpose.toNat.toUInt8, index.toNat.toUInt8]

/-- A 32-bit little-endian integer (e.g. `update_u32` in `src/moussaka/redeem.hpp:184-190`). -/
def u32le (v : ℕ) : Bytes :=
  [v.toUInt8, (v / 2 ^ 8).toUInt8, (v / 2 ^ 16).toUInt8, (v / 2 ^ 24).toUInt8]

/-! ## Byte-list lemmas -/

theorem length_slice_of_le {b : Bytes} {off len : ℕ} (h : off + len ≤ b.length) :
    (slice b off len).length = len := by
  simp [slice]; omega

/-- A slice inside the first part of a concatenation. -/
theorem slice_append_left {a b : Bytes} {off len : ℕ} (h : off + len ≤ a.length) :
    slice (a ++ b) off len = slice a off len := by
  unfold slice
  rw [List.drop_append_of_le_length (by omega)]
  exact List.take_append_of_le_length (by simp; omega)

/-- A slice that starts after the first part of a concatenation. -/
theorem slice_append_right {a b : Bytes} {off len : ℕ} (h : a.length ≤ off) :
    slice (a ++ b) off len = slice b (off - a.length) len := by
  unfold slice
  rw [List.drop_append, List.drop_eq_nil_of_le h, List.nil_append]

theorem slice_eq_self {a : Bytes} {len : ℕ} (h : a.length = len) : slice a 0 len = a := by
  simp [slice, ← h]

theorem take_append_eq {a b : Bytes} {n : ℕ} (h : a.length = n) : (a ++ b).take n = a := by
  subst h; simp

theorem drop_append_eq {a b : Bytes} {n : ℕ} (h : a.length = n) : (a ++ b).drop n = b := by
  subst h; simp

theorem length_xorBytes (a b : Bytes) : (xorBytes a b).length = min a.length b.length := by
  simp [xorBytes]

/-- XOR is an involution: `(h ⊕ r) ⊕ r = h` when `|h| ≤ |r|`. -/
theorem xorBytes_xorBytes_right {h r : Bytes} (hl : h.length ≤ r.length) :
    xorBytes (xorBytes h r) r = h := by
  induction h generalizing r with
  | nil => simp [xorBytes]
  | cons a h ih =>
    cases r with
    | nil => simp at hl
    | cons b r =>
      simp only [xorBytes, List.zipWith_cons_cons, List.cons.injEq] at ih ⊢
      exact ⟨by rw [UInt8.xor_assoc, UInt8.xor_self, UInt8.xor_zero],
        ih (by simp at hl; omega)⟩

/-- Concatenations of two fields, the first of a fixed length, determine both fields. -/
theorem concat_inj {a b a' b' : Bytes} (h : a ++ b = a' ++ b') (hl : a.length = a'.length) :
    a = a' ∧ b = b' :=
  List.append_inj h hl

/-- Concatenations of equally many fixed-length fields determine the fields. -/
theorem flatten_inj {n : ℕ} :
    ∀ {xs ys : List Bytes}, xs.length = ys.length → (∀ x ∈ xs, x.length = n) →
      (∀ y ∈ ys, y.length = n) → xs.flatten = ys.flatten → xs = ys
  | [], [], _, _, _, _ => rfl
  | x :: xs, y :: ys, hl, hx, hy, h => by
    simp only [List.flatten_cons] at h
    obtain ⟨h1, h2⟩ := List.append_inj h (by rw [hx x (by simp), hy y (by simp)])
    rw [h1, flatten_inj (by simpa using hl) (fun z hz => hx z (by simp [hz]))
      (fun z hz => hy z (by simp [hz])) h2]

theorem length_flatten_of_forall {n : ℕ} :
    ∀ {xs : List Bytes}, (∀ x ∈ xs, x.length = n) → xs.flatten.length = n * xs.length
  | [], _ => by simp
  | x :: xs, hx => by
    simp only [List.flatten_cons, List.length_append, List.length_cons]
    rw [hx x (by simp), length_flatten_of_forall (fun z hz => hx z (by simp [hz]))]
    ring

/-! ## UOV -/

/-- `uov::N`, `uov::M` (`include/vole_mole/uov.hpp:17-18`). -/
abbrev uovN : ℕ := 119
abbrev uovM : ℕ := 45

/-- `PUBLIC_KEY_DIGEST_BYTES` (`src/uov/public_key.hpp:24`). -/
abbrev digestBytes : ℕ := 32

/-- An expanded UOV public key: digest and expanded map (`ℕ → GF256`, zero beyond the end). -/
structure UOVKey where
  digest : Bytes
  map : ℕ → GF256

/-- `PublicKey::eval(s)`: `P(s)` as `M` bytes, the public map in the layout of
`for_each_monomial` (`Arith.UOV.publicMap`; Claim 2b of L7-uov.md identifies it with pqov's
`ov_publicmap`, and the known-answer checks confirm it on the KAT keys). -/
def UOVKey.eval (pk : UOVKey) (s : Bytes) : Bytes :=
  let a := s.toArray
  (List.finRange uovM).map fun k =>
    (UOV.publicMap uovN uovM pk.map (fun i => ⟨a.getD i 0⟩) k).val

theorem length_eval (pk : UOVKey) (s : Bytes) : (pk.eval s).length = uovM := by
  simp [UOVKey.eval]

/-- An expanded key from its byte array (`PublicKeyAccess::expanded`). -/
def UOVKey.ofExpanded (digest : Bytes) (b : ByteArray) : UOVKey :=
  ⟨digest, fun i => if h : i < b.size then ⟨b[i]⟩ else 0⟩

/-- `SecretKey::derive_preimage`, abstract. `none` models the `std::runtime_error` thrown when
pqov's 256 vinegar retries all fail. -/
structure Signer where
  derivePreimage : Bytes → Option Bytes

/-- The signer is correct for `pk`: any preimage it returns for an `M`-byte target is an `N`-byte
preimage under `pk`. -/
def Signer.Correct (sk : Signer) (pk : UOVKey) : Prop :=
  ∀ t s, t.length = uovM → sk.derivePreimage t = some s → s.length = uovN ∧ pk.eval s = t

/-! ## Keccak-p[800] on byte lists -/

/-- A 100-byte Keccak-p[800] state from a byte list (zero-padded / truncated). -/
def stateOfBytes (b : Bytes) : Keccak.State := Vector.ofFn fun k => b.getD k.1 0

/-! ## Known-answer files: `key value` lines, records separated by blank lines -/

/-- One record: its `key value` pairs in file order (keys may repeat). -/
abbrev KatRecord := Array (String × String)

/-- Parse a known-answer file; `#` lines are comments. -/
def parseKat (contents : String) : Array KatRecord := Id.run do
  let mut out : Array KatRecord := #[]
  let mut cur : KatRecord := #[]
  for line in contents.splitOn "\n" do
    if line.startsWith "#" then continue
    if line.trimAscii.isEmpty then
      if !cur.isEmpty then out := out.push cur
      cur := #[]
      continue
    match line.splitOn " " with
    | k :: rest => cur := cur.push (k, " ".intercalate rest)
    | [] => pure ()
  if !cur.isEmpty then out := out.push cur
  return out

namespace KatRecord

def get? (r : KatRecord) (k : String) : Option String := (r.find? (·.1 == k)).map (·.2)

def getAll (r : KatRecord) (k : String) : List String :=
  (r.filter (·.1 == k)).toList.map (·.2)

def bytes (r : KatRecord) (k : String) : Except String Bytes := do
  let some v := r.get? k | throw s!"missing field `{k}`"
  let some b := Hex.decode? v | throw s!"field `{k}`: bad hex"
  pure b

def nat (r : KatRecord) (k : String) : Except String ℕ := do
  let some v := r.get? k | throw s!"missing field `{k}`"
  let some n := v.toNat? | throw s!"field `{k}`: not a number"
  pure n

end KatRecord

/-- Accumulate a named check: `ok` if `a = b`, else an error with both values in hex. -/
def checkEq (what : String) (got want : Bytes) : List String :=
  if got = want then [] else
    [s!"{what}: got {Hex.bytesToHex got}, want {Hex.bytesToHex want}"]

end VoleMole.Spec
