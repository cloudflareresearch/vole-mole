import VoleMole.Arith.Ratatouille
import VoleMole.Arith.GFEmbedding
import VoleMole.Protocols.Ratatouille
import VoleMole.Spec.SHAKE

/-!
# An executable protocol-level model of Ratatouille (`src/ratatouille/*`)

This file models the protocol logic of `include/vole_mole/ratatouille.hpp` and
`src/ratatouille/ratatouille.cpp` byte for byte: the message formats, issuance, spending, refunds
and change tokens, the client's checks and its 64-bit credit arithmetic on `UInt64`, the move-only
client objects (`Token`, `PendingToken`, `PendingSpend`), and the Issuer's nullifier store as the
header prescribes it to the caller (`ratatouille.hpp:174-182`). `lake exe spec_kats`
(`Spec/RatatouilleKats.lean`) checks it against `tests/ratatouille/ratatouille_kat.txt`.

## What is concrete and what is abstract

* Concrete: `Com` and `Tag` (`Arith.Ratatouille.commit`, `comState`, `tagState` on the reference
  `keccakP800`, reused unchanged), the credit encoding, the seed expansion by SHAKE128
  (`Spec/SHAKE.lean`), the request/response framing, every validation and abort condition, and UOV
  verification `P(s) = Tag` (`uovEval`, the public map `Arith.UOV.publicMap` over the expanded key
  `ℕ → GF256`, as `PublicKey::eval` computes it).
* Abstract (`Prim`): VOLEitH proving and verification for the two relations, and UOV
  `derive_preimage`, with the C++ exceptions they can throw (`prove` grinding abort,
  `derive_preimage` failure) modelled as `none`. `Prim.Correct` states completeness of the
  proofs and correctness of the signer; the security assumptions (soundness, unforgeability,
  binding) appear only as explicit hypotheses of the balance theorem.

Exceptions are `Except Error`, and a consumed (moved-from) object is `none`: each client method
returns the object's state after the call alongside its result, so "consumed on failure" is a
statement about the model.

## Main results

* Framing: `parse_toBytes`, `respRefund_mk`, `respSig_mk`, `issueReqC_mk`, `issueReqProof_mk`,
  `decode_encode` (parsing inverts serialization).
* Arithmetic: `clientCheck_isSome` (the client's overflow-aware test, on `UInt64`, accepts iff
  `d ≤ t + x ∧ t + x − d < 2⁶⁴`), `clientCheck_eq` (then `t' = t + x − d` exactly), and
  `clientCheck_isSome_iff_clientAccepts` (agreement with `Protocols.Ratatouille.change_correct`).
* Correctness (N4): `issue_zero_rejected`, `issue_correct`, `spendRequest_invalid` and
  `spendRequest_notValid` (rejected, token kept), `spendRequest_valid`, `spend_correct` (the change
  token holds `t + x − d` and refund `x'` and is valid again), `honestSpend_valid`, and
  `honest_spends_balance`: over any sequence of honest spends, `t_n + x_n + Σ d = t_0 + x_0 + Σ x'`.
* Issuer: `issuerSpend_nodup`, `issuer_accepts_once` (a nullifier is accepted at most once per
  context); `ledger_balance` and `issuer_balance` (over an arbitrary sequence of adversarial
  requests, per context, `Σ d ≤ Σ T_init + Σ x'`, assuming each accepted spend has a valid
  witness and spends a state signed earlier with the same opening: soundness, unforgeability and
  binding, as hypotheses).
* Findings of `lean/docs/security/ratatouille.md` §7 that are deterministic: F2
  (`copied_request_first_wins`), F3 (`finalizeIssue_consumes`, `finalizeSpend_consumes`), F4
  (`finalizeSpend_any_refund`, `spendRequest_forced_minimum`), F5
  (`spendResponse_signs_duplicates`; `leak_breaks_balance`: one leaked duplicate-path response
  breaks the ledger balance).
-/

set_option linter.unusedSectionVars false

namespace VoleMole.Spec.Ratatouille

open VoleMole.Arith VoleMole.Arith.Keccak

/-! ## Byte strings and parameters (`ratatouille.hpp:17-34`, `commit.hpp:21-23`, `uov.hpp:17-18`) -/

/-- A fixed-length byte string. -/
abbrev Bytes (n : ℕ) := Vector UInt8 n

/-- A byte string as `ℕ → UInt8` (zero beyond the end), the form `Arith.Ratatouille` uses. -/
def Bytes.fn {n : ℕ} (v : Bytes n) : ℕ → UInt8 := fun i => if h : i < n then v[i] else 0

abbrev Nullifier := Bytes 24
abbrev Context := Bytes 16
abbrev Opening := Bytes 16
abbrev Commitment := Bytes 32
abbrev Target := Bytes 45
abbrev Preimage := Bytes 119
abbrev Seed := Bytes 32
/-- `ProveSeed<Relation>`: `secpar_bytes = 16` (`voleith.hpp:73-75`). -/
abbrev Rho := Bytes 16
abbrev IssueProof := Bytes 7000
abbrev SpendProof := Bytes 17319
/-- `IssueRequest = c ‖ π_iss`. -/
abbrev IssueRequest := Bytes 7032
/-- `SpendRequest = nf ‖ ⟨d⟩₈ ‖ c' ‖ π_spend`. -/
abbrev SpendRequest := Bytes 17383
/-- `SpendResponse = ⟨x'⟩₈ ‖ s'`. -/
abbrev SpendResponse := Bytes 127

/-- `Credits = uint64_t`. -/
abbrev Credits := UInt64

/-- `2⁶⁴`. -/
local notation "W" => (18446744073709551616 : ℕ)

/-- Slice `[off, off + m)` of a byte string. -/
def slice {n : ℕ} (b : Bytes n) (off m : ℕ) (h : off + m ≤ n) : Bytes m :=
  Vector.ofFn fun i => b[off + i.1]

/-! ## Credits (`commit.hpp:33-50`) -/

/-- `encode_credits(v)`: little-endian, 8 bytes (`Arith.Ratatouille.encodeCredits`). -/
def encodeCredits (v : Credits) : Bytes 8 :=
  Vector.ofFn fun i => VoleMole.Arith.Ratatouille.encodeCredits v.toNat i.1

/-- Little-endian bytes to a natural number. -/
def leDecode : List UInt8 → ℕ
  | [] => 0
  | b :: bs => b.toNat + 256 * leDecode bs

/-- `decode_credits(bytes)`. -/
def decodeCredits (b : Bytes 8) : Credits := UInt64.ofNat (leDecode b.toList)

theorem leDecode_ofFn (n : ℕ) : ∀ k : ℕ,
    leDecode (List.ofFn fun i : Fin k => UInt8.ofNat (n >>> (8 * i.1))) = n % 256 ^ k
  | 0 => by simp [leDecode, Nat.mod_one]
  | k + 1 => by
    rw [List.ofFn_succ, leDecode]
    have h : (fun i : Fin k => UInt8.ofNat (n >>> (8 * (i.succ : Fin (k + 1)).1))) =
        fun i : Fin k => UInt8.ofNat ((n / 256) >>> (8 * i.1)) := by
      funext i
      simp only [Fin.val_succ, Nat.shiftRight_eq_div_pow, Nat.div_div_eq_div_mul]
      congr 2
      rw [Nat.mul_add, pow_add]; norm_num; ring
    rw [h, leDecode_ofFn (n / 256) k, pow_succ', Nat.mod_mul]
    simp

theorem decode_encode (v : Credits) : decodeCredits (encodeCredits v) = v := by
  apply UInt64.toNat_inj.mp
  have hv := v.toNat_lt
  simp only [decodeCredits, encodeCredits, Vector.toList_ofFn, VoleMole.Arith.Ratatouille.encodeCredits]
  rw [leDecode_ofFn, Nat.mod_eq_of_lt (by norm_num; omega)]
  simp

/-! ## `Com`, `Tag` and UOV verification -/

/-- `Com(nf, ctx, t, r)` (`ratatouille.cpp:94-100`): `Arith.Ratatouille.commit` on 32 bytes. -/
def com (nf : Nullifier) (ctx : Context) (t : Credits) (r : Opening) : Commitment :=
  Vector.ofFn fun k => VoleMole.Arith.Ratatouille.commit nf.fn ctx.fn t.toNat r.fn k.1

/-- `Tag(c, x)` (`ratatouille.cpp:102-107`): the first 45 bytes of
`keccak_p800(encode_tag_state(c, x))`. -/
def tag (c : Commitment) (x : Credits) : Target :=
  Vector.ofFn fun k => VoleMole.Arith.Ratatouille.stateByte (keccakP800 (VoleMole.Arith.Ratatouille.tagState c.fn x.toNat)) k.1

/-- An expanded UOV public key (pqov's layout, `uov::detail::for_each_monomial`). -/
abbrev PublicKey := ℕ → GF256

/-- `PublicKey::eval(s)`: `P(s)` as bytes, with the public map `Arith.UOV.publicMap`. -/
def uovEval (pk : PublicKey) (s : Preimage) : Target :=
  Vector.ofFn fun k => (UOV.publicMap 119 45 pk (fun i => ⟨s.fn i⟩) k).val

/-! ## Seed expansion (`ratatouille.cpp:63-84`) -/

/-- `RATATOUILLE_ISSUE_SEED_DST = make_dst("rata", 0, 's', '0')` (`dst.hpp:50`). -/
def issueSeedDst : List UInt8 := [0x72, 0x61, 0x74, 0x61, 0, 0x73, 0x30]
/-- `RATATOUILLE_SPEND_SEED_DST = make_dst("rata", 0, 's', '1')` (`dst.hpp:53`). -/
def spendSeedDst : List UInt8 := [0x72, 0x61, 0x74, 0x61, 0, 0x73, 0x31]

/-- `expand_seed(dst, seed)`: SHAKE128 over `dst ‖ seed`, squeezing `nf` (24 bytes), `r` (16) and
`ρ` (16) in this order. -/
def expandSeed (dst : List UInt8) (seed : Seed) : Nullifier × Opening × Rho :=
  let out := SHAKE.shake128 (ByteArray.mk (dst.toArray ++ seed.toArray)) 56
  (Vector.ofFn fun i => out.get! i.1, Vector.ofFn fun i => out.get! (24 + i.1),
    Vector.ofFn fun i => out.get! (40 + i.1))

/-! ## Messages (`ratatouille.hpp:36-52`, `ratatouille.cpp:48-57`) -/

/-- `c ‖ π_iss` (`ratatouille.cpp:165-168`). -/
def issueReqBytes (cm : Commitment) (pf : IssueProof) : IssueRequest :=
  Vector.ofFn fun k => if h : k.1 < 32 then cm[k.1] else pf[k.1 - 32]

/-- The commitment and proof of an issue request (`ratatouille.cpp:173-178`). -/
def issueReqC (q : IssueRequest) : Commitment := slice q 0 32 (by norm_num)
def issueReqProof (q : IssueRequest) : IssueProof := slice q 32 7000 (by norm_num)

/-- The fields of a spend request. -/
structure SpendReq where
  nf : Nullifier
  d : Credits
  cNext : Commitment
  proof : SpendProof

/-- `nf ‖ ⟨d⟩₈ ‖ c' ‖ π` (`REQ_OFF_*`, `ratatouille.cpp:48-53`, `:243-246`). -/
def SpendReq.toBytes (q : SpendReq) : SpendRequest :=
  Vector.ofFn fun k =>
    if h : k.1 < 24 then q.nf[k.1]
    else if h' : k.1 < 32 then (encodeCredits q.d)[k.1 - 24]
    else if h'' : k.1 < 64 then q.cNext[k.1 - 32]
    else q.proof[k.1 - 64]

/-- Parsing in `spend_response` (`ratatouille.cpp:268-273`). -/
def SpendReq.parse (b : SpendRequest) : SpendReq where
  nf := slice b 0 24 (by norm_num)
  d := decodeCredits (slice b 24 8 (by norm_num))
  cNext := slice b 32 32 (by norm_num)
  proof := slice b 64 17319 (by norm_num)

/-- `⟨x'⟩₈ ‖ s'` (`RESP_OFF_*`, `ratatouille.cpp:55-57`, `:281-282`). -/
def spendResponseBytes (x : Credits) (s : Preimage) : SpendResponse :=
  Vector.ofFn fun k => if h : k.1 < 8 then (encodeCredits x)[k.1] else s[k.1 - 8]

/-- Parsing in `finalize_spend` (`ratatouille.cpp:293-296`). -/
def respRefund (b : SpendResponse) : Credits := decodeCredits (slice b 0 8 (by norm_num))
def respSig (b : SpendResponse) : Preimage := slice b 8 119 (by norm_num)

theorem issueReqC_mk (cm : Commitment) (pf : IssueProof) : issueReqC (issueReqBytes cm pf) = cm := by
  ext i hi
  simp [issueReqC, issueReqBytes, slice]

theorem issueReqProof_mk (cm : Commitment) (pf : IssueProof) :
    issueReqProof (issueReqBytes cm pf) = pf := by
  ext i hi
  simp [issueReqProof, issueReqBytes, slice]

theorem slice_encode_d (q : SpendReq) :
    slice q.toBytes 24 8 (by norm_num) = encodeCredits q.d := by
  ext i hi
  simp [slice, SpendReq.toBytes, show 24 + i < 32 by omega]

theorem parse_toBytes (q : SpendReq) : SpendReq.parse q.toBytes = q := by
  obtain ⟨nf, d, cm, pf⟩ := q
  simp only [SpendReq.parse, slice_encode_d, decode_encode, SpendReq.mk.injEq, true_and]
  refine ⟨?_, ?_, ?_⟩ <;> ext i hi
  · simp [slice, SpendReq.toBytes]
  · simp [slice, SpendReq.toBytes, show ¬ 32 + i < 24 by omega, show 32 + i < 64 by omega]
  · simp [slice, SpendReq.toBytes, show ¬ 64 + i < 24 by omega, show ¬ 64 + i < 32 by omega]

theorem respRefund_mk (x : Credits) (s : Preimage) : respRefund (spendResponseBytes x s) = x := by
  have : slice (spendResponseBytes x s) 0 8 (by norm_num) = encodeCredits x := by
    ext i hi
    simp [slice, spendResponseBytes]
  rw [respRefund, this, decode_encode]

theorem respSig_mk (x : Credits) (s : Preimage) : respSig (spendResponseBytes x s) = s := by
  ext i hi
  simp [respSig, slice, spendResponseBytes]

-- The protocol theorems below treat these as opaque (they are large `Vector.ofFn`s or call
-- Keccak); the lemmas above are their interface.
attribute [irreducible] com tag uovEval expandSeed issueReqBytes issueReqC issueReqProof
  SpendReq.toBytes SpendReq.parse spendResponseBytes respRefund respSig

/-! ## The client's 64-bit credit arithmetic (`ratatouille.cpp:226-236`) -/

/-- `spend_request_with_seed`'s test on `uint64_t`: `lo = t + x` (wrapping), `overflow = lo < t`;
reject if `!overflow && d > lo` or `overflow && d <= lo`; else `t' = lo - d` (wrapping). Returns
`some t'` iff the client accepts. -/
def clientCheck (t x d : Credits) : Option Credits :=
  let lo := t + x
  let overflow := decide (lo < t)
  if !overflow && decide (d > lo) then none
  else if overflow && decide (d ≤ lo) then none
  else some (lo - d)

/-- The test accepts exactly when the true change `t + x − d` is a credit value. -/
theorem clientCheck_isSome (t x d : Credits) :
    (clientCheck t x d).isSome ↔ d.toNat ≤ t.toNat + x.toNat ∧ t.toNat + x.toNat - d.toNat < W := by
  have ht := t.toNat_lt; have hx := x.toNat_lt; have hd := d.toNat_lt
  simp only [clientCheck, UInt64.lt_iff_toNat_lt, UInt64.le_iff_toNat_le, UInt64.toNat_add]
  split_ifs with h1 h2 <;> simp_all <;> omega

/-- When it accepts, `t' = t + x − d` exactly (no wrap). -/
theorem clientCheck_eq {t x d t' : Credits} (h : clientCheck t x d = some t') :
    t'.toNat + d.toNat = t.toNat + x.toNat := by
  have ht := t.toNat_lt; have hx := x.toNat_lt; have hd := d.toNat_lt
  simp only [clientCheck, UInt64.lt_iff_toNat_lt, UInt64.le_iff_toNat_le, UInt64.toNat_add] at h
  split_ifs at h with h1 h2
  cases h
  rw [UInt64.toNat_sub, UInt64.toNat_add]
  simp_all
  omega

/-- Agreement with the arithmetic model of `Protocols/Ratatouille.lean` (`clientAccepts`,
`change_correct`), which the security note cites. -/
theorem clientCheck_isSome_iff_clientAccepts (t x d : Credits) :
    (clientCheck t x d).isSome ↔
      VoleMole.Ratatouille.clientAccepts t.toNat x.toNat d.toNat := by
  have ht := t.toNat_lt; have hx := x.toNat_lt; have hd := d.toNat_lt
  rw [(VoleMole.Ratatouille.change_correct _ _ _ ht hx hd).1, clientCheck_isSome]

/-! ## Relations and the abstract primitives -/

/-- The issuance instance `(c, T_init, ctx)` and witness `(nf, r)` (`issue.hpp:1-5`). -/
structure IssueInstance where
  c : Commitment
  tInit : Credits
  ctx : Context

structure IssueWitness where
  nf : Nullifier
  r : Opening

/-- The spend instance `(P, nf, d, c', ctx)` and witness `(t, r, x, s, nf', t', r')`
(`spend.hpp:1-10`). -/
structure SpendInstance where
  pk : PublicKey
  nf : Nullifier
  d : Credits
  cNext : Commitment
  ctx : Context

structure SpendWitness where
  t : Credits
  r : Opening
  x : Credits
  s : Preimage
  nf' : Nullifier
  t' : Credits
  r' : Opening

/-- `R_iss`: `c = Com(nf, ctx, T_init, r)`. -/
def IssueRel (u : IssueInstance) (w : IssueWitness) : Prop := u.c = com w.nf u.ctx u.tInit w.r

/-- `R_spend`: V1 `P(s) = Tag(Com(nf, ctx, t, r), x)`, V2 `c' = Com(nf', ctx, t', r')`, V3
`t + x = t' + d` over ℕ; V4 holds by the types (`UInt64`). -/
def SpendRel (u : SpendInstance) (w : SpendWitness) : Prop :=
  uovEval u.pk w.s = tag (com u.nf u.ctx w.t w.r) w.x ∧ u.cNext = com w.nf' u.ctx w.t' w.r' ∧
    w.t.toNat + w.x.toNat = w.t'.toNat + u.d.toNat

/-- The abstract primitives, for a secret-key type `SK`: the expanded public key of a secret key,
`SecretKey::derive_preimage` (`none`: it throws), and VOLEitH proving (`none`: grinding abort,
it throws) and verification for both relations (`voleith_prove` / `voleith_verify`). -/
structure Prim (SK : Type) where
  pk : SK → PublicKey
  derive : SK → Target → Option Preimage
  proveIssue : IssueInstance → IssueWitness → Rho → Option IssueProof
  verifyIssue : IssueInstance → IssueProof → Bool
  proveSpend : SpendInstance → SpendWitness → Rho → Option SpendProof
  verifySpend : SpendInstance → SpendProof → Bool

variable {SK : Type}

/-- Correct primitives: `derive_preimage` returns preimages, and the proofs are complete. -/
structure Prim.Correct (P : Prim SK) : Prop where
  derive_correct : ∀ sk y s, P.derive sk y = some s → uovEval (P.pk sk) s = y
  issue_complete : ∀ u w ρ π, IssueRel u w → P.proveIssue u w ρ = some π → P.verifyIssue u π = true
  spend_complete : ∀ u w ρ π, SpendRel u w → P.proveSpend u w ρ = some π → P.verifySpend u π = true

/-! ## The protocol (`ratatouille.cpp:86-303`)

The C++ objects are move-only and every method consumes its object; a moved-from object is
`none`, and each method returns the object's state after the call together with its result. -/

/-- The exceptions of the API: `std::logic_error` (moved-from object), `std::invalid_argument`,
`std::runtime_error` (prover or `derive_preimage` failure). -/
inductive Error
  | logic
  | invalidArgument
  | runtime
  deriving DecidableEq, Repr

/-- `Token::Impl`: `(nf, t, r, x, s)`. -/
structure TokenS where
  nf : Nullifier
  t : Credits
  r : Opening
  x : Credits
  s : Preimage

/-- `PendingToken::Impl`: `(nf, r, T_init, c)`. -/
structure PendingTokenS where
  nf : Nullifier
  r : Opening
  tInit : Credits
  c : Commitment

/-- `PendingSpend::Impl`: the updated state `(nf', t', r', c')`. -/
structure PendingSpendS where
  nf : Nullifier
  t : Credits
  r : Opening
  c : Commitment

/-- A token is valid for `pk` and `ctx`: `P(s) = Tag(Com(nf, ctx, t, r), x)` (the check at
`ratatouille.cpp:221-225`). -/
def TokenS.Valid (pk : PublicKey) (ctx : Context) (τ : TokenS) : Prop :=
  uovEval pk τ.s = tag (com τ.nf ctx τ.t τ.r) τ.x

instance (pk : PublicKey) (ctx : Context) (τ : TokenS) : Decidable (τ.Valid pk ctx) :=
  inferInstanceAs (Decidable (_ = _))

/-- `issue_request_with_seed` (`ratatouille.cpp:158-169`). -/
def issueRequestWithSeed (P : Prim SK) (tInit : Credits) (ctx : Context) (seed : Seed) :
    Except Error (PendingTokenS × IssueRequest) :=
  if tInit = 0 then .error .invalidArgument else
  let e := expandSeed issueSeedDst seed
  match P.proveIssue ⟨com e.1 ctx tInit e.2.1, tInit, ctx⟩ ⟨e.1, e.2.1⟩ e.2.2 with
  | none => .error .runtime
  | some pf => .ok (⟨e.1, e.2.1, tInit, com e.1 ctx tInit e.2.1⟩, issueReqBytes (com e.1 ctx tInit e.2.1) pf)

/-- `issue_response` (`ratatouille.cpp:176-187`). -/
def issueResponse (P : Prim SK) (sk : SK) (req : IssueRequest) (tInit : Credits) (ctx : Context) :
    Except Error (Option Preimage) :=
  if tInit = 0 then .error .invalidArgument else
  let c := issueReqC req
  if !P.verifyIssue ⟨c, tInit, ctx⟩ (issueReqProof req) then .ok none else
  match P.derive sk (tag c 0) with
  | none => .error .runtime
  | some s => .ok (some s)

/-- `PendingToken::finalize_issue` (`ratatouille.cpp:189-201`): the pending token is moved out
before the response is checked. -/
def finalizeIssue (pk : PublicKey) (p : Option PendingTokenS) (resp : Preimage) :
    Option PendingTokenS × Except Error (Option TokenS) :=
  match p with
  | none => (none, .error .logic)
  | some p =>
    (none, .ok (if uovEval pk resp = tag p.c 0 then some ⟨p.nf, p.tInit, p.r, 0, resp⟩ else none))

/-- `spend_request_with_seed` (`ratatouille.cpp:213-250`): the token is consumed only once the
arguments are valid; a prover abort then throws with the token consumed. -/
def spendRequestWithSeed (P : Prim SK) (pk : PublicKey) (tok : Option TokenS) (d : Credits)
    (ctx : Context) (seed : Seed) : Option TokenS × Except Error (PendingSpendS × SpendRequest) :=
  match tok with
  | none => (none, .error .logic)
  | some τ =>
    if ¬ τ.Valid pk ctx then (some τ, .error .invalidArgument) else
    match clientCheck τ.t τ.x d with
    | none => (some τ, .error .invalidArgument)
    | some t' =>
      let e := expandSeed spendSeedDst seed
      match P.proveSpend ⟨pk, τ.nf, d, com e.1 ctx t' e.2.1, ctx⟩
          ⟨τ.t, τ.r, τ.x, τ.s, e.1, t', e.2.1⟩ e.2.2 with
      | none => (none, .error .runtime)
      | some pf => (none, .ok (⟨e.1, t', e.2.1, com e.1 ctx t' e.2.1⟩,
          SpendReq.toBytes ⟨τ.nf, d, com e.1 ctx t' e.2.1, pf⟩))

/-- `SpendResponseResult`. -/
structure SpendResult where
  response : SpendResponse
  nf : Nullifier
  d : Credits

/-- `spend_response` (`ratatouille.cpp:262-284`): parse, verify with the expanded public key of
`sk`, sign `Tag(c', x')`. There is no nullifier check: that is the caller's job. -/
def spendResponse (P : Prim SK) (sk : SK) (req : SpendRequest) (ctx : Context) (refund : Credits) :
    Except Error (Option SpendResult) :=
  let q := SpendReq.parse req
  if !P.verifySpend ⟨P.pk sk, q.nf, q.d, q.cNext, ctx⟩ q.proof then .ok none else
  match P.derive sk (tag q.cNext refund) with
  | none => .error .runtime
  | some s => .ok (some ⟨spendResponseBytes refund s, q.nf, q.d⟩)

/-- `PendingSpend::finalize_spend` (`ratatouille.cpp:286-303`): moved out before checking. -/
def finalizeSpend (pk : PublicKey) (p : Option PendingSpendS) (resp : SpendResponse) :
    Option PendingSpendS × Except Error (Option TokenS) :=
  match p with
  | none => (none, .error .logic)
  | some p =>
    let x' := respRefund resp
    let s' := respSig resp
    (none, .ok (if uovEval pk s' = tag p.c x' then some ⟨p.nf, p.t, p.r, x', s'⟩ else none))

/-- The Issuer's nullifier store, keyed by `(ctx_iss, nf)` for one key. -/
structure IssuerState where
  store : List (Context × Nullifier)

/-- The caller's side of a spend as `ratatouille.hpp:174-182` prescribes: run `spend_response`,
reject a recorded nullifier, record it, and only then release the response. -/
def issuerSpend (P : Prim SK) (sk : SK) (st : IssuerState) (req : SpendRequest) (ctx : Context)
    (refund : Credits) : IssuerState × Except Error (Option SpendResult) :=
  match spendResponse P sk req ctx refund with
  | .ok (some out) =>
    if (ctx, out.nf) ∈ st.store then (st, .ok none) else (⟨(ctx, out.nf) :: st.store⟩, .ok (some out))
  | other => (st, other)

/-! ## Correctness (N4, `security/ratatouille.md` Thm 4) -/

/-- `T_init = 0` is rejected on both sides (`ratatouille.cpp:86-90`). -/
theorem issue_zero_rejected (P : Prim SK) (sk : SK) (ctx : Context) (seed : Seed) (req : IssueRequest) :
    issueRequestWithSeed P 0 ctx seed = .error .invalidArgument ∧
      issueResponse P sk req 0 ctx = .error .invalidArgument := by
  simp [issueRequestWithSeed, issueResponse]

/-- Honest issuance: unless `derive_preimage` throws, the Issuer answers and the Client obtains a
valid token holding `(T_init, 0)`. -/
theorem issue_correct {P : Prim SK} (hP : P.Correct) (sk : SK) {tInit : Credits} {ctx : Context}
    {seed : Seed} {pt : PendingTokenS} {req : IssueRequest}
    (hreq : issueRequestWithSeed P tInit ctx seed = .ok (pt, req)) :
    tInit ≠ 0 ∧ pt.tInit = tInit ∧
      (issueResponse P sk req tInit ctx = .error .runtime ∨
        ∃ s, issueResponse P sk req tInit ctx = .ok (some s) ∧
          finalizeIssue (P.pk sk) (some pt) s = (none, .ok (some ⟨pt.nf, tInit, pt.r, 0, s⟩)) ∧
          TokenS.Valid (P.pk sk) ctx ⟨pt.nf, tInit, pt.r, 0, s⟩) := by
  by_cases h0 : tInit = 0
  · simp [issueRequestWithSeed, h0] at hreq
  simp only [issueRequestWithSeed, h0, ite_false] at hreq
  generalize expandSeed issueSeedDst seed = e at hreq
  obtain ⟨nf, r, ρ⟩ := e
  cases hpf : P.proveIssue ⟨com nf ctx tInit r, tInit, ctx⟩ ⟨nf, r⟩ ρ with
  | none => simp [hpf] at hreq
  | some pf =>
  simp only [hpf, Except.ok.injEq, Prod.mk.injEq] at hreq
  obtain ⟨rfl, rfl⟩ := hreq
  have hv := hP.issue_complete _ _ _ _ (by exact rfl) hpf
  refine ⟨h0, rfl, ?_⟩
  simp only [issueResponse, h0, ite_false, issueReqC_mk, issueReqProof_mk, hv, Bool.not_true,
    Bool.false_eq_true]
  cases hd : P.derive sk (tag (com nf ctx tInit r) 0) with
  | none => exact Or.inl rfl
  | some s =>
    have hs := hP.derive_correct _ _ _ hd
    exact Or.inr ⟨s, rfl, by simp [finalizeIssue, hs], hs⟩

/-- An invalid spend (`d > t + x`, or change `t + x − d ≥ 2⁶⁴`) throws `invalid_argument` and
leaves the token unconsumed. -/
theorem spendRequest_invalid (P : Prim SK) (pk : PublicKey) (τ : TokenS) (d : Credits) (ctx : Context)
    (seed : Seed) (h : ¬ (d.toNat ≤ τ.t.toNat + τ.x.toNat ∧ τ.t.toNat + τ.x.toNat - d.toNat < W)) :
    spendRequestWithSeed P pk (some τ) d ctx seed = (some τ, .error .invalidArgument) := by
  have hc : clientCheck τ.t τ.x d = none := by
    rw [← Option.not_isSome_iff_eq_none, clientCheck_isSome]; exact h
  simp only [spendRequestWithSeed, hc]
  split_ifs <;> rfl

/-- A token that is not valid for `pk` and `ctx` is rejected and kept. -/
theorem spendRequest_notValid (P : Prim SK) (pk : PublicKey) (τ : TokenS) (d : Credits) (ctx : Context)
    (seed : Seed) (h : ¬ τ.Valid pk ctx) :
    spendRequestWithSeed P pk (some τ) d ctx seed = (some τ, .error .invalidArgument) := by
  simp [spendRequestWithSeed, h]

/-- What a successful spend request contains. -/
theorem spendRequest_ok {P : Prim SK} {pk : PublicKey} {τ : TokenS} {d : Credits} {ctx : Context}
    {seed : Seed} {ps : PendingSpendS} {req : SpendRequest}
    (h : (spendRequestWithSeed P pk (some τ) d ctx seed).2 = .ok (ps, req)) :
    (spendRequestWithSeed P pk (some τ) d ctx seed).1 = none ∧ τ.Valid pk ctx ∧
      clientCheck τ.t τ.x d = some ps.t ∧ ps.c = com ps.nf ctx ps.t ps.r ∧
      ∃ ρ pf, P.proveSpend ⟨pk, τ.nf, d, ps.c, ctx⟩ ⟨τ.t, τ.r, τ.x, τ.s, ps.nf, ps.t, ps.r⟩ ρ = some pf ∧
        req = SpendReq.toBytes ⟨τ.nf, d, ps.c, pf⟩ := by
  by_cases hv : τ.Valid pk ctx
  swap
  · simp [spendRequestWithSeed, hv] at h
  simp only [spendRequestWithSeed, hv, not_true_eq_false, ite_false] at h ⊢
  cases hc : clientCheck τ.t τ.x d with
  | none => simp [hc] at h
  | some t' =>
  simp only [hc] at h ⊢
  generalize expandSeed spendSeedDst seed = e at h ⊢
  obtain ⟨nf', r', ρ⟩ := e
  cases hpf : P.proveSpend ⟨pk, τ.nf, d, com nf' ctx t' r', ctx⟩ ⟨τ.t, τ.r, τ.x, τ.s, nf', t', r'⟩ ρ with
  | none => simp [hpf] at h
  | some pf =>
  simp only [hpf, Except.ok.injEq, Prod.mk.injEq] at h ⊢
  obtain ⟨rfl, rfl⟩ := h
  refine ⟨?_, ?_, ?_, ?_, ρ, pf, hpf, rfl⟩ <;> trivial

/-- Honest spend: for a valid token and an affordable `d` whose change is a credit value, the
request is produced (unless the prover aborts) and consumes the token. -/
theorem spendRequest_valid (P : Prim SK) (pk : PublicKey) (τ : TokenS) (d : Credits) (ctx : Context)
    (seed : Seed) (hv : τ.Valid pk ctx)
    (h : d.toNat ≤ τ.t.toNat + τ.x.toNat ∧ τ.t.toNat + τ.x.toNat - d.toNat < W) :
    (spendRequestWithSeed P pk (some τ) d ctx seed).1 = none ∧
      ((spendRequestWithSeed P pk (some τ) d ctx seed).2 = .error .runtime ∨
        ∃ ps req, (spendRequestWithSeed P pk (some τ) d ctx seed).2 = .ok (ps, req)) := by
  obtain ⟨t', hc⟩ := Option.isSome_iff_exists.mp ((clientCheck_isSome _ _ _).mpr h)
  simp only [spendRequestWithSeed, hv, not_true_eq_false, ite_false, hc]
  generalize expandSeed spendSeedDst seed = e
  obtain ⟨nf', r', ρ⟩ := e
  cases P.proveSpend ⟨pk, τ.nf, d, com nf' ctx t' r', ctx⟩ ⟨τ.t, τ.r, τ.x, τ.s, nf', t', r'⟩ ρ <;> simp

/-- Honest spend response and change: for an honest request and any refund `x'`, the Issuer
answers with the request's `nf` and `d` (unless `derive_preimage` throws), and the Client obtains a
valid change token holding `t' = t + x − d` and refund `x'`. -/
theorem spend_correct {P : Prim SK} (hP : P.Correct) (sk : SK) {τ : TokenS} {d : Credits}
    {ctx : Context} {seed : Seed} {ps : PendingSpendS} {req : SpendRequest}
    (h : (spendRequestWithSeed P (P.pk sk) (some τ) d ctx seed).2 = .ok (ps, req)) (x' : Credits) :
    ps.t.toNat + d.toNat = τ.t.toNat + τ.x.toNat ∧
      (spendResponse P sk req ctx x' = .error .runtime ∨
        ∃ s, spendResponse P sk req ctx x' = .ok (some ⟨spendResponseBytes x' s, τ.nf, d⟩) ∧
          finalizeSpend (P.pk sk) (some ps) (spendResponseBytes x' s) =
            (none, .ok (some ⟨ps.nf, ps.t, ps.r, x', s⟩)) ∧
          TokenS.Valid (P.pk sk) ctx ⟨ps.nf, ps.t, ps.r, x', s⟩) := by
  obtain ⟨-, hv, hc, hcom, ρ, pf, hpf, rfl⟩ := spendRequest_ok h
  have hcons := clientCheck_eq hc
  have hver := hP.spend_complete _ _ _ _ (by refine ⟨hv, hcom, ?_⟩; dsimp only; omega) hpf
  refine ⟨hcons, ?_⟩
  simp only [spendResponse, parse_toBytes, hver, Bool.not_true, Bool.false_eq_true, ite_false]
  cases hd : P.derive sk (tag ps.c x') with
  | none => exact Or.inl rfl
  | some s =>
    have hs := hP.derive_correct _ _ _ hd
    refine Or.inr ⟨s, rfl, ?_, ?_⟩
    · simp [finalizeSpend, respRefund_mk, respSig_mk, hs]
    · simp only [TokenS.Valid, hs, ← hcom]

/-- One honest round trip of the client (request, Issuer response with refund `x'`, finalization);
`none` if any step fails. -/
def honestSpend (P : Prim SK) (sk : SK) (ctx : Context) (τ : TokenS) (d x' : Credits) (seed : Seed) :
    Option TokenS :=
  match (spendRequestWithSeed P (P.pk sk) (some τ) d ctx seed).2 with
  | .ok (ps, req) =>
    match spendResponse P sk req ctx x' with
    | .ok (some out) =>
      match (finalizeSpend (P.pk sk) (some ps) out.response).2 with
      | .ok (some τ') => some τ'
      | _ => none
    | _ => none
  | _ => none

/-- A sequence of honest spends `(d, x', seed)`, each spending the previous change token. -/
def honestRun (P : Prim SK) (sk : SK) (ctx : Context) : TokenS → List (Credits × Credits × Seed) →
    Option TokenS
  | τ, [] => some τ
  | τ, (d, x', seed) :: rest =>
    match honestSpend P sk ctx τ d x' seed with
    | some τ' => honestRun P sk ctx τ' rest
    | none => none

/-- One honest round trip moves the balance by `x' − d`: `t' + x'' + d = t + x + x'`, with the new
refund `x'' = x'`. (No assumption on the primitives is needed for this direction.) -/
theorem honestSpend_balance {P : Prim SK} {sk : SK} {ctx : Context} {τ τ' : TokenS} {d x' : Credits}
    {seed : Seed} (h : honestSpend P sk ctx τ d x' seed = some τ') :
    τ'.x = x' ∧ τ'.t.toNat + d.toNat = τ.t.toNat + τ.x.toNat := by
  unfold honestSpend at h
  split at h
  · rename_i ps req hreq
    obtain ⟨-, -, hc, -⟩ := spendRequest_ok hreq
    split at h
    · rename_i out hout
      split at h
      · rename_i τ'' hfin
        cases h
        simp only [spendResponse] at hout
        split_ifs at hout
        · cases hout
        split at hout
        · cases hout
        rename_i s hs
        cases hout
        simp only [finalizeSpend, respRefund_mk, respSig_mk] at hfin
        split_ifs at hfin
        · cases hfin
          exact ⟨rfl, clientCheck_eq hc⟩
        · cases hfin
      all_goals cases h
    all_goals cases h
  all_goals cases h

/-- **Client balance over any sequence of honest spends**: if the run succeeds, the final
effective balance plus everything spent equals the initial balance plus all refunds,
`t_n + x_n + Σ d = t_0 + x_0 + Σ x'` over ℕ. Every intermediate `t` is a credit value by type. -/
theorem honest_spends_balance {P : Prim SK} {sk : SK} {ctx : Context} :
    ∀ (ops : List (Credits × Credits × Seed)) (τ τ' : TokenS), honestRun P sk ctx τ ops = some τ' →
      τ'.t.toNat + τ'.x.toNat + (ops.map fun o => o.1.toNat).sum =
        τ.t.toNat + τ.x.toNat + (ops.map fun o => o.2.1.toNat).sum
  | [], τ, τ', h => by cases h; simp
  | (d, x', seed) :: rest, τ, τ', h => by
    unfold honestRun at h
    split at h
    · rename_i τ₁ h₁
      have ih := honest_spends_balance rest τ₁ τ' h
      obtain ⟨hx, ht⟩ := honestSpend_balance h₁
      simp only [List.map_cons, List.sum_cons]
      rw [← hx]
      omega
    · cases h

/-- Under correct primitives, each honest round trip either fails only through a `runtime_error`
(prover or `derive_preimage` abort) or yields a valid token, so valid tokens stay spendable. -/
theorem honestSpend_valid {P : Prim SK} (hP : P.Correct) {sk : SK} {ctx : Context} {τ τ' : TokenS}
    {d x' : Credits} {seed : Seed} (h : honestSpend P sk ctx τ d x' seed = some τ') :
    τ'.Valid (P.pk sk) ctx := by
  unfold honestSpend at h
  split at h
  · rename_i ps req hreq
    obtain ⟨-, hrest⟩ := spend_correct hP sk hreq x'
    rcases hrest with hr | ⟨s, hs, hfin, hval⟩
    · rw [hr] at h; cases h
    · rw [hs] at h
      dsimp only at h
      rw [hfin] at h
      cases h
      exact hval
  all_goals cases h

/-! ## The Issuer's nullifier store -/

/-- The store only grows by fresh keys, so it never holds a key twice. -/
theorem issuerSpend_store {P : Prim SK} {sk : SK} {st st' : IssuerState} {req : SpendRequest}
    {ctx : Context} {refund : Credits} {res : Except Error (Option SpendResult)}
    (h : issuerSpend P sk st req ctx refund = (st', res)) :
    (st' = st ∧ ∀ out, res ≠ .ok (some out)) ∨
      ∃ out, res = .ok (some out) ∧ spendResponse P sk req ctx refund = .ok (some out) ∧
        (ctx, out.nf) ∉ st.store ∧ st'.store = (ctx, out.nf) :: st.store := by
  unfold issuerSpend at h
  split at h
  · rename_i out hout
    split_ifs at h with hm
    · cases h; exact Or.inl ⟨rfl, by simp⟩
    · cases h; exact Or.inr ⟨out, rfl, hout, hm, rfl⟩
  · rename_i r hr
    cases h
    refine Or.inl ⟨rfl, fun out he => hr out ?_⟩
    rw [he]

theorem issuerSpend_nodup {P : Prim SK} {sk : SK} {st : IssuerState} (hst : st.store.Nodup)
    (req : SpendRequest) (ctx : Context) (refund : Credits) :
    (issuerSpend P sk st req ctx refund).1.store.Nodup := by
  rcases issuerSpend_store (Prod.mk.eta (p := issuerSpend P sk st req ctx refund)).symm with
    ⟨h, -⟩ | ⟨out, -, -, hm, h⟩
  · rw [h]; exact hst
  · rw [h]; exact List.nodup_cons.mpr ⟨hm, hst⟩

/-- **Nullifier uniqueness.** A spend is accepted only if its `(ctx, nf)` was not recorded, and
it is recorded on acceptance; so the same nullifier is accepted at most once per context. -/
theorem issuer_accepts_once {P : Prim SK} {sk : SK} {st : IssuerState} {req : SpendRequest}
    {ctx : Context} {refund : Credits} {out : SpendResult}
    (h : (issuerSpend P sk st req ctx refund).2 = .ok (some out)) :
    (ctx, out.nf) ∉ st.store ∧ (issuerSpend P sk st req ctx refund).1.store = (ctx, out.nf) :: st.store ∧
      ∀ (req' : SpendRequest) (refund' : Credits) (out' : SpendResult),
        (issuerSpend P sk (issuerSpend P sk st req ctx refund).1 req' ctx refund').2 = .ok (some out') →
        out'.nf ≠ out.nf := by
  rcases issuerSpend_store (Prod.mk.eta (p := issuerSpend P sk st req ctx refund)).symm with
    ⟨-, hne⟩ | ⟨out₁, h₁, -, hm, hst⟩
  · exact absurd h (hne out)
  rw [h] at h₁
  cases h₁
  refine ⟨hm, hst, fun req' refund' out' h' heq => ?_⟩
  rcases issuerSpend_store (Prod.mk.eta (p := issuerSpend P sk (issuerSpend P sk st req ctx refund).1
      req' ctx refund')).symm with ⟨-, hne⟩ | ⟨out₂, h₂, -, hm₂, -⟩
  · exact hne out' h'
  rw [h'] at h₂
  cases h₂
  rw [hst, heq] at hm₂
  exact hm₂ List.mem_cons_self

/-- **F2** (copied requests): `spend_response` depends only on `(sk, request, ctx, refund)`, so
whoever submits a request first is served; resubmitting the same bytes (e.g. the honest client
after an on-path party copied its request) is then rejected by the store. -/
theorem copied_request_first_wins {P : Prim SK} {sk : SK} {st : IssuerState} {req : SpendRequest}
    {ctx : Context} {refund : Credits} {out : SpendResult}
    (h : (issuerSpend P sk st req ctx refund).2 = .ok (some out)) (refund' : Credits) :
    (issuerSpend P sk (issuerSpend P sk st req ctx refund).1 req ctx refund').2 = .ok none ∨
      (issuerSpend P sk (issuerSpend P sk st req ctx refund).1 req ctx refund').2 = .error .runtime := by
  obtain ⟨-, hst, -⟩ := issuer_accepts_once h
  rcases issuerSpend_store (Prod.mk.eta (p := issuerSpend P sk st req ctx refund)).symm with
    ⟨-, hne⟩ | ⟨out₁, h₁, hresp, -, -⟩
  · exact absurd h (hne out)
  rw [h] at h₁; cases h₁
  -- The same request verifies again; only the signed refund may differ.
  simp only [spendResponse] at hresp
  split_ifs at hresp with hver
  · cases hresp
  have hnf : (SpendReq.parse req).nf = out.nf := by
    cases hd : P.derive sk (tag (SpendReq.parse req).cNext refund) with
    | none => rw [hd] at hresp; cases hresp
    | some s => rw [hd] at hresp; cases hresp; rfl
  generalize (issuerSpend P sk st req ctx refund).1 = st1 at hst ⊢
  unfold issuerSpend spendResponse
  simp only [hver]
  cases P.derive sk (tag (SpendReq.parse req).cNext refund') with
  | none => exact Or.inr rfl
  | some s' => left; simp [hst, hnf]

/-- **F5** (signing before the nullifier check): `spend_response` hands the caller a valid
signature on `Tag(c', x')` even when `nf` is already recorded; the caller's wrapper must withhold
it. (The store is not an input of `spendResponse`.) -/
theorem spendResponse_signs_duplicates {P : Prim SK} (hP : P.Correct) {sk : SK} {st : IssuerState}
    {req : SpendRequest} {ctx : Context} {refund : Credits}
    (hdup : (ctx, (SpendReq.parse req).nf) ∈ st.store)
    (hver : P.verifySpend ⟨P.pk sk, (SpendReq.parse req).nf, (SpendReq.parse req).d,
      (SpendReq.parse req).cNext, ctx⟩ (SpendReq.parse req).proof = true)
    {s : Preimage} (hs : P.derive sk (tag (SpendReq.parse req).cNext refund) = some s) :
    spendResponse P sk req ctx refund =
        .ok (some ⟨spendResponseBytes refund s, (SpendReq.parse req).nf, (SpendReq.parse req).d⟩) ∧
      uovEval (P.pk sk) (respSig (spendResponseBytes refund s)) =
        tag (SpendReq.parse req).cNext (respRefund (spendResponseBytes refund s)) ∧
      issuerSpend P sk st req ctx refund = (st, .ok none) := by
  have hresp : spendResponse P sk req ctx refund =
      .ok (some ⟨spendResponseBytes refund s, (SpendReq.parse req).nf, (SpendReq.parse req).d⟩) := by
    simp [spendResponse, hver, hs]
  refine ⟨hresp, ?_, ?_⟩
  · rw [respSig_mk, respRefund_mk]; exact hP.derive_correct _ _ _ hs
  · simp [issuerSpend, hresp, hdup]

/-! ## Balance at the Issuer, over arbitrary request sequences

The accounting (`security/ratatouille.md` Thm 1, and `Protocols/Ratatouille.lean`'s `Chain`) is
done on a ghost ledger. `Ledger` records the keys `(ctx, nf)` in the store, every signed state
released to the network with its opening `(ctx, nf, t)` and refund `x`, and the credits issued,
spent and refunded per context. Its invariant is

    spent(c) + live(c) ≤ issued(c) + refunded(c),

where `live(c)` sums `t + x` over the released states of context `c` whose nullifier is not in
the store. -/

/-- A store key. -/
abbrev Key := Context × Nullifier

/-- A released signed state: its key `(ctx, nf)`, credit `t` and refund `x` (as naturals). -/
structure Entry where
  key : Key
  t : ℕ
  x : ℕ

structure Ledger where
  spentKeys : List Key
  released : List Entry
  issued : List (Context × ℕ)
  spent : List (Context × ℕ)
  refunded : List (Context × ℕ)

/-- Ledger events: an accepted issuance of `T` credits to `(ctx, nf)`; an accepted spend of `d`
from the state `(ctx, nf, t, x)` to `(ctx, nf', t')` with refund `x'`; and (to state F5) a
signature released without being recorded. -/
inductive LEvent
  | issue (ctx : Context) (nf : Nullifier) (T : ℕ)
  | spend (ctx : Context) (nf : Nullifier) (t x d : ℕ) (nf' : Nullifier) (t' x' : ℕ)
  | leak (e : Entry)

def LEvent.isLeak : LEvent → Bool
  | .leak _ => true
  | _ => false

def Ledger.empty : Ledger := ⟨[], [], [], [], []⟩

def Ledger.step (L : Ledger) : LEvent → Ledger
  | .issue ctx nf T => { L with released := ⟨(ctx, nf), T, 0⟩ :: L.released,
                                 issued := (ctx, T) :: L.issued }
  | .spend ctx nf _ _ d nf' t' x' =>
      { L with spentKeys := (ctx, nf) :: L.spentKeys,
               released := ⟨(ctx, nf'), t', x'⟩ :: L.released,
               spent := (ctx, d) :: L.spent, refunded := (ctx, x') :: L.refunded }
  | .leak e => { L with released := e :: L.released }

/-- When an event may happen: a spend needs a fresh key (the store), a released parent state with
the same opening and refund (unforgeability + binding), and conservation `t + x = t' + d` (V3). -/
def Ledger.Allowed (L : Ledger) : LEvent → Prop
  | .spend ctx nf t x d _ t' _ =>
      (ctx, nf) ∉ L.spentKeys ∧ (⟨(ctx, nf), t, x⟩ : Entry) ∈ L.released ∧ t + x = t' + d
  | _ => True

def Ledger.ValidRun : Ledger → List LEvent → Prop
  | _, [] => True
  | L, e :: es => L.Allowed e ∧ (L.step e).ValidRun es

def Ledger.run : Ledger → List LEvent → Ledger
  | L, [] => L
  | L, e :: es => (L.step e).run es

/-- The total of a per-context list for context `c`. -/
def total (c : Context) (l : List (Context × ℕ)) : ℕ := ((l.filter fun p => p.1 = c).map (·.2)).sum

/-- The live value of context `c` in released states `R` with spent keys `K`. -/
def liveSum (R : List Entry) (K : List Key) (c : Context) : ℕ :=
  ((R.filter fun e => decide (e.key.1 = c ∧ e.key ∉ K)).map fun e => e.t + e.x).sum

/-- The value of the released states of key `k` (in context `c`). -/
def keySum (R : List Entry) (k : Key) (c : Context) : ℕ :=
  ((R.filter fun e => decide (e.key.1 = c ∧ e.key = k)).map fun e => e.t + e.x).sum

def Ledger.live (L : Ledger) (c : Context) : ℕ := liveSum L.released L.spentKeys c

def Ledger.Inv (L : Ledger) : Prop :=
  ∀ c, total c L.spent + L.live c ≤ total c L.issued + total c L.refunded

theorem total_cons (c c' : Context) (n : ℕ) (l : List (Context × ℕ)) :
    total c ((c', n) :: l) = (if c' = c then n else 0) + total c l := by
  by_cases h : c' = c <;> simp [total, h]

theorem liveSum_cons (e : Entry) (R : List Entry) (K : List Key) (c : Context) :
    liveSum (e :: R) K c = (if e.key.1 = c ∧ e.key ∉ K then e.t + e.x else 0) + liveSum R K c := by
  unfold liveSum
  by_cases h : e.key.1 = c ∧ e.key ∉ K
  · rw [List.filter_cons_of_pos (by simpa using h)]; simp [h]
  · rw [List.filter_cons_of_neg (by simpa using h)]; simp [h]

theorem liveSum_nil (K : List Key) (c : Context) : liveSum [] K c = 0 := rfl

/-- Recording a key removes exactly the value of its released states from the live value. -/
theorem live_split (R : List Entry) (K : List Key) (c : Context) (k : Key) (hk : k ∉ K) :
    liveSum R K c = liveSum R (k :: K) c + keySum R k c := by
  induction R with
  | nil => rfl
  | cons e R ih =>
    rw [liveSum_cons, liveSum_cons, ih]
    unfold keySum
    by_cases h2 : e.key = k
    · subst h2
      by_cases h1 : e.key.1 = c
      · rw [List.filter_cons_of_pos (by simpa using h1)]
        simp [h1, hk]; omega
      · rw [List.filter_cons_of_neg (by simpa using h1)]
        simp [h1]
    · rw [List.filter_cons_of_neg (by simp [h2])]
      by_cases h1 : e.key.1 = c <;> by_cases h3 : e.key ∈ K <;> simp [h1, h2, h3]
      all_goals omega

theorem le_keySum (R : List Entry) (e : Entry) (he : e ∈ R) (c : Context) (hc : e.key.1 = c) :
    e.t + e.x ≤ keySum R e.key c :=
  List.le_sum_of_mem (List.mem_map.mpr ⟨e, List.mem_filter.mpr ⟨he, by simp [hc]⟩, rfl⟩)

theorem keySum_other (R : List Entry) (k : Key) (c : Context) (hc : k.1 ≠ c) : keySum R k c = 0 := by
  unfold keySum
  rw [List.sum_eq_zero]
  intro a ha
  simp only [List.mem_map, List.mem_filter, decide_eq_true_eq] at ha
  obtain ⟨e, ⟨-, he1, he2⟩, -⟩ := ha
  rw [he2] at he1; exact absurd he1 hc

theorem Ledger.inv_step (L : Ledger) (e : LEvent) (hA : L.Allowed e) (hl : e.isLeak = false)
    (hI : L.Inv) : (L.step e).Inv := by
  intro c
  have hc := hI c
  simp only [Ledger.live] at hc
  cases e with
  | issue ctx nf T =>
    simp only [Ledger.step, Ledger.live, total_cons, liveSum_cons]
    split_ifs <;> simp_all <;> omega
  | leak e => simp [LEvent.isLeak] at hl
  | spend ctx nf t x d nf' t' x' =>
    obtain ⟨hfresh, hpar, hcons⟩ := hA
    have hsplit := live_split L.released L.spentKeys c (ctx, nf) hfresh
    simp only [Ledger.step, Ledger.live, total_cons, liveSum_cons]
    by_cases h1 : ctx = c
    · subst h1
      have hpv := le_keySum L.released _ hpar ctx rfl
      dsimp only at hpv
      simp only [ite_true, true_and]
      split_ifs <;> omega
    · rw [keySum_other _ _ _ h1] at hsplit
      simp only [h1, ite_false, false_and]
      omega

theorem Ledger.inv_run : ∀ (L : Ledger) (es : List LEvent), L.ValidRun es →
    (∀ e ∈ es, e.isLeak = false) → L.Inv → (L.run es).Inv
  | _, [], _, _, hI => hI
  | L, e :: es, ⟨hA, hV⟩, hl, hI =>
    Ledger.inv_run (L.step e) es hV (fun e' he' => hl e' (List.mem_cons_of_mem _ he'))
      (L.inv_step e hA (hl e List.mem_cons_self) hI)

/-- **Ledger balance**: in every valid run without leaks, per context,
`Σ d ≤ Σ T_init + Σ x'`. -/
theorem ledger_balance (es : List LEvent) (hV : Ledger.empty.ValidRun es)
    (hl : ∀ e ∈ es, e.isLeak = false) (c : Context) :
    total c (Ledger.empty.run es).spent ≤
      total c (Ledger.empty.run es).issued + total c (Ledger.empty.run es).refunded := by
  have := Ledger.inv_run _ es hV hl (fun c => by simp [Ledger.empty, total, Ledger.live, liveSum]) c
  omega

/-- **F5**, the accounting side: one signature released on the duplicate-nullifier path (a
"refresh" of an already-spent token, `d = 0`, change 1) lets a valid run spend 2 credits
against 1 issued and 0 refunded. -/
theorem leak_breaks_balance : ∃ es : List LEvent, Ledger.empty.ValidRun es ∧
    (es.filter LEvent.isLeak).length = 1 ∧
    total (Vector.replicate 16 0) (Ledger.empty.run es).spent >
      total (Vector.replicate 16 0) (Ledger.empty.run es).issued +
        total (Vector.replicate 16 0) (Ledger.empty.run es).refunded := by
  let c : Context := Vector.replicate 16 0
  let n (i : UInt8) : Nullifier := Vector.replicate 24 i
  refine ⟨[.issue c (n 0) 1, .spend c (n 0) 1 0 1 (n 1) 0 0, .leak ⟨(c, n 2), 1, 0⟩,
    .spend c (n 2) 1 0 1 (n 3) 0 0], ?_, by decide, ?_⟩
  · have h02 : n 0 ≠ n 2 := by
      intro h; have := congrArg (fun v => v[0]) h; simp [n] at this
    simp [Ledger.ValidRun, Ledger.Allowed, Ledger.step, Ledger.empty, Ne.symm h02]
  · simp [Ledger.run, Ledger.step, Ledger.empty, total, c]

/-! ### The concrete Issuer on the ledger

The Issuer processes an arbitrary sequence of (adversarial) requests. Each step is annotated with
a ghost witness (what the extractor of `security/ratatouille.md` Thm 1 would output); it is used
only to label the ledger. -/

/-- An Issuer operation: `issue_response(req, T_init, ctx)`, or the caller's spend handling
(`issuerSpend`) with the caller's refund. -/
inductive Op
  | issue (req : IssueRequest) (tInit : Credits) (ctx : Context)
  | spend (req : SpendRequest) (ctx : Context) (refund : Credits)

structure World where
  st : IssuerState
  L : Ledger

/-- One Issuer step, with the ghost annotation `(wi, ws)`. -/
def World.step (P : Prim SK) (sk : SK) (w : World) : Op × IssueWitness × SpendWitness → World
  | (.issue req tInit ctx, wi, _) =>
    match issueResponse P sk req tInit ctx with
    | .ok (some _) => { w with L := w.L.step (.issue ctx wi.nf tInit.toNat) }
    | _ => w
  | (.spend req ctx refund, _, ws) =>
    match issuerSpend P sk w.st req ctx refund with
    | (st', .ok (some out)) =>
      ⟨st', w.L.step (.spend ctx out.nf ws.t.toNat ws.x.toNat out.d.toNat ws.nf' ws.t'.toNat
        refund.toNat)⟩
    | (st', _) => ⟨st', w.L⟩

/-- The security assumptions, per accepted spend, on the ghost witness: it satisfies `R_spend`
for the instance the Issuer verified (proof soundness), and the state it spends was released
earlier with the same opening and refund (UOV unforgeability on `Tag` + commitment binding). -/
def World.Hyp (P : Prim SK) (sk : SK) (w : World) : Op × IssueWitness × SpendWitness → Prop
  | (.spend req ctx refund, _, ws) =>
    ∀ out, (issuerSpend P sk w.st req ctx refund).2 = .ok (some out) →
      SpendRel ⟨P.pk sk, out.nf, out.d, (SpendReq.parse req).cNext, ctx⟩ ws ∧
        (⟨(ctx, out.nf), ws.t.toNat, ws.x.toNat⟩ : Entry) ∈ w.L.released
  | _ => True

def World.HypRun (P : Prim SK) (sk : SK) : World → List (Op × IssueWitness × SpendWitness) → Prop
  | _, [] => True
  | w, o :: os => w.Hyp P sk o ∧ (w.step P sk o).HypRun P sk os

def World.run (P : Prim SK) (sk : SK) : World → List (Op × IssueWitness × SpendWitness) → World
  | w, [] => w
  | w, o :: os => (w.step P sk o).run P sk os

theorem World.step_inv (P : Prim SK) (sk : SK) (w : World) (o : Op × IssueWitness × SpendWitness)
    (hs : w.st.store = w.L.spentKeys) (hH : w.Hyp P sk o) (hI : w.L.Inv) :
    (w.step P sk o).st.store = (w.step P sk o).L.spentKeys ∧ (w.step P sk o).L.Inv := by
  obtain ⟨op, wi, ws⟩ := o
  cases op with
  | issue req tInit ctx =>
    simp only [World.step]
    split
    · exact ⟨hs, w.L.inv_step _ trivial rfl hI⟩
    · exact ⟨hs, hI⟩
  | spend req ctx refund =>
    simp only [World.step]
    split
    · rename_i st' out heq
      have hH' := hH out (by rw [heq])
      rcases issuerSpend_store heq with ⟨-, hne⟩ | ⟨out', h₁, -, hm, hst⟩
      · exact absurd rfl (hne out)
      cases h₁
      refine ⟨by rw [hst, hs]; rfl, w.L.inv_step _ ?_ rfl hI⟩
      exact ⟨by rw [← hs]; exact hm, hH'.2, by have := hH'.1.2.2; dsimp only at this; omega⟩
    · rename_i st' r hr heq
      rcases issuerSpend_store heq with ⟨h, -⟩ | ⟨out', h₁, -⟩
      · subst h; exact ⟨hs, hI⟩
      · exact absurd h₁ (hr out')

/-- **Issuer balance over arbitrary request sequences.** For any sequence of issuance and spend
requests (arbitrary bytes, arbitrary refunds), if every accepted spend satisfies the security
assumptions (`World.Hyp`), then per context the credits accepted as spent are at most the credits
issued plus the refunds granted: `Σ d ≤ Σ T_init + Σ x'`. The ledger records exactly the `T_init`
of each issuance the Issuer answered and the `d`, `x'` of each spend it released. -/
theorem issuer_balance (P : Prim SK) (sk : SK) (os : List (Op × IssueWitness × SpendWitness))
    (hH : World.HypRun P sk ⟨⟨[]⟩, Ledger.empty⟩ os) (c : Context) :
    let w := World.run P sk ⟨⟨[]⟩, Ledger.empty⟩ os
    total c w.L.spent ≤ total c w.L.issued + total c w.L.refunded := by
  suffices ∀ (os : List (Op × IssueWitness × SpendWitness)) (w : World), w.HypRun P sk os →
      w.st.store = w.L.spentKeys → w.L.Inv → (w.run P sk os).L.Inv by
    have := this os _ hH rfl (fun c => by simp [Ledger.empty, total, Ledger.live, liveSum]) c
    dsimp only
    omega
  intro os
  induction os with
  | nil => intro w _ _ hI; exact hI
  | cons o os ih =>
    intro w ⟨h1, h2⟩ hs hI
    obtain ⟨hs', hI'⟩ := World.step_inv P sk w o hs h1 hI
    exact ih _ h2 hs' hI'

/-! ## Findings F3 and F4 -/

/-- **F3**: `finalize_issue` consumes the pending token even when the response is invalid. -/
theorem finalizeIssue_consumes (pk : PublicKey) (p : PendingTokenS) (resp : Preimage) :
    (finalizeIssue pk (some p) resp).1 = none ∧
      (uovEval pk resp ≠ tag p.c 0 → (finalizeIssue pk (some p) resp).2 = .ok none) := by
  refine ⟨rfl, fun h => ?_⟩
  simp [finalizeIssue, h]

/-- **F3**: `finalize_spend` consumes the pending spend even when the response is invalid; a
retry with a corrected response then throws `logic_error`. -/
theorem finalizeSpend_consumes (pk : PublicKey) (p : PendingSpendS) (resp resp' : SpendResponse) :
    (finalizeSpend pk (some p) resp).1 = none ∧
      (uovEval pk (respSig resp) ≠ tag p.c (respRefund resp) →
        (finalizeSpend pk (some p) resp).2 = .ok none) ∧
      finalizeSpend pk (finalizeSpend pk (some p) resp).1 resp' = (none, .error .logic) := by
  refine ⟨rfl, fun h => ?_, rfl⟩
  simp [finalizeSpend, h]

/-- **F4**: `finalize_spend` accepts any refund the Issuer signs; nothing bounds `t' + x'`. -/
theorem finalizeSpend_any_refund (pk : PublicKey) (p : PendingSpendS) (x' : Credits) (s : Preimage)
    (h : uovEval pk s = tag p.c x') :
    finalizeSpend pk (some p) (spendResponseBytes x' s) =
      (none, .ok (some ⟨p.nf, p.t, p.r, x', s⟩)) := by
  simp [finalizeSpend, respRefund_mk, respSig_mk, h]

/-- **F4**: a token with `t + x ≥ 2⁶⁴` (reachable by F4's large refunds) can only spend
`d ≥ t + x − (2⁶⁴ − 1)`: any smaller spend is rejected (and the token kept). -/
theorem spendRequest_forced_minimum (P : Prim SK) (pk : PublicKey) (τ : TokenS) (d : Credits)
    (ctx : Context) (seed : Seed) (h : d.toNat + (W - 1) < τ.t.toNat + τ.x.toNat) :
    spendRequestWithSeed P pk (some τ) d ctx seed = (some τ, .error .invalidArgument) :=
  spendRequest_invalid P pk τ d ctx seed (by omega)

/-! ## Witness layouts (`issue.hpp:94-105`, `spend.hpp:231-268`), for the cross-check

The witnesses are inputs of the abstract prover; they are modelled only so that
`lake exe spec_kats` can check them against the C++. -/

/-- `encode_committed_states`: the states after rounds 5 and 9 (`SEGMENT_START = [0, 5, 9]`). -/
def committedStates (s : State) : List UInt8 :=
  let s5 := keccakP800Rounds 0 5 s
  s5.toList ++ (keccakP800Rounds 5 4 s5).toList

/-- `encode_issue_witness(nf, ctx, T_init, r)`: `r ‖ nf ‖ s5 ‖ s9` (240 bytes). -/
def encodeIssueWitness (nf : Nullifier) (ctx : Context) (tInit : Credits) (r : Opening) : List UInt8 :=
  r.toList ++ nf.toList ++
    committedStates (VoleMole.Arith.Ratatouille.comState nf.fn ctx.fn tInit.toNat r.fn)

/-- `carries(a, b)`: the carries `k₁, …, k₆₄` of `a + b`, `k_{i+1}` at bit `i`
(`spend.hpp:174-184`). -/
def carries (a b : Credits) : Credits := Id.run do
  let mut k : UInt64 := 0
  let mut out : UInt64 := 0
  for i in [0:64] do
    let ai := (a >>> i.toUInt64) &&& 1
    let bi := (b >>> i.toUInt64) &&& 1
    k := (ai &&& bi) ||| (ai &&& k) ||| (bi &&& k)
    out := out ||| (k <<< i.toUInt64)
  return out

/-- `encode_spend_witness` (847 bytes): `r ‖ ⟨t⟩ ‖ ⟨x⟩ ‖ c ‖ nf' ‖ ⟨t'⟩ ‖ r' ‖ s ‖ ⟨carries(t, x)⟩ ‖
⟨carries(t', d)⟩ ‖ states(Com) ‖ states(Tag) ‖ states(Com')`. -/
def encodeSpendWitness (nf : Nullifier) (w : SpendWitness) (d : Credits) (ctx : Context) :
    List UInt8 :=
  let c := com nf ctx w.t w.r
  w.r.toList ++ (encodeCredits w.t).toList ++ (encodeCredits w.x).toList ++ c.toList ++
    w.nf'.toList ++ (encodeCredits w.t').toList ++ w.r'.toList ++ w.s.toList ++
    (encodeCredits (carries w.t w.x)).toList ++ (encodeCredits (carries w.t' d)).toList ++
    committedStates (VoleMole.Arith.Ratatouille.comState nf.fn ctx.fn w.t.toNat w.r.fn) ++
    committedStates (VoleMole.Arith.Ratatouille.tagState c.fn w.x.toNat) ++
    committedStates (VoleMole.Arith.Ratatouille.comState w.nf'.fn ctx.fn w.t'.toNat w.r'.fn)

end VoleMole.Spec.Ratatouille
