import VoleMole.Arith.GFField

/-!
# `GF256` is the field GF(2⁸)

`Arith/GF.lean` defines pqov's GF(256) (`GF256`, a byte with XOR and `gf256_mul`) with only `0`,
`1`, `+`, `*`, and proves that the embedding `iota : GF256 → GF128` is an injective map preserving
`0`, `1`, `+` and `*` (`iota_injective`, `iota_add`, `iota_mul`; `GF128` is a field by
`Arith/GFField.lean`). Here this is turned into a `Field GF256` instance:

* `instCommRing`: `Function.Injective.commRing` along `iota`, with `-a = a` and `a - b = a + b`
  (characteristic 2) and the recursive `•`, `^` and casts; `GF.lean`'s `0`, `1`, `+`, `*` are kept.
* `instField`: `GF256` is a finite domain (`iota` is an injective ring map into a field), hence a
  field (`Fintype.fieldOfDomain`).
* `card_eq`: `Fintype.card GF256 = 256`; `instCharP`: characteristic 2.

Nothing here is evaluated by the kernel beyond what `GF.lean` already checks.
-/

namespace VoleMole.Arith.GF256

open VoleMole.Arith

instance : Neg GF256 := ⟨fun a => a⟩
instance : Sub GF256 := ⟨fun a b => a + b⟩
instance : SMul ℕ GF256 := ⟨nsmulRec⟩
instance : SMul ℤ GF256 := ⟨zsmulRec nsmulRec⟩
instance : Pow GF256 ℕ := ⟨fun a n => npowRec n a⟩
instance : NatCast GF256 := ⟨fun n => nsmulRec n 1⟩
instance : IntCast GF256 := ⟨fun z => zsmulRec nsmulRec z 1⟩

lemma iota_neg (a : GF256) : iota (-a) = -iota a := (CharTwo.neg_eq (iota a)).symm

lemma iota_sub (a b : GF256) : iota (a - b) = iota a - iota b := by
  rw [CharTwo.sub_eq_add]; exact iota_add a b

lemma iota_nsmul (n : ℕ) (a : GF256) : iota (n • a) = n • iota a := by
  induction n with
  | zero => exact iota_zero.trans (zero_smul ℕ _).symm
  | succ n ih =>
    change iota (nsmulRec n a + a) = _
    rw [iota_add, succ_nsmul]
    exact congrArg (· + iota a) ih

lemma iota_zsmul (n : ℤ) (a : GF256) : iota (n • a) = n • iota a := by
  cases n with
  | ofNat n =>
    change iota (nsmulRec n a) = _
    rw [Int.ofNat_eq_natCast, natCast_zsmul]
    exact iota_nsmul n a
  | negSucc n =>
    change iota (-(nsmulRec (n + 1) a)) = _
    rw [iota_neg, negSucc_zsmul]
    exact congrArg Neg.neg (iota_nsmul (n + 1) a)

lemma iota_npow (a : GF256) (n : ℕ) : iota (a ^ n) = iota a ^ n := by
  induction n with
  | zero => exact iota_one.trans (pow_zero _).symm
  | succ n ih =>
    change iota (npowRec n a * a) = _
    rw [iota_mul, pow_succ]
    exact congrArg (· * iota a) ih

lemma iota_natCast (n : ℕ) : iota (n : GF256) = n := by
  have h := iota_nsmul n 1
  rw [iota_one, nsmul_one] at h
  exact h

lemma iota_intCast (n : ℤ) : iota (n : GF256) = n := by
  have h := iota_zsmul n 1
  rw [iota_one, zsmul_one] at h
  exact h

/-- **`GF256` is a commutative ring**, with `GF.lean`'s `0`, `1`, `+`, `*`. -/
noncomputable instance instCommRing : CommRing GF256 :=
  Function.Injective.commRing iota (fun a b h => iota_injective a b h) iota_zero iota_one iota_add
    iota_mul iota_neg iota_sub iota_nsmul iota_zsmul iota_npow iota_natCast iota_intCast

/-- `iota` as a ring homomorphism. -/
noncomputable def iotaHom : GF256 →+* GF128 where
  toFun := iota
  map_one' := iota_one
  map_mul' := iota_mul
  map_zero' := iota_zero
  map_add' := iota_add

instance instIsDomain : IsDomain GF256 :=
  Function.Injective.isDomain iotaHom fun a b h => iota_injective a b h

/-- `GF256 ≃ Fin 256` (the byte's value). -/
def equivFin : GF256 ≃ Fin 256 where
  toFun a := ⟨a.val.toNat, a.val.toNat_lt⟩
  invFun n := ⟨n.val.toUInt8⟩
  left_inv a := ext' UInt8.ofNat_toNat
  right_inv n := Fin.ext (by simp [Nat.toUInt8])

instance instFintype : Fintype GF256 := Fintype.ofEquiv _ equivFin.symm

theorem card_eq : Fintype.card GF256 = 256 := by
  rw [Fintype.card_congr equivFin, Fintype.card_fin]

/-- **`GF256` is a field** (a finite domain). -/
noncomputable instance instField : Field GF256 := Fintype.fieldOfDomain GF256

instance instCharP : CharP GF256 2 :=
  ⟨fun n => by
    rw [← CharP.cast_eq_zero_iff GF128 2, ← iota_natCast, ← iota_zero]
    exact ⟨fun h => h ▸ rfl, fun h => iota_injective _ _ h⟩⟩

end VoleMole.Arith.GF256
