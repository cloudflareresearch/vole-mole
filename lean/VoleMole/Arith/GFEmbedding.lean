import VoleMole.Arith.GF
import VoleMole.Arith.UOV

/-!
# The concrete embedding satisfies `UOV.IsEmbedding`

For the concrete fields of `VoleMole/Arith/GF.lean`, the hypotheses `UOV.IsEmbedding` of the UOV
gadget hold with `β := beta`, `toBits := GF256.toBits`, `ofByte := GF256.ofBits`, proved in the
kernel from `iota_add`, `iota_mul`, `iota_injective`. (The UOV theorems themselves assume a `Field`;
`GF128` gets one only in `Arith/GFField.lean`, which this file does not import. `lake exe
arith_vectors` also checks the embedding hypotheses exhaustively at run time.)
-/

namespace VoleMole.Arith

open XorGroup

/-- `from_8_byte` as the UOV gadget writes it is `iota`. -/
theorem embed_toBits (a : GF256) : UOV.embed beta (GF256.toBits a) = iota a := by
  have hbit : ∀ (c : Bool) (x : GF128), bitF c * x = if c then x else 0 := by
    intro c x; cases c
    · exact GF128.zero_mul x
    · exact GF128.one_mul x
  have hsel : ∀ (c : Bool) (acc x : GF128),
      (if c then acc + x else acc) = acc + if c then x else 0 := by
    intro c acc x; cases c
    · exact (add_zero acc).symm
    · rfl
  simp only [UOV.embed, hbit, iota, foldSel, hsel]
  rw [show List.finRange 8 = [0, 1, 2, 3, 4, 5, 6, 7] from rfl]
  simp only [List.foldl_cons, List.foldl_nil, XorGroup.zero_add]

theorem toBits_ofBits (v : Fin 8 → Bool) : GF256.toBits (GF256.ofBits v) = v := by
  revert v; decide +kernel

/-- `UOV.IsEmbedding` for the concrete `β`, GF(256) bits and decoder. -/
theorem isEmbedding : UOV.IsEmbedding beta GF256.toBits GF256.ofBits where
  toBits_ofByte := toBits_ofBits
  map_zero := by rw [embed_toBits]; exact iota_zero
  map_add a b := by simp only [embed_toBits, iota_add]
  map_mul a b := by simp only [embed_toBits, iota_mul]
  injective a b h := iota_injective a b (by simpa only [embed_toBits] using h)

end VoleMole.Arith
