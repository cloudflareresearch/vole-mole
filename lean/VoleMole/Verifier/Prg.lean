import VoleMole.Verifier.AES

/-!
# The CTR PRG of the BAVC and the VOLE expansion, as a parameter

The BAVC (`BAVC.children`, `BAVC.leafCom`), the small VOLEs (`prgWords`) and the root PRG's `u_hi`
(`Prover.uMaskOf`) call one function, faest-arch-opt's AES-CTR PRG `AES.prg key iv tweak counter n`
(`n` blocks). They call it through the class `HasPrg`, whose only global instance is AES (`aesPrg`),
so the executable verifier and prover are unchanged: every executable call site resolves the
instance to `AES.prg`.

The class exists for the proofs: a statement made for any instance holds for every PRG of the right
output length, in particular for the ideal-cipher PRG of `ZK/HopsH4.lean` (`icPrg E`: the CTR PRG
with the cipher a table `E`), which is how the ideal-cipher model of hop H4 replaces AES in the
whole prover and verifier (`lean/docs/zk.md` §10.1, `ZK/HopsIC.lean`).
-/

namespace VoleMole.Verifier

/-- **The CTR PRG** `prg key iv tweak counter n` (`n` blocks of 16 bytes) that the BAVC and the
VOLE expansion call. The executable code uses AES (`aesPrg`). -/
class HasPrg where
  prg : ByteArray → ByteArray → UInt32 → UInt32 → Nat → ByteArray
  /-- The output has `16 n` bytes. -/
  prg_size : ∀ (key iv : ByteArray) (t c : UInt32) (n : Nat), (prg key iv t c n).size = 16 * n

namespace AES

private theorem pushLE32_size' (b : ByteArray) (x : UInt32) : (pushLE32 b x).size = b.size + 4 := by
  simp only [pushLE32, ByteArray.size_push]

private theorem encrypt_size' (rk pt : ByteArray) : (encrypt rk pt).size = 16 := by
  unfold encrypt
  simp only [Id.run]
  show (pushLE32 (pushLE32 (pushLE32 (pushLE32 (ByteArray.emptyWithCapacity 16) _) _) _) _).size = 16
  rw [pushLE32_size', pushLE32_size', pushLE32_size', pushLE32_size']
  rfl

private theorem prgExpanded_eq' (rk iv : ByteArray) (t c : UInt32) (n : Nat) :
    prgExpanded rk iv t c n = (List.range n).foldl
      (fun out j => out ++ encrypt rk (ctrBlock iv (c + j.toUInt32) t))
      (ByteArray.emptyWithCapacity (16 * n)) := by
  simp [prgExpanded, Std.Legacy.Range.forIn_eq_forIn_range', List.range_eq_range',
    Std.Legacy.Range.size]

private theorem foldl_encrypt_size (rk iv : ByteArray) (t c : UInt32) :
    ∀ (l : List Nat) (o : ByteArray), (l.foldl (fun out j =>
      out ++ encrypt rk (ctrBlock iv (c + j.toUInt32) t)) o).size = o.size + 16 * l.length
  | [], o => by simp
  | j :: l, o => by
    rw [List.foldl_cons, foldl_encrypt_size rk iv t c l, ByteArray.size_append, encrypt_size']
    simp only [List.length_cons]
    omega

/-- The AES-CTR PRG's output has `16 n` bytes. -/
theorem prg_size_aes (key iv : ByteArray) (t c : UInt32) (n : Nat) :
    (prg key iv t c n).size = 16 * n := by
  rw [prg, prgExpanded_eq', foldl_encrypt_size, List.length_range]
  show 0 + 16 * n = 16 * n
  omega

end AES

/-- **AES-CTR, the executable PRG.** -/
instance aesPrg : HasPrg := ⟨AES.prg, AES.prg_size_aes⟩

end VoleMole.Verifier
