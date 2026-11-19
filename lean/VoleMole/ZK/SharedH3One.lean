import VoleMole.ZK.SharedH3Two

/-!
# The shared provers are the executable prover with one `H₃`

`ZK/SharedH3.lean` gives a proof its slice as the column of the shared tables at its prefix
(`h3At s (preKey (wPrefix ‖ μ₁))`) and runs the executable prover with the record whose `H₃`
answers the proof's seed inputs from that slice (`recHp`). Here the record is the one the scheme
has: **one** `H₃` table on **every** seed input `x ‖ ρ ‖ 3` with `|x| < preMax`, `|ρ| = 16`
(`recOne`, answered by `H₃(x ‖ ρ ‖ 3) = h3At s (preKey x) ρ`), the same `H₂³` and `H₅` tables; and
the executable prover with that record is the shared prover (`prove_recOne`).

* `seedEnc` (the seed input of a prefix and a `ρ`) is injective (`seedEnc_injective`), so `recOne`
  is a table of `H₃` indexed by its inputs: uniform shared tables give a uniform `H₃` on the seed
  inputs, one value per input, the same for every proof.
* `prove_recOne`: for every statement, witness and 16-byte `rho` with a prefix of fewer than
  `preMax` bytes, `Prover.prove` with `recOne` is `realROb` with the slice at the proof's prefix.
-/

open Finset

set_option synthInstance.maxSize 1024

set_option linter.unusedSectionVars false

namespace VoleMole.ZK.Sim

open VoleMole.Verifier VoleMole.Verifier.Bridge VoleMole.ZK VoleMole.Privacy

/-- The bytes of a prefix. -/
def preBytes (k : Pre) : ByteArray := ⟨Array.ofFn k.2⟩

lemma preBytes_size (k : Pre) : (preBytes k).size = k.1 := by
  simp [preBytes, ByteArray.size]

lemma preBytes_eq_ba (k : Pre) : preBytes k = ba k.2 := rfl

lemma preBytes_preKey {b : ByteArray} (hb : b.size < preMax) : preBytes (preKey b) = b := by
  rw [preKey_def, dite_eq_left_of_eq_true (eq_true hb)]
  refine byteArray_ext_get! (by rw [preBytes_size]) fun k hk => ?_
  rw [preBytes_size] at hk
  rw [preBytes_eq_ba, get!_ba _ hk]

lemma preBytes_injective : Function.Injective preBytes := by
  rintro ⟨n, f⟩ ⟨m, g⟩ h
  have hs : n = m := Fin.ext (by
    have := congrArg ByteArray.size h
    rwa [preBytes_size, preBytes_size] at this)
  subst hs
  have hd : Array.ofFn f = Array.ofFn g := congrArg ByteArray.data h
  have hfg : f = g := by
    funext i
    have := congrArg (fun a : Array UInt8 => a[i.1]?) hd
    simpa using this
  rw [hfg]

/-- **The seed input of a prefix and a `ρ`**: `x ‖ ρ ‖ 3`. -/
def seedEnc (a : Pre × Bytes 16) : ByteArray := (preBytes a.1 ++ ba a.2).push 3

lemma seedEnc_injective : Function.Injective seedEnc := by
  rintro ⟨k, ρ⟩ ⟨k', ρ'⟩ h
  have hρ : ρ = ρ' := eq_of_seed_eq h
  subst hρ
  have h1 : preBytes k ++ ba ρ = preBytes k' ++ ba ρ := push_injective 3 h
  have h2 : (preBytes k).data.toList ++ (ba ρ).data.toList =
      (preBytes k').data.toList ++ (ba ρ).data.toList := by
    have := congrArg (fun z : ByteArray => z.data.toList) h1
    simpa [ByteArray.data_append] using this
  have h3 : preBytes k = preBytes k' :=
    ByteArray.ext (Array.ext' (List.append_cancel_right h2))
  rw [preBytes_injective h3]

variable {R : Type} [CipherRow R] {p : Params}

/-- **The record with one `H₃`**: `H₃` on every seed input of a short prefix answered by the
shared tables' columns, `H₂³` and `H₅` the shared tables, every other domain `Hb`'s. -/
noncomputable def recOne (p : Params) (Hb : Hashes) (s : ShG (RowH R) p) : Hashes :=
  ((Hb.withTable .h3 seedEnc fun a => h3At s a.1 a.2).withTable .h23 (enc2 p) s.1).withTable .h5
    enc5 s.2.1

variable {Hb : Hashes} {st : Statement} {w : ByteArray}

lemma recOne_mu1 (s : ShG (RowH R) p) : st.mu1 (recOne p Hb s) = st.mu1 Hb := by
  have h1 : (recOne p Hb s).hash .mu = Hb.hash .mu := by
    funext x; simp only [recOne, Hashes.withTable, reduceCtorEq, ite_false]
  have h2 : (recOne p Hb s).hash .muDelayed = Hb.hash .muDelayed := by
    funext x; simp only [recOne, Hashes.withTable, reduceCtorEq, ite_false]
  simp only [Statement.mu1, VoleMole.Verifier.mu, h1, h2]

lemma recOne_h3 (s : ShG (RowH R) p) :
    (recOne p Hb s).hash .h3 = (Hb.withTable .h3 seedEnc fun a => h3At s a.1 a.2).hash .h3 := by
  funext x
  simp only [recOne, Hashes.withTable, reduceCtorEq, ite_false]

lemma recOne_agreeOff (s : ShG (RowH R) st.params) (G3 : Tab3) :
    (recOne st.params Hb s).AgreeOff .h3 (recHp st.params Hb st w G3 s.1 s.2.1) := by
  intro k hk
  funext x
  by_cases h5 : k = .h5
  · subst h5; simp only [recOne, recHp, Hashes.withTable, reduceCtorEq, ite_true, ite_false]
  by_cases h23 : k = .h23
  · subst h23; simp only [recOne, recHp, Hashes.withTable, reduceCtorEq, ite_true, ite_false]
    split <;> rfl
  · simp only [recOne, recHp, Hashes.withTable, h5, h23, hk, ite_false]

/-- **The executable prover with one `H₃` is the shared prover**: with the record `recOne` (one
`H₃` table for every proof), the prover's output is `realROb` with the slice of the shared tables
at its prefix `wPrefix ‖ μ₁`, for every statement, witness and 16-byte `rho` (the prefix shorter
than `preMax`). -/
theorem prove_recOne (s : ShG (RowH R) st.params) (rho : ByteArray) (hρ : rho.size = 16)
    (hk : (w.extract 0 st.params.witnessBytes ++ st.mu1 Hb).size < preMax) :
    @Prover.prove (icPrg (rowFn s.2.2)) (recOne st.params Hb s) CrtGen.tables st w rho
        st.params.witnessBytes =
      realROb st.params Hb st w rho
        (h3At s (preKey (w.extract 0 st.params.witnessBytes ++ st.mu1 Hb))) s := by
  unfold realROb
  refine @prove_h3_congr (icPrg (rowFn s.2.2)) _ _ (recOne_agreeOff s _) _ _ _ _ _ ?_
  rw [recOne_mu1, recOne_h3, recHp_h3]
  set k := preKey (w.extract 0 st.params.witnessBytes ++ st.mu1 Hb)
  have e1 : (w.extract 0 st.params.witnessBytes ++ st.mu1 Hb ++ rho).push 3 = seedEnc (k, blk 16 rho) := by
    simp only [seedEnc, k, preBytes_preKey hk, ba_blk_of_size hρ]
  have e2 : (w.extract 0 st.params.witnessBytes ++ st.mu1 Hb ++ rho).push 3 =
      seedInput (st.mu1 Hb) (w.extract 0 st.params.witnessBytes) (blk 16 rho) := by
    simp only [seedInput, ba_blk_of_size hρ]
  have l := Hashes.withTable_enc Hb .h3 seedEnc (fun a => h3At s a.1 a.2) (k, blk 16 rho)
  have r := Hashes.withTable_enc Hb .h3 (seedInput (st.mu1 Hb) (w.extract 0 st.params.witnessBytes))
    (h3At s k) (blk 16 rho)
  rw [keyOf_eq seedEnc_injective] at l
  rw [keyOf_eq (seedInput_injective _ _)] at r
  rw [← e1] at l
  rw [← e2] at r
  exact l.trans r.symm

end VoleMole.ZK.Sim
