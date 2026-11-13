import VoleMole.ZK.CollideAd2
import VoleMole.ZK.SharedH3Two

/-!
# One shared `H₃`: an environment's `H₂³` reads against the real two-phase grinding block

`ZK/CollideAd2.lean`'s `pr_tail2A` for the two-phase prover that reads its slice off the shared
tables at its prefix `k` (`ZK/SharedH3Two.lean`), the continuation and the read set reading the
shared tables (rows: the cipher and `H₃`'s columns), possibly the prover's own column.

**`pr_tail2Sh`**: for a continuation `K` (reading `H₅` at `k₅` and the rows at `k_E` keys, not
`H₂³`) and a read set `Qf` (at most `m` keys, read off step 1's output and the shared tables at
`(a₅, a_E)` keys, not off `H₂³`),

    Pr[K continues ∧ Qf meets the real prefix's block]
      ≤ 2⁻¹¹³ + εz(k_E + a_E + k_E, k₅ + a₅ + 312 + k₅, k_E + a_E + 4607 + k_E) + m·2^(−8·16(d−1)).

The proof re-samples the prover's column (`pr_prod_setK`, as `zk2_sharedA`): the tables with the
column at `k` overwritten by an independent slice `G` are uniform, the run then reads `G`, and
`pr_tail2A` applies to the continuation and the read set at the overwritten tables, whose reads of
`G` are row reads (`rd3_setK`).
-/

open Finset

set_option synthInstance.maxSize 1024

set_option linter.unusedSectionVars false

namespace VoleMole.ZK.Sim

open VoleMole.Verifier VoleMole.Verifier.Bridge VoleMole.ZK VoleMole.Privacy

variable {R : Type} [Fintype R] [Nonempty R] [CipherRow R] [ZKRow R] [ZK2ARow R]

/-- **A table-reading environment's `H₂³` reads meet the grinding block of the real two-phase
prover that reads its slice off the shared tables** (one shared `H₃`; the slice argument `a.1.2`
of the probability space is unused). -/
theorem pr_tail2Sh (Hb : Hashes) (st : Statement) (r : ByteArray) (n : ℕ) (k : Pre)
    (K : ShG (RowH R) st.params → Cont2) {k5 kE : ℕ} (hhyp : ∀ s, Hyp2 st r (K s))
    (hsize : r.size = n) (h2 : ∀ (s : ShG (RowH R) st.params) G2, K (G2, s.2) = K s)
    (h5 : ∀ o1, Rd5 (fun s => K s o1) k5) (hE : ∀ o1, RdE (fun s => K s o1) kE)
    (hHb : HashesWF Hb) (hp : SmallParams st.params)
    (Qf : ByteArray × ByteArray → ShG (RowH R) st.params → Finset (K2 st.params))
    (hQ2 : ∀ o1 (s : ShG (RowH R) st.params) (G2 : Tab2G st.params), Qf o1 (G2, s.2) = Qf o1 s)
    {m : ℕ} (hm : ∀ o1 s, (Qf o1 s).card ≤ m) {a5 aE : ℕ}
    (hQ5 : ∀ o1, Rd5 (fun s => Qf o1 s) a5) (hQE : ∀ o1, RdE (fun s => Qf o1 s) aE) :
    pr ((Bytes 16 × Tab3) × ShG (RowH R) st.params) (fun a =>
        (K a.2 (o1R2 Hb st r ((a.1.1, h3At a.2 k), a.2))).isSome ∧
          ∃ κ ∈ Qf (o1R2 Hb st r ((a.1.1, h3At a.2 k), a.2)) a.2,
            κ.1 = blk (preLen st.params) (preR2 Hb st r (fun _ => K) ((a.1.1, h3At a.2 k), a.2))) ≤
      1 / 2 ^ 113 + ZKRow.εz R st.params (kE + aE + kE) (k5 + a5 + 312 + k5) (kE + aE + 4607 + kE) +
        m / 2 ^ (8 * (16 * (st.params.qsDegree - 1))) := by
  have hh' : Hyp2RA st r n (fun G s => K (setK s k G)) kE k5 kE :=
    ⟨fun _ _ => hhyp _, hsize, fun G s G2 => h2 (setK s k G) G2,
      fun o1 s => rd3_setK (hE o1) s k, fun o1 G => rd5_setK (h5 o1) k G,
      fun o1 G => rdE_setK (hE o1) k G⟩
  have h := pr_tail2A (R := RowH R) Hb st r n (fun G s => K (setK s k G)) hh' hHb hp
    (fun o1 G s => Qf o1 (setK s k G)) (fun o1 G s G2 => hQ2 o1 (setK s k G) G2)
    (fun o1 G s => hm _ _) (fun o1 s => rd3_setK (hQE o1) s k) (fun o1 G => rd5_setK (hQ5 o1) k G)
    (fun o1 G => rdE_setK (hQE o1) k G)
  refine le_of_eq_of_le ?_ h
  -- The unused slice marginalized, the column at `k` re-sampled.
  let Φ : Bytes 16 → ShG (RowH R) st.params → Prop := fun ρ s =>
    (K s (o1R2 Hb st r ((ρ, h3At s k), s))).isSome ∧
      ∃ κ ∈ Qf (o1R2 Hb st r ((ρ, h3At s k), s)) s,
        κ.1 = blk (preLen st.params) (preR2 Hb st r (fun _ => K) ((ρ, h3At s k), s))
  let e0 : (Bytes 16 × ShG (RowH R) st.params) × Tab3 ≃ (Bytes 16 × Tab3) × ShG (RowH R) st.params :=
    { toFun := fun z => ((z.1.1, z.2), z.1.2)
      invFun := fun a => ((a.1.1, a.2), a.1.2)
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  let e1 : Bytes 16 × (Tab3 × ShG (RowH R) st.params) ≃ (Bytes 16 × Tab3) × ShG (RowH R) st.params :=
    { toFun := fun z => ((z.1, z.2.1), z.2.2)
      invFun := fun a => (a.1.1, (a.1.2, a.2))
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have hL : pr ((Bytes 16 × Tab3) × ShG (RowH R) st.params) (fun a => Φ a.1.1 a.2) =
      pr (Bytes 16 × ShG (RowH R) st.params) (fun z => Φ z.1 z.2) := by
    rw [← pr_equiv e0]
    exact pr_prod_fst (β := Tab3) (fun z : Bytes 16 × ShG (RowH R) st.params => Φ z.1 z.2)
  refine hL.trans ?_
  rw [← pr_prod_setK (A := Bytes 16) (fun _ => k) Φ, ← pr_equiv e1]
  refine pr_congr fun z => ?_
  simp only [Φ, e1, Equiv.coe_fn_mk, h3At_setK]
  exact Iff.rfl

end VoleMole.ZK.Sim
