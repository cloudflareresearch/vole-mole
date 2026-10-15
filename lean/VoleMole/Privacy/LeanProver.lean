import VoleMole.ZK.Exec
import VoleMole.Privacy.Moussaka
import VoleMole.Privacy.Ratatouille

/-!
# The privacy theorems with the executable Lean prover (`lean/docs/zk.md` §10)

`Privacy/*` take zero knowledge of abstract proof systems as a hypothesis. Here the proof system
is the executable Lean prover (`Verifier/Prover.lean`) with dedicated label rows, and that
hypothesis is discharged by `ZK.Sim.labelRows_zeroKnowledge` (`ZK/Exec.lean`) down to its
remaining hypotheses: the tape hypothesis `TapeHyp` (hybrids H1, H4, H6 and the random-oracle
answers at the grinding points) and the deterministic ones (`ZKHyp`, `BAVCComplete`,
`CrtComplete`).

* `ZeroKnowledge.transfer`: zero knowledge moves along instance, witness and output maps.
* `leanNIZK Hs T stOf`: the Lean prover and verifier as a `Spec.Moussaka.NIZK`, for any
  statement builder `stOf` (the instance's `Verifier.Statement`); `leanSim p`: the simulator.
  `leanNIZK_zeroKnowledge`.
* **`Moussaka.anonymity_lean`**: Theorem 4(a) of `security/moussaka.md` with both proof systems
  the Lean prover: `≤ 4εI + 4εR + 2εhide`, where `εI`, `εR` bound the tape hypotheses of the
  issuance and redemption proofs.
* **`Ratatouille.unlinkability_lean`**: the same for `Privacy.Ratatouille.unlinkability`, for
  primitives whose provers are the Lean prover followed by any fixed encoding of its output into
  the spec's proof type (`Spec.Ratatouille` fixes the proof sizes of `main`; with dedicated label
  rows the proofs are 256 bytes longer, so the encoding is the caller's choice).

PomFRIT's blindness (`Privacy.PomFRIT.blindness`) needs two-phase zero knowledge with a delayed,
adaptively chosen instance (`Privacy.PomFRIT.ZeroKnowledge`); `labelRows_zeroKnowledge` is for a
fixed statement whose constraints the witness satisfies for every `chal1`, which PomFRIT's
instance `h = hash_to_target(…, chal1, …)` violates. That case remains on paper (zk.md §7.5).
-/

open Finset

namespace VoleMole.Privacy

/-- **Zero knowledge moves along instance, witness and output maps.** -/
theorem ZeroKnowledge.transfer {I I' W W' ρ C O O' : Type*} [Fintype ρ] [Fintype C]
    {R : I → W → Prop} {R' : I' → W' → Prop} {prove : I → W → ρ → O} {sim : I → C → O} {ε : ℝ}
    (h : ZeroKnowledge R prove sim ε) (fI : I' → I) (fW : I' → W' → W)
    (hR : ∀ x w, R' x w → R (fI x) (fW x w)) (φ : O → O') :
    ZeroKnowledge R' (fun x w r => φ (prove (fI x) (fW x w) r)) (fun x c => φ (sim (fI x) c)) ε :=
  fun x w hxw => (h _ _ (hR x w hxw)).map φ

open VoleMole.Verifier VoleMole.Verifier.Bridge VoleMole.ZK.Sim VoleMole.Arith

/-- The tape of `ρ`, as the spec passes it. -/
lemma toBA_ofFn (ρ : Coins 16) : toBA (List.ofFn ρ) = ba ρ := by
  simp only [toBA, ba, List.toArray_ofFn]

/-- Zero knowledge of the Lean prover on byte-list witnesses, from `labelRows_zeroKnowledge`. -/
theorem lean_zeroKnowledge {I : Type*} (Hs : Hashes) (T : CrtTables) (stOf : I → Statement)
    (p : Params) (hp : ∀ x, (stOf x).params = p) (hlr : p.labelRows = true)
    {W : Type*} (enc : I → W → ByteArray) (R : I → W → Prop)
    (cs : I → ByteArray → ByteArray → System GF128)
    (h : ∀ x w, R x w → ZKHyp T (stOf x) (enc x w) (cs x)) (hHs : HashesWF Hs)
    (hbavc : BAVCComplete)
    (hcrt : ∀ x w, R x w → ∀ rho : ByteArray, CrtComplete (Hs.hash .h5) T (Prover.voleGen Hs T
      (stOf x).params ((stOf x).mu1 Hs) ((enc x w).extract 0 (stOf x).params.witnessBytes) rho
      (stOf x).binder1))
    {ε : ℝ} (ht : ∀ x w, R x w → TapeHyp Hs T (stOf x) (enc x w) ε) :
    ZeroKnowledge R (fun x w (ρ : Coins 16) => Prover.prove Hs T (stOf x) (enc x w) (ba ρ))
      (fun _ c => simulate p c) ε := by
  intro x w hxw
  exact labelRows_zeroKnowledge Hs T stOf p hp hlr (fun x w' => ∃ w, R x w ∧ enc x w = w') cs
    (fun x _ ⟨w, hw, e⟩ => by subst e; exact h x w hw) hHs hbavc
    (fun x _ ⟨w, hw, e⟩ => by subst e; exact hcrt x w hw)
    (fun x _ ⟨w, hw, e⟩ => by subst e; exact ht x w hw) x (enc x w) ⟨w, hxw, rfl⟩

/-! ## Moussaka -/

namespace Moussaka

open VoleMole.Spec VoleMole.Spec.Moussaka

/-- The Lean prover (and verifier) as an abstract `NIZK`, for a statement builder `stOf`; a
failed run (grinding overflow, or a witness that does not satisfy the constraints) gives the empty
proof. -/
def leanNIZK {I : Type} (Hs : Hashes) (T : CrtTables) (stOf : I → Statement) : NIZK I where
  prove w x rho := toL ((Prover.prove Hs T (stOf x) (toBA w) (toBA rho)).toOption.getD .empty)
  verify pf x := (verify Hs T (stOf x) (toBA pf)).accept

/-- The simulator, as the spec's proofs. -/
def leanSim (p : Params) {I : Type} (_ : I) (c : SimCoins p) : Bytes :=
  toL ((simulate p c).toOption.getD .empty)

/-- **Zero knowledge of `leanNIZK`** (`Privacy.ZeroKnowledge` with the spec's uniform `rho`). -/
theorem leanNIZK_zeroKnowledge {I : Type} (Hs : Hashes) (T : CrtTables) (stOf : I → Statement)
    (p : Params) (hp : ∀ x, (stOf x).params = p) (hlr : p.labelRows = true)
    (R : I → Bytes → Prop) (cs : I → ByteArray → ByteArray → System GF128)
    (h : ∀ x w, R x w → ZKHyp T (stOf x) (toBA w) (cs x)) (hHs : HashesWF Hs)
    (hbavc : BAVCComplete)
    (hcrt : ∀ x w, R x w → ∀ rho : ByteArray, CrtComplete (Hs.hash .h5) T (Prover.voleGen Hs T
      (stOf x).params ((stOf x).mu1 Hs) ((toBA w).extract 0 (stOf x).params.witnessBytes) rho
      (stOf x).binder1))
    {ε : ℝ} (ht : ∀ x w, R x w → TapeHyp Hs T (stOf x) (toBA w) ε) :
    ZeroKnowledge R (proveR (leanNIZK Hs T stOf)) (leanSim p) ε := by
  have := (lean_zeroKnowledge Hs T stOf p hp hlr (fun _ w => toBA w) R cs h hHs hbavc hcrt
    ht).transfer id (fun _ w => w) (fun _ _ hw => hw) (fun o => toL (o.toOption.getD .empty))
  refine fun x w hxw => (this x w hxw).congr (fun ρ => ?_) fun _ => rfl
  simp only [proveR, leanNIZK, toBA_ofFn, id]

/-- **Moussaka issuer hiding and unlinkability with the Lean prover** (Theorem 4(a)): for any
statement builders `stI`, `stR` with dedicated label rows whose witnesses satisfy the deterministic
hypotheses, if the issuance and redemption runs' tapes are `εI`- and `εR`-close to uniform
(`TapeHyp`) and the hiding reductions have advantage `≤ εhide`, the two worlds differ by at most
`4εI + 4εR + 2εhide`. -/
theorem anonymity_lean (A : Adversary) (idx : AnchorSet → UOVKey → ℕ) (Hs : Hashes) (T : CrtTables)
    (stI : IssueInstance → Statement) (stR : RedeemInstance → Statement) (pI pR : Params)
    (hpI : ∀ x, (stI x).params = pI) (hpR : ∀ x, (stR x).params = pR)
    (hlrI : pI.labelRows = true) (hlrR : pR.labelRows = true)
    (csI : IssueInstance → ByteArray → ByteArray → System GF128)
    (csR : RedeemInstance → ByteArray → ByteArray → System GF128)
    (hI : ∀ x w, IssueRel x w → ZKHyp T (stI x) (toBA w) (csI x))
    (hR : ∀ x w, RedeemRel x w → ZKHyp T (stR x) (toBA w) (csR x))
    (hHs : HashesWF Hs) (hbavc : BAVCComplete)
    (hcrtI : ∀ x w, IssueRel x w → ∀ rho : ByteArray, CrtComplete (Hs.hash .h5) T
      (Prover.voleGen Hs T (stI x).params ((stI x).mu1 Hs)
        ((toBA w).extract 0 (stI x).params.witnessBytes) rho (stI x).binder1))
    (hcrtR : ∀ x w, RedeemRel x w → ∀ rho : ByteArray, CrtComplete (Hs.hash .h5) T
      (Prover.voleGen Hs T (stR x).params ((stR x).mu1 Hs)
        ((toBA w).extract 0 (stR x).params.witnessBytes) rho (stR x).binder1))
    {εI εR εhide : ℝ} (hεR : 0 ≤ εR)
    (htI : ∀ x w, IssueRel x w → TapeHyp Hs T (stI x) (toBA w) εI)
    (htR : ∀ x w, RedeemRel x w → TapeHyp Hs T (stR x) (toBA w) εR)
    (hhide : ∀ b c, hidingAdv A.ci A.cr
      (reduction A idx (leanSim pI) (leanSim pR) b c) ≤ εhide) :
    |pr _ (realGame A idx (leanNIZK Hs T stI) (leanNIZK Hs T stR) false) -
        pr _ (realGame A idx (leanNIZK Hs T stI) (leanNIZK Hs T stR) true)| ≤
      4 * εI + 4 * εR + 2 * εhide :=
  anonymity A idx (leanSim pI) (leanSim pR) (leanNIZK Hs T stI) (leanNIZK Hs T stR) hεR
    (leanNIZK_zeroKnowledge Hs T stI pI hpI hlrI IssueRel csI hI hHs hbavc hcrtI htI)
    (leanNIZK_zeroKnowledge Hs T stR pR hpR hlrR RedeemRel csR hR hHs hbavc hcrtR htR) hhide

end Moussaka

/-! ## Ratatouille -/

namespace Ratatouille

open VoleMole.Spec.Ratatouille

variable {SK : Type}

/-- **Ratatouille unlinkability with the Lean prover** (Theorem 2): for primitives whose provers
are the Lean prover on statements `stI`, `stS` with dedicated label rows, followed by fixed
encodings `φI`, `φS` of its output into the spec's proof types (`hPI`, `hPS`), the worlds differ by
at most `4εI + 4εS + 2εhide` with `εI`, `εS` the tape hypotheses' errors. -/
theorem unlinkability_lean (A : Adversary) (P : Prim SK) (Hs : Hashes) (T : CrtTables)
    (stI : IssueInstance → Statement) (stS : SpendInstance → Statement) (pI pS : Params)
    (hpI : ∀ x, (stI x).params = pI) (hpS : ∀ x, (stS x).params = pS)
    (hlrI : pI.labelRows = true) (hlrS : pS.labelRows = true)
    (encI : IssueInstance → IssueWitness → ByteArray)
    (encS : SpendInstance → SpendWitness → ByteArray)
    (φI : Except String ByteArray → Option IssueProof)
    (φS : Except String ByteArray → Option SpendProof)
    (hPI : ∀ x w (ρ : Coins 16), P.proveIssue x w (vec ρ) =
      φI (Prover.prove Hs T (stI x) (encI x w) (ba ρ)))
    (hPS : ∀ x w (ρ : Coins 16), P.proveSpend x w (vec ρ) =
      φS (Prover.prove Hs T (stS x) (encS x w) (ba ρ)))
    (csI : IssueInstance → ByteArray → ByteArray → System GF128)
    (csS : SpendInstance → ByteArray → ByteArray → System GF128)
    (hI : ∀ x w, IssueRel x w → ZKHyp T (stI x) (encI x w) (csI x))
    (hS : ∀ x w, SpendRel x w → ZKHyp T (stS x) (encS x w) (csS x))
    (hHs : HashesWF Hs) (hbavc : BAVCComplete)
    (hcrtI : ∀ x w, IssueRel x w → ∀ rho : ByteArray, CrtComplete (Hs.hash .h5) T
      (Prover.voleGen Hs T (stI x).params ((stI x).mu1 Hs)
        ((encI x w).extract 0 (stI x).params.witnessBytes) rho (stI x).binder1))
    (hcrtS : ∀ x w, SpendRel x w → ∀ rho : ByteArray, CrtComplete (Hs.hash .h5) T
      (Prover.voleGen Hs T (stS x).params ((stS x).mu1 Hs)
        ((encS x w).extract 0 (stS x).params.witnessBytes) rho (stS x).binder1))
    {εI εS εhide : ℝ} (hεI : 0 ≤ εI) (hεS : 0 ≤ εS)
    (htI : ∀ x w, IssueRel x w → TapeHyp Hs T (stI x) (encI x w) εI)
    (htS : ∀ x w, SpendRel x w → TapeHyp Hs T (stS x) (encS x w) εS)
    (hhide : ∀ b₁ b₂ co, hidingAdv A.ctx (reduction A (fun _ c => φI (simulate pI c))
      (fun _ c => φS (simulate pS c)) b₁ b₂ co) ≤ εhide)
    (b₁ b₂ b₁' b₂' : Bool) :
    |pr _ (realGame A P b₁ b₂) - pr _ (realGame A P b₁' b₂')| ≤ 4 * εI + 4 * εS + 2 * εhide := by
  have zI := (lean_zeroKnowledge Hs T stI pI hpI hlrI encI IssueRel csI hI hHs hbavc hcrtI
    htI).transfer id (fun _ w => w) (fun _ _ hw => hw) φI
  have zS := (lean_zeroKnowledge Hs T stS pS hpS hlrS encS SpendRel csS hS hHs hbavc hcrtS
    htS).transfer id (fun _ w => w) (fun _ _ hw => hw) φS
  refine unlinkability A (fun _ c => φI (simulate pI c)) (fun _ c => φS (simulate pS c)) P hεI hεS
    (fun x w hxw => (zI x w hxw).congr (fun ρ => ?_) fun _ => rfl)
    (fun x w hxw => (zS x w hxw).congr (fun ρ => ?_) fun _ => rfl) hhide b₁ b₂ b₁' b₂'
  · simp only [proveI, hPI, id]
  · simp only [proveS, hPS, id]

end Ratatouille

end VoleMole.Privacy
