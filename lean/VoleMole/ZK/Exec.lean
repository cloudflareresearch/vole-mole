import VoleMole.ZK.IdealSim
import VoleMole.ZK.TapeOf

/-!
# Zero knowledge of the executable prover (`lean/docs/zk.md` §§5–6, §10)

The executable Lean prover (`Verifier/Prover.lean`, which reproduces the C++ proofs byte for byte)
against the simulator `Sim.simulate` (`ZK/Sim.lean`):

* **`zk_reduction`** (no probabilistic hypothesis): for every distinguisher `D`, the advantage
  of `D` between real proofs (uniform `rho`) and simulated proofs is *equal* to its advantage
  between the real run's tape `tapeOf … rho` and a uniform ideal tape, seen through the
  ideal-tape prover. This composes `prove_eq_proveIdeal` (`ZK/TapeOf.lean`: the real prover is the
  ideal-tape prover at its own tape) and `proveIdeal_close` (`ZK/IdealSim.lean`: on a uniform tape,
  the ideal-tape prover's output is distributed as the simulator's; hybrids H2, H5–H7).
* `TapeHyp Hs T st w ε`: the real run's tape is `ε`-close to uniform, against distinguishers that
  see it through the ideal-tape prover. **This is the hypothesis of the remaining hops**: H1 (the
  seed and `iv_pre` from `H₃` are uniform), H4 (the hidden leaves' PRG outputs, the root's
  `u_hi`, the hidden commitments and the opened seeds are uniform: AES as a PRP, GGM), H6 (the
  `H₅` answers at the sibling labels are uniform and independent of everything the distinguisher
  sees: identical until a query hits a sibling label) and the random-oracle answers at the
  grinding points (H2's freshness of `chal2`). `TapeHyp` follows from the tape statement
  `Close ε (tapeOf …) id` (`tapeHyp_of_close`). As every statement against all distinguishers in
  `Privacy/Basic.lean`, it is an idealization: with a fixed hash record it holds only for
  distinguishers that cannot invert AES or find the sibling labels (on paper: `ε_rho + ε_prog +
  2·ε_hide + ε_lab`, zk.md §3). With dedicated label rows the label offset is uniform and
  independent of the ideal-tape proof (`Sim.prove_guess_theta`), which is what makes the H6 part
  hold; on `main` it fails (`ZK.pomfrit_attack_test`).
* **`labelRows_zeroKnowledge`**: `Privacy.ZeroKnowledge` for a family of statements with dedicated
  label rows, from `TapeHyp` and the deterministic hypotheses.
* `simulateRO_accept` (`ZK/SimAccept.lean`): the verifier, with `H₂³` programmed by
  `Sim.simulateRO`, accepts the simulated proof whenever its run reaches `chal3`.

Deterministic hypotheses (`ZKHyp`, `BAVCComplete`, `CrtComplete`): the statement's evaluator is a
system of degree `≤ d` that the witness satisfies for every `chal1` and combination (not PomFRIT,
whose instance depends on `chal1`: its two-phase zero knowledge `Privacy.PomFRIT.ZeroKnowledge`
is not covered); `N_MASK ≤ 32`; the CRT certificate (`maskInvOk_tables`); correct
interpolation (`InterpOk d`); and the two correctness facts the completeness theorem assumes.
-/

open Finset

namespace VoleMole.ZK.Sim

open VoleMole.Verifier VoleMole.Verifier.Bridge VoleMole.Arith VoleMole.ZK VoleMole.Privacy

variable (Hs : Hashes) (T : CrtTables) (st : Statement) (w : ByteArray)

/-- **The tape hypothesis**: the real run's tape, seen through the ideal-tape prover, is
`ε`-close to a uniform ideal tape (hybrids H1, H4, H6 and the random-oracle answers at the
grinding points). -/
def TapeHyp (ε : ℝ) : Prop :=
  Close ε (fun ρ : Bytes 16 => proveIdeal Hs T st w (tapeOf Hs T st w (ba ρ)))
    (proveIdeal Hs T st w)

/-- The tape statement implies the tape hypothesis. -/
theorem tapeHyp_of_close {ε : ℝ}
    (h : Close ε (fun ρ : Bytes 16 => tapeOf Hs T st w (ba ρ)) (id : IdealTape st.params → _)) :
    TapeHyp Hs T st w ε :=
  h.map (proveIdeal Hs T st w)

/-- The deterministic hypotheses, for every `rho`. -/
structure RunHyp (cs : ByteArray → ByteArray → System GF128) : Prop where
  zk : ZKHyp T st w cs
  hHs : HashesWF Hs
  hbavc : BAVCComplete
  hcrt : ∀ rho : ByteArray, CrtComplete (Hs.hash .h5) T (Prover.voleGen Hs T st.params (st.mu1 Hs)
    (w.extract 0 st.params.witnessBytes) rho st.binder1)
  hlab : st.params.labelRowOffset + 128 ≤ st.params.correctionRows

lemma ZKHyp.q {cs : ByteArray → ByteArray → System GF128} (h : ZKHyp T st w cs) :
    ZKHypQ st w cs :=
  ⟨h.hvals, h.hdeg, h.hd, h.hd', h.hsat, h.hw, h.hI⟩

/-- **The reduction**: the zero-knowledge advantage of any distinguisher equals its tape
advantage (no probabilistic hypothesis). -/
theorem zk_reduction {cs : ByteArray → ByteArray → System GF128} (h : RunHyp Hs T st w cs)
    (D : Except String ByteArray → Prop) :
    |pr (Bytes 16) (fun ρ => D (Prover.prove Hs T st w (ba ρ))) -
        pr (SimCoins st.params) (fun c => D (simulate st.params c))| =
      |pr (Bytes 16) (fun ρ => D (proveIdeal Hs T st w (tapeOf Hs T st w (ba ρ)))) -
        pr (IdealTape st.params) (fun t => D (proveIdeal Hs T st w t))| := by
  have h1 : ∀ ρ : Bytes 16, Prover.prove Hs T st w (ba ρ) =
      proveIdeal Hs T st w (tapeOf Hs T st w (ba ρ)) := fun ρ =>
    prove_eq_proveIdeal Hs T st w (ba ρ) cs h.zk.q h.hHs h.hbavc (h.hcrt _) h.hlab
  have h2 := proveIdeal_close Hs T st w cs h.zk D
  rw [abs_nonpos_iff, sub_eq_zero] at h2
  simp only [h1, h2]

/-- **Zero knowledge of the executable prover from the tape hypothesis.** -/
theorem prove_close {cs : ByteArray → ByteArray → System GF128} (h : RunHyp Hs T st w cs) {ε : ℝ}
    (ht : TapeHyp Hs T st w ε) :
    Close ε (fun ρ : Bytes 16 => Prover.prove Hs T st w (ba ρ)) (simulate st.params) := by
  intro D
  have e := zk_reduction Hs T st w h D
  have ht' := ht D
  dsimp only at ht' ⊢
  rw [e]
  exact ht'

lemma close_params {α : Type*} [Fintype α] {ε : ℝ} {X : α → Except String ByteArray}
    {p q : Params} (e : p = q) (h : Close ε X (simulate p)) : Close ε X (simulate q) := by
  subst e; exact h

/-- **Zero knowledge in the sense of `Privacy.ZeroKnowledge`**, for a family of statements `stOf`
with dedicated label rows and fixed parameters `p`, a relation `R` whose witnesses satisfy the
deterministic hypotheses, and the tape hypothesis with error `ε`. The simulator `simulate p` reads
neither the witness nor the instance (the instance only enters through the programmed oracle,
`simulateRO`). -/
theorem labelRows_zeroKnowledge {I : Type*} (stOf : I → Statement) (p : Params)
    (hp : ∀ x, (stOf x).params = p) (hlr : p.labelRows = true) (R : I → ByteArray → Prop)
    (cs : I → ByteArray → ByteArray → System GF128)
    (h : ∀ x w, R x w → ZKHyp T (stOf x) w (cs x)) (hHs : HashesWF Hs) (hbavc : BAVCComplete)
    (hcrt : ∀ x w, R x w → ∀ rho : ByteArray, CrtComplete (Hs.hash .h5) T (Prover.voleGen Hs T
      (stOf x).params ((stOf x).mu1 Hs) (w.extract 0 (stOf x).params.witnessBytes) rho
      (stOf x).binder1))
    {ε : ℝ} (ht : ∀ x w, R x w → TapeHyp Hs T (stOf x) w ε) :
    ZeroKnowledge R (fun x w (ρ : Bytes 16) => Prover.prove Hs T (stOf x) w (ba ρ))
      (fun _ c => simulate p c) ε := by
  intro x w hxw
  have hlab : (stOf x).params.labelRowOffset + 128 ≤ (stOf x).params.correctionRows := by
    rw [hp x]; simp [Params.labelRowOffset, Params.correctionRows, hlr]
  exact close_params (hp x)
    (prove_close Hs T (stOf x) w ⟨h x w hxw, hHs, hbavc, hcrt x w hxw, hlab⟩ (ht x w hxw))

end VoleMole.ZK.Sim
