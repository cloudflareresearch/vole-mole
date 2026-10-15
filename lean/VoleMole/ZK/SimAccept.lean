import VoleMole.ZK.Sim
import VoleMole.Verifier.Bridge.Prover

/-!
# The verifier accepts simulated proofs under the programmed oracle (`lean/docs/zk.md` §5, H8)

`Sim.simulateRO` returns the simulated proof and the hashes `Hs` with `H₂³` programmed at the
proof's grinding points (`Sim.program`, `Sim.programPoints`). Here:

* `program_hash_ne`: the programmed record answers every query outside `H₂³` as `Hs` does.
* `Reaches Hs T st proof`: the verifier's run with `Hs` gets to `chal3` (`check_format` passes,
  the opening reconstructs, the lifted `Δ` is nonzero).
* `verify_program_accept`: **if the run with `Hs` reaches `chal3`, the run with the programmed
  record accepts.** Nothing about the proof is assumed beyond that: the programmed record agrees
  with `Hs` before `chal3`, so the verifier recomputes the same `chal2` and `qs_check`, and `chal3`
  is the programmed `Δ`.
* `simulateRO_accept`: the same for `simulateRO`'s proof and record. That a simulated proof's
  run reaches `chal3` (`check_format` passes, the sampled opening reconstructs: `BAVC.reconstruct`
  reads exactly `openCount Δ` seeds and zero padding) is checked by `lake exe zk_sim`, not proved;
  `Δ' ≠ 0` fails with probability `2⁻¹²⁰` for the real prover as well.
-/

namespace VoleMole.ZK.Sim

open VoleMole.Verifier VoleMole.Verifier.Bridge VoleMole.Arith

theorem program_hash_ne (Hs : Hashes) (pts : List (ByteArray × ByteArray)) {k : Kind}
    (hk : k ≠ .h23) (x : ByteArray) : (program Hs pts).hash k x = Hs.hash k x := by
  simp [program, hk]

theorem program_hash_head (Hs : Hashes) (x y : ByteArray) (rest : List (ByteArray × ByteArray)) :
    (program Hs ((x, y) :: rest)).hash .h23 x = y := by
  have hx : (x == x) = true := (byteArray_beq_iff x x).2 rfl
  simp [program, List.find?_cons, hx]

theorem program_hash_head' (Hs : Hashes) {x' x y : ByteArray} (rest : List (ByteArray × ByteArray))
    (h : x' = x) : (program Hs ((x, y) :: rest)).hash .h23 x' = y := h ▸ program_hash_head Hs x y rest

/-- The verifier's run with `Hs` gets to `chal3`. -/
def Reaches (Hs : Hashes) (T : CrtTables) (st : Statement) (proof : ByteArray) : Prop :=
  let pf : Proof := { params := st.params, bytes := proof }
  let iv := ivOf Hs pf (st.mu1 Hs)
  pf.checkFormat = true ∧ ∃ leaves, BAVC.reconstruct iv pf.opening pf.delta = some leaves ∧
    (crtReconstruct Hs pf T iv (convertToVole pf iv leaves)).deltaLifted.toGF ≠ 0

/-- The transcript of a run that reaches `chal3`. -/
theorem verify_reaches (Hs : Hashes) (T : CrtTables) (st : Statement) (proof : ByteArray)
    (pf : Proof) (hpf : pf = { params := st.params, bytes := proof }) (leaves : BAVC.Leaves)
    (hf : pf.checkFormat = true)
    (hl : BAVC.reconstruct (ivOf Hs pf (st.mu1 Hs)) pf.opening pf.delta = some leaves)
    (hΔ : (crtReconstruct Hs pf T (ivOf Hs pf (st.mu1 Hs))
      (convertToVole pf (ivOf Hs pf (st.mu1 Hs)) leaves)).deltaLifted.toGF ≠ 0) :
    let mu1 := st.mu1 Hs
    let iv := ivOf Hs pf mu1
    let c1 := chal1 Hs pf mu1 (BAVC.check (Hs.hash .h1) leaves.coms) st.binder1
    let crt := crtReconstruct Hs pf T iv (convertToVole pf iv leaves)
    let deltaL := crt.deltaLifted.toGF
    let hV := voleHashReceiver st.params c1 crt.rows crt.qMask deltaL pf.voleCheck
    let c2 := chal2 Hs pf c1 hV (st.muDelayed Hs c1) st.binder2
    let cs := constraintKeys st.params (correctedKeys pf crt.rows deltaL) deltaL
      (st.values c1 (st.combBytes Hs c2))
    let check := qsCheck pf c2 cs crt.qMask deltaL
    (verify Hs T st proof).chal2 = c2 ∧ (verify Hs T st proof).qsCheck = gfToBytes check ∧
      ((verify Hs T st proof).accept = true ↔ chal3 Hs pf c2 check = pf.delta) := by
  subst hpf
  simp only [verify, Id.run]
  simp only [hf, Bool.not_true, Bool.false_eq_true, ↓reduceIte, hl]
  simp only [beq_iff_eq, hΔ, ↓reduceIte, pure, byteArray_beq_iff, and_self]

/-- The steps before `chal3` do not read `H₂³`. -/
lemma steps_program (Hs : Hashes) (pts : List (ByteArray × ByteArray)) (T : CrtTables)
    (st : Statement) (pf : Proof) :
    st.mu1 (program Hs pts) = st.mu1 Hs ∧
    (∀ mu1, ivOf (program Hs pts) pf mu1 = ivOf Hs pf mu1) ∧
    (program Hs pts).hash .h1 = Hs.hash .h1 ∧
    (∀ mu1 c b, chal1 (program Hs pts) pf mu1 c b = chal1 Hs pf mu1 c b) ∧
    (∀ iv cols, crtReconstruct (program Hs pts) pf T iv cols = crtReconstruct Hs pf T iv cols) ∧
    (∀ c1 h m b, chal2 (program Hs pts) pf c1 h m b = chal2 Hs pf c1 h m b) ∧
    (∀ c1, st.muDelayed (program Hs pts) c1 = st.muDelayed Hs c1) ∧
    (∀ c2, st.combBytes (program Hs pts) c2 = st.combBytes Hs c2) := by
  have h : ∀ k, k ≠ Kind.h23 → (program Hs pts).hash k = Hs.hash k := fun k hk =>
    funext (program_hash_ne Hs pts hk)
  refine ⟨?_, fun _ => ?_, h _ (by decide), fun _ _ _ => ?_, fun _ _ => ?_, fun _ _ _ _ => ?_,
    fun _ => ?_, fun _ => ?_⟩
  · simp only [Statement.mu1, mu, h .mu (by decide), h .muDelayed (by decide)]
  · simp only [ivOf, h .h4 (by decide)]
  · simp only [chal1, h .h21 (by decide)]
  · simp only [crtReconstruct, h .h5 (by decide)]
  · simp only [chal2, h .h22 (by decide)]
  · simp only [Statement.muDelayed, mu, h .mu (by decide)]
  · unfold Statement.combBytes
    split
    · rfl
    · rename_i M dst _
      rw [h (.comb M) (by simp)]

/-- **The verifier accepts under the programmed oracle.** If the verifier's run with `Hs` reaches
`chal3`, then with `H₂³` programmed at `programPoints` it accepts. -/
theorem verify_program_accept (Hs : Hashes) (T : CrtTables) (st : Statement) (proof : ByteArray)
    (g : Fin nGrind → Bytes 16) (ctr : ℕ) (h : Reaches Hs T st proof) :
    (verify (program Hs (programPoints Hs T st proof g ctr)) T st proof).accept = true := by
  obtain ⟨hf, leaves, hl, hΔ⟩ := h
  set pf : Proof := { params := st.params, bytes := proof } with hpf
  obtain ⟨hmu, hiv, hh1, hc1, hcrt, hc2, hmd, hcb⟩ :=
    steps_program Hs (programPoints Hs T st proof g ctr) T st pf
  have hl' : BAVC.reconstruct (ivOf (program Hs (programPoints Hs T st proof g ctr)) pf
      (st.mu1 (program Hs (programPoints Hs T st proof g ctr)))) pf.opening pf.delta =
      some leaves := by rw [hmu, hiv]; exact hl
  have hΔ' := hΔ
  rw [← hcrt, ← hiv, ← hmu] at hΔ'
  obtain ⟨-, -, hacc⟩ := verify_reaches (program Hs (programPoints Hs T st proof g ctr)) T st proof
    pf hpf leaves hf hl' hΔ'
  obtain ⟨hc2t, hqt, -⟩ := verify_reaches Hs T st proof pf hpf leaves hf hl hΔ
  rw [hacc]
  simp only [hmu, hiv, hh1, hc1, hcrt, hc2, hmd, hcb]
  rw [chal3, chal3Input]
  unfold programPoints
  dsimp only
  rw [hc2t, hqt]
  refine program_hash_head' Hs _ ?_
  rfl

/-- **The simulator's programmed oracle makes the verifier accept its proof** (whenever the run
with the original hashes reaches `chal3`). -/
theorem simulateRO_accept (Hs : Hashes) (T : CrtTables) (st : Statement) (c : SimCoins st.params)
    {proof : ByteArray} {Hs' : Hashes} (h : simulateRO Hs T st c = .ok (proof, Hs'))
    (hr : Reaches Hs T st proof) : (verify Hs' T st proof).accept = true := by
  unfold simulateRO at h
  cases hs : simulate st.params c with
  | error e => rw [hs] at h; cases h
  | ok pf =>
    rw [hs] at h
    simp only [bind, Except.bind, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact verify_program_accept Hs T st pf _ _ hr

end VoleMole.ZK.Sim
