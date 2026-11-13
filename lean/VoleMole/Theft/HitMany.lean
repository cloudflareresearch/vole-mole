import VoleMole.Theft.HitLevel
import VoleMole.Theft.ManyPlain

/-!
# `ε_hit` for `N` simulated proofs, with the chain hashes random tables

The many-token theft theorems reduce `WeakSEN` to plain extraction and one programmed-point term
per simulated proof (`SlotEvN i`, `Theft/ManyPlain.lean`): the fresh forgery's verifier reads
`H₂³` at a grinding key of simulated proof `i`'s recomputed prefix. Here that term is bounded, in
the model with the extra table `XTab L M` (`hbX`), as `Theft/HitLevel.lean` does for two proofs.

* `simPre_mem`: the log of `n` simulated slots contains slot `i < n`'s entry.
* `seLog_fst_congr`: the `H₂³` table after `n` programmings depends on the extra table only
  through the `n` simulations' prefixes.
* `qtree_forgerN`: the forgery's point at one level is computed by a tree with `N` more queries
  than the adversary's (`QTree.of_cells`: the `N` simulations' points).
* **`slotEvN_chain`**: for a simulator whose programming is `SimProg`, a freshness under which a
  forgery has chain inputs of at most `L` bytes and an `H₂⁰` input other than those of the logged
  simulated statements, and adversaries whose last stage reads the chain tables with `q_μ`, `q₂₁`,
  `q₂₂` queries (`AdmHitN`),

      ε_hit,i ≤ (q₂₂+N+1)·2⁻⁴⁴⁸ + (q₂₁+N+1)·2⁻¹⁰⁸⁸ + (q_μ+N+1)·2⁻²⁵⁶   (`epsHitN`).
-/

-- (The coin types are large products: their `Fintype` instances exceed the default size.)
set_option synthInstance.maxSize 1024

namespace VoleMole.Theft

open VoleMole.Privacy

/-- **The log of `n` simulated slots contains slot `i`'s entry**, `i < n`. -/
theorem simPre_mem {Ω O C S : Type*} (Sm : Ω → List O → C → O) (pg : Ω → List O → C → S → S)
    (ω : Ω) (cs : ℕ → C) (i : ℕ) :
    ∀ n, i < n → Sm ω (simPre Sm pg ω cs i).1 (cs i) ∈ (simPre Sm pg ω cs n).1
  | 0, h => absurd h (Nat.not_lt_zero _)
  | n + 1, h => by
    simp only [simPre, List.mem_append, List.mem_singleton]
    rcases Nat.lt_succ_iff_lt_or_eq.1 h with h | rfl
    · exact Or.inl (simPre_mem Sm pg ω cs i n h)
    · exact Or.inr rfl

namespace Hit

open VoleMole.Verifier VoleMole.Verifier.Bridge VoleMole.ZK.Sim VoleMole.ZK VoleMole.Theft.ComOW
open VoleMole.Theft.Chain
open VoleMole.ROM.IC (muIn)

variable {R : Type} [CipherRow R] {p : Params} {L M : ℕ}

section N

variable {α I P C : Type} {sim : I → C → Option P} {prog : I → C → ShT R p L M → ShT R p L M}
  {D : I → C → SD}

/-- **The `H₂³` table after `n` programmings depends on the extra table only through the `n`
simulations' prefixes.** -/
lemma seLog_fst_congr (hp : SimProg prog D) (x : α → List (Option (I × P)) → Option I) (a : α)
    (cs : ℕ → C) (G2 : Tab2G p) (G5E : Tab5F × (Blk → R)) (y y' : XTab L M) :
    ∀ n, (∀ j < n, ∀ xj, x a (seLog sim prog x a cs j).1 = some xj →
        simPreT (p := p) (G2, (G5E, y)) (D xj (cs j)) = simPreT (G2, (G5E, y')) (D xj (cs j))) →
      ∀ H : Tab2G p, ((seLog sim prog x a cs n).2 (H, (G5E, y))).1 =
        ((seLog sim prog x a cs n).2 (H, (G5E, y'))).1
  | 0, _, _ => rfl
  | n + 1, h, H => by
    have e1 : (progO prog (x a (seLog sim prog x a cs n).1) (cs n) (H, (G5E, y))).1 =
        (progO prog (x a (seLog sim prog x a cs n).1) (cs n) (H, (G5E, y'))).1 := by
      rcases hx : x a (seLog sim prog x a cs n).1 with _ | xj
      · rfl
      · exact hp.2.2.1 xj (cs n) H G5E y y' (h n (Nat.lt_succ_self n) xj hx)
    have s2 : ∀ w, progO prog (x a (seLog sim prog x a cs n).1) (cs n) (H, (G5E, w)) =
        ((progO prog (x a (seLog sim prog x a cs n).1) (cs n) (H, (G5E, w))).1, (G5E, w)) :=
      fun w => Prod.ext rfl (progO_snd hp.1 _ _ _)
    show ((seLog sim prog x a cs n).2
        (progO prog (x a (seLog sim prog x a cs n).1) (cs n) (H, (G5E, y)))).1 =
      ((seLog sim prog x a cs n).2
        (progO prog (x a (seLog sim prog x a cs n).1) (cs n) (H, (G5E, y')))).1
    rw [s2 y, s2 y', e1]
    exact seLog_fst_congr hp x a cs G2 G5E y y' n (fun j hj => h j (Nat.lt_succ_of_lt hj)) _

/-- **The forgery's point at one level is computed by a tree** with `N` more queries than the
adversary's: the `N` simulations' points (which fix the programmed `H₂³` table), then the
adversary's tree. -/
lemma qtree_forgerN {Out : Type*} {n : ℕ} (setX : (KL L → ZK.Sim.Bytes n) → XTab L M → XTab L M)
    {q : ℕ} (Pf : Out → ShT R p L M → ByteArray) (Ps : SimD → ShT R p L M → ByteArray)
    (hPf : ∀ op G2 G5E x T T', Pf op (G2, (G5E, setX T x)) = Pf op (G2, (G5E, setX T' x)))
    (hPs : ∀ d G2 G5E x T T', Ps d (G2, (G5E, setX T x)) = Ps d (G2, (G5E, setX T' x)))
    (hpre : ∀ (d : SD) G2 G5E x T T', d.1.delayed = false →
      (∀ k, keyL L (Ps (some d) (G2, (G5E, setX T x))) = some k → T k = T' k) →
      simPreT (p := p) (G2, (G5E, setX T x)) d = simPreT (G2, (G5E, setX T' x)) d)
    (hp : SimProg prog D) (x : α → List (Option (I × P)) → Option I) (a : α) (cs : ℕ → C) (N : ℕ)
    (F : ShT R p L M → Out) (hF : ∀ G2 G5E x, QTree (fun T => F (G2, (G5E, setX T x))) q)
    (G2 : Tab2G p) (G5E : Tab5F × (Blk → R)) (x₀ : XTab L M) :
    QTree (fun T => keyL L (Pf (F ((seLog sim prog x a cs N).2 (G2, (G5E, setX T x₀))))
      (G2, (G5E, setX T x₀)))) (q + N) := by
  let T₀ : KL L → ZK.Sim.Bytes n := fun _ _ => 0
  let cell : ℕ → KL L := fun j =>
    (keyL L (Ps (sdO D (x a (seLog sim prog x a cs j).1) (cs j)) (G2, (G5E, setX T₀ x₀)))).getD
      default
  have hH : ∀ T T' : KL L → ZK.Sim.Bytes n, (∀ c ∈ (List.range N).map cell, T c = T' c) →
      ((seLog sim prog x a cs N).2 (G2, (G5E, setX T x₀))).1 =
        ((seLog sim prog x a cs N).2 (G2, (G5E, setX T' x₀))).1 := by
    intro T T' h
    refine seLog_fst_congr hp x a cs G2 G5E _ _ N (fun j hj xj hx => ?_) G2
    refine hpre _ G2 G5E x₀ T T' (hp.2.2.2 xj (cs j)) fun k hk => ?_
    have hc := h (cell j) (List.mem_map.2 ⟨j, List.mem_range.2 hj, rfl⟩)
    rw [hPs _ G2 G5E x₀ T T₀] at hk
    simp only [cell, hx, sdO, Option.map_some, hk, Option.getD_some] at hc
    exact hc
  have h := QTree.of_cells
    (fun H2 T => keyL L (Pf (F (H2, (G5E, setX T x₀))) (G2, (G5E, setX T₀ x₀))))
    (fun H2 => (hF H2 G5E x₀).map fun op => keyL L (Pf op (G2, (G5E, setX T₀ x₀))))
    ((List.range N).map cell)
    (fun T => ((seLog sim prog x a cs N).2 (G2, (G5E, setX T x₀))).1) hH
  rw [List.length_map, List.length_range] at h
  refine cast (congrArg (fun f => QTree f (q + N)) (funext fun T => ?_)) h
  have e : (seLog sim prog x a cs N).2 (G2, (G5E, setX T x₀)) =
      (((seLog sim prog x a cs N).2 (G2, (G5E, setX T x₀))).1, (G5E, setX T x₀)) :=
    Prod.ext rfl ((seLog_isProgs sim prog x a cs N).snd hp.1 _)
  show keyL L (Pf _ _) = keyL L (Pf _ _)
  rw [← e, hPf _ G2 G5E x₀ T T₀]

end N

/-- **The adversaries of `ε_hit` with `N` simulated proofs**: the last stage reads each chain
table by a decision tree with `q_μ`, `q₂₁`, `q₂₂` queries (`TreeT`), at every value of the
slices. -/
def AdmHitN {N : ℕ} {G Out : Type*} (qMu q21 q22 : ℕ) (F : (Fin N → G) → ShT R p L M → Out) :
    Prop :=
  ∀ g, TreeT qMu q21 q22 (F g)

omit [CipherRow R] in
/-- A last stage that does not read the tables is admissible with no queries. -/
lemma admHitN_const {N : ℕ} {G Out : Type*} (o : Out) :
    AdmHitN (R := R) (p := p) (L := L) (M := M) (N := N) (G := G) 0 0 0 fun _ _ => o :=
  fun _ => ⟨fun _ _ _ => .ret _ _, fun _ _ _ => .ret _ _, fun _ _ _ => .ret _ _⟩

/-- **The bound for one of `N` simulated proofs**:
`(q₂₂+N+1)·2⁻⁴⁴⁸ + (q₂₁+N+1)·2⁻¹⁰⁸⁸ + (q_μ+N+1)·2⁻²⁵⁶`. -/
noncomputable def epsHitN (N qMu q21 q22 : ℕ) : ℝ :=
  (q22 + N + 1 : ℕ) * (1 / 2 ^ 448) + (q21 + N + 1 : ℕ) * (1 / 2 ^ 1088) +
    (qMu + N + 1 : ℕ) * (1 / 2 ^ 256)

lemma epsHitN_nonneg (N qMu q21 q22 : ℕ) : 0 ≤ epsHitN N qMu q21 q22 := by
  unfold epsHitN
  positivity

/-- **`ε_hit` of simulated proof `i` of `N`, with the chain hashes random tables.** With `H₂⁰`,
`H₂¹`, `H₂²` uniform tables on the inputs of at most `L` bytes (`hbX`), a simulator whose
programming is `SimProg`, and a freshness `Fresh` under which a forgery (`fd`) has chain inputs of
at most `L` bytes (`hfd`) and an `H₂⁰` input other than those of the logged simulated statements
(`hfr`): against adversaries that read the chain tables with `q_μ`, `q₂₁`, `q₂₂` queries
(`AdmHitN`), a fresh forgery whose verifier reads `H₂³` at a grinding key of simulated proof
`i`'s prefix (`hE`) has probability

    ≤ (q₂₂+N+1)·2⁻⁴⁴⁸ + (q₂₁+N+1)·2⁻¹⁰⁸⁸ + (q_μ+N+1)·2⁻²⁵⁶. -/
theorem slotEvN_chain [Fintype R] [Nonempty R] {I P Out G C : Type} [Fintype C] [Nonempty C]
    [Fintype G] [Nonempty G] {N : ℕ} (i : Fin N) {sim : I → C → Option P}
    {prog : I → C → ShT R p L M → ShT R p L M} {D : I → C → SD} (hp : SimProg prog D)
    (fd : Out → FD) {Fresh : List (Option (I × P)) → Out → Prop}
    {E : I → C → Out → ShT R p L M → Prop}
    (hfd : ∀ l op, Fresh l op → FOk L (fd op).1)
    (hE : ∀ xi c op t, E xi c op t → ∃ k : K2 p,
      enc2 p k = (@vPre (prgT t) (recT t) CrtGen.tables (fd op).1 (fd op).2 ++
        (pfOf (fd op).1 (fd op).2).ctr).push 11 ∧ k.1 = blk (preLen p) (simPreT t (D xi c)))
    (hfr : ∀ l op xi c, Fresh l op → pairO (some xi) (sim xi c) ∈ l →
      (∃ b, (D xi c).2 = .ok b) → muIn (fd op).1 ≠ muIn (D xi c).1)
    (qMu q21 q22 : ℕ) :
    SlotEvN N i sim prog Fresh E (AdmHitN (N := N) (G := G) qMu q21 q22)
      (epsHitN N qMu q21 q22) := by
  intro α _ _ x out hout
  let Tp := (α × (Fin N → C × G)) × ShT R p L M
  let ℓ : TLens Tp R p L M := lensS _
  let cs : Tp → ℕ → C := fun z => extN fun j => (z.1.2 j).1
  let op : Tp → Out := fun z =>
    out z.1.1 (seLog sim prog x z.1.1 (cs z) N).1 (fun j => (z.1.2 j).2)
      ((seLog sim prog x z.1.1 (cs z) N).2 z.2)
  let d : Tp → SimD := fun z => sdO D (x z.1.1 (seLog sim prog x z.1.1 (cs z) i).1) (z.1.2 i).1
  have hH : pr Tp (fun z => HitAt (fd (op z)) z.2 (d z)) ≤
      (q22 + N + 1 : ℕ) * (1 / 2 ^ (8 * 56)) + (q21 + N + 1 : ℕ) * (1 / 2 ^ (8 * 136)) +
        (qMu + N + 1 : ℕ) * (1 / 2 ^ (8 * 32)) := by
    refine pr_hitAt_le ℓ d (fun _ _ => rfl) (fun z => fd (op z)) (fun z => ?_) (fun z => ?_)
      (fun z => ?_)
    · exact qtree_forgerN set22 (fun o t => fPt22 (fd o) t) sPt22 (fun o => hPf22 (fd o)) hPs22
        (fun d G2 G5E x T T' _ h => hpre22 d G2 G5E x T T' h) hp x z.1.1 (cs z) N
        (out z.1.1 (seLog sim prog x z.1.1 (cs z) N).1 (fun j => (z.1.2 j).2))
        (fun G2 G5E y => (hout _ _ _).2.2 G2 G5E y) z.2.1 z.2.2.1 z.2.2.2
    · exact qtree_forgerN set21 (fun o t => fPt21 (fd o) t) sPt21 (fun o => hPf21 (fd o)) hPs21
        (fun d G2 G5E x T T' _ h => hpre21 d G2 G5E x T T' h) hp x z.1.1 (cs z) N
        (out z.1.1 (seLog sim prog x z.1.1 (cs z) N).1 (fun j => (z.1.2 j).2))
        (fun G2 G5E y => (hout _ _ _).2.1 G2 G5E y) z.2.1 z.2.2.1 z.2.2.2
    · exact qtree_forgerN setMu (fun o _ => fPtMu (fd o)) (fun d _ => sPtMu d)
        (fun _ _ _ _ _ _ => rfl) (fun _ _ _ _ _ _ => rfl)
        (fun d G2 G5E x T T' hdl h => hpreMu d G2 G5E x T T' hdl h) hp x z.1.1 (cs z) N
        (out z.1.1 (seLog sim prog x z.1.1 (cs z) N).1 (fun j => (z.1.2 j).2))
        (fun G2 G5E y => (hout _ _ _).1 G2 G5E y) z.2.1 z.2.2.1 z.2.2.2
  refine (Privacy.pr_mono (Q := fun z => HitAt (fd (op z)) z.2 (d z)) fun z hz => ?_).trans
    (hH.trans (le_of_eq ?_))
  · obtain ⟨hfresh, xi, hxi, hev⟩ := hz
    obtain ⟨k, hk, hkp⟩ := hE _ _ _ _ hev
    have hd : d z = some (D xi (z.1.2 i).1) := by
      simp only [d, cs, hxi, sdO, Option.map_some]
    rw [hd]
    refine hitAt_of (fd (op z)) (hfd _ _ hfresh) z.2 _ (hp.2.2.2 xi _) k hk hkp fun hok => ?_
    refine hfr _ _ xi _ hfresh ?_ hok
    have hm := simPre_mem (fun a l c => pairO (x a l) (simO sim (x a l) c))
      (fun a l c => progO prog (x a l) c) z.1.1 (cs z) i.val N i.isLt
    have hc : cs z i.val = (z.1.2 i).1 := extN_val (fun j => (z.1.2 j).1) i
    have hxi' : x z.1.1 (simPre (fun a l c => pairO (x a l) (simO sim (x a l) c))
        (fun a l c => progO prog (x a l) c) z.1.1 (cs z) i.val).1 = some xi := hxi
    rw [hxi', hc] at hm
    exact hm
  · simp only [epsHitN, show 8 * 56 = 448 from rfl, show 8 * 136 = 1088 from rfl,
      show 8 * 32 = 256 from rfl]

end Hit

end VoleMole.Theft
