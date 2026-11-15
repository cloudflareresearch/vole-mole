import VoleMole.Theft.MoussakaManyHit
import VoleMole.Theft.MoussakaDigest
import VoleMole.Theft.MoussakaUnboundDigest
import VoleMole.Theft.MoussakaUnboundHit
import VoleMole.Audit.Theft
import VoleMole.Audit.UnboundRest

/-!
# Audit of the many-token Moussaka and unbound Moussaka theorems with `ε_hit` bounded

* **The hypotheses can hold together.** `noRedirectN_leanX_plain`, `noRedirectN_leanX_hit`
  (`Theft/MoussakaManyHit.lean`) and `nmUN_leanX_plain`, `nmUN_leanX_hit`, `nmUN_leanX_hit_one`
  (`Theft/MoussakaUnboundTables.lean`, `Theft/MoussakaUnboundHit.lean`) are instantiated at a
  well-formed trivial adversary (the lengths of the C++ types, one Anchor Set with a 32-byte
  digest), whose last stage reads no chain table (`AdmHitN 0 0 0`, `admHitN_const`), and a
  constant extractor, with `L = Lmin` (`6293`, bound) and `L = LminU` (`9749`, unbound), for every
  `U ≥ 1` and `M`. Plain extraction and the programming term hold with error `1`.
* **`HitWfN` is satisfiable** (`hitWfN_thiefNMW`, `hitWfN_thiefNUW`), and **`FreshOkN` is the
  game's freshness on well-formed statements**: `FreshOkN.freshOpN` (both files) and
  `freshOkN_of_sim` are the two directions used.
* **The collision form's hypotheses hold** (`Theft/MoussakaDigest.lean`): `HitLenN` and
  `KeysOkN` for the same adversary, whose one key is `⟨sha [], exp []⟩` for a digest function
  and an expansion that map the empty compressed key to its digest and map
  (`keysOkN_thiefNMW`), and `noRedirectN_leanX_hitC` is instantiated; the same for unbound
  Moussaka (`Theft/MoussakaUnboundDigest.lean`, `nmUN_leanX_hitC`).

This checks that the hypotheses are consistent, not that they are small.

No `sorry`, no `axiom`.
-/

-- (The coin types are large products: their `Fintype` instances exceed the default size.)
set_option synthInstance.maxSize 1024

namespace VoleMole.Audit.TheftManyHit

open VoleMole.Privacy VoleMole.Theft VoleMole.ZK.Sim
open VoleMole.Audit.Theft (setW)

/-! ## Moussaka -/

section Mous

open VoleMole.Theft.Moussaka VoleMole.Spec VoleMole.Spec.Moussaka VoleMole.Privacy.Moussaka

variable {G S : Type} {U M : ℕ}

/-- **A well-formed trivial adversary** against `U ≥ 1` tokens: constant choices with the lengths
of the C++ types, always token `0` under its own Anchor Set, and a constant redemption request
under that set as its output. -/
def thiefNMW (U M : ℕ) [NeZero U] (G S : Type) : ThiefN U M G S :=
  ⟨fun _ _ => 0, fun _ _ => 0, fun _ => ⟨List.replicate digestBytes 0, fun _ => 0⟩,
    fun _ _ _ => 0, fun _ _ => (0, setW, List.replicate cdBytes 0),
    fun _ _ _ _ => .redeem setW [] (List.replicate ctxBytes 0) (List.replicate ctxBytes 0)
      (List.replicate cdBytes 0)⟩

/-- **`HitWfN` is satisfiable.** -/
theorem hitWfN_thiefNMW [NeZero U] : HitWfN (thiefNMW U M G S) := by
  refine ⟨fun reqs reds => ⟨fun pk hpk => ?_, by simp [thiefNMW]⟩, ?_⟩
  · simp only [thiefNMW, setW, List.mem_singleton] at hpk
    subst hpk
    simp
  · intro reqs reds g s S' req ci cr cd h
    simp only [thiefNMW, MOp.redeem.injEq] at h
    obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := h
    refine ⟨fun pk hpk => ?_, by simp, by simp, by simp, fun _ _ _ => rfl⟩
    simp only [setW, List.mem_singleton] at hpk
    subst hpk
    simp

/-- `noRedirectN_leanX_plain`'s hypotheses hold for the trivial adversary and a constant
extractor, with any base records. -/
example [NeZero U] (L M' : ℕ) :=
  noRedirectN_leanX_plain (R := Blk → Blk) (X := XTab L M') (Hb := hbX) (thiefNMW U M _ _)
    (e := fun _ _ _ _ => []) hbX_wf (Adm := fun _ => True) (Adm₀ := fun _ => True) (ε₀ := 1)
    (εm := 1) (a3 := 0) (a5 := 0) (aE := 0) (x3 := 0) (x5 := 0) (xE := 0)
    (fun _ _ => StageBudgetNX.const _) (fun _ => StageBudgetNX.const _)
    (plainSEN_one _ _ _ _ _ _) (progMovesN_one _ _ _ _ _ _) (fun _ _ => trivial)
    fun _ _ _ _ => trivial

/-- `noRedirectN_leanX_hit`'s hypotheses hold for the well-formed trivial adversary (no
chain-table queries) and a constant extractor, with `L = Lmin`. -/
example [NeZero U] (M' : ℕ) :=
  noRedirectN_leanX_hit (R := Blk → Blk) (L := Hit.Mous.Lmin) (M' := M') (thiefNMW U M _ _)
    hitWfN_thiefNMW le_rfl (e := fun _ _ _ _ => []) (Adm := Hit.AdmHitN 0 0 0)
    (Adm₀ := fun _ => True) (ε₀ := 1) (a3 := 0) (a5 := 0) (aE := 0) (x3 := 0) (x5 := 0) (xE := 0)
    (fun _ _ => StageBudgetNX.const _) (fun _ => StageBudgetNX.const _)
    (plainSEN_one _ _ _ _ _ _) (fun _ _ => Hit.admHitN_const _) (fun _ h => h)
    fun _ _ _ _ => trivial

/-- `HitLenN` holds for the well-formed trivial adversary. -/
theorem hitLenN_thiefNMW [NeZero U] : HitLenN (thiefNMW U M G S) :=
  ⟨hitWfN_thiefNMW.1, fun reqs reds g s S' req ci cr cd h =>
    let ⟨h1, h2, h3, h4, _⟩ := hitWfN_thiefNMW.2 reqs reds g s S' req ci cr cd h
    ⟨h1, h2, h3, h4⟩⟩

/-- **`KeysOkN` is satisfiable**: the adversary's one key is the digest and expansion of the
empty compressed key, for a digest function and an expansion that give it. -/
theorem keysOkN_thiefNMW [NeZero U] :
    KeysOkN (thiefNMW U M G S) (fun _ => List.replicate digestBytes 0) (fun _ _ => 0) := by
  have hk : ∀ pk ∈ setW.keys, KeyOk (fun _ => List.replicate digestBytes 0) (fun _ _ => 0) pk := by
    intro pk hpk
    simp only [setW, List.mem_singleton] at hpk
    exact ⟨[], hpk⟩
  refine ⟨fun _ _ => hk, fun reqs reds g s S' req ci cr cd h => ?_⟩
  simp only [thiefNMW, MOp.redeem.injEq] at h
  obtain ⟨rfl, -⟩ := h
  exact hk

/-- `noRedirectN_leanX_hitC`'s hypotheses hold for the well-formed trivial adversary (no
chain-table queries) and a constant extractor, with `L = Lmin`. -/
example [NeZero U] (M' : ℕ) :=
  noRedirectN_leanX_hitC (R := Blk → Blk) (L := Hit.Mous.Lmin) (M' := M')
    (fun _ => List.replicate digestBytes 0) (fun _ _ => 0) (thiefNMW U M _ _) hitLenN_thiefNMW
    keysOkN_thiefNMW le_rfl (e := fun _ _ _ _ => []) (Adm := Hit.AdmHitN 0 0 0)
    (Adm₀ := fun _ => True) (ε₀ := 1) (a3 := 0) (a5 := 0) (aE := 0) (x3 := 0) (x5 := 0) (xE := 0)
    (fun _ _ => StageBudgetNX.const _) (fun _ => StageBudgetNX.const _)
    (plainSEN_one _ _ _ _ _ _) (fun _ _ => Hit.admHitN_const _) (fun _ h => h)
    fun _ _ _ _ => trivial

end Mous

/-! ## Unbound Moussaka -/

section Unb

open VoleMole.Theft.MoussakaUnbound VoleMole.Spec VoleMole.Spec.MoussakaUnbound
  VoleMole.Privacy.MoussakaUnbound VoleMole.Audit.UnboundRest
open VoleMole.Spec.Moussaka (ctxBytes cdBytes)

variable {G S : Type} {U M : ℕ}

/-- **A well-formed trivial adversary** against `U ≥ 1` unbound tokens: constant choices with the
lengths of the C++ types, always token `0` under its own Anchor Set, and a constant redemption
request under that set as its output. -/
def thiefNUW (U M : ℕ) [NeZero U] (G S : Type) : ThiefN U M G S :=
  ⟨fun _ _ => 0, fun _ => ⟨List.replicate digestBytes 0, fun _ => 0⟩, fun _ _ _ => 0,
    fun _ _ => (0, setW, fun _ => 0, List.replicate cdBytes 0),
    fun _ _ _ _ => .redeem setW [] (List.replicate ctxBytes 0) (List.replicate ctxBytes 0)
      (List.replicate cdBytes 0)⟩

/-- **`HitWfN` is satisfiable** for the unbound game. -/
theorem hitWfN_thiefNUW [NeZero U] : MoussakaUnbound.HitWfN (thiefNUW U M G S) := by
  refine ⟨fun reqs reds => ⟨fun pk hpk => ?_, by simp [thiefNUW]⟩, ?_⟩
  · simp only [thiefNUW, setW, List.mem_singleton] at hpk
    subst hpk
    simp
  · intro reqs reds g s S' req ci cr cd h
    simp only [thiefNUW, UOp.redeem.injEq] at h
    obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := h
    refine ⟨fun pk hpk => ?_, by simp, fun _ _ _ => rfl⟩
    simp only [setW, List.mem_singleton] at hpk
    subst hpk
    simp

/-- `nmUN_leanX_plain`'s hypotheses hold for the trivial adversary and a constant extractor. -/
example [NeZero U] (L M' : ℕ) (pts : Fin (M + 1) → Coins ctxBytes)
    (hpts : Function.Injective pts) :=
  nmUN_leanX_plain (R := Blk → Blk) (X := XTab L M') (Hb := hbX) (thiefNUW U M _ _)
    (e := fun _ _ _ _ => []) hbX_wf (Adm := fun _ => True) (Adm₀ := fun _ => True) (ε₀ := 1)
    (εm := 1) (a3 := 0) (a5 := 0) (aE := 0) (x3 := 0) (x5 := 0) (xE := 0)
    (fun _ _ => StageBudgetNX.const _) (fun _ => StageBudgetNX.const _)
    (plainSEN_one _ _ _ _ _ _) (progMovesN_one _ _ _ _ _ _) (fun _ _ => trivial)
    (fun _ _ _ _ => trivial) pts hpts (fun _ _ => prf1Adv_le_one _ _)

/-- `nmUN_leanX_hit`'s hypotheses hold for the well-formed trivial adversary (no chain-table
queries) and a constant extractor, with `L = LminU`. -/
example [NeZero U] (M' : ℕ) (pts : Fin (M + 1) → Coins ctxBytes)
    (hpts : Function.Injective pts) :=
  nmUN_leanX_hit (R := Blk → Blk) (L := LminU) (M' := M') (thiefNUW U M _ _) hitWfN_thiefNUW
    le_rfl (e := fun _ _ _ _ => []) (Adm := Hit.AdmHitN 0 0 0) (Adm₀ := fun _ => True)
    (ε₀ := 1) (a3 := 0) (a5 := 0) (aE := 0) (x3 := 0) (x5 := 0) (xE := 0)
    (fun _ _ => StageBudgetNX.const _) (fun _ => StageBudgetNX.const _)
    (plainSEN_one _ _ _ _ _ _) (fun _ _ => Hit.admHitN_const _) (fun _ h => h)
    (fun _ _ _ _ => trivial) pts hpts (fun _ _ => prf1Adv_le_one _ _)

/-- `nmUN_leanX_hit_one`'s hypotheses hold for the well-formed trivial adversary with one token
and one redemption. -/
example (M' : ℕ) (pts : Fin (1 + 1) → Coins ctxBytes) (hpts : Function.Injective pts) :=
  nmUN_leanX_hit_one (R := Blk → Blk) (L := LminU) (M' := M') (thiefNUW 1 1 _ _)
    hitWfN_thiefNUW le_rfl (e := fun _ _ _ _ => []) (Adm := Hit.AdmHitN 0 0 0)
    (Adm₀ := fun _ => True) (ε₀ := 1) (a3 := 0) (a5 := 0) (aE := 0) (x3 := 0) (x5 := 0) (xE := 0)
    (fun _ _ => StageBudgetNX.const _) (fun _ => StageBudgetNX.const _)
    (plainSEN_one _ _ _ _ _ _) (fun _ _ => Hit.admHitN_const _) (fun _ h => h)
    (fun _ _ _ _ => trivial) pts hpts (fun _ _ => prf1Adv_le_one _ _)

/-- `HitLenN` holds for the well-formed trivial unbound adversary. -/
theorem hitLenN_thiefNUW [NeZero U] : MoussakaUnbound.HitLenN (thiefNUW U M G S) :=
  ⟨hitWfN_thiefNUW.1, fun reqs reds g s S' req ci cr cd h =>
    let ⟨h1, h2, _⟩ := hitWfN_thiefNUW.2 reqs reds g s S' req ci cr cd h
    ⟨h1, h2⟩⟩

/-- **`KeysOkN` is satisfiable** for the unbound game. -/
theorem keysOkN_thiefNUW [NeZero U] :
    MoussakaUnbound.KeysOkN (thiefNUW U M G S) (fun _ => List.replicate digestBytes 0)
      (fun _ _ => 0) := by
  have hk : ∀ pk ∈ setW.keys,
      Moussaka.KeyOk (fun _ => List.replicate digestBytes 0) (fun _ _ => 0) pk := by
    intro pk hpk
    simp only [setW, List.mem_singleton] at hpk
    exact ⟨[], hpk⟩
  refine ⟨fun _ _ => hk, fun reqs reds g s S' req ci cr cd h => ?_⟩
  simp only [thiefNUW, UOp.redeem.injEq] at h
  obtain ⟨rfl, -⟩ := h
  exact hk

/-- `nmUN_leanX_hitC`'s hypotheses hold for the well-formed trivial adversary. -/
example [NeZero U] (M' : ℕ) (pts : Fin (M + 1) → Coins ctxBytes)
    (hpts : Function.Injective pts) :=
  nmUN_leanX_hitC (R := Blk → Blk) (L := LminU) (M' := M')
    (fun _ => List.replicate digestBytes 0) (fun _ _ => 0) (thiefNUW U M _ _) hitLenN_thiefNUW
    keysOkN_thiefNUW le_rfl (e := fun _ _ _ _ => []) (Adm := Hit.AdmHitN 0 0 0)
    (Adm₀ := fun _ => True) (ε₀ := 1) (a3 := 0) (a5 := 0) (aE := 0) (x3 := 0) (x5 := 0) (xE := 0)
    (fun _ _ => StageBudgetNX.const _) (fun _ => StageBudgetNX.const _)
    (plainSEN_one _ _ _ _ _ _) (fun _ _ => Hit.admHitN_const _) (fun _ h => h)
    (fun _ _ _ _ => trivial) pts hpts (fun _ _ => prf1Adv_le_one _ _)

end Unb

end VoleMole.Audit.TheftManyHit
