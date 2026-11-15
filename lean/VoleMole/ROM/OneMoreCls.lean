import VoleMole.ROM.OneMoreShiftSim
import VoleMole.ROM.LemmaPClsBound

/-!
# U1 with the class extractor: `E₁^cls` on the log, and the reduction's `H₅` queries

`lean/docs/security/pomfrit.md` §6.4 (gap G8-cls), `pomfrit-lemmap-tight.md` §6A. Theorem U1^cls
programs the target at `x` with the class extractor's output `E₁^cls(x)` instead of `E₁(x)`.
`E₁^cls` reads the check value at the decoder's points (`clsPts`), so it needs the gate hash `H₅`
at the gate inputs of these points. The paper's reduction evaluates `H₅` there itself.

In the game of `ROM/OneMorePomfrit.lean` the reduction's own queries are fixed (`auxSpec`) and the
hint is a function of the cipher table and the log. So the reduction here runs the forger
**wrapped** (`wrapE`): before each `H₂¹` query `x₁` of the forger, the wrapper asks `mu₁`, `iv` at
`x₁`, and `H₅` at every gate input of the decoder's points for the data committed at `x₁`
(`decIns`, from the log before `x₁` and the cipher table `E`). The wrapper is part of the reduction:
it reads `E`, which the reduction samples (the forger only queries the cipher). It must: the decoder's
gate inputs depend on the committed leaf keys, which the straight-line extractor finds with `E` at
cells the forger may never have queried, so a wrapper that only queries the cipher cannot compute
them without a guessing event. The forger never sees the wrapper's answers, so its view and its
forgeries are unchanged (`pomWin_le_wrapE`).

* `decIns`: the decoder's `H₅` inputs at `x₁`: the gate inputs of `clsPts` at the trees of the
  second wide class (all such trees; the class extractor decodes one of them).
* `coverIC`, `coverAt`, `clsW`, `wrapE`: the wrapper.
* `e1C`: `E₁^cls` on the log at the target query: the data committed at the first `H₂¹` preimage
  `x₁` of `x`'s `chal1` (as `e1P`), with `ũ`, `d[0..45)` and `chal1` read off `x` and `H₅` read off
  the log; the output of `PomFRIT.clsExt`.
* `CovL`: the log covers the decoder: every `H₂¹` query is preceded by the `H₅` queries of
  `decIns` for the data committed before it.

No `sorry`, no `axiom`.
-/

open Finset OracleComp OracleSpec
open scoped ENNReal

namespace VoleMole.ROM.OneMore.Pomfrit

open VoleMole.Prob VoleMole.Arith VoleMole.Verifier VoleMole.ROM VoleMole.ROM.IC
open VoleMole.EndToEnd VoleMole.ZK.Sim VoleMole.Verifier.Bridge VoleMole.PomFRIT

/-! ## The decoder's `H₅` inputs at an `H₂¹` input -/

section Dec

/-- The chain committed at the `H₂¹` input `x₁` with `iv`, from the joint log `Lb` before `x₁`: the
proof's fields up to `iv_pre` and the committed leaf keys (as `preCore`). -/
def pcOf (lr : Bool) (E : CTable) (Lb : QueryLog specIC) (x1 iv : ByteArray) : Chain :=
  { proof := xPre (pomfritParams lr) x1, keys := keyPre E (hashEnt Lb) Lb iv x1, iv := iv,
    h5 := fun _ => ByteArray.empty, chal1 := ByteArray.empty, hV := #[], z := 0,
    chal2 := ByteArray.empty, vals := fun _ => [] }

/-- The trees with no committed dead leaf at `x₁`. -/
def aliveOf (E : CTable) (Lb : QueryLog specIC) (x1 iv : ByteArray) : Finset (Fin BAVC.tau) :=
  univ.filter fun i => deadPre E (hashEnt Lb) Lb iv x1 i = ∅

/-- The trees the class extractor may decode for the alive trees `S` and the class keys `key`:
if the widest class has width at least 51, the trees of the other classes of width at least
51. -/
def wideOther {Kt : Type*} [DecidableEq Kt] (S : Finset (Fin BAVC.tau)) (key : Fin BAVC.tau → Kt) :
    Finset (Fin BAVC.tau) :=
  match majTree S key with
  | some i₁ => if 51 ≤ grpW S key (key i₁) then
      S.filter fun i => key i ≠ key i₁ ∧ 51 ≤ grpW S key (key i) else ∅
  | none => ∅

/-- **The decoder's `H₅` inputs at the `H₂¹` input `x₁`**: for the data committed before `x₁`
(the log `Lb`, `iv`), the gate inputs of the committed response at every point where the decoder
reads the check value, for each tree that the class extractor may decode. -/
noncomputable def decIns (lr : Bool) (E : CTable) (Lb : QueryLog specIC) (x1 iv : ByteArray) :
    List ByteArray :=
  letI : HasPrg := icPrg E.cipher
  let ch := pcOf lr E Lb x1 iv
  let S := aliveOf E Lb x1 iv
  let hd := hdOf (deadPre E (hashEnt Lb) Lb iv x1)
  (wideOther S (clsKey (stE lr) ch)).toList.flatMap fun i =>
    (clsPts (stE lr) ch S hd i).toList.flatMap fun Δ => gateIns (stE lr) ch CrtGen.tables Δ

end Dec

/-! ## The wrapper -/

section Wrap

/-- A computation against the hashes and the cipher, as one of the forger. -/
def toU {α : Type} (oa : OracleComp specIC α) : OracleComp specU α :=
  simulateQ (fun d => (liftM (specU.query (.inl d)) : OracleComp specU (AnsIC d))) oa

/-- **The wrapper's queries before the `H₂¹` query `x₁`**, from its log `L`: `mu₁`, `iv` at `x₁`,
and `H₅` at `decIns`; returns their log entries. -/
noncomputable def coverIC (lr : Bool) (E : CTable) (L : QueryLog specIC) (x1 : ByteArray) :
    OracleComp specIC (QueryLog specIC) := do
  let um ← (liftM (specIC.query (.inl muCell)) : OracleComp specIC (Ans muCell))
  let ui ← (liftM (specIC.query (.inl (ivCell lr x1 um.ba))) :
    OracleComp specIC (Ans (ivCell lr x1 um.ba)))
  let hs ← (decIns lr E L x1 ui.ba).mapM fun inp =>
    (fun u => (⟨.inl (.h5, inp), u⟩ : (t : DomIC) × AnsIC t)) <$>
      (liftM (specIC.query (.inl (.h5, inp))) : OracleComp specIC (Ans (.h5, inp)))
  pure (⟨.inl muCell, um⟩ :: ⟨.inl (ivCell lr x1 um.ba), ui⟩ :: hs)

/-- The wrapper's queries before the query `d`: `coverIC` before an `H₂¹` query, none otherwise. -/
noncomputable def coverAt (lr : Bool) (E : CTable) (L : QueryLog specIC) :
    DomIC → OracleComp specIC (QueryLog specIC)
  | .inl (k, x1) => if k = .h21 then coverIC lr E L x1 else pure []
  | .inr _ => pure []

/-- **The wrapper** (part of the reduction; it reads the cipher table `E`): it logs the forger's
hash and cipher queries; before each `H₂¹` query it makes the queries of `coverIC` (logged too);
everything else is forwarded. -/
noncomputable def clsW (lr : Bool) (E : CTable) :
    QueryImpl specU (StateT (QueryLog specIC) (OracleComp specU))
  | .inl d => StateT.mk fun L => do
      let cv ← toU (coverAt lr E L d)
      let u ← (liftM (specU.query (.inl d)) : OracleComp specU (AnsIC d))
      pure (u, L ++ cv ++ [⟨d, u⟩])
  | .inr q => StateT.mk fun L =>
      (fun u => (u, L)) <$> (liftM (specU.query (.inr q)) : OracleComp specU (AnsU (.inr q)))

/-- **The wrapped forger** for the cipher table `E`. -/
noncomputable def wrapE (lr : Bool) (E : CTable) (A : Forger) : Forger := fun pk =>
  (simulateQ (clsW lr E) (A pk)).run' []

end Wrap

/-! ## `E₁^cls` on the log -/

section E1C

/-- The `ũ` field of a `hash_to_target` input (bytes `175 … 239`). -/
def xU (x : ByteArray) : ByteArray := x.extract 175 239

/-- The chain of `E₁^cls` at `x`: the chain committed at `x₁`, with `ũ` and `d[0..45)` from `x`
(the rest of `d` zero) and `x`'s `chal1`. -/
def pcdC (pc : Chain) (x : ByteArray) : Chain :=
  { pc with proof := pc.proof ++ xU x ++ xDpre x ++ zerosBA 119, chal1 := xChal1 x }

open Classical in
/-- **`E₁^cls` on the log `L` at the target input `x`** (`pomfrit-lemmap-tight.md` §6A.2): the
first `H₂¹` preimage `x₁` of `x`'s `chal1` in `L` (`0` if none); the data committed at `x₁`
(`preCore`, `iv` and `H₅` read off `L`); the trees with no committed dead leaf; the class
extractor's output for their candidates `u ⊕ d`, classes by witness and label rows, and the
decoder's certificates on the check value of the chain with `ũ` and `chal1` from `x`. -/
noncomputable def e1C (lr : Bool) (E : CTable) (L : QueryLog specIC) (x : ByteArray) : TG :=
  match x1Of L x with
  | none => 0
  | some x1 =>
    letI : HasPrg := icPrg E.cipher
    let Gx := logBefore (.h21, x1) (hashEnt L)
    let Jx := logBefore (.inl (.h21, x1)) L
    let pc := preCore (stE lr) E Gx Jx x1 (tableOfLog (hashEnt L))
    let alive := univ.filter fun i => deadPre E Gx Jx pc.iv x1 i = ∅
    let ch := pcdC pc x
    toTG ((clsExt alive (clsKey (stE lr) ch)
      (fun i => preB (candidate (F := GF128) (ch.u (stE lr)) (ch.dc (stE lr)) i))
      (fun i => clsCert (stE lr) ch CrtGen.tables alive (hdOf (deadPre E Gx Jx pc.iv x1)) i)).getD [])

end E1C

/-! ## The log covers the decoder -/

/-- **The log `L` covers the decoder** at the hash table `g`: before the first occurrence of each
`H₂¹` query `x₁`, the log holds the `H₅` queries at `decIns` for the data committed there. -/
def CovL (lr : Bool) (E : CTable) (g : Table) (L : QueryLog specIC) : Prop :=
  ∀ x1, ((.h21, x1) : Dom) ∈ hashLog L →
    ∀ inp ∈ decIns lr E (logBefore (.inl (.h21, x1)) L) x1 (ivX (stE lr) x1 g),
      ((.h5, inp) : Dom) ∈ hashLog (logBefore (.inl (.h21, x1)) L)

end VoleMole.ROM.OneMore.Pomfrit
