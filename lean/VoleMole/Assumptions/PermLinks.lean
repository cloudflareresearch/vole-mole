import VoleMole.Assumptions.CTUFPerm
import VoleMole.Assumptions.SimLinks
import VoleMole.Assumptions.UnboundLinks

/-!
# The protocol theorems down to one-more-UOV, with `Com` a random permutation (inverse queries)

`Assumptions/SimLinks.lean` (`omuf_le_num_ompr_sim`) and `Assumptions/UnboundLinks.lean`
(`omufU_le_num_ompr_sim`) with the modelling step moved from the random-function model of `Com`
to the permutation model (`Assumptions/CTUFPerm.lean`, `uov-assumptions.md` §5.4): `KP800` is a
random permutation of the blocks `T × Z`, with forward and inverse queries, in the standalone
CT-UF^open game. The modelling hypothesis `hmodelP` states that the concrete CT-UF^open advantage
of `B₂` is at most the permutation-model advantage `advCTUFPermAt` of some forger `F` within a
budget `(q_f, q_i, q_S)`, for an injective encoding `emb` of the openings into the blocks. The
OMPR bound then carries the permutation terms explicitly (`permEps`):

    Pr[Win] ≤ εIR^sim + AdvBind(B₁)
              + Σ_j (Adv^{ompr}_{key j}(B_j; n, q_S) + n·failPr_{key j})
              + (q_f + q_i + q_S + 1)²/|T × Z| + q_i·|Xc|/|T × Z|,

`n = (q_f + q_S + 1) + 2q_S + 1`. For KP800, `|T × Z| = 2^{800}` and `|Xc| = 2^{576}`.

* **`omuf_le_num_ompr_perm`** (Moussaka), **`omufU_le_num_ompr_perm`** (unbound Moussaka).

No `sorry`, no `axiom`.
-/

open OracleComp OracleSpec
open scoped ENNReal

namespace VoleMole.Assumptions.UOV.Links

open VoleMole.ROM VoleMole.ROM.IC VoleMole.Prob VoleMole.Verifier VoleMole.ZK.Sim
open CTUFOpen CTUFPerm

section Moussaka

open VoleMole.ROM.IC.OMUF

variable {K qR : ℕ} (lr : Bool) (pk : Fin K → UovPk) (sk : Fin K → Spec.Signer) (qI : ℕ)
  {A : Adversary K qR} {q : Kind → ℕ} {qE n : ℕ}
  {DR : Type} [DecidableEq DR] {AR : DR → Type} [∀ d, SampleableType (AR d)]
  {Xc T Z S PK SK : Type} [DecidableEq Xc] [DecidableEq T] [DecidableEq Z] [Inhabited T]
  [SampleableType T] [SampleableType Z] [Fintype T] [Fintype Z] [Fintype Xc]
  (tr : Trapdoor PK SK T S) (ks : Fin K → PK × SK) {qf qi qS : ℕ}

/-- **Theorem 1 down to OMPR, `Com` a random permutation with inverse queries** (simultaneous
extraction). `hmodelP` is **the modelling step, a hypothesis**: `B₂`'s CT-UF^open advantage with
the concrete `Com = KP800(·)|_{360}` is at most the permutation-model advantage of some forger `F`
within the budget `(q_f, q_i, q_S)` against the signers of keys `ks` of a trapdoor `tr`, `Com(x)`
the first component of `π(emb x)`. Under it,

    Pr[Win] ≤ εIR^sim + AdvBind(B₁) + Σ_j (Adv^{ompr}_{key j}(B_j; n, q_S) + n·failPr_{key j})
              + permEps(q_f + q_i + q_S + 1, q_i, |Xc|, |T × Z|),

`n = (q_f + q_S + 1) + 2q_S + 1`. -/
theorem omuf_le_num_ompr_perm (hA : A.Budget q qE n) (hdig : ∀ k, (pk k).digest.size = 32)
    (hdinj : Function.Injective fun k => (pk k).digest) {emb : Xc → T × Z}
    (hemb : Function.Injective emb)
    (F : ProbComp (OracleComp (specCP AR K T Z S) (CTOut K S Xc)))
    (hF : ∀ f ∈ support F, CPBudget qf qi qS f)
    (hmodelP : advCTUFOpenAt (verK pk) comO WFO
        (signers (fun (sk : Spec.Signer) => sk.derivePreimage) sk) (ctufForger lr pk qI A) ≤
      advCTUFPermAt (fun k => tr.IsPre (ks k).1) (signers tr.D fun k => (ks k).2) emb F) :
    Pr{let E ← $ᵗ CTable; let r ← (simulateQ randomOracle (runE E (OMUF.game lr pk sk qI A))).run' ∅}[
        Win r.1] ≤
      epsIRsim (gameK q qI qR) (gameE lr qE qI qR) (gameH n qI qR) qI qR +
      Pr{let E ← $ᵗ CTable; let v ← (simulateQ randomOracle (extAll lr pk sk qI A E)).run' ∅}[
        Coll lr pk E v] +
      (∑ j : Fin K, (advOMPR (tr.atKey (ks j)) ((qf + qS + 1) + 2 * qS + 1) qS
          (ompRed qS fun _ => guessF j (signers tr.D fun k => (ks k).2) <$> permRed emb F) +
        (((qf + qS + 1) + 2 * qS + 1 : ℕ) : ℝ≥0∞) * preFailPr (tr.atKey (ks j))) +
        permEps (qf + qi + qS + 1) qi (Fintype.card Xc) (Fintype.card (T × Z))) :=
  (omuf_le_num_open_sim lr pk sk qI hA hdig hdinj).trans
    (add_le_add le_rfl (hmodelP.trans (advCTUFPermAt_le_ompr tr ks hemb F hF)))

end Moussaka

section Unbound

open VoleMole.ROM.IC.OMUF VoleMole.ROM.IC.OMUFU

variable {K qR : ℕ} (lr : Bool) (pk : Fin K → UovPk) (sk : Fin K → Spec.Signer) (qI : ℕ)
  {A : OMUFU.Adversary K qR} {q : Kind → ℕ} {qE n : ℕ}
  {DR : Type} [DecidableEq DR] {AR : DR → Type} [∀ d, SampleableType (AR d)]
  {Xc T Z S PK SK : Type} [DecidableEq Xc] [DecidableEq T] [DecidableEq Z] [Inhabited T]
  [SampleableType T] [SampleableType Z] [Fintype T] [Fintype Z] [Fintype Xc]
  (tr : Trapdoor PK SK T S) (ks : Fin K → PK × SK) {qf qi qS : ℕ}

/-- **Theorem U1 down to OMPR, `Com ∪ UCom` a random permutation with inverse queries**
(simultaneous extraction; `emb` encodes the union domain's openings, both input spaces, into the
blocks). `hmodelP` is the modelling step, a hypothesis, as in `omuf_le_num_ompr_perm`:

    Pr[Win] ≤ εI^sim + εU^sim + AdvBind(B₁) + Σ_j (Adv^{ompr}_{key j}(B_j; n, q_S) + n·failPr_{key j})
              + permEps(q_f + q_i + q_S + 1, q_i, |Xc|, |T × Z|). -/
theorem omufU_le_num_ompr_perm (hA : A.Budget q qE n) (hdig : ∀ k, (pk k).digest.size = 32)
    (hdinj : Function.Injective fun k => (pk k).digest) {emb : Xc → T × Z}
    (hemb : Function.Injective emb)
    (F : ProbComp (OracleComp (specCP AR K T Z S) (CTOut K S Xc)))
    (hF : ∀ f ∈ support F, CPBudget qf qi qS f)
    (hmodelP : advCTUFOpenAt (verK pk) comX WFX
        (signers (fun (sk : Spec.Signer) => sk.derivePreimage) sk) (ctufForgerU lr pk qI A) ≤
      advCTUFPermAt (fun k => tr.IsPre (ks k).1) (signers tr.D fun k => (ks k).2) emb F) :
    Pr{let E ← $ᵗ CTable; let r ← (simulateQ randomOracle
        (runE E (OMUFU.game lr pk sk qI A))).run' ∅}[OMUFU.Win r.1] ≤
      epsIsim (OMUFU.gameK q qI qR) (OMUFU.gameE lr qE qI qR) qI +
      epsUsim (OMUFU.gameK q qI qR) (OMUFU.gameE lr qE qI qR) (OMUFU.gameH n qI qR) qI qR +
      Pr{let E ← $ᵗ CTable; let v ← (simulateQ randomOracle
        (OMUFU.extAll lr pk sk qI A E)).run' ∅}[OMUFU.Coll lr pk E v] +
      (∑ j : Fin K, (advOMPR (tr.atKey (ks j)) ((qf + qS + 1) + 2 * qS + 1) qS
          (ompRed qS fun _ => guessF j (signers tr.D fun k => (ks k).2) <$> permRed emb F) +
        (((qf + qS + 1) + 2 * qS + 1 : ℕ) : ℝ≥0∞) * preFailPr (tr.atKey (ks j))) +
        permEps (qf + qi + qS + 1) qi (Fintype.card Xc) (Fintype.card (T × Z))) :=
  (omufU_le_num_open_sim lr pk sk qI hA hdig hdinj).trans
    (add_le_add le_rfl (hmodelP.trans (advCTUFPermAt_le_ompr tr ks hemb F hF)))

end Unbound

end VoleMole.Assumptions.UOV.Links
