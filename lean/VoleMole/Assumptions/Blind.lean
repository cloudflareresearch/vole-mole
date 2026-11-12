import VoleMole.Assumptions.Shift

/-!
# OMPR is at most one-more unforgeability of a blind preimage scheme (Theorem 6, generic core)

`lean/docs/security/uov-assumptions.md` §5.6. Protocol-independent; the one-more game is
`OneMore.omuf` with the programmed target `H_T(x) + h` of `addHint` (PomFRIT's U1 game shape).

**The scheme** (`Client`): an honest client whose session `k` first computes, with its own random
oracle (`specR AC`, the protocol's hashes) and coins `κ`, a label `x` (the `H_T` input), a blinding
`r` and a state (`start`); the blinded request is `H_T(x) + r`; after the Issuer's answer `s` the
sessions are finished and verified by `post` (any oracle computation over the client's oracle and
`H_T`, no Issuer), which returns one acceptance flag. For PomFRIT, `start` is `issue_request` up
to `hash_to_target`'s input, `r` the client's blinding, `post` the finalization and `pomfritVerify`
of every session.

**The forger** (`blindAdv`): from an OMPR adversary `B` (labelled targets on demand, `omExp`),
it runs `B` with its world forwarded (`B`'s world is separate from the client's: the composed
world is the sum `Sum.elim AR AC`), answers `B`'s `k`-th request (`k < n`) by running session `k`
and passing on its blinded request `H_T(x) + r`, and forwards `B`'s preimage queries to the
Issuer. It claims, for each claim `(x', s)` of `B`, the label of `x'`'s session with `s`.

**Theorem** (`ompr_le_blind`): if the sessions' labels are pairwise distinct (on the supports),

    Adv^{ompr}(B; n, ℓ) ≤ Pr[Forges] + Pr[CompFail],

`CompFail`: the forger's `ℓ + 1` claims are preimages of their programmed targets
`H_T(x) + r` (on distinct labels, within `ℓ` Issuer queries) but `post` rejects: a completeness
failure of the client. The proof: the target oracle is programmed perfectly
(`OneMore.real_eqd_comb`), so `B` sees each challenge `t = (t − r) + r` exactly as in `omExp`
(`bcomb_eqd`, the client's runs integrated out: they read only the client's oracle).

With U1 (`pomfrit_U1_ompr`) this is the equivalence of §5.6 up to Lemma P's and the completeness
terms. **Not done**: the PomFRIT instance. It needs the Lean client (`issue_request`, `finalize`)
as an oracle computation over the game's oracles and its completeness in this lazy random-oracle
model (`ZK/CompleteRO.lean` proves it, `≤ 2⁻¹¹³` per session, in the finite-table model), and a
`Forger` with coins.

No `sorry`, no `axiom`.
-/

open OracleComp OracleSpec VoleMole.ROM.OneMore VoleMole.Assumptions.UOV VoleMole.Assumptions.Shift
open scoped ENNReal

namespace VoleMole.Assumptions.Blind

section Defs

variable {DR DC : Type} (AR : DR → Type) (AC : DC → Type)

/-- The composed world: `B`'s world and the client's oracle. -/
abbrev WA : DR ⊕ DC → Type := Sum.elim AR AC

instance instSampWA [∀ d, SampleableType (AR d)] [∀ d, SampleableType (AC d)] :
    ∀ d, SampleableType (WA AR AC d)
  | .inl d => inferInstanceAs (SampleableType (AR d))
  | .inr d => inferInstanceAs (SampleableType (AC d))

variable (X G : Type)

/-- The oracles of the client's finishing phase: its oracle and `H_T` (with a hint). -/
abbrev specV : OracleSpec (DC ⊕ (X × G)) := OracleSpec.ofFn (Sum.elim AC fun _ : X × G => G × G)

variable (Hn' St : Type)

/-- A session: its index, label, blinding, state, the `H_T` answer, and `B`'s hint. -/
structure Ses where
  idx : ℕ
  x : X
  r : G
  st : St
  u : G
  hB : Hn'

variable (X' : Type)

/-- The forger's state: the number of sessions started, and the session of each of `B`'s labels. -/
structure BSt where
  k : ℕ
  ses : X' → Option (Ses X G Hn' St)

end Defs

variable {DR DC : Type} [DecidableEq DR] [DecidableEq DC] {AR : DR → Type} {AC : DC → Type}
  [∀ d, SampleableType (AR d)] [∀ d, SampleableType (AC d)]
  {X' Hn' X G S St Cn PK : Type} [DecidableEq X'] [DecidableEq X] [AddCommGroup G]

variable (AC X G S St Cn PK) in
/-- **An honest blind-preimage client**: coins, the first phase of session `k` (label, blinding,
state) over its oracle, and the finishing phase of the claimed sessions `(x, r, st, u, s)` (`u`
the `H_T` answer, `s` the Issuer's preimage) with one acceptance flag. -/
structure Client where
  coins : ProbComp Cn
  start : PK → Cn → ℕ → OracleComp (specR AC) (X × G × St)
  post : PK → Cn → List (X × G × St × G × S) → OracleComp (specV AC X G) Bool

/-- The client's oracle inside the composed adversary. -/
def liftC : QueryImpl (specR AC) (OracleComp (specA (WA AR AC) X G G S)) := fun d =>
  liftM ((specA (WA AR AC) X G G S).query (.inl (.inr d)))

/-- The finishing phase inside the composed adversary. -/
def liftV : QueryImpl (specV AC X G) (OracleComp (specA (WA AR AC) X G G S))
  | .inl d => liftM ((specA (WA AR AC) X G G S).query (.inl (.inr d)))
  | .inr q => liftM ((specA (WA AR AC) X G G S).query (.inr (.inl q)))

variable (cl : Client AC X G S St Cn PK) (n : ℕ)

/-- **The blinding forger's handler** for `B`'s queries. -/
def blindImpl (pk : PK) (κ : Cn) :
    QueryImpl (specB AR X' Hn' G S) (StateT (BSt X G Hn' St X') (OracleComp (specA (WA AR AC) X G G S)))
  | .inl d => StateT.mk fun s => (fun a => (a, s)) <$>
      (liftM ((specA (WA AR AC) X G G S).query (.inl (.inl d))) :
        OracleComp (specA (WA AR AC) X G G S) (AR d))
  | .inr (.inl (x', hB)) => StateT.mk fun s =>
      if s.k < n then do
        let o ← simulateQ liftC (cl.start pk κ s.k)
        let a ← (liftM ((specA (WA AR AC) X G G S).query (.inr (.inl (o.1, o.2.1)))) :
          OracleComp (specA (WA AR AC) X G G S) (G × G))
        pure (some (a.1 + o.2.1),
          ⟨s.k + 1, Function.update s.ses x' (some ⟨s.k, o.1, o.2.1, o.2.2, a.1, hB⟩)⟩)
      else pure (none, s)
  | .inr (.inr t) => StateT.mk fun s => (fun a => (a, s)) <$>
      (liftM ((specA (WA AR AC) X G G S).query (.inr (.inr t))) :
        OracleComp (specA (WA AR AC) X G G S) S)

/-- The initial forger state. -/
def bs0 : BSt X G Hn' St X' := ⟨0, fun _ => none⟩

/-- The claimed sessions: for each claim `(x', s)` of `B` with a session, the session's data and
`s`. -/
def claimed (z : List (X' × S) × BSt X G Hn' St X') : List (X × G × St × G × S) :=
  z.1.filterMap fun p => (z.2.ses p.1).map fun e => (e.x, e.r, e.st, e.u, p.2)

/-- **The blinding forger** (a composed adversary of `OneMore.omuf`, hints the blindings): `B`
with its requests answered by fresh sessions, then the client's finishing phase. Its claims are
the claimed sessions' labels with `B`'s preimages. -/
def blindAdv (B : PK → ProbComp (OracleComp (specB AR X' Hn' G S) (List (X' × S)))) (pk : PK) :
    ProbComp (OracleComp (specA (WA AR AC) X G G S) (List (X × S) × Bool)) := do
  let b ← B pk
  let κ ← cl.coins
  pure do
    let z ← (simulateQ (blindImpl cl n pk κ) b).run bs0
    let f ← simulateQ liftV (cl.post pk κ (claimed z))
    pure ((claimed z).map fun e => (e.1, e.2.2.2.2), f)

end VoleMole.Assumptions.Blind
