import VoleMole.Privacy.Basic
import VoleMole.Spec.PomFRITLayout

/-!
# PomFRIT blindness on the executable spec (`security/pomfrit.md` §8.2, Theorem B)

The blindness game of paper Def. 2.4 in its selective-failure form, against a malicious Issuer
that chooses the key, both messages and both responses, run on `Spec/PomFRIT.lean`'s
`issueRequest` and `finalizeIssue`, with the proof system abstract, on either proof layout
(`Spec/PomFRITLayout.lean`: `Layout.main`, where the definitions are the spec's, or
`Layout.labelRows`).

## Zero knowledge of the two-phase prover

PomFRIT's prover runs in two phases (`voleith_vole_gen`, then `voleith_prove_commit` once the
instance `(pk, h)` is known), so its zero-knowledge property has a delayed instance
(`lean/docs/zk.md` §7.5). `Simulator` has two phases: `phase1` from the binder only, `phase2` from
the instance chosen after phase 1. `ZeroKnowledge P S ε`: for every witness prefix `r`, binder `b`
and continuation `k` (which, after seeing phase 1's output, picks the instance, the witness suffix
`s` and the second binder, or stops) whose choices satisfy `P_pk(s) = h ⊕ r`, the real run
(`realRun`, over uniform `rho`) and the simulated run (`simRun`) are `ε`-close against every
distinguisher. The distinguisher may know `r` and `s`.

**On `main` this hypothesis is false**: the Issuer, knowing `t` and the signature, recovers `r`
(`ZK.issuerGuess_eq`), its sibling-label query hits with probability 1 (`ZK.pomfrit_issuer_hits`,
`ZK.pomfrit_issuer_prU_hit`), and the test of `lean/docs/zk.md` Prop. 4.1 accepts every real proof
(`ZK.pomfrit_attack_test`), so a distinguisher that knows `r` separates real proofs from those of
any simulator (phase 1 sees no instance, so its output cannot depend on `r`). It is the
zero-knowledge theorem of `lean/docs/zk.md` with the label-row fix (`voleith-label-rows`),
derived for the executable Lean prover in `Privacy/PomFRITLean.lean` (`lean_zeroKnowledge`,
`blindness_lean`).

## The game

`Adversary`: the key `pk`, messages `msg false = µ₀`, `msg true = µ₁`, the responses (a function
of both requests, in session order) and the final guess, which sees both requests and, only if both
sessions complete, the two signatures in message order (`outcome`). The Issuer knows `pk`, `s` and
`t`, so it computes the per-session abort pattern (`finalize_issue`'s length check and
`P(s) = t`, `pomfrit.cpp:207`) itself. World `b`: the first session signs `µ_b`, the second
`µ_{¬b}`.

The randomness of a session is the output `(rho, refresher, r)` of `XOF_seed`, drawn uniformly
(hybrid G1 of Theorem B; `issueRequest_eq` is the spec's `issueRequest` with `XOF_seed` applied).
G0 → G1 (the Issuer does not query `XOF_seed` at a session's 32-byte seed, `2·Q_X·2⁻²⁵⁶`, and
Lemma DS) is a random-oracle step that stays on paper.

## Results

* `sessionClose_real_sim`: one session with the real prover and with the simulator are `ε`-close,
  for every response strategy (G1 → G2, one session).
* `simGame_eq`: with both sessions simulated, the two worlds have exactly the same distribution
  (G3). The request `t = h ⊕ r` is a one-time pad (`padEquiv`, `xorBytes_pad`), so after
  re-parametrising `r` the requests are uniform and independent of the messages and simulator
  coins; swapping the two sessions' simulator coins and refreshers (`swapEquiv`) exchanges the
  worlds. The signatures are revealed only when both sessions complete (`outcome_check`).
* **`blindness`**: `|Pr[A accepts in world 0] − Pr[A accepts in world 1]| ≤ 4ε`, i.e.
  `|Pr[b' = b] − 1/2| ≤ 2ε` (Theorem B's `ε_ZK^fix(Q_P = 2)`, without the G0 → G1 term).
  The only further hypothesis is that phase 1 outputs a full-length proof buffer (`hlen`, part of
  `Spec.PomFRIT.Correct` and `Layout.Correct`).
-/

open Finset

namespace VoleMole.Privacy.PomFRIT

open VoleMole.Spec VoleMole.Spec.PomFRIT

variable {St C SimSt : Type}

/-! ## The spec with the seed expansion's output given -/

/-- `issueRequest` with the output `(rho, refresher, r)` of `XOF_seed` as arguments. -/
def issueRequestOf (L : Layout) (P : Prover St) (pk : UOVKey) (msg rho refresher r : Bytes) :
    Pending St × Bytes :=
  let refresherCom := commitRefresher refresher
  let g := P.voleGen r rho refresherCom
  let sig := g.1 ++ refresherCom ++ refresher
  let h := L.hashToTarget pk.digest g.2.1 sig msg
  let t := xorBytes h r
  (⟨pk.digest, t, h, sig, g.2.2⟩, t)

/-- The spec's `issueRequest` is `issueRequestOf` at the output of `XOF_seed` (`main_issueRequest`:
at `Layout.main`, `L.issueRequest` is `Spec.PomFRIT.issueRequest`). -/
theorem issueRequest_eq (L : Layout) (P : Prover St) (pk : UOVKey) (msg seed : Bytes) :
    L.issueRequest P pk msg seed =
      issueRequestOf L P pk msg (expandSeed pk.digest msg seed).1
        (expandSeed pk.digest msg seed).2.1 (expandSeed pk.digest msg seed).2.2 := rfl

/-! ## Zero knowledge of the two-phase prover -/

/-- A two-phase simulator. `phase1 binder c`: the step-1 proof buffer, `chal1` and a state, from the
binder and coins `c` only. `phase2 proof pk h binder₂ σ`: the completed proof, from the instance
`(pk, h)` chosen after phase 1. -/
structure Simulator (C SimSt : Type) where
  phase1 : Bytes → C → Bytes × Bytes × SimSt
  phase2 : Bytes → UOVKey → Bytes → Bytes → SimSt → Bytes

/-- What the environment does after phase 1, from its output `(proof, chal1)`: the instance
`(pk, h)`, the witness suffix `s` and the second binder, or `none` (no second phase). -/
abbrev Cont := Bytes × Bytes → Option (UOVKey × Bytes × Bytes × Bytes)

/-- Every instance the continuation picks is satisfied by the witness `(r, s)`:
`R((pk, h), (r, s)) ⇔ P(s) = h ⊕ r`, with `h` of `M` bytes and `s` of `N` bytes. -/
def Cont.Valid (r : Bytes) (k : Cont) : Prop :=
  ∀ o pk h s b₂, k o = some (pk, h, s, b₂) → h.length = uovM ∧ s.length = uovN ∧
    pk.eval s = xorBytes h r

/-- The real two-phase run on witness prefix `r` and binder `b`, with uniform `rho`. -/
def realRun (P : Prover St) (r b : Bytes) (k : Cont) (ρ : Coins proveSeedBytes) :
    Bytes × Bytes × Option Bytes :=
  let g := P.voleGen r (List.ofFn ρ) b
  (g.1, g.2.1, (k (g.1, g.2.1)).map fun i => P.proveCommit g.1 i.1 i.2.1 i.2.2.1 i.2.2.2 g.2.2)

/-- The simulated run: the witness is never read. -/
def simRun (S : Simulator C SimSt) (b : Bytes) (k : Cont) (c : C) :
    Bytes × Bytes × Option Bytes :=
  let g := S.phase1 b c
  (g.1, g.2.1, (k (g.1, g.2.1)).map fun i => S.phase2 g.1 i.1 i.2.1 i.2.2.2 g.2.2)

/-- **Zero knowledge with a delayed instance**, error `ε`. -/
def ZeroKnowledge [Fintype C] (P : Prover St) (S : Simulator C SimSt) (ε : ℝ) : Prop :=
  ∀ r b k, r.length = uovM → Cont.Valid r k → Close ε (realRun P r b k) (simRun S b k)

/-! ## Sessions and the game -/

/-- A session as the Issuer meets it: the request `t`, and the Client's `finalize_issue` as a
function of the response. -/
abbrev Session := Bytes × (Bytes → Except Error (Option Bytes))

/-- A real session, from `(rho, refresher, r)`. -/
def realSession (L : Layout) (P : Prover St) (pk : UOVKey) (msg : Bytes)
    (x : Coins proveSeedBytes × Coins refresherBytes × Coins uovM) : Session :=
  let q := issueRequestOf L P pk msg (List.ofFn x.1) (List.ofFn x.2.1) (List.ofFn x.2.2)
  (q.2, L.finalizeIssue P pk q.1)

/-- The Client's checks on a response, then the signature `sig` (`finalize_issue` for an honest
pending state). -/
def finish (pk : UOVKey) (t sig s : Bytes) : Except Error (Option Bytes) :=
  if s.length ≠ uovN then .error .malformed
  else if pk.eval s ≠ t then .ok none
  else .ok (some sig)

/-- The target `h` of a simulated session, from its simulator coins and refresher. -/
def simTarget (L : Layout) (S : Simulator C SimSt) (pk : UOVKey) (msg : Bytes) (c : C)
    (ref : Coins refresherBytes) : Bytes :=
  let com := commitRefresher (List.ofFn ref)
  L.hashToTarget pk.digest (S.phase1 com c).2.1 ((S.phase1 com c).1 ++ com ++ List.ofFn ref) msg

/-- The final signature of a simulated session. -/
def simSig (L : Layout) (S : Simulator C SimSt) (pk : UOVKey) (msg : Bytes) (c : C)
    (ref : Coins refresherBytes) : Bytes :=
  let com := commitRefresher (List.ofFn ref)
  S.phase2 (S.phase1 com c).1 pk (simTarget L S pk msg c ref) (List.ofFn ref)
      (S.phase1 com c).2.2 ++
    com ++ List.ofFn ref

/-- A simulated session, from simulator coins, `refresher` and `r`. -/
def simSession (L : Layout) (S : Simulator C SimSt) (pk : UOVKey) (msg : Bytes)
    (x : C × Coins refresherBytes × Coins uovM) : Session :=
  let t := xorBytes (simTarget L S pk msg x.1 x.2.1) (List.ofFn x.2.2)
  (t, finish pk t (simSig L S pk msg x.1 x.2.1))

/-- The Issuer: a key, two messages, the responses in session order, and the final guess. -/
structure Adversary where
  pk : UOVKey
  msg : Bool → Bytes
  respond : Bytes → Bytes → Bool → Bytes
  guess : Bytes → Bytes → Option (Bytes × Bytes) → Prop

/-- The signatures in message order, revealed only if both sessions complete (the session `false`
signs `µ_b`). -/
def outcome (b : Bool) (o₀ o₁ : Except Error (Option Bytes)) : Option (Bytes × Bytes) :=
  match o₀, o₁ with
  | .ok (some x), .ok (some y) => some (bif b then (y, x) else (x, y))
  | _, _ => none

/-- The Issuer's view and guess, from the two sessions. -/
def view (A : Adversary) (b : Bool) (s₀ s₁ : Session) : Prop :=
  A.guess s₀.1 s₁.1
    (outcome b (s₀.2 (A.respond s₀.1 s₁.1 false)) (s₁.2 (A.respond s₀.1 s₁.1 true)))

/-- The game in world `b` with sessions drawn by `g₀`, `g₁`. -/
def game {T₀ T₁ : Type} (A : Adversary) (b : Bool) (g₀ : T₀ → Session) (g₁ : T₁ → Session)
    (x : T₀ × T₁) : Prop :=
  view A b (g₀ x.1) (g₁ x.2)

/-- **The real game** (G1): world `b`, the first session on `µ_b`, the second on `µ_{¬b}`. -/
def realGame (L : Layout) (A : Adversary) (P : Prover St) (b : Bool) :
    (Coins proveSeedBytes × Coins refresherBytes × Coins uovM) ×
      (Coins proveSeedBytes × Coins refresherBytes × Coins uovM) → Prop :=
  game A b (realSession L P A.pk (A.msg b)) (realSession L P A.pk (A.msg !b))

/-- Both sessions simulated (G2). -/
def simGame (L : Layout) (A : Adversary) (S : Simulator C SimSt) (b : Bool) :
    (C × Coins refresherBytes × Coins uovM) × (C × Coins refresherBytes × Coins uovM) → Prop :=
  game A b (simSession L S A.pk (A.msg b)) (simSession L S A.pk (A.msg !b))

/-! ## Hops on one session -/

/-- Two session samplers are `ε`-close for every response strategy `f`. -/
def SessionClose {T T' : Type} [Fintype T] [Fintype T'] (ε : ℝ) (g : T → Session)
    (g' : T' → Session) : Prop :=
  ∀ f : Bytes → Bytes, Close ε (fun x => ((g x).1, (g x).2 (f (g x).1)))
    (fun x => ((g' x).1, (g' x).2 (f (g' x).1)))

variable {T₀ T₁ T₀' T₁' : Type} [Fintype T₀] [Fintype T₁] [Fintype T₀'] [Fintype T₁']

theorem game_hop₀ [Nonempty T₁] (A : Adversary) (b : Bool) {ε : ℝ} {g₀ : T₀ → Session}
    {g₀' : T₀' → Session} (g₁ : T₁ → Session) (h : SessionClose ε g₀ g₀') :
    |pr (T₀ × T₁) (game A b g₀ g₁) - pr (T₀' × T₁) (game A b g₀' g₁)| ≤ ε :=
  abs_pr_prod_sub_le' _ _ fun x₁ => h (fun t => A.respond t (g₁ x₁).1 false)
    (fun p => A.guess p.1 (g₁ x₁).1 (outcome b p.2 ((g₁ x₁).2 (A.respond p.1 (g₁ x₁).1 true))))

theorem game_hop₁ [Nonempty T₀] (A : Adversary) (b : Bool) {ε : ℝ} (g₀ : T₀ → Session)
    {g₁ : T₁ → Session} {g₁' : T₁' → Session} (h : SessionClose ε g₁ g₁') :
    |pr (T₀ × T₁) (game A b g₀ g₁) - pr (T₀ × T₁') (game A b g₀ g₁')| ≤ ε :=
  abs_pr_prod_sub_le _ _ fun x₀ => h (fun t => A.respond (g₀ x₀).1 t true)
    (fun p => A.guess (g₀ x₀).1 p.1 (outcome b ((g₀ x₀).2 (A.respond (g₀ x₀).1 p.1 false)) p.2))

/-- **G1 → G2 for one session.** A real session and a simulated one are `ε`-close, whatever the
Issuer answers, if the prover is `ε`-zero-knowledge. -/
theorem sessionClose_real_sim [Fintype C] (L : Layout) (P : Prover St) (S : Simulator C SimSt)
    {ε : ℝ} (hlen : ∀ r ρ b, (P.voleGen r ρ b).1.length = L.proofBytes)
    (hZK : ZeroKnowledge P S ε) (pk : UOVKey) (msg : Bytes) :
    SessionClose ε (realSession L P pk msg) (simSession L S pk msg) := by
  intro f
  refine Close.congr (Close.prod_left (X := fun ρ y => ((realSession L P pk msg (ρ, y)).1,
      (realSession L P pk msg (ρ, y)).2 (f (realSession L P pk msg (ρ, y)).1)))
    (Y := fun c y => ((simSession L S pk msg (c, y)).1,
      (simSession L S pk msg (c, y)).2 (f (simSession L S pk msg (c, y)).1))) fun y => ?_)
    (fun _ => rfl) (fun _ => rfl)
  -- Fix `refresher` and `r`; only `rho` (resp. the simulator coins) varies.
  set ref := List.ofFn y.1 with href
  set rr := List.ofFn y.2 with hrr
  set com := commitRefresher ref with hcom
  let hOf : Bytes × Bytes → Bytes := fun o => L.hashToTarget pk.digest o.2 (o.1 ++ com ++ ref) msg
  let k : Cont := fun o =>
    if (f (xorBytes (hOf o) rr)).length = uovN ∧ pk.eval (f (xorBytes (hOf o) rr)) =
      xorBytes (hOf o) rr then some (pk, hOf o, f (xorBytes (hOf o) rr), ref) else none
  have hk : Cont.Valid rr k := by
    intro o pk' h s b₂ hko
    simp only [k] at hko
    split_ifs at hko with hc
    cases hko
    exact ⟨L.length_hashToTarget _ _ _ _, hc.1, hc.2⟩
  let Φ : Bytes × Bytes × Option Bytes → Bytes × Except Error (Option Bytes) := fun z =>
    (xorBytes (hOf (z.1, z.2.1)) rr,
      if (f (xorBytes (hOf (z.1, z.2.1)) rr)).length ≠ uovN then .error .malformed else
        match z.2.2 with
        | none => .ok none
        | some p => .ok (some (p ++ com ++ ref)))
  refine Close.congr ((hZK rr com k (by simp [hrr]) hk).map Φ) (fun ρ => ?_) (fun c => ?_)
  · -- The real session is `Φ` of the real run.
    have hpl := hlen rr (List.ofFn ρ) com
    obtain ⟨f1, f2, f3, -, -, -⟩ := L.sig_fields hpl (length_commitRefresher ref)
      (by simp [href, refresherBytes] : ref.length = refresherBytes)
    simp only [realSession, issueRequestOf, Layout.finalizeIssue, realRun, Φ, k, hOf, ← href,
      ← hrr, ← hcom, ne_eq, not_true_eq_false, ↓reduceIte]
    split_ifs with h1 h2 h3 <;> simp_all
  · -- So is the simulated session.
    simp only [simSession, simTarget, simSig, simRun, finish, Φ, k, hOf, ← href, ← hrr, ← hcom]
    split_ifs with h1 h2 h3 <;> simp_all

/-! ## G3: with both sessions simulated, the worlds coincide -/

/-- XOR with the first `n` bytes of `h`. -/
def pad {n : ℕ} (h : Bytes) (u : Coins n) : Coins n := fun i => h.getD i 0 ^^^ u i

theorem pad_pad {n : ℕ} (h : Bytes) (u : Coins n) : pad h (pad h u) = u := by
  funext i
  simp [pad]

/-- **The one-time pad**: `t = h ⊕ r` at `r = pad h u` is `u`. -/
theorem xorBytes_pad {n : ℕ} {h : Bytes} (hl : h.length = n) (u : Coins n) :
    xorBytes h (List.ofFn (pad h u)) = List.ofFn u := by
  apply List.ext_getElem
  · simp [length_xorBytes, hl]
  · intro i h1 h2
    simp only [xorBytes, List.getElem_zipWith, List.getElem_ofFn, pad]
    rw [List.getD_eq_getElem _ _ (by simp [length_xorBytes, hl] at h1; omega), ← UInt8.xor_assoc,
      UInt8.xor_self, UInt8.zero_xor]

/-- Re-parametrise `r` by the session's one-time pad. -/
def padEquiv (L : Layout) (S : Simulator C SimSt) (pk : UOVKey) (msg : Bytes) :
    (C × Coins refresherBytes × Coins uovM) ≃ (C × Coins refresherBytes × Coins uovM) where
  toFun x := (x.1, x.2.1, pad (simTarget L S pk msg x.1 x.2.1) x.2.2)
  invFun x := (x.1, x.2.1, pad (simTarget L S pk msg x.1 x.2.1) x.2.2)
  left_inv x := by simp [pad_pad]
  right_inv x := by simp [pad_pad]

/-- The ideal session: the request is the uniform `u`, the signature is simulated. -/
def idealSession (L : Layout) (S : Simulator C SimSt) (pk : UOVKey) (msg : Bytes)
    (x : C × Coins refresherBytes × Coins uovM) : Session :=
  (List.ofFn x.2.2, finish pk (List.ofFn x.2.2) (simSig L S pk msg x.1 x.2.1))

theorem simSession_padEquiv (L : Layout) (S : Simulator C SimSt) (pk : UOVKey) (msg : Bytes)
    (x : C × Coins refresherBytes × Coins uovM) :
    simSession L S pk msg (padEquiv L S pk msg x) = idealSession L S pk msg x := by
  have ht : xorBytes (simTarget L S pk msg x.1 x.2.1)
      (List.ofFn (pad (simTarget L S pk msg x.1 x.2.1) x.2.2)) = List.ofFn x.2.2 :=
    xorBytes_pad (L.length_hashToTarget _ _ _ _) _
  simp only [simSession, padEquiv, Equiv.coe_fn_mk, idealSession, ht]

/-- The outcome of two honest-format sessions: the signatures iff both checks pass. -/
theorem outcome_finish (b : Bool) (pk : UOVKey) (t₀ t₁ x y s₀ s₁ : Bytes) :
    outcome b (finish pk t₀ x s₀) (finish pk t₁ y s₁) =
      if (s₀.length = uovN ∧ pk.eval s₀ = t₀) ∧ (s₁.length = uovN ∧ pk.eval s₁ = t₁) then
        some (bif b then (y, x) else (x, y)) else none := by
  unfold finish
  by_cases h0 : s₀.length = uovN <;> by_cases e0 : pk.eval s₀ = t₀ <;>
    by_cases h1 : s₁.length = uovN <;> by_cases e1 : pk.eval s₁ = t₁ <;>
    simp [outcome, h0, e0, h1, e1]

/-- Exchange the simulator coins and refreshers of the two sessions, keeping the requests. -/
def swapEquiv :
    (C × Coins refresherBytes × Coins uovM) × (C × Coins refresherBytes × Coins uovM) ≃
      (C × Coins refresherBytes × Coins uovM) × (C × Coins refresherBytes × Coins uovM) where
  toFun x := ((x.2.1, x.2.2.1, x.1.2.2), (x.1.1, x.1.2.1, x.2.2.2))
  invFun x := ((x.2.1, x.2.2.1, x.1.2.2), (x.1.1, x.1.2.1, x.2.2.2))
  left_inv _ := rfl
  right_inv _ := rfl

/-- **G3.** With both sessions simulated, the Issuer's acceptance probability is the same in both
worlds: exactly, with no assumption. -/
theorem simGame_eq [Fintype C] (L : Layout) (A : Adversary) (S : Simulator C SimSt) :
    pr _ (simGame L A S false) = pr _ (simGame L A S true) := by
  let pe (b : Bool) := (padEquiv L S A.pk (A.msg b)).prodCongr (padEquiv L S A.pk (A.msg !b))
  have hideal (b : Bool) (x) : simGame L A S b (pe b x) ↔
      game A b (idealSession L S A.pk (A.msg b)) (idealSession L S A.pk (A.msg !b)) x := by
    simp only [simGame, game, pe, Equiv.prodCongr_apply, Prod.map, simSession_padEquiv]
  rw [← pr_equiv (pe false) (simGame L A S false), ← pr_equiv (pe true) (simGame L A S true),
    pr_congr (hideal false), pr_congr (hideal true), ← pr_equiv swapEquiv]
  refine pr_congr fun x => ?_
  simp only [game, view, idealSession, swapEquiv, Equiv.coe_fn_mk, outcome_finish, Bool.not_true,
    Bool.not_false, Bool.cond_true, Bool.cond_false]

/-! ## Blindness -/

/-- **Blindness (Theorem B, from G1).** If the two-phase prover is `ε`-zero-knowledge (true with
the label-row fix, false on `main`) and phase 1 outputs a full-length proof buffer, then for every
Issuer (any key, messages and responses) the acceptance probabilities in the two worlds differ by
at most `4ε`. -/
theorem blindness [Fintype C] [Nonempty C] (L : Layout) (A : Adversary) (P : Prover St)
    (S : Simulator C SimSt) {ε : ℝ} (hlen : ∀ r ρ b, (P.voleGen r ρ b).1.length = L.proofBytes)
    (hZK : ZeroKnowledge P S ε) :
    |pr _ (realGame L A P false) - pr _ (realGame L A P true)| ≤ 4 * ε := by
  have hS := sessionClose_real_sim L P S hlen hZK A.pk
  have hw (b : Bool) : |pr _ (realGame L A P b) - pr _ (simGame L A S b)| ≤ 2 * ε := by
    have h0 := game_hop₀ A b (realSession L P A.pk (A.msg !b)) (hS (A.msg b))
    have h1 := game_hop₁ A b (simSession L S A.pk (A.msg b)) (hS (A.msg !b))
    calc _ ≤ _ := abs_sub_le _ (pr _ (game A b (simSession L S A.pk (A.msg b))
            (realSession L P A.pk (A.msg !b)))) _
      _ ≤ ε + ε := add_le_add h0 h1
      _ = 2 * ε := by ring
  have h0 := hw false
  have h1 := hw true
  rw [simGame_eq L A S] at h0
  calc _ ≤ _ := abs_sub_le _ (pr _ (simGame L A S true)) _
    _ ≤ 2 * ε + 2 * ε := add_le_add h0 (by rw [abs_sub_comm]; exact h1)
    _ = 4 * ε := by ring

end VoleMole.Privacy.PomFRIT
