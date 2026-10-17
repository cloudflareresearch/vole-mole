import Mathlib

/-!
# Domain separation of every SHAKE128 call in vole-mole

Paper proof: `lean/docs/security/domain-separation.md` (§3). The proof-system rows are those of
`lean/docs/extraction/L0-L2-commitments.md` §2.1, refined per relation; the application rows come from
`src/pomfrit/pomfrit.cpp`, `src/moussaka/moussaka.cpp`, `src/ratatouille/ratatouille.cpp` and
`src/uov/circuit.hpp`. Every length was measured by tracing the examples (§2.4 of the paper proof).

A domain is described by a known prefix, a known suffix, and a set of possible input lengths. A
string belongs to the domain if it has the prefix, the suffix and an allowed length. Two domains
are *separated* if their length sets are disjoint, or their prefixes disagree at some position, or
their suffixes do. Separation implies that no string belongs to both (`sep_sound`).

We prove:
* `clean_pairwise`: the 23 domains other than PomFRIT's `hash_to_target` and seed XOF are
  pairwise separated;
* `target_sep`, `seed_sep`: those two are separated from every other domain except the listed
  proof-system domains;
* `target_meets_*`, `seed_meets_*`: for each listed exception there is a concrete string in both
  domains, so the exceptions are real;
* `fixed_pairwise`: after appending a final byte `0x20` to those two inputs (the proposed fix),
  all 25 domains are pairwise separated.
-/

namespace VoleMole.Protocols.DomainSeparation

/-! ## Shapes and the separation criterion -/

/-- The allowed input lengths: an explicit list, or every length from a bound on. -/
inductive LenSpec
  | exact (s : List ℕ)
  | atLeast (n : ℕ)

def LenSpec.mem : LenSpec → ℕ → Prop
  | .exact s, n => n ∈ s
  | .atLeast m, n => m ≤ n

instance (L : LenSpec) (n : ℕ) : Decidable (L.mem n) := by
  cases L <;> simp only [LenSpec.mem] <;> infer_instance

/-- A hash domain: known first bytes, known last bytes, allowed lengths. -/
structure Shape where
  pre : List ℕ
  suf : List ℕ
  len : LenSpec

def Shape.mem (D : Shape) (x : List ℕ) : Prop :=
  D.pre <+: x ∧ D.suf <:+ x ∧ D.len.mem x.length

/-- The two length sets have no common element. -/
def lenDisjoint : LenSpec → LenSpec → Bool
  | .exact s, .exact t => s.all fun a => !(t.contains a)
  | .exact s, .atLeast m => s.all fun a => decide (a < m)
  | .atLeast m, .exact t => t.all fun a => decide (a < m)
  | .atLeast _, .atLeast _ => false

/-- The two lists differ at some position below both lengths. -/
def conflict : List ℕ → List ℕ → Bool
  | a :: p, b :: q => a != b || conflict p q
  | _, _ => false

def sep (D E : Shape) : Bool :=
  lenDisjoint D.len E.len || conflict D.pre E.pre || conflict D.suf.reverse E.suf.reverse

theorem lenDisjoint_sound {a b : LenSpec} (h : lenDisjoint a b = true) {n : ℕ}
    (ha : a.mem n) : ¬ b.mem n := by
  cases a with
  | exact s =>
    cases b with
    | exact t =>
      intro hb
      have := (List.all_eq_true.mp h) n ha
      have h2 : t.contains n = true := by simpa [LenSpec.mem] using hb
      rw [h2] at this
      exact Bool.false_ne_true this
    | atLeast m =>
      intro hb
      have := (List.all_eq_true.mp h) n ha
      simp only [decide_eq_true_eq] at this
      exact absurd hb (Nat.not_le.mpr this)
  | atLeast m =>
    cases b with
    | exact t =>
      intro hb
      have := (List.all_eq_true.mp h) n hb
      simp only [decide_eq_true_eq] at this
      exact absurd ha (Nat.not_le.mpr this)
    | atLeast _ => simp [lenDisjoint] at h

theorem conflict_append_right (p r : List ℕ) : conflict p (p ++ r) = false := by
  induction p with
  | nil => rfl
  | cons a p ih => simp [conflict, ih]

theorem conflict_append_left (p r : List ℕ) : conflict (p ++ r) p = false := by
  induction p with
  | nil => cases r <;> rfl
  | cons a p ih => simp [conflict, ih]

/-- Two lists that are both prefixes of one string do not conflict. -/
theorem conflict_prefix {p q x : List ℕ} (hp : p <+: x) (hq : q <+: x) : conflict p q = false := by
  rcases List.prefix_or_prefix_of_prefix hp hq with ⟨r, rfl⟩ | ⟨r, rfl⟩
  · exact conflict_append_right p r
  · exact conflict_append_left q r

theorem sep_sound {D E : Shape} (h : sep D E = true) {x : List ℕ} (hD : D.mem x) : ¬ E.mem x := by
  rintro ⟨hpre, hsuf, hlen⟩
  simp only [sep, Bool.or_eq_true] at h
  rcases h with (h | h) | h
  · exact lenDisjoint_sound h hD.2.2 hlen
  · rw [conflict_prefix hD.1 hpre] at h; exact Bool.false_ne_true h
  · rw [conflict_prefix (List.reverse_prefix.mpr hD.2.1) (List.reverse_prefix.mpr hsuf)] at h
    exact Bool.false_ne_true h

/-! ## Byte constants (`src/dst.hpp`) -/

/-- `make_dst(protocol, 0, purpose, index)`; VERSION is 0 for all three protocols. -/
def mous (purpose index : ℕ) : List ℕ := [0x6d, 0x6f, 0x75, 0x73, 0, purpose, index]
def pomf (purpose index : ℕ) : List ℕ := [0x70, 0x6f, 0x6d, 0x66, 0, purpose, index]
def rata (purpose index : ℕ) : List ℕ := [0x72, 0x61, 0x74, 0x61, 0, purpose, index]

def c' : ℕ := 0x63
def h' : ℕ := 0x68
def i' : ℕ := 0x69
def l' : ℕ := 0x6c
def p' : ℕ := 0x70
def r' : ℕ := 0x72
def s' : ℕ := 0x73
def z0 : ℕ := 0x30
def z1 : ℕ := 0x31

/-! ## The domains -/

/-- Moussaka redeem: `u32(MAX_ANCHORS) ‖ u32(k) ‖ k·32 ‖ nf ‖ ctx ‖ ctx ‖ digest ‖ DST ‖ 08`,
`1 ≤ k ≤ 64`. -/
def mrLens : List ℕ := (List.range 64).map fun k => 104 + 32 * (k + 1)

/-- Proof-system domains (suffix-tagged), per relation where the lengths differ. -/
def proofSystem : List (String × Shape) :=
  [("H1 leaves k=8", ⟨[], [0x01], .exact [8193]⟩),
   ("H1 leaves k=7", ⟨[], [0x01], .exact [4097]⟩),
   ("H1 com", ⟨[], [0x01], .exact [545]⟩),
   ("H2^0 pomfrit", ⟨[], pomf p' z0 ++ [0x08], .exact [85]⟩),
   ("H2^0 moussaka issue", ⟨[], mous i' z0 ++ [0x08], .exact [69]⟩),
   ("H2^0 moussaka redeem", ⟨[0x40, 0, 0, 0], mous r' z0 ++ [0x08], .exact mrLens⟩),
   ("H2^0 ratatouille issue", ⟨[], rata i' z0 ++ [0x08], .exact [64]⟩),
   ("H2^0 ratatouille spend", ⟨[], rata p' z0 ++ [0x08], .exact [120]⟩),
   ("H2^4 pomfrit", ⟨pomf p' z0, [0x0C], .exact [8]⟩),
   ("H3", ⟨[], [0x03], .exact [94, 305, 392, 289, 896]⟩),
   ("H4", ⟨[], [0x04], .exact [49]⟩),
   ("H5", ⟨[], [0x05], .exact [37]⟩),
   ("H2^1", ⟨[], [0x09], .exact [2932, 4645, 6037, 4389, 14101]⟩),
   ("H2^2", ⟨[], [0x0A], .exact [493, 521, 608, 505, 1112]⟩),
   ("H2^3", ⟨[], [0x0B], .exact [93, 205]⟩),
   ("UOV combination pomfrit", ⟨[], pomf l' z0, .exact [63]⟩),
   ("UOV combination moussaka", ⟨[], mous l' z0, .exact [63]⟩),
   ("UOV combination ratatouille", ⟨[], rata l' z0, .exact [63]⟩)]

/-- Application domains with fixed length (prefix-tagged). -/
def appFixed : List (String × Shape) :=
  [("PomFRIT refresher_com", ⟨pomf r' z0, [], .exact [39]⟩),
   ("Moussaka issue seed", ⟨mous s' z0, [], .exact [39]⟩),
   ("Moussaka redeem seed", ⟨mous s' z1, [], .exact [39]⟩),
   ("Ratatouille issue seed", ⟨rata s' z0, [], .exact [39]⟩),
   ("Ratatouille spend seed", ⟨rata s' z1, [], .exact [39]⟩)]

/-- PomFRIT `hash_to_target`: DST ‖ digest(32) ‖ chal1(136) ‖ vole_check_proof(64) ‖ corr(45) ‖ msg. -/
def target : Shape := ⟨pomf h' z0, [], .atLeast 284⟩

/-- PomFRIT seed XOF: DST ‖ seed(32) ‖ digest(32) ‖ msg. -/
def seedXof : Shape := ⟨pomf s' z0, [], .atLeast 71⟩

def clean : List (String × Shape) := proofSystem ++ appFixed

/-- All pairs of a list satisfy `sep`, as a Boolean. -/
def allSep : List (String × Shape) → Bool
  | [] => true
  | a :: l => l.all (fun b => sep a.2 b.2) && allSep l

theorem allSep_sound {l : List (String × Shape)} (h : allSep l = true) :
    l.Pairwise fun a b => sep a.2 b.2 = true := by
  induction l with
  | nil => exact List.Pairwise.nil
  | cons a l ih =>
    simp only [allSep, Bool.and_eq_true, List.all_eq_true] at h
    exact List.Pairwise.cons h.1 (ih h.2)

/-! ## As implemented -/

theorem clean_pairwise : clean.Pairwise fun a b => sep a.2 b.2 = true :=
  allSep_sound (by decide)

/-- The proof-system domains that `hash_to_target` is *not* separated from. -/
def targetExceptions : List String := ["H1 leaves k=8", "H1 leaves k=7", "H1 com", "H3", "H2^1", "H2^2"]

/-- The proof-system domains that PomFRIT's seed XOF is *not* separated from. -/
def seedExceptions : List String :=
  ["H1 leaves k=8", "H1 leaves k=7", "H1 com", "H2^0 pomfrit", "H2^0 ratatouille spend", "H3",
   "H2^1", "H2^2", "H2^3"]

theorem target_sep :
    ∀ d ∈ clean, d.1 ∉ targetExceptions → sep target d.2 = true := by decide

theorem seed_sep :
    ∀ d ∈ clean, d.1 ∉ seedExceptions → sep seedXof d.2 = true := by decide

theorem target_seed_sep : sep target seedXof = true := by decide

/-! ### The exceptions are real: explicit strings in both domains -/

/-- `pre ‖ 0^n ‖ suf` has prefix `pre`, suffix `suf` and length `|pre| + n + |suf|`. -/
theorem mem_of_pad (pre suf : List ℕ) (n : ℕ) (L : LenSpec)
    (hL : L.mem (pre.length + n + suf.length)) :
    (Shape.mk pre [] L).mem (pre ++ List.replicate n 0 ++ suf) ∧
    (Shape.mk [] suf L).mem (pre ++ List.replicate n 0 ++ suf) := by
  have hlen : (pre ++ List.replicate n 0 ++ suf).length = pre.length + n + suf.length := by
    simp [Nat.add_assoc]
  refine ⟨⟨?_, List.nil_suffix, hlen ▸ hL⟩, ⟨List.nil_prefix, ?_, hlen ▸ hL⟩⟩
  · rw [List.append_assoc]; exact List.prefix_append _ _
  · exact List.suffix_append _ _

/-- A string in `target` and in the domain `⟨[], suf, .exact ls⟩`, given an allowed length. -/
theorem target_meets (suf ls : List ℕ) (n : ℕ) (hn : 7 + n + suf.length ∈ ls)
    (h284 : 284 ≤ 7 + n + suf.length) :
    ∃ x, target.mem x ∧ (Shape.mk [] suf (.exact ls)).mem x := by
  refine ⟨pomf h' z0 ++ List.replicate n 0 ++ suf, ?_, ?_⟩
  · exact (mem_of_pad (pomf h' z0) suf n (.atLeast 284) h284).1
  · exact (mem_of_pad (pomf h' z0) suf n (.exact ls) hn).2

/-- E.g. `x = "pomf\0h0" ‖ 0^4089 ‖ 01` is a `hash_to_target` input (msg = 0^3812 ‖ 01) and an
H₁ leaf-hash input for a k = 7 tree. -/
theorem target_meets_H1_leaves7 :
    ∃ x, target.mem x ∧ (Shape.mk [] [0x01] (.exact [4097])).mem x :=
  target_meets [0x01] [4097] 4089 (by decide) (by decide)

theorem target_meets_H1_leaves8 :
    ∃ x, target.mem x ∧ (Shape.mk [] [0x01] (.exact [8193])).mem x :=
  target_meets [0x01] [8193] 8185 (by decide) (by decide)

theorem target_meets_H1_com :
    ∃ x, target.mem x ∧ (Shape.mk [] [0x01] (.exact [545])).mem x :=
  target_meets [0x01] [545] 537 (by decide) (by decide)

theorem target_meets_H3 :
    ∃ x, target.mem x ∧ (Shape.mk [] [0x03] (.exact [94, 305, 392, 289, 896])).mem x :=
  target_meets [0x03] _ 297 (by decide) (by decide)

theorem target_meets_H21 :
    ∃ x, target.mem x ∧ (Shape.mk [] [0x09] (.exact [2932, 4645, 6037, 4389, 14101])).mem x :=
  target_meets [0x09] _ 2924 (by decide) (by decide)

theorem target_meets_H22 :
    ∃ x, target.mem x ∧ (Shape.mk [] [0x0A] (.exact [493, 521, 608, 505, 1112])).mem x :=
  target_meets [0x0A] _ 485 (by decide) (by decide)

/-- E.g. `"pomf\0s0" ‖ 0^70 ‖ "pomf\0p0" ‖ 08` is a seed-XOF input (seed = digest = 0^32,
msg = 0^6 ‖ "pomf\0p0" ‖ 08) and an H₂⁰ input of the PomFRIT relation. -/
theorem seed_meets_H20_pomfrit :
    ∃ x, seedXof.mem x ∧ (Shape.mk [] (pomf p' z0 ++ [0x08]) (.exact [85])).mem x :=
  ⟨_, (mem_of_pad (pomf s' z0) (pomf p' z0 ++ [0x08]) 70 (.atLeast 71) (by decide)).1,
    (mem_of_pad (pomf s' z0) (pomf p' z0 ++ [0x08]) 70 (.exact [85]) (by decide)).2⟩

theorem seed_meets_H23 :
    ∃ x, seedXof.mem x ∧ (Shape.mk [] [0x0B] (.exact [93, 205])).mem x :=
  ⟨_, (mem_of_pad (pomf s' z0) [0x0B] 85 (.atLeast 71) (by decide)).1,
    (mem_of_pad (pomf s' z0) [0x0B] 85 (.exact [93, 205]) (by decide)).2⟩

/-! ## With the proposed fix: a final byte 0x20 on the two variable-length inputs -/

def APP_TAG : ℕ := 0x20

def targetFixed : Shape := ⟨pomf h' z0, [APP_TAG], .atLeast 285⟩
def seedXofFixed : Shape := ⟨pomf s' z0, [APP_TAG], .atLeast 72⟩

def fixed : List (String × Shape) :=
  clean ++ [("PomFRIT hash_to_target (fixed)", targetFixed), ("PomFRIT seed XOF (fixed)", seedXofFixed)]

theorem fixed_pairwise : fixed.Pairwise fun a b => sep a.2 b.2 = true :=
  allSep_sound (by decide)

/-- Consequence used by the paper proof: two distinct entries of the fixed table share no input. -/
theorem fixed_disjoint {a b : String × Shape} (hab : List.Pairwise (fun a b => sep a.2 b.2 = true) [a, b])
    {x : List ℕ} (ha : a.2.mem x) : ¬ b.2.mem x := by
  have := List.pairwise_cons.mp hab
  exact sep_sound (this.1 b (List.mem_singleton_self b)) ha

end VoleMole.Protocols.DomainSeparation
