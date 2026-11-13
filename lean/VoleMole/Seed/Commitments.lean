import Mathlib

/-!
# Lemma L0, AES part: the AES-CTR input blocks of one proof are pairwise distinct across roles

Paper proof: `lean/docs/extraction/L0-L2-commitments.md`, §2.3 (AES) and §2.1–2.2 (SHAKE domains).

`aes_ctr_prg` (faest-arch-opt `prgs.hpp:197-206`) encrypts, for counter `c` and tweak `t`, the
block `iv ⊞ (c, 0, 0, t)`, where `⊞` is lane-wise addition of four 32-bit lanes
(`_mm_add_epi32`, `avx2/block_impl.hpp:34-42`). We model a block as `Fin 4 → ZMod (2^32)`.

We prove:
* `ctrInput_inj`: for a fixed `iv`, `(c, t) ↦ iv ⊞ (c, 0, 0, t)` is injective on 32-bit values;
* `leaf_second_block`: the two blocks of a leaf commitment sit at `x` and `x ⊞ e₀`;
* `roles_disjoint`: for FAEST-EM-128f (`L = 2304` leaves, `τ = 17`) the tweak ranges of the four
  AES roles (GGM nodes, leaf commitments, mask top bits, ConvertToVOLE) are pairwise disjoint;
* `role_inputs_ne`: hence, under a fixed `iv`, two AES inputs from different roles differ.
-/

namespace VoleMole.Seed.Commitments

/-- A 32-bit lane. -/
abbrev Lane := ZMod (2 ^ 32)

/-- A 128-bit AES block as four 32-bit lanes. -/
abbrev Block := Fin 4 → Lane

/-- The AES input of counter `c` and tweak `t` under `iv`: `iv ⊞ (c, 0, 0, t)`. -/
def ctrInput (iv : Block) (c t : ℕ) : Block := iv + ![(c : Lane), 0, 0, (t : Lane)]

lemma natCast_lane_inj {a b : ℕ} (ha : a < 2 ^ 32) (hb : b < 2 ^ 32)
    (h : (a : Lane) = (b : Lane)) : a = b := by
  rw [ZMod.natCast_eq_natCast_iff'] at h
  rwa [Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at h

/-- For a fixed `iv`, `(c, t) ↦ iv ⊞ (c, 0, 0, t)` is injective on 32-bit counters and tweaks. -/
theorem ctrInput_inj (iv : Block) {c t c' t' : ℕ} (hc : c < 2 ^ 32) (ht : t < 2 ^ 32)
    (hc' : c' < 2 ^ 32) (ht' : t' < 2 ^ 32) (h : ctrInput iv c t = ctrInput iv c' t') :
    c = c' ∧ t = t' := by
  have h' : (![(c : Lane), 0, 0, (t : Lane)] : Block) = ![(c' : Lane), 0, 0, (t' : Lane)] :=
    add_left_cancel h
  refine ⟨natCast_lane_inj hc hc' ?_, natCast_lane_inj ht ht' ?_⟩
  · simpa using congrFun h' 0
  · simpa using congrFun h' 3

/-- The unit vector in lane 0. -/
def e0 : Block := ![1, 0, 0, 0]

/-- The second block of a leaf commitment `PRG(k, iv, t)[0..2λ)` is encrypted at `x ⊞ e₀`, where
`x` is the input of the first block. -/
theorem leaf_second_block (iv : Block) (t : ℕ) : ctrInput iv 1 t = ctrInput iv 0 t + e0 := by
  funext i
  fin_cases i <;> simp [ctrInput, e0] <;> rfl

/-- Number of GGM leaves in the one-tree BAVC of FAEST-EM-128f: `1·2^8 + 16·2^7`
(`vector_com.hpp:116-117`, `constants.hpp:312-317` with `n_Δ = 120`, `τ = 17`). -/
def L : ℕ := 1 * 2 ^ 8 + 16 * 2 ^ 7

/-- Number of trees (small VOLEs). -/
def τ : ℕ := 17

lemma L_eq : L = 2304 := by decide

/-- The four AES roles. -/
inductive Role | ggm | leaf | mask | vole
  deriving DecidableEq

/-- Tweak range of each role:
* GGM node `a` (internal, `0 ≤ a ≤ L - 2`) uses tweak `a` (`vector_com.inc:674-727`);
* the leaf commitment of tree `i` uses `i + L - 1` (`vector_com.inc:754`);
* the mask top bits use `2^31 - 1` (`vole_commit.inc:241`);
* ConvertToVOLE of tree `i` uses `2^31 + i` (`vole_commit.inc:106,168`). -/
def tweaks : Role → Finset ℕ
  | .ggm => Finset.Ico 0 (L - 1)
  | .leaf => Finset.Ico (L - 1) (L - 1 + τ)
  | .mask => Finset.Ico (2 ^ 31 - 1) (2 ^ 31)
  | .vole => Finset.Ico (2 ^ 31) (2 ^ 31 + τ)

lemma tweaks_lt (r : Role) {t : ℕ} (ht : t ∈ tweaks r) : t < 2 ^ 32 := by
  cases r <;> simp [tweaks, L, τ] at ht <;> omega

theorem roles_disjoint {r s : Role} (hrs : r ≠ s) : Disjoint (tweaks r) (tweaks s) := by
  rw [Finset.disjoint_left]
  intro t hr hs
  cases r <;> cases s <;> simp_all [tweaks, L, τ] <;> omega

/-- Under a fixed `iv`, AES inputs of different roles are different blocks (any 32-bit counters).
-/
theorem role_inputs_ne (iv : Block) {r s : Role} (hrs : r ≠ s) {t t' c c' : ℕ}
    (ht : t ∈ tweaks r) (ht' : t' ∈ tweaks s) (hc : c < 2 ^ 32) (hc' : c' < 2 ^ 32) :
    ctrInput iv c t ≠ ctrInput iv c' t' := by
  intro h
  have := (ctrInput_inj iv hc (tweaks_lt r ht) hc' (tweaks_lt s ht') h).2
  subst this
  exact Finset.disjoint_left.mp (roles_disjoint hrs) ht ht'

/-! ## Domain separation of the SHAKE128 calls (L0.1)

Every in-scope SHAKE128 input ends in a fixed byte; the two H₁ shapes share a byte and are told
apart by length. Distinct last bytes, or distinct lengths, make inputs distinct. -/

/-- A hash domain: its final byte and, if fixed, its input length in bytes. -/
structure Domain where
  tag : ℕ
  len : Option ℕ

/-- An input belongs to a domain if it ends in the tag and has the stated length (if any). -/
def Domain.mem (D : Domain) (x : List ℕ) : Prop :=
  x.getLast? = some D.tag ∧ ∀ n, D.len = some n → x.length = n

theorem Domain.disjoint {D E : Domain} (h : D.tag ≠ E.tag ∨
    (∃ n m, D.len = some n ∧ E.len = some m ∧ n ≠ m)) {x : List ℕ} (hD : D.mem x) :
    ¬ E.mem x := by
  rintro hE
  rcases h with h | ⟨n, m, hn, hm, hnm⟩
  · exact h (Option.some.inj (hD.1.symm.trans hE.1))
  · exact hnm ((hD.2 n hn).symm.trans (hE.2 m hm))

/-- The in-scope domains (`lean/docs/extraction/L0-L2-commitments.md`, table in §2.1). -/
def domains : List (String × Domain) :=
  [("H1 leaves, k=8", ⟨0x01, some (256 * 32 + 1)⟩),
   ("H1 leaves, k=7", ⟨0x01, some (128 * 32 + 1)⟩),
   ("H1 com", ⟨0x01, some (17 * 32 + 1)⟩),
   ("H2^0", ⟨0x08, none⟩), ("H2^1", ⟨0x09, none⟩), ("H2^2", ⟨0x0A, none⟩),
   ("H2^3", ⟨0x0B, none⟩), ("H2^4", ⟨0x0C, some (7 + 1)⟩),
   ("H3", ⟨0x03, none⟩), ("H4", ⟨0x04, some (16 + 32 + 1)⟩),
   ("H5", ⟨0x05, some (16 + 4 + 16 + 1)⟩), ("UOV combination", ⟨0x30, some (56 + 7)⟩)]

/-- Any two listed domains are separated by their tag or by their fixed lengths. -/
theorem domains_separated :
    ∀ a ∈ domains, ∀ b ∈ domains, a ≠ b →
      a.2.tag ≠ b.2.tag ∨ (∃ n m, a.2.len = some n ∧ b.2.len = some m ∧ n ≠ m) := by
  intro a ha b hb hab
  simp only [domains, List.mem_cons, List.not_mem_nil, or_false] at ha hb
  rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
  rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
  first | exact absurd rfl hab | (left; decide) | (right; exact ⟨_, _, rfl, rfl, by decide⟩)

end VoleMole.Seed.Commitments
