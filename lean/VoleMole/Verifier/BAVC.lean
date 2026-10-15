import VoleMole.Verifier.Prg

/-!
# The one-tree BAVC of FAEST-EM-128f (executable): commit and verifier-side reconstruction

faest-arch-opt's `one_tree_bavc` (`vector_com.inc:628-979`) with the parameters of all of
vole-mole's relations (`IssueParams` etc.: `s128`, `τ = 17`, `delta_bits = 120`, AES-CTR tree PRG,
`leaf_hash::aes_ctr`, `T_OPEN = 105`), and the VOLE commitment check `hash_hashed_leaves`
(`vole_commit.inc:28-80`).

## The model (spec order, no in-memory permutations)

* Small VOLE `i` has `k_i = 8` bits for `i = 0` and `k_i = 7` for `i = 1 … 16`
  (`VECTOR_COMMITMENT_CONSTANTS`, `constants.hpp:305-331`: `MAX_K = 120/17 + 1`,
  `NUM_MAX_K = 120 mod 17 = 1`), so `L = 256 + 16·128 = 2304` leaves.
* The tree is a heap of `2L − 1` nodes: node `0` is the seed and the children `2n+1, 2n+2` of node
  `n < L − 1` are the two blocks of `PRG(node n, iv, tweak = n)` (`expand_one_roots`,
  `expand_one_tree`, `vector_com.inc:674-727`: `tweak_increment` starting at the node index).
* Leaf `j` of vector `i` is node `L − 1 + pos(i, j)` with `pos(i, j) = 17 j + i` for `j < 128` and
  `2048 + j + i` otherwise (`BATCH_VEC_POS_IN_TREE`, `vector_com.inc:628-641`: the vectors are
  interleaved). Its key is the node itself and its commitment is the 32 bytes of
  `PRG(key, iv, tweak = i + L − 1)` (`prg_leaf_hash::hash`, `vector_com.inc:1069-1085`).
* `Δ_i = Σ_d δ_{p_i + d} 2^d` with `p_i = Σ_{i' < i} k_{i'}` and `δ_b` bit `b % 8` of byte `b / 8`
  of the proof's `delta` (`expand_bits_to_bytes`, then the loop in `verify`,
  `vector_com.inc:880-893`).
* Verification (`one_tree_bavc::verify`, `vector_com.inc:855-979`): mark the hidden leaves and
  their ancestors; walking `n = L − 2, …, 0`, whenever exactly one child of `n` is hidden, read the
  other child's seed from the opening (after the `τ` commitments of the hidden leaves; `openNodes`,
  the walk the prover's `openSeeds` also uses); reject if the opening runs out or any unused
  trailing byte is nonzero. Every other node outside the hidden paths is derived top-down. The
  imperative loops of the C++ are folds here (`markStep`, `deriveStep`). The verifier's leaves are the leaf keys with the hidden ones zero,
  and its commitments are the computed ones with the hidden ones taken from the opening.
* `check` (`hash_hashed_leaves`) is `H(H(c_0 ‖ 1) ‖ … ‖ H(c_16 ‖ 1) ‖ 1)` with `c_i` the
  concatenated commitments of vector `i` and `H` = `H₁` (SHAKE128 to 32 bytes; `check` takes it as
  an argument, `Hashes.hash .h1` in `Verify.lean`).

Checked by `lake exe verifier_vectors` against `lean/vectors/verifier_bavc.txt` (commit and open
for a fixed seed) and `verifier_kat.txt` (the first Moussaka issuance KAT proof).
-/

namespace VoleMole.Verifier.BAVC

open VoleMole.Verifier.AES

-- The CTR PRG (`HasPrg`; AES for the executable code, `Verifier/Prg.lean`).
variable [HasPrg]

def tau : Nat := 17
def numLeaves : Nat := 2304
def numNodes : Nat := 2 * numLeaves - 1
/-- Bytes of a leaf commitment. -/
def hashLen : Nat := 32
/-- `OPEN_SIZE = τ · 32 + T_OPEN · 16`. -/
def openSize : Nat := tau * hashLen + 105 * 16

/-- `k_i`. -/
def kOf (i : Nat) : Nat := if i < 1 then 8 else 7

/-- Index of the first leaf of vector `i` in the concatenation of all vectors. -/
def leafOffset (i : Nat) : Nat := (List.range i).foldl (fun acc i' => acc + 2 ^ kOf i') 0

/-- Index of the first bit of `Δ_i` in `Δ`. -/
def bitOffset (i : Nat) : Nat := (List.range i).foldl (fun acc i' => acc + kOf i') 0

/-- `BATCH_VEC_POS_IN_TREE(i, j)`. -/
def treePos (i j : Nat) : Nat :=
  numLeaves - 1 + (if j < 128 then tau * j + i else 16 * 128 + j + i)

/-- Bytes `16 n … 16 n + 15`. -/
@[inline] def block (b : ByteArray) (n : Nat) : ByteArray := b.extract (16 * n) (16 * n + 16)

def zeroBlock : ByteArray := ⟨Array.replicate 16 0⟩

/-- The two children of a node with index `n`: `PRG(node, iv, n)`, 2 blocks. -/
def children (iv node : ByteArray) (n : Nat) : ByteArray := HasPrg.prg node iv n.toUInt32 0 2

/-- The commitment of leaf key `key` of vector `i`. -/
def leafCom (iv key : ByteArray) (i : Nat) : ByteArray :=
  HasPrg.prg key iv (i + numLeaves - 1).toUInt32 0 2

/-- The prover's tree (all `numNodes` nodes). -/
def expandTree (seed iv : ByteArray) : Array ByteArray := Id.run do
  let mut t : Array ByteArray := Array.replicate numNodes zeroBlock
  t := t.set! 0 seed
  for n in [0:numLeaves - 1] do
    let c := children iv t[n]! n
    t := t.set! (2 * n + 1) (block c 0)
    t := t.set! (2 * n + 2) (block c 1)
  return t

/-- Output of commit or reconstruction, both in spec order. -/
structure Leaves where
  /-- Leaf keys, 16 bytes each, vector after vector. -/
  keys : ByteArray
  /-- Leaf commitments, 32 bytes each, same order. -/
  coms : ByteArray

/-- Read the leaves of all vectors off a tree; `hidden i` is the hidden leaf of vector `i` (if
any), whose key is set to zero and whose commitment is taken from `hiddenCom i`. -/
def leavesOf (iv : ByteArray) (t : Array ByteArray) (hidden : Nat → Option Nat)
    (hiddenCom : Nat → ByteArray) : Leaves := Id.run do
  let mut keys := ByteArray.emptyWithCapacity (16 * numLeaves)
  let mut coms := ByteArray.emptyWithCapacity (hashLen * numLeaves)
  for i in [0:tau] do
    for j in [0:2 ^ kOf i] do
      if hidden i == some j then
        keys := keys ++ zeroBlock
        coms := coms ++ hiddenCom i
      else
        let key := t[treePos i j]!
        keys := keys ++ key
        coms := coms ++ leafCom iv key i
  return ⟨keys, coms⟩

/-- `one_tree_bavc::commit`: the tree and the leaves. -/
def commit (seed iv : ByteArray) : Array ByteArray × Leaves :=
  let t := expandTree seed iv
  (t, leavesOf iv t (fun _ => none) (fun _ => ByteArray.empty))

/-- The small VOLE whose bits of `Δ` contain bit `c < 120` (`bitOffset i ≤ c < bitOffset i + k_i`). -/
def treeOf (c : Nat) : Nat := if c < 8 then 0 else (c - 8) / 7 + 1

/-- Bit `c` of the 16-byte `delta` (bit `c % 8` of byte `c / 8`), for the 120 bits `c < 120` that
encode the `Δ_i` (`false` above; bits `120 … 127` are the grinding bits). -/
def deltaBit (delta : ByteArray) (c : Nat) : Bool :=
  decide (c < 120) && (delta.get! (c / 8) >>> (c % 8).toUInt8) &&& 1 == 1

/-- `Δ_i = Σ_{d < k_i} Δ_{p_i + d} 2^d`, from the bits of `Δ`. -/
def hiddenIndex (dbit : Nat → Bool) (i : Nat) : Nat :=
  (List.range (kOf i)).foldl (fun x d => if dbit (bitOffset i + d) then x + 2 ^ d else x) 0

/-- `Δ_i` from the 16-byte `delta`. -/
def deltaIndex (delta : ByteArray) (i : Nat) : Nat := hiddenIndex (deltaBit delta) i

/-- The hidden leaves of `Δ`, marked (the start of the walk of `openNodes`). -/
def hiddenLeafMarks (delta : ByteArray) : Array Bool :=
  (List.range tau).foldl (fun h i => h.set! (treePos i (deltaIndex delta i)) true)
    (Array.replicate numNodes false)

/-- Step `m` of the bottom-up walk, at node `n = L − 2 − m`: mark `n` if a child is marked, and
record the unmarked child if exactly one is. -/
def markStep (x : Array Bool × Array Nat) (m : Nat) : Array Bool × Array Nat :=
  let n := numLeaves - 2 - m
  let l := x.1[2 * n + 1]!
  let r := x.1[2 * n + 2]!
  (x.1.set! n (l || r), if l != r then x.2.push (if l then 2 * n + 2 else 2 * n + 1) else x.2)

/-- The nodes whose seeds an opening at `Δ` reveals, in the order `verify` reads them: with the
hidden leaves and their ancestors marked, walking `n = L − 2, …, 0`, the unmarked child of every
node with exactly one marked child. -/
def openNodes (delta : ByteArray) : Array Nat :=
  ((List.range (numLeaves - 1)).foldl markStep (hiddenLeafMarks delta, #[])).2

/-- Top-down derivation at node `n`: if its seed is known, so are its children's. -/
def deriveStep (iv : ByteArray) (known : Array (Option ByteArray)) (n : Nat) :
    Array (Option ByteArray) :=
  match known[n]! with
  | some node =>
    let c := children iv node n
    (known.set! (2 * n + 1) (some (block c 0))).set! (2 * n + 2) (some (block c 1))
  | none => known

/-- `one_tree_bavc::verify`: the verifier's leaves, or `none` if the opening is malformed (wrong
size, more than `T_OPEN` seeds, or a nonzero byte after the seeds). -/
def reconstruct (iv opening delta : ByteArray) : Option Leaves :=
  let nodes := openNodes delta
  -- The opening: the `τ` hidden commitments, the seeds of `nodes`, zero padding.
  let seedsEnd := tau * hashLen + 16 * nodes.size
  if opening.size != openSize || seedsEnd > openSize ||
      (List.range (openSize - seedsEnd)).any fun k => opening.get! (seedsEnd + k) != 0 then none
  else
    -- Place the opened seeds, then derive the rest top-down.
    let placed := (List.range nodes.size).foldl (fun known k =>
        known.set! nodes[k]! (some (opening.extract (tau * hashLen + 16 * k)
          (tau * hashLen + 16 * k + 16))))
      (Array.replicate numNodes none)
    let t := ((List.range (numLeaves - 1)).foldl (deriveStep iv) placed).map (·.getD zeroBlock)
    some (leavesOf iv t (fun i => some (deltaIndex delta i))
      (fun i => opening.extract (hashLen * i) (hashLen * i + hashLen)))

/-- The inputs `c_i ‖ 1` of the 17 leaf hashes of `hash_hashed_leaves`. -/
def leafHashInputs (coms : ByteArray) : List ByteArray :=
  (List.range tau).map fun i =>
    (coms.extract (hashLen * leafOffset i) (hashLen * (leafOffset i + 2 ^ kOf i))).push 1

/-- The input `h_0 ‖ … ‖ h_16 ‖ 1` of the outer hash, from the leaf hashes `h_i`. -/
def comInput (hs : List ByteArray) : ByteArray := (hs.foldl (· ++ ·) ByteArray.empty).push 1

/-- `hash_hashed_leaves`: the VOLE commitment check value (32 bytes), with `h1` = `H₁`. -/
def check (h1 : ByteArray → ByteArray) (coms : ByteArray) : ByteArray :=
  h1 (comInput ((leafHashInputs coms).map h1))

#guard treePos 16 0 == numLeaves - 1 + 16 && treePos 0 255 == numNodes - 1
#guard leafOffset tau == numLeaves && bitOffset tau == 120

end VoleMole.Verifier.BAVC
