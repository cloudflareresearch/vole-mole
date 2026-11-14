//! The one-tree batch all-but-one vector commitment of FAEST v2/v3.

use crate::aes::keygen_ctr;
use crate::block::{Block, as_bytes};
use crate::hash::{Shake128, Shake128X4};
use crate::params::{DELTA_BITS, TAU, tree_col, tree_k};

pub const COMMIT_LEAVES: usize = 2304;
pub const COMMIT_NODES: usize = 2 * COMMIT_LEAVES - 1;
const FIRST_LEAF: usize = COMMIT_LEAVES - 1;
pub const T_OPEN: usize = 105;
pub const HASH_LEN: usize = 32;
pub const OPEN_SIZE: usize = TAU * HASH_LEN + T_OPEN * 16;

/// Position in the tree of leaf `leaf` of vector `vec`. The vectors are interleaved.
#[inline(always)]
pub fn leaf_pos(vec: usize, leaf: usize) -> usize {
    FIRST_LEAF + if leaf < 128 { TAU * leaf + vec } else { 16 * 128 + leaf + vec }
}

/// Index of the hash of leaf `leaf` of vector `vec` (each hash is 2 blocks).
#[inline(always)]
pub fn hash_pos(vec: usize, leaf: usize) -> usize {
    (if vec == 0 { 0 } else { 128 * (vec + 1) }) + leaf
}

/// The VOLE key index permutation: Gray's code on the index of each chunk of 8 keys.
#[inline(always)]
pub fn vole_permute_key_index(i: usize) -> usize {
    i ^ ((i >> 1) & !7)
}

/// Leaf index in vector `vec` (with hidden leaf `delta_i`) used as the `j`th small VOLE key.
#[inline(always)]
pub fn vole_key_leaf(j: usize, delta_i: usize) -> usize {
    vole_permute_key_index(j) ^ delta_i
}

/// The leaf index hidden in each tree by Delta.
pub fn parse_delta(delta: &[u8; 16]) -> [usize; TAU] {
    let d = u128::from_le_bytes(*delta);
    core::array::from_fn(|i| ((d >> tree_col(i)) & ((1 << tree_k(i)) - 1)) as usize)
}

#[inline(always)]
fn expand_nodes<const N: usize>(iv: Block, tree: &mut [Block], first: usize, revealed: Option<&[bool]>) {
    let keys: [Block; N] = core::array::from_fn(|l| tree[first + l]);
    let tweaks: [u32; N] = core::array::from_fn(|l| (first + l) as u32);
    let mut out = [[Block::ZERO; 2]; N];
    keygen_ctr(&keys, iv, &tweaks, 0, None, &mut out);
    for l in 0..N {
        let child = 2 * (first + l) + 1;
        match revealed {
            None => {
                tree[child] = out[l][0];
                tree[child + 1] = out[l][1];
            }
            Some(r) => {
                if !r[child] {
                    tree[child] = out[l][0];
                }
                if !r[child + 1] {
                    tree[child + 1] = out[l][1];
                }
            }
        }
    }
}

/// Expand all internal nodes from `start` (0 or 1) on.
fn expand_tree(iv: Block, tree: &mut [Block], start: usize, revealed: Option<&[bool]>) {
    if start == 0 {
        expand_nodes::<1>(iv, tree, 0, revealed);
    }
    expand_nodes::<2>(iv, tree, 1, revealed);
    expand_nodes::<4>(iv, tree, 3, revealed);
    let mut i = 7;
    while i < FIRST_LEAF {
        expand_nodes::<8>(iv, tree, i, revealed);
        i += 8;
    }
    debug_assert_eq!(i, FIRST_LEAF);
}

/// Hash every leaf: 2 blocks of PRG output under the leaf key.
fn hash_leaves(iv: Block, tree: &[Block], hashed: &mut [Block]) {
    for vec in 0..TAU {
        let tweak = (vec + FIRST_LEAF) as u32;
        for chunk in (0..1 << tree_k(vec)).step_by(8) {
            let keys: [Block; 8] = core::array::from_fn(|l| tree[leaf_pos(vec, chunk + l)]);
            let mut out = [[Block::ZERO; 2]; 8];
            keygen_ctr(&keys, iv, &[tweak; 8], 0, None, &mut out);
            for l in 0..8 {
                let h = hash_pos(vec, chunk + l);
                hashed[2 * h] = out[l][0];
                hashed[2 * h + 1] = out[l][1];
            }
        }
    }
}

pub struct ProverCommitment {
    pub tree: Vec<Block>,
    /// The leaf hashes, 2 blocks each, ordered by vector then leaf.
    pub hashed: Vec<Block>,
}

pub fn commit(seed: Block, iv: Block) -> ProverCommitment {
    let mut tree = crate::block::zeroed(COMMIT_NODES);
    tree[0] = seed;
    expand_tree(iv, &mut tree, 0, None);
    let mut hashed = crate::block::zeroed(2 * COMMIT_LEAVES);
    hash_leaves(iv, &tree, &mut hashed);
    ProverCommitment { tree, hashed }
}

/// Hash of all leaf hashes, binding the commitment.
pub fn hash_hashed_leaves(hashed: &[Block]) -> [u8; 32] {
    let bytes = as_bytes(hashed);
    let long = 256 * HASH_LEN;
    let short = 128 * HASH_LEN;
    let mut outer = Shake128::new();
    let mut h = Shake128::new();
    h.update(&bytes[..long]).update_byte(1);
    outer.update(&h.finalize::<32>());
    for g in 0..4 {
        let start = long + 4 * g * short;
        let mut h = Shake128X4::new();
        h.update(core::array::from_fn(|j| &bytes[start + j * short..start + (j + 1) * short]));
        h.update_1(&[1]);
        let mut out = [[0u8; 32]; 4];
        let [o0, o1, o2, o3] = &mut out;
        h.squeeze([o0, o1, o2, o3]);
        for o in &out {
            outer.update(o);
        }
    }
    outer.update_byte(1);
    outer.finalize()
}

/// Mark the nodes on the paths to the hidden leaves. Returns the number of marked nodes.
fn mark_hidden(delta_i: &[usize; TAU], hidden: &mut [bool]) -> usize {
    let mut count = 0;
    for (vec, &d) in delta_i.iter().enumerate() {
        let mut pos = leaf_pos(vec, d);
        hidden[pos] = true;
        count += 1;
        while pos > 0 && !hidden[(pos - 1) / 2] {
            pos = (pos - 1) / 2;
            hidden[pos] = true;
            count += 1;
        }
    }
    count
}

/// Open the commitment at Delta, or return false if the opening would be too large.
pub fn open(com: &ProverCommitment, delta: &[u8; 16], opening: &mut [u8]) -> bool {
    let delta_i = parse_delta(delta);
    let mut hidden = vec![false; COMMIT_NODES];
    let count = mark_hidden(&delta_i, &mut hidden);
    if count + 1 - 2 * TAU > T_OPEN {
        return false;
    }
    let mut w = 0;
    for (vec, &d) in delta_i.iter().enumerate() {
        let h = hash_pos(vec, d);
        opening[w..w + HASH_LEN].copy_from_slice(as_bytes(&com.hashed[2 * h..2 * h + 2]));
        w += HASH_LEN;
    }
    for i in (0..FIRST_LEAF).rev() {
        let (l, r) = (hidden[2 * i + 1], hidden[2 * i + 2]);
        if l ^ r {
            com.tree[2 * i + 1 + l as usize].store(&mut opening[w..]);
            w += 16;
        }
    }
    opening[w..OPEN_SIZE].fill(0);
    true
}

pub struct VerifierCommitment {
    /// The tree, with garbage on the paths to the hidden leaves (zero at the hidden leaves).
    pub tree: Vec<Block>,
    pub hashed: Vec<Block>,
    pub delta_i: [usize; TAU],
}

pub fn verify(iv: Block, opening: &[u8], delta: &[u8; 16]) -> Option<VerifierCommitment> {
    let delta_i = parse_delta(delta);
    let mut tree = crate::block::zeroed(COMMIT_NODES);
    let mut revealed = vec![false; COMMIT_NODES];
    {
        let mut hidden = vec![false; COMMIT_NODES];
        for (vec, &d) in delta_i.iter().enumerate() {
            hidden[leaf_pos(vec, d)] = true;
        }
        let mut pos = TAU * HASH_LEN;
        for i in (0..FIRST_LEAF).rev() {
            let (l, r) = (hidden[2 * i + 1], hidden[2 * i + 2]);
            hidden[i] = l || r;
            if l ^ r {
                if pos >= OPEN_SIZE {
                    return None;
                }
                let node = 2 * i + 1 + l as usize;
                revealed[node] = true;
                tree[node] = Block::load(&opening[pos..]);
                pos += 16;
            }
        }
        if opening[pos..OPEN_SIZE].iter().any(|&b| b != 0) {
            return None;
        }
    }
    expand_tree(iv, &mut tree, 1, Some(&revealed));
    let mut hashed = crate::block::zeroed(2 * COMMIT_LEAVES);
    hash_leaves(iv, &tree, &mut hashed);
    for (vec, &d) in delta_i.iter().enumerate() {
        tree[leaf_pos(vec, d)] = Block::ZERO;
        let h = hash_pos(vec, d);
        hashed[2 * h] = Block::load(&opening[HASH_LEN * vec..]);
        hashed[2 * h + 1] = Block::load(&opening[HASH_LEN * vec + 16..]);
    }
    let _ = DELTA_BITS;
    Some(VerifierCommitment { tree, hashed, delta_i })
}

#[cfg(test)]
mod tests {
    use super::*;

    fn inv(i: usize) -> usize {
        let mut j = i;
        let mut shift = 1;
        while shift < 8 - 3 {
            j ^= j >> shift;
            shift <<= 1;
        }
        (j & !7) + (i % 8)
    }

    fn inv_increment(i: usize, offset: usize) -> usize {
        let diff_in = i ^ (i + offset);
        let even = diff_in & (0x5555 | 7);
        let odd = diff_in & (0xAAAA | 7);
        if odd > even { odd } else { even }
    }

    #[test]
    fn key_permutation() {
        for d in 0..256 {
            // The C++ walks leaf indices, writing leaf i to an incrementally computed position.
            let mut perm = inv(d);
            let mut pos = [usize::MAX; 256];
            for i in 0..256 {
                pos[perm] = i;
                perm ^= inv_increment(i, 1);
            }
            for j in 0..256 {
                assert_eq!(pos[j], vole_key_leaf(j, d), "d={d} j={j}");
            }
        }
    }

    #[test]
    fn open_verify_roundtrip() {
        let iv = Block::from_u64(1, 2);
        let com = commit(Block::from_u64(3, 4), iv);
        let mut opening = vec![0u8; OPEN_SIZE];
        let mut delta = [0u8; 16];
        let mut found = 0;
        for t in 0..50u8 {
            for (i, b) in delta.iter_mut().enumerate().take(15) {
                *b = t.wrapping_mul(37).wrapping_add((i as u8).wrapping_mul(101)) ^ (i as u8);
            }
            if !open(&com, &delta, &mut opening) {
                continue;
            }
            found += 1;
            let v = verify(iv, &opening, &delta).unwrap();
            assert_eq!(hash_hashed_leaves(&v.hashed), hash_hashed_leaves(&com.hashed));
            for vec in 0..TAU {
                for leaf in 0..1 << tree_k(vec) {
                    if leaf != v.delta_i[vec] {
                        assert_eq!(v.tree[leaf_pos(vec, leaf)], com.tree[leaf_pos(vec, leaf)]);
                    }
                }
            }
        }
        assert!(found > 0);
    }
}
