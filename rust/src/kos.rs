//! The KOS-style VOLE consistency check (with CRT masks).

use crate::block::Block;
use crate::gf128::{HashKey, Hasher, Wide, mul};
use crate::hash::Shake128;
use crate::params::{N_MASK, QS_DEGREE, VOLE_CHECK_PROOF_BYTES};

const N_EXTRA: usize = QS_DEGREE - 1;

struct Challenge {
    matrix: [Block; 4],
    keys: [HashKey; 5],
}

impl Challenge {
    fn load(chal: &[u8]) -> Challenge {
        let matrix = core::array::from_fn(|i| Block::load(&chal[16 * i..]));
        let keys = core::array::from_fn(|i| {
            if i < 4 {
                HashKey::new(Block::load(&chal[64 + 16 * i..]))
            } else {
                HashKey::new(Block::from_u64(u64::from_le_bytes(chal[128..136].try_into().unwrap()), 0))
            }
        });
        Challenge { matrix, keys }
    }

    fn combine(&self, s: [Block; 5], mask: &[Block]) -> [Block; 4] {
        core::array::from_fn(|i| {
            let mut acc = Wide::from(mask[i] ^ s[i + 1]);
            acc.add_mul(s[0], self.matrix[i]);
            acc.reduce()
        })
    }
}

/// Hash rows (a multiple of 8) followed by the first N_EXTRA masks.
fn hash_rows(ch: &Challenge, rows: &[Block], mask: &[Block]) -> [Block; 5] {
    let mut hs: [Hasher; 5] = Default::default();
    for (h, k) in hs.iter_mut().zip(&ch.keys) {
        for &r in rows.iter().chain(&mask[..N_EXTRA]) {
            h.update(k, r);
        }
    }
    core::array::from_fn(|i| hs[i].finalize(&ch.keys[i]))
}

/// Hash the bits of `u` (LSB first) followed by the first N_EXTRA masks.
fn hash_bits(ch: &Challenge, u: &[u8], mask: &[Block]) -> [Block; 5] {
    core::array::from_fn(|i| {
        let k = &ch.keys[i];
        // table[b] = Σ_j b_j k^(7-j)
        let mut table = [Block::ZERO; 256];
        for j in 0..8 {
            let p = if j == 7 { Block::from_u128(1) } else { k.pow(7 - j) };
            let bit = 1usize << j;
            for b in 0..bit {
                table[b | bit] = table[b] ^ p;
            }
        }
        let k8 = k.pow(8);
        let mut s = Block::ZERO;
        for &b in u {
            s = mul(s, k8) ^ table[b as usize];
        }
        let mut acc = Wide::mul(s, k8);
        for j in 0..7 {
            acc.add_mul(mask[j], k.pow(7 - j));
        }
        acc.add(mask[7]);
        acc.reduce()
    })
}

fn absorb(h: &[Block; 4], hasher: &mut Shake128) {
    for x in h {
        hasher.update(&x.to_bytes());
    }
}

/// `u` is the witness part of the first VOLE's u (corr_rows bits), `v` the corr_rows tags.
pub fn sender(
    chal: &[u8],
    u: &[u8],
    v: &[Block],
    u_mask: &[Block; N_MASK],
    v_mask: &[Block; N_MASK],
    proof: &mut [u8],
    hasher: &mut Shake128,
) {
    let ch = Challenge::load(chal);
    let hu = ch.combine(hash_bits(&ch, u, u_mask), &u_mask[N_EXTRA..]);
    for (i, x) in hu.iter().enumerate() {
        x.store(&mut proof[16 * i..]);
    }
    hasher.update(&proof[..VOLE_CHECK_PROOF_BYTES]);
    let hv = ch.combine(hash_rows(&ch, v, v_mask), &v_mask[N_EXTRA..]);
    absorb(&hv, hasher);
}

pub fn receiver(
    chal: &[u8],
    delta: Block,
    q: &[Block],
    q_mask: &[Block; N_MASK],
    proof: &[u8],
    hasher: &mut Shake128,
) {
    let ch = Challenge::load(chal);
    hasher.update(&proof[..VOLE_CHECK_PROOF_BYTES]);
    let mut hq = ch.combine(hash_rows(&ch, q, q_mask), &q_mask[N_EXTRA..]);
    for (i, x) in hq.iter_mut().enumerate() {
        *x ^= mul(delta, Block::load(&proof[16 * i..]));
    }
    absorb(&hq, hasher);
}
