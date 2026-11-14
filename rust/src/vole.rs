//! VOLE commitment with CRT VOLE masks (FAEST v3): SoftSpoken small VOLEs over the BAVC leaves,
//! then lifted to a VOLE over GF(2^128).

use crate::aes::{RoundKeys, ctr_block, encrypt_many, keygen_ctr};
use crate::bavc::{self, ProverCommitment, leaf_pos, vole_key_leaf};
use crate::block::{Block, as_bytes, as_bytes_mut, zeroed};
use crate::crt::{self, barrett_reduce};
use crate::crt_tables::{DIV_X64_BY_M_I, M_I, M_TREE, N_MULT};
use crate::gf128;
use crate::hash::{Shake128, Shake128X4};
use crate::params::{DELTA_BITS, MAX_USED_K, N_MASK, N_MULT_BYTES, Params, TAU, tree_col, tree_k};

/// Sum of the PRG outputs (index 0) and of those with bit c of the key index set (index c + 1).
#[inline(always)]
fn xor_reduce(x: &mut [Block; 8]) {
    let mut stride = 1;
    let mut i: usize = 0;
    while stride < 8 {
        let mut j = 0;
        while j < 8 {
            for d in 0..=i {
                x[j + d] = x[j + d] ^ x[j + d + stride];
            }
            x[j + i + 1] = x[j + stride];
            j += 2 * stride;
        }
        stride *= 2;
        i += 1;
    }
}

/// One small VOLE over 2^k keys. `vq` holds the k columns of `cb` blocks each, and must be
/// initialized by the caller. For the receiver, key 0 is a dummy.
fn small_vole(
    receiver: bool,
    k: usize,
    keys: &[Block],
    iv: Block,
    tweak: u32,
    cb: usize,
    vq: &mut [Block],
    accum: &mut [Block],
) {
    let mut i: usize = 0;
    if receiver {
        let k7: [Block; 7] = core::array::from_fn(|l| keys[1 + l]);
        let mut rks: [RoundKeys; 7] = core::array::from_fn(|_| RoundKeys::new(Block::ZERO));
        let mut out = [[Block::ZERO; 1]; 7];
        keygen_ctr(&k7, iv, &[tweak; 7], 0, Some(&mut rks), &mut out);
        for j in 0..cb {
            let y: [Block; 7] = if j == 0 {
                core::array::from_fn(|l| out[l][0])
            } else {
                encrypt_many(&rks, &[ctr_block(iv, j as u32, tweak); 7])
            };
            let mut x = [Block::ZERO; 8];
            x[1..].copy_from_slice(&y);
            xor_reduce(&mut x);
            for c in 0..3 {
                vq[c * cb + j] ^= x[c + 1];
            }
        }
        i = 8;
    }
    while i < 1 << k {
        let output_col = ((i + 8) | (1 << (k - 1))).trailing_zeros() as usize;
        let k8: [Block; 8] = core::array::from_fn(|l| keys[i + l]);
        let mut rks: [RoundKeys; 8] = core::array::from_fn(|_| RoundKeys::new(Block::ZERO));
        let mut out = [[Block::ZERO; 1]; 8];
        keygen_ctr(&k8, iv, &[tweak; 8], 0, Some(&mut rks), &mut out);
        for j in 0..cb {
            let mut x: [Block; 8] = if j == 0 {
                core::array::from_fn(|l| out[l][0])
            } else {
                encrypt_many(&rks, &[ctr_block(iv, j as u32, tweak); 8])
            };
            xor_reduce(&mut x);
            accum[j] ^= x[0];
            for c in 0..3 {
                vq[c * cb + j] ^= x[c + 1];
            }
            vq[output_col * cb + j] ^= accum[j];
        }
        i += 8;
    }
}

/// The gate hashes: the first 4 bytes of H(iv || e || L[e] || 5) for each gate e.
fn gate_hashes(iv: Block, labels: &[Block; N_MULT], offset: Block) -> [u32; N_MULT] {
    let mut out = [0u32; N_MULT];
    let ivb = iv.to_bytes();
    let mut e = 0;
    while e + 4 <= N_MULT {
        let mut h = Shake128X4::new();
        h.update_1(&ivb);
        let ctrs: [[u8; 4]; 4] = core::array::from_fn(|l| ((e + l) as u32).to_le_bytes());
        h.update(core::array::from_fn(|l| &ctrs[l][..]));
        let ls: [[u8; 16]; 4] = core::array::from_fn(|l| (labels[e + l] ^ offset).to_bytes());
        h.update(core::array::from_fn(|l| &ls[l][..]));
        h.update_1(&[5]);
        let mut o = [[0u8; 4]; 4];
        let [o0, o1, o2, o3] = &mut o;
        h.squeeze([o0, o1, o2, o3]);
        for l in 0..4 {
            out[e + l] = u32::from_le_bytes(o[l]);
        }
        e += 4;
    }
    for e in e..N_MULT {
        let mut h = Shake128::new();
        h.update(&ivb).update(&(e as u32).to_le_bytes());
        h.update(&(labels[e] ^ offset).to_bytes()).update_byte(5);
        out[e] = u32::from_le_bytes(h.finalize());
    }
    out
}

/// Row m: bit e is bit m of h[e].
fn transpose_hashes(h: &[u32; N_MULT], m: usize) -> [u8; N_MULT_BYTES] {
    let mut out = [0u8; N_MULT_BYTES];
    for (e, &x) in h.iter().enumerate() {
        out[e / 8] |= (((x >> m) & 1) as u8) << (e % 8);
    }
    out
}

#[inline(always)]
fn extract_bits(src: &[u8], pos: usize, n: usize) -> u64 {
    let mut chunk = [0u8; 8];
    let start = pos / 8;
    let len = (pos % 8 + n).div_ceil(8);
    chunk[..len].copy_from_slice(&src[start..start + len]);
    (u64::from_le_bytes(chunk) >> (pos % 8)) & ((1 << n) - 1)
}

/// r_tilde: for each mask and tree, the polynomial Σ_t row_t << t reduced mod M_i.
fn r_tilde(p: &Params, rows: &[Block], m: usize) -> Block {
    let mut out = 0u128;
    for i in 0..TAU {
        let (k, col) = (tree_k(i), tree_col(i));
        let mut r = 0u64;
        for t in 0..k {
            let row = rows[p.corr_rows + m * MAX_USED_K + t].to_u128();
            r ^= (((row >> col) as u64) & ((1 << k) - 1)) << t;
        }
        let r = barrett_reduce(r, M_I[i], DIV_X64_BY_M_I[i]);
        out |= (r as u128) << col;
    }
    Block::from_u128(out)
}

/// Lift the first `p.corr_rows` rows by W_CRT.
fn lift_rows(p: &Params, rows: &mut [Block]) {
    let w = crt::w_crt();
    for r in &mut rows[..p.corr_rows] {
        *r = w.apply_block(*r);
    }
}

pub struct ProverVole {
    pub com: ProverCommitment,
    pub u: Vec<Block>,
    /// The lifted VOLE tags, one per row.
    pub v: Vec<Block>,
    pub u_mask: [Block; N_MASK],
    pub v_mask: [Block; N_MASK],
}

impl ProverVole {
    pub fn u_bytes(&self) -> &[u8] {
        as_bytes(&self.u)
    }
}

/// VOLE commitment. Writes the corrections and c_mult into `proof`, and returns the commitment
/// check.
pub fn commit(p: &Params, seed: Block, iv: Block, proof: &mut [u8]) -> (ProverVole, [u8; 32]) {
    let cb = p.col_blocks;
    let com = bavc::commit(seed, iv);
    let check = bavc::hash_hashed_leaves(&com.hashed);

    let mut cols = zeroed(128 * cb);
    let mut u = zeroed(cb);
    let mut u_extra = [[0u8; 12]; TAU - 1];
    let mut accum = zeroed(cb);
    let mut keys = vec![Block::ZERO; 256];
    for i in 0..TAU {
        let k = tree_k(i);
        for (j, key) in keys[..1 << k].iter_mut().enumerate() {
            *key = com.tree[leaf_pos(i, vole_key_leaf(j, 0))];
        }
        accum.fill(Block::ZERO);
        let col = tree_col(i);
        small_vole(
            false,
            k,
            &keys,
            iv,
            (1 << 31) + i as u32,
            cb,
            &mut cols[col * cb..(col + k) * cb],
            &mut accum,
        );
        if i == 0 {
            u.copy_from_slice(&accum);
        } else {
            let a = as_bytes(&accum);
            let ub = as_bytes(&u);
            let out = &mut proof[p.off_corrections + (i - 1) * p.corr_bytes..][..p.corr_bytes];
            for (o, (x, y)) in out.iter_mut().zip(a.iter().zip(ub)) {
                *o = x ^ y;
            }
            u_extra[i - 1].copy_from_slice(&a[p.corr_bytes..p.corr_bytes + 12]);
        }
    }

    // Gate hashes from the unlifted label rows (the first 128 rows).
    let label_cols: Vec<Block> = (0..DELTA_BITS).map(|c| cols[c * cb]).collect();
    let labels = crt::g_lift_columns(&label_cols);
    let h0 = gate_hashes(iv, &labels, Block::ZERO);
    let h1 = gate_hashes(iv, &labels, u[0]);

    let mut v = crt::transpose_columns(&cols, cb);
    drop(cols);
    lift_rows(p, &mut v);

    // u_mask
    let prg = {
        let mut out = [[Block::ZERO; 1]; 1];
        keygen_ctr(&[seed], iv, &[(1 << 31) - 1], 0, None, &mut out);
        out[0][0].to_bytes()
    };
    let m_tree = Block::from_bytes(&M_TREE);
    let ub = as_bytes(&u);
    let u_mask: [Block; N_MASK] = core::array::from_fn(|m| {
        let mut low = 0u128;
        for i in 0..TAU {
            let src = if i == 0 { &ub[p.corr_bytes..] } else { &u_extra[i - 1][..] };
            low |= (extract_bits(src, m * MAX_USED_K, tree_k(i)) as u128) << tree_col(i);
        }
        crt::w_crt().apply_block(Block::from_u128(low))
            ^ gf128::mul(Block::from_u64(prg[m] as u64, 0), m_tree)
    });

    // v_mask and c_mult
    let mut v_mask = [Block::ZERO; N_MASK];
    for m in 0..N_MASK {
        let t0 = transpose_hashes(&h0, m);
        v_mask[m] = crt::w_tree().apply_block(r_tilde(p, &v, m)) ^ crt::w_gate().apply(&t0);
        let t1 = transpose_hashes(&h1, m);
        let f = crt::f_lift(u_mask[m]);
        let out = &mut proof[p.off_cmult + m * N_MULT_BYTES..][..N_MULT_BYTES];
        for b in 0..N_MULT_BYTES {
            out[b] = t0[b] ^ t1[b] ^ (f[b / 8] >> (8 * (b % 8))) as u8;
        }
    }

    (ProverVole { com, u, v, u_mask, v_mask }, check)
}

pub struct VerifierVole {
    /// The lifted VOLE keys, one per row (before applying the witness correction).
    pub q: Vec<Block>,
    pub q_mask: [Block; N_MASK],
    /// The lifted Delta.
    pub delta: Block,
}

pub fn reconstruct(p: &Params, iv: Block, proof: &[u8]) -> Option<(VerifierVole, [u8; 32])> {
    let cb = p.col_blocks;
    let delta_bytes: [u8; 16] = proof[p.off_delta..p.off_delta + 16].try_into().unwrap();
    let delta_raw = Block::from_bytes(&delta_bytes);
    let vc = bavc::verify(iv, &proof[p.off_open..p.off_open + bavc::OPEN_SIZE], &delta_bytes)?;
    let check = bavc::hash_hashed_leaves(&vc.hashed);

    let mut cols = zeroed(128 * cb);
    let mut keys = vec![Block::ZERO; 256];
    let mut accum = zeroed(cb);
    for i in 0..TAU {
        let k = tree_k(i);
        for (j, key) in keys[..1 << k].iter_mut().enumerate() {
            *key = vc.tree[leaf_pos(i, vole_key_leaf(j, vc.delta_i[i]))];
        }
        let col = tree_col(i);
        let q = &mut cols[col * cb..(col + k) * cb];
        if i > 0 {
            let corr = &proof[p.off_corrections + (i - 1) * p.corr_bytes..][..p.corr_bytes];
            for c in 0..k {
                if delta_raw.bit(col + c) == 1 {
                    as_bytes_mut(&mut q[c * cb..(c + 1) * cb])[..p.corr_bytes].copy_from_slice(corr);
                }
            }
        }
        accum.fill(Block::ZERO);
        small_vole(true, k, &keys, iv, (1 << 31) + i as u32, cb, q, &mut accum);
    }

    let label_cols: Vec<Block> = (0..DELTA_BITS).map(|c| cols[c * cb]).collect();
    let labels = crt::g_lift_columns(&label_cols);
    let h = gate_hashes(iv, &labels, Block::ZERO);

    let mut q = crt::transpose_columns(&cols, cb);
    drop(cols);
    lift_rows(p, &mut q);

    let gamma = crt::g_lift(delta_raw);
    let cmult = &proof[p.off_cmult..p.off_cmult + N_MASK * N_MULT_BYTES];
    let q_mask: [Block; N_MASK] = core::array::from_fn(|m| {
        let mut row = transpose_hashes(&h, m);
        for b in 0..N_MULT_BYTES {
            row[b] ^= (gamma[b / 8] >> (8 * (b % 8))) as u8 & cmult[m * N_MULT_BYTES + b];
        }
        crt::w_tree().apply_block(r_tilde(p, &q, m)) ^ crt::w_gate().apply(&row)
    });

    let delta = crt::w_crt().apply_block(delta_raw);
    Some((VerifierVole { q, q_mask, delta }, check))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn vole_correlation() {
        let p = Params::new(256);
        let iv = Block::from_u64(11, 22);
        let seed = Block::from_u64(33, 44);
        let mut proof = vec![0u8; p.proof_bytes];
        let (pv, check) = commit(&p, seed, iv, &mut proof);
        // Find an openable delta.
        let mut delta = [0u8; 16];
        let mut t = 0u32;
        loop {
            t += 1;
            for (i, b) in delta.iter_mut().enumerate().take(15) {
                *b = (t.wrapping_mul(2654435761) >> (i % 4 * 8)) as u8 ^ i as u8;
            }
            if bavc::open(&pv.com, &delta, &mut proof[p.off_open..p.off_open + bavc::OPEN_SIZE]) {
                break;
            }
        }
        proof[p.off_delta..p.off_delta + 16].copy_from_slice(&delta);
        let (vv, check2) = reconstruct(&p, iv, &proof).unwrap();
        assert_eq!(check, check2);
        // q = v + u·Delta on the corrected rows, with u the witness-row bits of the first VOLE.
        let ub = pv.u_bytes();
        for r in 0..p.corr_rows {
            let ubit = (ub[r / 8] >> (r % 8)) & 1;
            let want = pv.v[r] ^ if ubit == 1 { vv.delta } else { Block::ZERO };
            assert_eq!(vv.q[r], want, "row {r}");
        }
        for m in 0..N_MASK {
            assert_eq!(vv.q_mask[m], pv.v_mask[m] ^ gf128::mul(pv.u_mask[m], vv.delta), "mask {m}");
        }
    }
}
