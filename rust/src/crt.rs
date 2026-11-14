//! Linear maps used by the CRT VOLE masks, and the bit-matrix transpose.

use std::sync::OnceLock;

use crate::block::Block;
use crate::crt_tables::{F_ROWS, G_ROWS, N_MULT, W_CRT_ROWS, W_GATE_ROWS, W_TREE_ROWS};
use crate::params::DELTA_BITS;

/// Row-vector times matrix, with a 256-entry lookup table per input byte.
pub struct RowLift {
    tables: Vec<[Block; 256]>,
}

impl RowLift {
    fn new(rows: &[[u64; 2]]) -> RowLift {
        assert_eq!(rows.len() % 8, 0);
        let tables = rows
            .chunks(8)
            .map(|g| {
                let mut t = [Block::ZERO; 256];
                for b in 1..256usize {
                    let j = b.trailing_zeros() as usize;
                    t[b] = t[b & (b - 1)] ^ Block::from_u64(g[j][0], g[j][1]);
                }
                t
            })
            .collect();
        RowLift { tables }
    }

    /// Multiply the row given by its little-endian bytes (at least one byte per table).
    #[inline(always)]
    pub fn apply(&self, row: &[u8]) -> Block {
        let mut acc = Block::ZERO;
        for (t, &b) in self.tables.iter().zip(row) {
            acc ^= t[b as usize];
        }
        acc
    }

    #[inline(always)]
    pub fn apply_block(&self, row: Block) -> Block {
        self.apply(&row.to_bytes())
    }
}

pub fn w_crt() -> &'static RowLift {
    static T: OnceLock<RowLift> = OnceLock::new();
    T.get_or_init(|| RowLift::new(&W_CRT_ROWS))
}

pub fn w_tree() -> &'static RowLift {
    static T: OnceLock<RowLift> = OnceLock::new();
    T.get_or_init(|| RowLift::new(&W_TREE_ROWS))
}

pub fn w_gate() -> &'static RowLift {
    static T: OnceLock<RowLift> = OnceLock::new();
    T.get_or_init(|| RowLift::new(&W_GATE_ROWS))
}

/// The 320-bit row `x · M` for a matrix with 320-bit rows, `x` given by its first `rows.len()` bits.
fn row_lift_320(x: Block, rows: &[[u64; 5]]) -> [u64; 5] {
    let mut out = [0u64; 5];
    for (j, r) in rows.iter().enumerate() {
        let m = 0u64.wrapping_sub(x.bit(j));
        for w in 0..5 {
            out[w] ^= m & r[w];
        }
    }
    out
}

pub fn f_lift(x: Block) -> [u64; 5] {
    row_lift_320(x, &F_ROWS)
}

pub fn g_lift(x: Block) -> [u64; 5] {
    row_lift_320(x, &G_ROWS[..DELTA_BITS])
}

/// `idx[g][j]`: bits 8g..8g+8 of column j of G.
fn g_column_index() -> &'static [[u8; N_MULT]; DELTA_BITS / 8] {
    static T: OnceLock<Box<[[u8; N_MULT]; DELTA_BITS / 8]>> = OnceLock::new();
    T.get_or_init(|| {
        let mut idx = Box::new([[0u8; N_MULT]; DELTA_BITS / 8]);
        for (i, row) in G_ROWS.iter().enumerate() {
            for j in 0..N_MULT {
                if (row[j / 64] >> (j % 64)) & 1 == 1 {
                    idx[i / 8][j] |= 1 << (i % 8);
                }
            }
        }
        idx
    })
}

/// The gate labels: `out[j] = Σ_i G[i][j] · cols[i]` over the first DELTA_BITS columns.
pub fn g_lift_columns(cols: &[Block]) -> [Block; N_MULT] {
    let idx = g_column_index();
    let mut out = [Block::ZERO; N_MULT];
    for g in 0..DELTA_BITS / 8 {
        let mut t = [Block::ZERO; 256];
        for b in 1..256usize {
            let j = b.trailing_zeros() as usize;
            t[b] = t[b & (b - 1)] ^ cols[8 * g + j];
        }
        for j in 0..N_MULT {
            out[j] ^= t[idx[g][j] as usize];
        }
    }
    out
}

/// Transpose a 128x128 bit matrix: bit c of a[r] moves to bit r of a[c].
pub fn transpose128(a: &mut [u128; 128]) {
    let mut j = 64;
    let mut m: u128 = u64::MAX as u128;
    while j != 0 {
        let mut k = 0;
        while k < 128 {
            let t = ((a[k] >> j) ^ a[k + j]) & m;
            a[k] ^= t << j;
            a[k + j] ^= t;
            k = (k + j + 1) & !j;
        }
        j >>= 1;
        m ^= m << j;
    }
}

/// Transpose 128 columns of `cb` blocks each (column-major) into `128 * cb` rows.
pub fn transpose_columns(cols: &[Block], cb: usize) -> Vec<Block> {
    let mut rows = crate::block::zeroed(128 * cb);
    let mut a = [0u128; 128];
    for b in 0..cb {
        for c in 0..128 {
            a[c] = cols[c * cb + b].to_u128();
        }
        transpose128(&mut a);
        for r in 0..128 {
            rows[128 * b + r] = Block::from_u128(a[r]);
        }
    }
    rows
}

/// `x mod q` by Barrett reduction, as in faest-arch-opt.
#[inline(always)]
pub fn barrett_reduce(x: u64, q: u64, x64_div_q: u64) -> u64 {
    let xb = Block::from_u64(x, 0);
    let t = Block::clmul_ll(xb, Block::from_u64(x64_div_q, 0));
    x ^ Block::clmul_hl(t, Block::from_u64(q, 0)).lo()
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn transpose_matches_naive() {
        let mut a = [0u128; 128];
        let mut x = 0x0123456789abcdef_fedcba9876543210u128;
        for v in a.iter_mut() {
            x = x.wrapping_mul(0x2545f4914f6cdd1d_9e3779b97f4a7c15).wrapping_add(7);
            *v = x;
        }
        let orig = a;
        transpose128(&mut a);
        for r in 0..128 {
            for c in 0..128 {
                assert_eq!((a[c] >> r) & 1, (orig[r] >> c) & 1);
            }
        }
    }

    #[test]
    fn lifts_agree() {
        // Row lift by table equals bitwise row lift.
        let x = Block::from_u64(0x1234_5678_9abc_def0, 0x00ff_ee00_1122_3344);
        let mut want = Block::ZERO;
        for (j, r) in W_CRT_ROWS.iter().enumerate() {
            if x.bit(j) == 1 {
                want ^= Block::from_u64(r[0], r[1]);
            }
        }
        assert_eq!(w_crt().apply_block(x), want);

        // Column lift of G is the transpose of the row lifts.
        let cols: Vec<Block> =
            (0..DELTA_BITS as u64).map(|i| Block::from_u64(i * 0x9e37_79b9, !i << 3)).collect();
        let out = g_lift_columns(&cols);
        for r in [0usize, 5, 64, 127] {
            let mut row = 0u128;
            for (i, c) in cols.iter().enumerate() {
                row |= (c.bit(r) as u128) << i;
            }
            let lifted = g_lift(Block::from_u128(row));
            for j in 0..N_MULT {
                assert_eq!(out[j].bit(r), (lifted[j / 64] >> (j % 64)) & 1);
            }
        }
    }
}
