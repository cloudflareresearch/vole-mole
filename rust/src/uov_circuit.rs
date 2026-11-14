//! Evaluation of a random linear combination of the UOV public map on committed values.

use crate::block::Block;
use crate::gf128::{EMBED_BASIS, mul};
use crate::hash::Shake128;
use crate::qs::Qs;
use crate::uov::{M, N, PublicKey, for_each_monomial};

/// sum_k l[k] * a[k], with l derived from chal2.
pub struct Combination {
    l: [Block; M],
    tables: Vec<[Block; 256]>,
}

impl Combination {
    pub fn new(chal2: &[u8], dst: &[u8]) -> Combination {
        let mut h = Shake128::new();
        h.update(chal2).update(dst);
        let bytes: [u8; 16 * M] = h.finalize();
        Combination::from_coeffs(core::array::from_fn(|k| Block::load(&bytes[16 * k..])))
    }

    pub fn from_coeffs(l: [Block; M]) -> Combination {
        let tables = l
            .iter()
            .map(|&lk| {
                let mut t = [Block::ZERO; 256];
                for b in 0..8 {
                    let p = mul(lk, EMBED_BASIS[b]);
                    let bit = 1 << b;
                    for a in 0..bit {
                        t[a | bit] = t[a] ^ p;
                    }
                }
                t
            })
            .collect();
        Combination { l, tables }
    }

    pub fn coeff(&self, k: usize) -> Block {
        self.l[k]
    }

    #[inline(always)]
    pub fn combine(&self, a: &[u8; M]) -> Block {
        let mut out = self.tables[0][a[0] as usize];
        for k in 1..M {
            out ^= self.tables[k][a[k] as usize];
        }
        out
    }
}

/// sum_k l[k] * P(s)[k], evaluated as sum_i s_i (sum_{j >= i} c_ij s_j).
pub fn qs_eval_combined_public_map<Q: Qs>(
    q: &Q,
    pk: &PublicKey,
    s: &[Q::Val<1>; N],
    l: &Combination,
) -> Q::Val<2> {
    let zero = q.val_const::<1>(Block::ZERO);
    let mut y = q.val_const::<2>(Block::ZERO);
    let mut row = zero;
    let mut cur = 0;
    for_each_monomial(pk.expanded(), |i, j, coeffs| {
        if i != cur {
            y = q.val_add(&y, &q.val_mul::<1, 1, 2>(&s[cur], &row));
            row = zero;
            cur = i;
        }
        row = q.val_add(&row, &q.val_scale(l.combine(coeffs), &s[j]));
    });
    q.val_add(&y, &q.val_mul::<1, 1, 2>(&s[cur], &row))
}
