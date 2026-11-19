//! Constraint building blocks shared by the relations.

use crate::keccak800::OUTPUT_DEGREE;
use crate::qs::Qs;
use crate::voleith::Dst;

pub const fn make_dst(protocol: &[u8; 4], version: u8, purpose: u8, index: u8) -> Dst {
    [protocol[0], protocol[1], protocol[2], protocol[3], version, purpose, index]
}

/// Each of the first `n` witness bits is a bit.
pub fn add_bit_constraints<Q: Qs>(q: &mut Q, n: usize) {
    for i in 0..n {
        let b = q.witness_bit(i);
        q.add_bit_constraint(&b);
    }
}

/// The first 8 * bytes.len() bits of `out` equal `bytes`.
pub fn add_output_constraints<Q: Qs>(q: &mut Q, out: &[Q::Bit<OUTPUT_DEGREE>], bytes: &[u8]) {
    for i in 0..8 * bytes.len() {
        let x = if (bytes[i / 8] >> (i % 8)) & 1 == 1 { q.bit_add_one(&out[i]) } else { out[i] };
        let v = q.bit_to_val(&x);
        q.add_constraint::<OUTPUT_DEGREE>(&v);
    }
}

/// Constant-time equality mask: all ones if a == b.
#[inline(always)]
pub fn ct_eq_mask(a: usize, b: usize) -> usize {
    let x = (a ^ b) as u64;
    // (x | -x) has its top bit set iff x != 0.
    let nz = (x | x.wrapping_neg()) >> 63;
    (nz as usize).wrapping_sub(1)
}
