//! The VOLE-in-the-Head proof system of FAEST v3 (FAEST-EM-128f parameters, CRT VOLE masks),
//! generic over the relation being proven.

use crate::bavc;
use crate::block::Block;
use crate::hash::{Shake128, Shake128X4};
use crate::kos;
use crate::params::{
    COMMIT_CHECK_BYTES, DELTA_BITS, Params, QS_CHALLENGE_BYTES, QS_PROOF_BYTES,
    VOLE_CHECK_CHALLENGE_BYTES, VOLE_CHECK_PROOF_BYTES,
};
use crate::qs::{self, Qs};
use crate::vole;

pub type Dst = [u8; 7];

/// A relation, together with the instance being proven.
pub trait Relation {
    const WITNESS_BYTES: usize;
    const DST: Dst;
    const PARAMS: Params = Params::new(Self::WITNESS_BYTES);

    fn hash_instance(&self, h: &mut Shake128);
    fn constraints<Q: Qs>(&self, qs: &mut Q, chal2: &[u8; QS_CHALLENGE_BYTES]);
}

pub const fn proof_bytes<R: Relation>() -> usize {
    R::PARAMS.proof_bytes
}

fn hash_mu<R: Relation>(inst: &R) -> [u8; 32] {
    let mut h = Shake128::new();
    inst.hash_instance(&mut h);
    h.update(&R::DST).update_byte(8);
    h.finalize()
}

fn hash_iv(iv_pre: &[u8], mu: &[u8; 32]) -> Block {
    let mut h = Shake128::new();
    h.update(iv_pre).update(mu).update_byte(4);
    Block::from_bytes(&h.finalize())
}

fn hash_chal1(p: &Params, mu: &[u8; 32], check: &[u8; COMMIT_CHECK_BYTES], proof: &[u8]) -> [u8; VOLE_CHECK_CHALLENGE_BYTES] {
    let mut h = Shake128::new();
    h.update(mu)
        .update(check)
        .update(&proof[p.off_corrections..p.off_vole_check])
        .update(&proof[p.off_iv_pre..p.off_iv_pre + 16])
        .update_byte(9);
    h.finalize()
}

pub fn prove<R: Relation>(inst: &R, witness: &[u8], rho: &[u8; 16]) -> Vec<u8> {
    let p = R::PARAMS;
    assert_eq!(witness.len(), p.witness_bytes);
    let mut proof = vec![0u8; p.proof_bytes];

    let mu = hash_mu(inst);
    let seed_iv_pre: [u8; 32] = {
        let mut h = Shake128::new();
        h.update(witness).update(&mu).update(rho).update_byte(3);
        h.finalize()
    };
    let seed = Block::load(&seed_iv_pre[..16]);
    let iv_pre = &seed_iv_pre[16..];
    proof[p.off_iv_pre..p.off_iv_pre + 16].copy_from_slice(iv_pre);
    let iv = hash_iv(iv_pre, &mu);

    let (pv, check) = vole::commit(&p, seed, iv, &mut proof);
    let chal1 = hash_chal1(&p, &mu, &check, &proof);

    let mut h2 = Shake128::new();
    h2.update(&chal1);
    let u = pv.u_bytes();
    kos::sender(
        &chal1,
        &u[..p.corr_bytes],
        &pv.v[..p.corr_rows],
        &pv.u_mask,
        &pv.v_mask,
        &mut proof[p.off_vole_check..p.off_vole_check + VOLE_CHECK_PROOF_BYTES],
        &mut h2,
    );
    let corr = &mut proof[p.off_correction..p.off_correction + p.witness_bytes];
    for (c, (a, b)) in corr.iter_mut().zip(u.iter().zip(witness)) {
        *c = a ^ b;
    }
    h2.update(corr).update_byte(10);
    let chal2: [u8; QS_CHALLENGE_BYTES] = h2.finalize();

    let mut qs = qs::Prover::new(witness, &pv.v, &chal2);
    inst.constraints(&mut qs, &chal2);
    let qs_check = qs.prove(&pv.u_mask, &pv.v_mask, &mut proof[p.off_qs_proof..p.off_open]);

    // Grinding.
    let mut gh = Shake128X4::new();
    gh.update_1(&chal2);
    gh.update_1(&qs_check);
    gh.update_1(&proof[p.off_qs_proof..p.off_open]);
    let mut ctr = 0u32;
    loop {
        let mut g = gh.clone();
        let c: [[u8; 5]; 4] = core::array::from_fn(|i| {
            let mut b = [0u8; 5];
            b[..4].copy_from_slice(&(ctr + i as u32).to_le_bytes());
            b[4] = 11;
            b
        });
        g.update([&c[0], &c[1], &c[2], &c[3]]);
        let mut d = [[0u8; 16]; 4];
        let [d0, d1, d2, d3] = &mut d;
        g.squeeze([d0, d1, d2, d3]);
        for (i, delta) in d.iter().enumerate() {
            if delta[15] != 0 {
                continue;
            }
            if bavc::open(&pv.com, delta, &mut proof[p.off_open..p.off_delta]) {
                proof[p.off_delta..p.off_delta + 16].copy_from_slice(delta);
                proof[p.off_ctr..p.off_ctr + 4].copy_from_slice(&(ctr + i as u32).to_le_bytes());
                return proof;
            }
        }
        ctr = ctr.checked_add(4).expect("VOLEitH: grinding failed");
    }
}

pub fn verify<R: Relation>(inst: &R, proof: &[u8]) -> bool {
    let p = R::PARAMS;
    if proof.len() != p.proof_bytes {
        return false;
    }
    let delta_bytes = &proof[p.off_delta..p.off_delta + 16];
    if (DELTA_BITS..128).any(|i| (delta_bytes[i / 8] >> (i % 8)) & 1 == 1) {
        return false;
    }

    let mu = hash_mu(inst);
    let iv = hash_iv(&proof[p.off_iv_pre..p.off_iv_pre + 16], &mu);
    let Some((mut vv, check)) = vole::reconstruct(&p, iv, proof) else {
        return false;
    };
    let chal1 = hash_chal1(&p, &mu, &check, proof);

    let mut h2 = Shake128::new();
    h2.update(&chal1);
    kos::receiver(
        &chal1,
        vv.delta,
        &vv.q[..p.corr_rows],
        &vv.q_mask,
        &proof[p.off_vole_check..p.off_vole_check + VOLE_CHECK_PROOF_BYTES],
        &mut h2,
    );
    let corr = &proof[p.off_correction..p.off_correction + p.witness_bytes];
    h2.update(corr).update_byte(10);
    let chal2: [u8; QS_CHALLENGE_BYTES] = h2.finalize();

    for (i, q) in vv.q[..p.corr_rows].iter_mut().enumerate() {
        *q ^= vv.delta & Block::mask(((corr[i / 8] >> (i % 8)) & 1) as u64);
    }

    let qs_proof = &proof[p.off_qs_proof..p.off_qs_proof + QS_PROOF_BYTES];
    let mut qs = qs::Verifier::new(&vv.q, vv.delta, &chal2);
    inst.constraints(&mut qs, &chal2);
    let qs_check = qs.verify(&vv.q_mask, qs_proof);

    let mut h3 = Shake128::new();
    h3.update(&chal2)
        .update(&qs_check)
        .update(qs_proof)
        .update(&proof[p.off_ctr..p.off_ctr + 4])
        .update_byte(11);
    let delta_check: [u8; 16] = h3.finalize();
    delta_check == delta_bytes
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::gf128::embed8;

    /// Knowledge of w with w[0] * w[1] = inst[0] in GF(2^8) and all bits being bits.
    struct Toy(u8);
    impl Relation for Toy {
        const WITNESS_BYTES: usize = 32;
        const DST: Dst = *b"toy\0\0\0\0";
        fn hash_instance(&self, h: &mut Shake128) {
            h.update_byte(self.0);
        }
        fn constraints<Q: Qs>(&self, qs: &mut Q, _chal2: &[u8; QS_CHALLENGE_BYTES]) {
            for i in 0..8 * Self::WITNESS_BYTES {
                let b = qs.witness_bit(i);
                qs.add_bit_constraint(&b);
            }
            let a = qs.witness_byte(0);
            let b = qs.witness_byte(1);
            let ab = qs.val_mul::<1, 1, 2>(&a, &b);
            let c = qs.val_const::<2>(embed8(self.0));
            let x = qs.val_add(&ab, &c);
            let x9 = qs.val_lift::<2, 9>(&x);
            qs.add_constraint(&x9);
            let bit = qs.witness_bit(17);
            let y = qs.bit_val_mul::<1, 2, 3>(&bit, &x);
            qs.add_constraint(&y);
        }
    }

    fn gf256_mul(mut a: u8, mut b: u8) -> u8 {
        let mut r = 0;
        while b != 0 {
            if b & 1 != 0 {
                r ^= a;
            }
            a = (a << 1) ^ if a & 0x80 != 0 { 0x1b } else { 0 };
            b >>= 1;
        }
        r
    }

    #[test]
    fn roundtrip() {
        let w: Vec<u8> = (0..32u8).map(|i| i.wrapping_mul(37) ^ 0x5a).collect();
        let inst = Toy(gf256_mul(w[0], w[1]));
        let proof = prove(&inst, &w, &[7; 16]);
        assert!(verify(&inst, &proof));
        assert!(!verify(&Toy(inst.0 ^ 1), &proof));
        for off in [0, Toy::PARAMS.off_vole_check + 3, Toy::PARAMS.off_qs_proof + 5, Toy::PARAMS.off_correction] {
            let mut bad = proof.clone();
            bad[off] ^= 1;
            assert!(!verify(&inst, &bad), "tamper at {off}");
        }
    }
}
