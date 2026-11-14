//! Keccak-p[800, 12] and its QuickSilver arithmetization with committed intermediate states.
//!
//! The witness holds the states after rounds 5 and 9. Constraints are
//!
//!   R_2(R_1(R_0(s0)))  = R_3^-1(R_4^-1(s5))   (degree 9)
//!   R_6(R_5(s5))       = R_7^-1(R_8^-1(s9))   (degree 9)
//!   out = R_11(R_10(R_9(s9)))                 (degree 8)
//!
//! meeting just before chi of the first backward round.

use crate::qs::Qs;

pub const STATE_BYTES: usize = 100;
pub const STATE_BITS: usize = 800;
pub const ROUNDS: usize = 12;
pub type State = [u8; STATE_BYTES];

pub const NUM_COMMITTED_STATES: usize = 2;
pub const COMMITTED_STATES_BYTES: usize = NUM_COMMITTED_STATES * STATE_BYTES;
pub const NUM_SEGMENT_CONSTRAINTS: usize = NUM_COMMITTED_STATES * STATE_BITS;
const SEGMENT_START: [usize; 3] = [0, 5, 9];
pub const OUTPUT_DEGREE: usize = 8;

const W: usize = 32;

const fn rc_bit(t: usize) -> u32 {
    if t % 255 == 0 {
        return 1;
    }
    let mut r: u32 = 1;
    let mut i = 1;
    while i <= t % 255 {
        r <<= 1;
        let r8 = (r >> 8) & 1;
        r ^= r8 | (r8 << 4) | (r8 << 5) | (r8 << 6);
        r &= 0xff;
        i += 1;
    }
    r & 1
}

pub const RC: [u32; 12] = {
    let mut out = [0u32; 12];
    let mut i = 0;
    while i < 12 {
        let ir = 10 + i;
        let mut rc = 0;
        let mut j = 0;
        while j <= 5 {
            rc |= rc_bit(j + 7 * ir) << ((1u32 << j) - 1);
            j += 1;
        }
        out[i] = rc;
        i += 1;
    }
    out
};

/// Rho offsets indexed [x][y], mod 32.
const RHO: [[u32; 5]; 5] = {
    let mut out = [[0u32; 5]; 5];
    let (mut x, mut y) = (1usize, 0usize);
    let mut t = 0;
    while t < 24 {
        out[x][y] = (((t + 1) * (t + 2) / 2) % W) as u32;
        let nx = y;
        let ny = (2 * x + 3 * y) % 5;
        x = nx;
        y = ny;
        t += 1;
    }
    out
};

/// (1 + X^2 + X^3)^-1 = 1 + X + X^4 in GF(2)[X]/(X^5 + 1).
const THETA_INV_Q: u8 = 0b10011;

const _: () = assert!(RC[0] == 0x80008009 && RC[11] == 0x00008080);

#[inline(always)]
const fn idx(x: usize, y: usize, z: usize) -> usize {
    W * (5 * y + x) + z
}

#[inline(always)]
fn round800(a: &mut [u32; 25], rc: u32) {
    let mut c = [0u32; 5];
    for x in 0..5 {
        c[x] = a[x] ^ a[x + 5] ^ a[x + 10] ^ a[x + 15] ^ a[x + 20];
    }
    for x in 0..5 {
        let d = c[(x + 4) % 5] ^ c[(x + 1) % 5].rotate_left(1);
        for y in 0..5 {
            a[x + 5 * y] ^= d;
        }
    }
    let mut b = [0u32; 25];
    for x in 0..5 {
        for y in 0..5 {
            let (sx, sy) = ((x + 3 * y) % 5, x);
            b[x + 5 * y] = a[sx + 5 * sy].rotate_left(RHO[sx][sy]);
        }
    }
    for y in 0..5 {
        for x in 0..5 {
            a[x + 5 * y] = b[x + 5 * y] ^ (!b[(x + 1) % 5 + 5 * y] & b[(x + 2) % 5 + 5 * y]);
        }
    }
    a[0] ^= rc;
}

pub fn keccak_p800_rounds(state: &mut State, first: usize, n: usize) {
    assert!(first <= ROUNDS && n <= ROUNDS - first);
    let mut lanes: [u32; 25] =
        core::array::from_fn(|i| u32::from_le_bytes(state[4 * i..4 * i + 4].try_into().unwrap()));
    for r in first..first + n {
        round800(&mut lanes, RC[r]);
    }
    for i in 0..25 {
        state[4 * i..4 * i + 4].copy_from_slice(&lanes[i].to_le_bytes());
    }
}

pub fn keccak_p800(mut state: State) -> State {
    keccak_p800_rounds(&mut state, 0, ROUNDS);
    state
}

pub fn encode_committed_states(out: &mut [u8], mut state: State) {
    for k in 0..NUM_COMMITTED_STATES {
        keccak_p800_rounds(
            &mut state,
            SEGMENT_START[k],
            SEGMENT_START[k + 1] - SEGMENT_START[k],
        );
        out[k * STATE_BYTES..(k + 1) * STATE_BYTES].copy_from_slice(&state);
    }
}

// ---------------------------------------------------------------------------------------------
// Circuit

fn theta_rho_pi<T: Copy>(a: &[T], add: impl Fn(&T, &T) -> T) -> Vec<T> {
    let mut c = Vec::with_capacity(5 * W);
    for x in 0..5 {
        for z in 0..W {
            let mut s = add(&a[idx(x, 0, z)], &a[idx(x, 1, z)]);
            for y in 2..5 {
                s = add(&s, &a[idx(x, y, z)]);
            }
            c.push(s);
        }
    }
    let mut d = Vec::with_capacity(5 * W);
    for x in 0..5 {
        for z in 0..W {
            d.push(add(
                &c[W * ((x + 4) % 5) + z],
                &c[W * ((x + 1) % 5) + (z + W - 1) % W],
            ));
        }
    }
    (0..STATE_BITS)
        .map(|i| {
            let (lane, z) = (i / W, i % W);
            let (x, y) = (lane % 5, lane / 5);
            let (sx, sy) = ((x + 3 * y) % 5, x);
            let sz = (z + W - RHO[sx][sy] as usize) % W;
            add(&a[idx(sx, sy, sz)], &d[W * sx + sz])
        })
        .collect()
}

fn theta_rho_pi_inverse<T: Copy>(b: &[T], add: impl Fn(&T, &T) -> T) -> Vec<T> {
    let mut a: Vec<T> = (0..STATE_BITS)
        .map(|i| {
            let (lane, sz) = (i / W, i % W);
            let (sx, sy) = (lane % 5, lane / 5);
            let (x, y) = (sy, (2 * (sx + 5 - sy)) % 5);
            let z = (sz + RHO[sx][sy] as usize) % W;
            b[idx(x, y, z)]
        })
        .collect();
    let mut c = Vec::with_capacity(5 * W);
    for x in 0..5 {
        for z in 0..W {
            let mut s = add(&a[idx(x, 0, z)], &a[idx(x, 1, z)]);
            for y in 2..5 {
                s = add(&s, &a[idx(x, y, z)]);
            }
            c.push(s);
        }
    }
    let mut p = c.clone();
    let mut s = 1;
    while s < W {
        let mut next = Vec::with_capacity(5 * W);
        for x in 0..5 {
            for z in 0..W {
                let t = add(&p[W * x + z], &p[W * ((x + 5 - s % 5) % 5) + z]);
                next.push(add(&t, &p[W * ((x + s) % 5) + (z + W - s) % W]));
            }
        }
        p = next;
        s *= 2;
    }
    let mut d = Vec::with_capacity(5 * W);
    for x in 0..5 {
        for z in 0..W {
            let mut acc = c[W * x + z];
            for i in 0..5 {
                if (THETA_INV_Q >> i) & 1 == 1 {
                    acc = add(&acc, &p[W * ((x + i) % 5) + z]);
                }
            }
            d.push(acc);
        }
    }
    for (i, ai) in a.iter_mut().enumerate() {
        let (lane, z) = (i / W, i % W);
        *ai = add(ai, &d[W * (lane % 5) + z]);
    }
    a
}

/// One round: degree D in, E = 2D out. Only the first `n_out` bits are computed.
fn round<Q: Qs, const D: usize, const E: usize>(
    q: &Q,
    inp: &[Q::Bit<D>],
    r: usize,
    n_out: usize,
) -> Vec<Q::Bit<E>> {
    let b = theta_rho_pi(inp, |x, y| q.bit_add::<D>(x, y));
    let mut out: Vec<Q::Bit<E>> = (0..n_out)
        .map(|i| {
            let (lane, z) = (i / W, i % W);
            let (x, y) = (lane % 5, lane / 5);
            let nb = q.bit_add_one::<D>(&b[idx((x + 1) % 5, y, z)]);
            let prod = q.bit_mul::<D, D, E>(&nb, &b[idx((x + 2) % 5, y, z)]);
            q.bit_add::<E>(&q.bit_lift::<D, E>(&b[i]), &prod)
        })
        .collect();
    let rc = RC[r];
    for z in 0..W.min(n_out) {
        if (rc >> z) & 1 == 1 {
            out[z] = q.bit_add_one::<E>(&out[z]);
        }
    }
    out
}

/// Inverse of iota and chi: degree D in, T = 3D out (with E = 2D).
fn iota_chi_inverse<Q: Qs, const D: usize, const E: usize, const T: usize>(
    q: &Q,
    inp: &[Q::Bit<D>],
    r: usize,
) -> Vec<Q::Bit<T>> {
    let mut a = inp.to_vec();
    let rc = RC[r];
    for z in 0..W {
        if (rc >> z) & 1 == 1 {
            a[z] = q.bit_add_one::<D>(&a[z]);
        }
    }
    let mut out = Vec::with_capacity(STATE_BITS);
    for y in 0..5 {
        for x in 0..5 {
            for z in 0..W {
                let g = |k: usize| &a[idx((x + k) % 5, y, z)];
                // a ^ (~b & (c ^ (~d & e)))
                let de = q.bit_mul::<D, D, E>(&q.bit_add_one::<D>(g(3)), g(4));
                let cde = q.bit_add::<E>(&q.bit_lift::<D, E>(g(2)), &de);
                let bcde = q.bit_mul::<D, E, T>(&q.bit_add_one::<D>(g(1)), &cde);
                out.push(q.bit_add::<T>(&q.bit_lift::<D, T>(g(0)), &bcde));
            }
        }
    }
    out
}

/// Map from input byte to witness byte index, or -1 if public.
pub type InputMap = [i32; STATE_BYTES];

pub fn qs_input<Q: Qs>(q: &Q, public: &State, map: &InputMap) -> Vec<Q::Bit<1>> {
    (0..STATE_BITS)
        .map(|i| match map[i / 8] {
            w if w >= 0 => q.witness_bit(8 * w as usize + i % 8),
            _ => q.bit_const::<1>((public[i / 8] >> (i % 8)) & 1 == 1),
        })
        .collect()
}

fn load_state<Q: Qs>(q: &Q, bit_off: usize) -> Vec<Q::Bit<1>> {
    (0..STATE_BITS)
        .map(|i| q.witness_bit(bit_off + i))
        .collect()
}

fn meet<Q: Qs, const F: usize>(q: &mut Q, fwd: &[Q::Bit<F>], bwd: &[Q::Bit<9>]) {
    let lin = theta_rho_pi(fwd, |x, y| q.bit_add::<F>(x, y));
    for (l, b) in lin.iter().zip(bwd) {
        let s = q.bit_add::<9>(&q.bit_lift::<F, 9>(l), b);
        let v = q.bit_to_val::<9>(&s);
        q.add_constraint::<9>(&v);
    }
}

/// Two backward rounds ending before `end`, without the first round's linear layer.
fn backward2<Q: Qs>(q: &Q, next: &[Q::Bit<1>], end: usize) -> Vec<Q::Bit<9>> {
    let b1 = iota_chi_inverse::<Q, 1, 2, 3>(q, next, end - 1);
    let b1 = theta_rho_pi_inverse(&b1, |x, y| q.bit_add::<3>(x, y));
    iota_chi_inverse::<Q, 3, 6, 9>(q, &b1, end - 2)
}

/// Evaluate Keccak-p[800, 12] on committed `state`, with the committed intermediate states at
/// witness byte `wit_off`. Returns the first `n_out` output bits.
pub fn qs_keccak<Q: Qs>(
    q: &mut Q,
    state: &[Q::Bit<1>],
    wit_off: usize,
    n_out: usize,
) -> Vec<Q::Bit<8>> {
    // Segment 0: 3 forward, 2 backward.
    let s5 = load_state(q, 8 * wit_off);
    {
        let f1 = round::<Q, 1, 2>(q, state, 0, STATE_BITS);
        let f2 = round::<Q, 2, 4>(q, &f1, 1, STATE_BITS);
        let f3 = round::<Q, 4, 8>(q, &f2, 2, STATE_BITS);
        let bwd = backward2(q, &s5, SEGMENT_START[1]);
        meet::<Q, 8>(q, &f3, &bwd);
    }
    // Segment 1: 2 forward, 2 backward.
    let s9 = load_state(q, 8 * (wit_off + STATE_BYTES));
    {
        let f1 = round::<Q, 1, 2>(q, &s5, 5, STATE_BITS);
        let f2 = round::<Q, 2, 4>(q, &f1, 6, STATE_BITS);
        let bwd = backward2(q, &s9, SEGMENT_START[2]);
        meet::<Q, 4>(q, &f2, &bwd);
    }
    let f1 = round::<Q, 1, 2>(q, &s9, 9, STATE_BITS);
    let f2 = round::<Q, 2, 4>(q, &f1, 10, STATE_BITS);
    round::<Q, 4, 8>(q, &f2, 11, n_out)
}

/// Byte k of a committed state, embedded in GF(2^128).
pub fn qs_byte<Q: Qs, const D: usize>(q: &Q, state: &[Q::Bit<D>], k: usize) -> Q::Val<D> {
    let bits: [Q::Bit<D>; 8] = core::array::from_fn(|j| state[8 * k + j]);
    q.combine8::<D>(&bits)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::block::Block;
    use crate::qs::Prover;

    fn unhex(s: &str) -> Vec<u8> {
        (0..s.len())
            .step_by(2)
            .map(|i| u8::from_str_radix(&s[i..i + 2], 16).unwrap())
            .collect()
    }

    #[test]
    fn known_answers() {
        let kat = include_str!("../testdata/keccak_kat.txt");
        let mut input = None;
        let mut n = 0;
        for line in kat.lines() {
            if let Some(h) = line.strip_prefix("input ") {
                input = Some(unhex(h));
            } else if let Some(h) = line.strip_prefix("output ") {
                let inp: State = input.take().unwrap().try_into().unwrap();
                assert_eq!(keccak_p800(inp).to_vec(), unhex(h));
                n += 1;
            }
        }
        assert!(n > 0);
    }

    #[test]
    fn inverse_linear_layer() {
        let a: Vec<bool> = (0..STATE_BITS)
            .map(|i| (i * 7919 + i / 3) % 5 < 2)
            .collect();
        let b = theta_rho_pi(&a, |x, y| x ^ y);
        assert_eq!(theta_rho_pi_inverse(&b, |x, y| x ^ y), a);
    }

    #[test]
    fn circuit_matches_plain() {
        // Witness: input state (public map: bytes 0..50 from the witness), then committed states.
        let mut input = [0u8; 100];
        for (i, b) in input.iter_mut().enumerate() {
            *b = (i as u8).wrapping_mul(29) ^ 0xa5;
        }
        let mut witness = vec![0u8; 50 + COMMITTED_STATES_BYTES];
        witness[..50].copy_from_slice(&input[..50]);
        encode_committed_states(&mut witness[50..], input);
        let mut map = [-1i32; 100];
        for (i, m) in map.iter_mut().enumerate().take(50) {
            *m = i as i32;
        }
        let macs = vec![Block::ZERO; 8 * witness.len()];
        let chal = [0u8; 56];
        let mut q = Prover::new(&witness, &macs, &chal);
        let st = qs_input(&q, &input, &map);
        // Constraints are checked by debug assertions.
        let out = qs_keccak(&mut q, &st, 50, STATE_BITS);
        let want = keccak_p800(input);
        for i in 0..STATE_BITS {
            assert_eq!(
                out[i].v.is_zero(),
                (want[i / 8] >> (i % 8)) & 1 == 0,
                "bit {i}"
            );
        }
    }
}
