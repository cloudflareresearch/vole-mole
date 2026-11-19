//! UOV OV(256,119,45) with compressed public keys (pqov's `uov-Ip-pkc`).
//!
//! A port of the parts of pqov used by `src/uov/uov.cpp`: key generation from a seed, public key
//! expansion, preimage derivation (`ov_derive_preimage`), and constant-time evaluation of the
//! public map (`ov_publicmap_ct`). Outputs are byte-identical to pqov.

#![allow(clippy::needless_range_loop)]

use aes::Aes128;
use aes::cipher::{Array, BlockCipherEncrypt, KeyInit, consts::U16};

/// Number of variables (preimage length).
pub const N: usize = 119;
/// Number of equations (target length).
pub const M: usize = 45;
/// Number of vinegar variables. The last `M` variables are the oil variables.
pub const V: usize = N - M;

pub const SECRET_KEY_BYTES: usize = 32;
pub const PUBLIC_KEY_BYTES: usize = PK_SEED_BYTES + P3_BYTES;
/// Size of the expanded public map: `M` coefficients for each monomial x_i * x_j with i <= j.
pub const EXPANDED_PUBLIC_KEY_BYTES: usize = M * N * (N + 1) / 2;
pub const PUBLIC_KEY_DIGEST_BYTES: usize = 32;

pub type Target = [u8; M];
pub type Preimage = [u8; N];

const O: usize = M;
const PK_SEED_BYTES: usize = 16;
const P1_BYTES: usize = M * V * (V + 1) / 2;
const P2_BYTES: usize = M * V * O;
const P3_BYTES: usize = M * O * (O + 1) / 2;
const MAX_ATTEMPT_VINEGAR: usize = 256;
const PREIMAGE_DST: &[u8] = b"pqov-derive-preimage";

const _: () = assert!(PUBLIC_KEY_BYTES == 46591);
const _: () = assert!(EXPANDED_PUBLIC_KEY_BYTES == P1_BYTES + P2_BYTES + P3_BYTES);

/// Key generation or preimage derivation failed.
#[derive(Debug)]
pub struct Error;

impl core::fmt::Display for Error {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.write_str("UOV operation failed")
    }
}

impl std::error::Error for Error {}

/// Generate a fresh secret key using the operating system's random number generator.
///
/// Panics if the operating system's random number generator fails.
pub fn generate_secret_key_bytes() -> [u8; SECRET_KEY_BYTES] {
    let mut bytes = [0u8; SECRET_KEY_BYTES];
    getrandom::fill(&mut bytes).expect("OS random number generator failed");
    bytes
}

/// An expanded secret key, alongside the compressed and expanded public key.
pub struct SecretKey {
    sk_seed: [u8; SECRET_KEY_BYTES],
    /// The secret oil space, column-major: column j (oil variable j) is `o[j * V..(j + 1) * V]`.
    o: Box<[u8; V * O]>,
    /// S = (P1 + P1^T) O + P2, in the layout of P2.
    s: Box<[u8]>,
    public_key: Box<[u8; PUBLIC_KEY_BYTES]>,
    expanded_public_key: PublicKey,
}

impl SecretKey {
    /// Expand the key pair from the compact secret key (pqov's `generate_keypair_pkc`).
    pub fn new(bytes: &[u8; SECRET_KEY_BYTES]) -> Result<Self, Error> {
        Ok(keygen::<Native>(bytes))
    }

    /// The compressed public key bytes.
    pub fn public_key_bytes(&self) -> &[u8; PUBLIC_KEY_BYTES] {
        &self.public_key
    }

    /// The expanded public key, i.e., `PublicKey::new(self.public_key_bytes())`.
    pub fn expanded_public_key(&self) -> &PublicKey {
        &self.expanded_public_key
    }

    /// Derive the preimage of the given target, i.e., P(preimage) = target, where P is the public
    /// map (pqov's `ov_derive_preimage`).
    ///
    /// WARNING: This can be used to construct a UOV signature for any message. The secret key must
    /// not be reused for applications that require full UOV signatures.
    pub fn derive_preimage(&self, target: &Target) -> Result<Preimage, Error> {
        derive_preimage::<Native>(self, target)
    }

    fn p1(&self) -> &[u8] {
        &self.expanded_public_key.expanded[..P1_BYTES]
    }
}

/// An expanded public key.
pub struct PublicKey {
    expanded: Box<[u8]>,
    digest: [u8; PUBLIC_KEY_DIGEST_BYTES],
}

impl PublicKey {
    /// Expand the compressed public key (pqov's `expand_pk`).
    pub fn new(bytes: &[u8; PUBLIC_KEY_BYTES]) -> Self {
        let mut expanded = vec![0u8; EXPANDED_PUBLIC_KEY_BYTES].into_boxed_slice();
        let seed: &[u8; PK_SEED_BYTES] = bytes[..PK_SEED_BYTES].try_into().unwrap();
        expand_p1p2(seed, &mut expanded[..P1_BYTES + P2_BYTES]);
        expanded[P1_BYTES + P2_BYTES..].copy_from_slice(&bytes[PK_SEED_BYTES..]);
        let mut digest = [0u8; PUBLIC_KEY_DIGEST_BYTES];
        shake256(&[bytes], &mut digest);
        Self { expanded, digest }
    }

    /// Evaluate the public map P at `preimage` in constant time (pqov's `ov_publicmap_ct`).
    pub fn eval(&self, preimage: &Preimage) -> Target {
        eval::<Native>(&self.expanded, preimage)
    }

    /// The expanded public map in pqov's layout (see [`for_each_monomial`]).
    pub fn expanded(&self) -> &[u8] {
        &self.expanded
    }

    /// A digest of the compressed public key (SHAKE256), which identifies the key.
    pub fn digest(&self) -> &[u8; PUBLIC_KEY_DIGEST_BYTES] {
        &self.digest
    }
}

/// Call `f(i, j, coeffs)` for each monomial x_i * x_j (i <= j) of the public map P, where `coeffs`
/// holds the coefficients of the monomial in each of the M components of P.
///
/// Monomials are visited in increasing order of i. The expanded public map is laid out as three
/// blocks, stored one after the other and each row by row: P1 (vinegar x vinegar, upper
/// triangular), P2 (vinegar x oil), and P3 (oil x oil, upper triangular).
pub fn for_each_monomial(pk: &[u8], mut f: impl FnMut(usize, usize, &[u8; M])) {
    assert_eq!(pk.len(), EXPANDED_PUBLIC_KEY_BYTES);
    let coeffs = |off: usize| -> &[u8; M] { pk[off..off + M].try_into().unwrap() };
    let mut p1 = 0;
    let mut p2 = P1_BYTES;
    let mut p3 = P1_BYTES + P2_BYTES;
    for i in 0..V {
        for j in i..V {
            f(i, j, coeffs(p1));
            p1 += M;
        }
        for j in V..N {
            f(i, j, coeffs(p2));
            p2 += M;
        }
    }
    for i in V..N {
        for j in i..N {
            f(i, j, coeffs(p3));
            p3 += M;
        }
    }
}

// ---------------------------------------------------------------------------------------------
// Layout helpers

/// Offset of the coefficients of x_i x_j (i <= j < V) in P1.
const fn p1_off(i: usize, j: usize) -> usize {
    M * (i * (2 * V - i + 1) / 2 + (j - i))
}

/// Offset of the coefficients of x_i x_{V+j} in P2 (relative to the start of P2).
const fn p2_off(i: usize, j: usize) -> usize {
    M * (i * O + j)
}

/// Offset of the coefficients of x_{V+a} x_{V+b} (a <= b) in P3 (relative to the start of P3).
const fn p3_off(a: usize, b: usize) -> usize {
    M * (a * (2 * O - a + 1) / 2 + (b - a))
}

// ---------------------------------------------------------------------------------------------
// Symmetric primitives

const SHAKE256_RATE: usize = 136;

/// Incremental SHAKE256 (pqov's `hash_ctx` with the bundled fips202).
#[derive(Clone)]
struct Shake256 {
    st: [u64; 25],
    pos: usize,
    keccak: keccak::Keccak,
}

impl Shake256 {
    fn new() -> Self {
        Self {
            st: [0; 25],
            pos: 0,
            keccak: keccak::Keccak::new(),
        }
    }

    fn absorb(&mut self, mut data: &[u8]) {
        let Self { st, pos, keccak } = self;
        keccak.with_f1600(|f| {
            while !data.is_empty() {
                if *pos == 0 && data.len() >= SHAKE256_RATE {
                    let (block, rest) = data.split_at(SHAKE256_RATE);
                    for (s, w) in st.iter_mut().zip(block.chunks_exact(8)) {
                        *s ^= u64::from_le_bytes(w.try_into().unwrap());
                    }
                    f(st);
                    data = rest;
                    continue;
                }
                let take = (SHAKE256_RATE - *pos).min(data.len());
                for (i, &b) in data[..take].iter().enumerate() {
                    let p = *pos + i;
                    st[p / 8] ^= (b as u64) << (8 * (p % 8));
                }
                *pos += take;
                data = &data[take..];
                if *pos == SHAKE256_RATE {
                    f(st);
                    *pos = 0;
                }
            }
        });
    }

    fn finalize(self, out: &mut [u8]) {
        let Self {
            mut st,
            pos,
            keccak,
        } = self;
        st[pos / 8] ^= 0x1f << (8 * (pos % 8));
        st[(SHAKE256_RATE - 1) / 8] ^= 0x80 << (8 * ((SHAKE256_RATE - 1) % 8));
        keccak.with_f1600(|f| {
            for chunk in out.chunks_mut(SHAKE256_RATE) {
                f(&mut st);
                for (i, b) in chunk.iter_mut().enumerate() {
                    *b = (st[i / 8] >> (8 * (i % 8))) as u8;
                }
            }
        });
    }
}

fn shake256(parts: &[&[u8]], out: &mut [u8]) {
    let mut h = Shake256::new();
    for p in parts {
        h.absorb(p);
    }
    h.finalize(out);
}

/// Expand P1 || P2 from the public seed: AES-128-CTR with a zero nonce and a 32-bit big-endian
/// block counter in the last four bytes, starting at zero (pqov's `prng_gen_publicinputs`).
fn expand_p1p2(seed: &[u8; PK_SEED_BYTES], out: &mut [u8]) {
    let cipher = Aes128::new(&Array::from(*seed));
    let counter_block = |t: usize| {
        let mut b = [0u8; 16];
        b[12..].copy_from_slice(&(t as u32).to_be_bytes());
        b
    };
    let (blocks, rest) = out.as_chunks_mut::<16>();
    for (t, b) in blocks.iter_mut().enumerate() {
        *b = counter_block(t);
    }
    let n_blocks = blocks.len();
    cipher.encrypt_blocks(Array::<u8, U16>::cast_slice_from_core_mut(blocks));
    if !rest.is_empty() {
        let mut b = Array::from(counter_block(n_blocks));
        cipher.encrypt_block(&mut b);
        let len = rest.len();
        rest.copy_from_slice(&b[..len]);
    }
}

// ---------------------------------------------------------------------------------------------
// GF(256) arithmetic, GF(2)[x] / (x^8 + x^4 + x^3 + x + 1).

/// Constant-time multiplication in GF(256).
const fn gf_mul(a: u8, b: u8) -> u8 {
    let mut r = 0u8;
    let mut a = a;
    let mut i = 0;
    while i < 8 {
        r ^= a & 0u8.wrapping_sub((b >> i) & 1);
        a = (a << 1) ^ ((a >> 7) * 0x1b);
        i += 1;
    }
    r
}

/// Reduction tables for 16-bit carry-less products: the high byte h (< 0x80) contributes
/// `R_LO[h & 15] ^ R_HI[h >> 4]`.
#[cfg_attr(not(target_arch = "aarch64"), allow(dead_code))]
const R_LO: [u8; 16] = {
    let mut t = [0u8; 16];
    let mut n = 0;
    while n < 16 {
        t[n] = gf_mul(n as u8, 0x1b);
        n += 1;
    }
    t
};
#[cfg_attr(not(target_arch = "aarch64"), allow(dead_code))]
const R_HI: [u8; 16] = {
    let mut t = [0u8; 16];
    let mut n = 0;
    while n < 16 {
        t[n] = gf_mul((n as u8) << 4, 0x1b);
        n += 1;
    }
    t
};

/// 0xff if x == 0, else 0x00, in constant time.
#[inline(always)]
fn ct_is_zero(x: u8) -> u8 {
    ((x as u32).wrapping_sub(1) >> 8) as u8
}

/// Vector operations on 16-byte chunks of GF(256) elements.
///
/// `Acc` accumulates sums of products of chunks with scalars, possibly unreduced.
trait Backend {
    type Ch: Copy;
    type Sc: Copy;
    type Acc: Copy;

    fn zero() -> Self::Ch;
    fn splat(b: u8) -> Self::Ch;
    /// # Safety
    /// `p` must be valid for reading 16 bytes.
    unsafe fn load(p: *const u8) -> Self::Ch;
    /// # Safety
    /// `p` must be valid for writing 16 bytes.
    unsafe fn store(p: *mut u8, v: Self::Ch);
    fn xor(a: Self::Ch, b: Self::Ch) -> Self::Ch;
    fn and(a: Self::Ch, b: Self::Ch) -> Self::Ch;
    fn sc(c: u8) -> Self::Sc;
    fn acc_zero() -> Self::Acc;
    /// acc += a * c
    fn madd(acc: &mut Self::Acc, a: Self::Ch, c: Self::Sc);
    fn reduce(acc: Self::Acc) -> Self::Ch;
    fn mul_u8(a: u8, b: u8) -> u8;

    /// acc += a * c + b * d
    #[inline(always)]
    fn madd2(acc: &mut Self::Acc, a: Self::Ch, c: Self::Sc, b: Self::Ch, d: Self::Sc) {
        Self::madd(acc, a, c);
        Self::madd(acc, b, d);
    }

    #[inline(always)]
    fn mul(a: Self::Ch, c: Self::Sc) -> Self::Ch {
        let mut acc = Self::acc_zero();
        Self::madd(&mut acc, a, c);
        Self::reduce(acc)
    }
}

/// Portable backend: bitwise multiplication on pairs of u64 lanes.
#[cfg_attr(target_arch = "aarch64", allow(dead_code))]
mod soft {
    use super::Backend;

    pub(super) struct Soft;

    const LO7: u64 = 0x7f7f_7f7f_7f7f_7f7f;
    const ONES: u64 = 0x0101_0101_0101_0101;

    #[inline(always)]
    fn xtime(x: u64) -> u64 {
        ((x & LO7) << 1) ^ (((x >> 7) & ONES) * 0x1b)
    }

    impl Backend for Soft {
        type Ch = [u64; 2];
        type Sc = u8;
        type Acc = [u64; 2];

        #[inline(always)]
        fn zero() -> [u64; 2] {
            [0; 2]
        }
        #[inline(always)]
        fn splat(b: u8) -> [u64; 2] {
            [ONES * b as u64; 2]
        }
        #[inline(always)]
        unsafe fn load(p: *const u8) -> [u64; 2] {
            let b = unsafe { p.cast::<[u8; 16]>().read_unaligned() };
            [
                u64::from_le_bytes(b[..8].try_into().unwrap()),
                u64::from_le_bytes(b[8..].try_into().unwrap()),
            ]
        }
        #[inline(always)]
        unsafe fn store(p: *mut u8, v: [u64; 2]) {
            let mut b = [0u8; 16];
            b[..8].copy_from_slice(&v[0].to_le_bytes());
            b[8..].copy_from_slice(&v[1].to_le_bytes());
            unsafe { p.cast::<[u8; 16]>().write_unaligned(b) };
        }
        #[inline(always)]
        fn xor(a: [u64; 2], b: [u64; 2]) -> [u64; 2] {
            [a[0] ^ b[0], a[1] ^ b[1]]
        }
        #[inline(always)]
        fn and(a: [u64; 2], b: [u64; 2]) -> [u64; 2] {
            [a[0] & b[0], a[1] & b[1]]
        }
        #[inline(always)]
        fn sc(c: u8) -> u8 {
            c
        }
        #[inline(always)]
        fn acc_zero() -> [u64; 2] {
            [0; 2]
        }
        #[inline(always)]
        fn madd(acc: &mut [u64; 2], a: [u64; 2], c: u8) {
            let mut x = a;
            for i in 0..8 {
                let m = 0u64.wrapping_sub(((c >> i) & 1) as u64);
                acc[0] ^= x[0] & m;
                acc[1] ^= x[1] & m;
                x = [xtime(x[0]), xtime(x[1])];
            }
        }
        #[inline(always)]
        fn reduce(acc: [u64; 2]) -> [u64; 2] {
            acc
        }
        #[inline(always)]
        fn mul_u8(a: u8, b: u8) -> u8 {
            super::gf_mul(a, b)
        }
    }
}

/// NEON backend: carry-less multiplication (PMULL.8) with lazy reduction.
#[cfg(target_arch = "aarch64")]
#[allow(unused_unsafe)]
mod neon {
    use super::{Backend, R_HI, R_LO};
    use core::arch::aarch64::*;

    pub(super) struct Neon;

    /// Unreduced 16-bit products of the low and high halves of a chunk.
    #[derive(Clone, Copy)]
    pub(super) struct Acc(uint16x8_t, uint16x8_t);

    impl Backend for Neon {
        type Ch = uint8x16_t;
        type Sc = uint8x16_t;
        type Acc = Acc;

        #[inline(always)]
        fn zero() -> uint8x16_t {
            unsafe { vdupq_n_u8(0) }
        }
        #[inline(always)]
        fn splat(b: u8) -> uint8x16_t {
            unsafe { vdupq_n_u8(b) }
        }
        #[inline(always)]
        unsafe fn load(p: *const u8) -> uint8x16_t {
            unsafe { vld1q_u8(p) }
        }
        #[inline(always)]
        unsafe fn store(p: *mut u8, v: uint8x16_t) {
            unsafe { vst1q_u8(p, v) }
        }
        #[inline(always)]
        fn xor(a: uint8x16_t, b: uint8x16_t) -> uint8x16_t {
            unsafe { veorq_u8(a, b) }
        }
        #[inline(always)]
        fn and(a: uint8x16_t, b: uint8x16_t) -> uint8x16_t {
            unsafe { vandq_u8(a, b) }
        }
        #[inline(always)]
        fn sc(c: u8) -> uint8x16_t {
            unsafe { vdupq_n_u8(c) }
        }
        #[inline(always)]
        fn acc_zero() -> Acc {
            unsafe { Acc(vdupq_n_u16(0), vdupq_n_u16(0)) }
        }
        #[inline(always)]
        fn madd(acc: &mut Acc, a: uint8x16_t, c: uint8x16_t) {
            unsafe {
                let pa = vreinterpretq_p8_u8(a);
                let pc = vreinterpretq_p8_u8(c);
                let lo = vmull_p8(vget_low_p8(pa), vget_low_p8(pc));
                let hi = vmull_high_p8(pa, pc);
                acc.0 = veorq_u16(acc.0, vreinterpretq_u16_p16(lo));
                acc.1 = veorq_u16(acc.1, vreinterpretq_u16_p16(hi));
            }
        }
        #[cfg(target_feature = "sha3")]
        #[inline(always)]
        fn madd2(acc: &mut Acc, a: uint8x16_t, c: uint8x16_t, b: uint8x16_t, d: uint8x16_t) {
            unsafe {
                let (pa, pc) = (vreinterpretq_p8_u8(a), vreinterpretq_p8_u8(c));
                let (pb, pd) = (vreinterpretq_p8_u8(b), vreinterpretq_p8_u8(d));
                let lo0 = vreinterpretq_u16_p16(vmull_p8(vget_low_p8(pa), vget_low_p8(pc)));
                let lo1 = vreinterpretq_u16_p16(vmull_p8(vget_low_p8(pb), vget_low_p8(pd)));
                let hi0 = vreinterpretq_u16_p16(vmull_high_p8(pa, pc));
                let hi1 = vreinterpretq_u16_p16(vmull_high_p8(pb, pd));
                acc.0 = veor3q_u16(acc.0, lo0, lo1);
                acc.1 = veor3q_u16(acc.1, hi0, hi1);
            }
        }
        #[inline(always)]
        fn reduce(acc: Acc) -> uint8x16_t {
            unsafe {
                let l = vreinterpretq_u8_u16(acc.0);
                let h = vreinterpretq_u8_u16(acc.1);
                let lo = vuzp1q_u8(l, h);
                let hi = vuzp2q_u8(l, h);
                let r_lo = vld1q_u8(R_LO.as_ptr());
                let r_hi = vld1q_u8(R_HI.as_ptr());
                let t0 = vqtbl1q_u8(r_lo, vandq_u8(hi, vdupq_n_u8(0x0f)));
                let t1 = vqtbl1q_u8(r_hi, vshrq_n_u8::<4>(hi));
                veorq_u8(lo, veorq_u8(t0, t1))
            }
        }
        #[inline(always)]
        fn mul_u8(a: u8, b: u8) -> u8 {
            unsafe { vgetq_lane_u8::<0>(Self::mul(vdupq_n_u8(a), vdupq_n_u8(b))) }
        }
    }
}

#[cfg(target_arch = "aarch64")]
type Native = neon::Neon;
#[cfg(not(target_arch = "aarch64"))]
type Native = soft::Soft;

/// Constant-time inversion in GF(256) (0 maps to 0): a^254.
fn gf_inv<B: Backend>(a: u8) -> u8 {
    let a2 = B::mul_u8(a, a);
    let a4 = B::mul_u8(a2, a2);
    let a8 = B::mul_u8(a4, a4);
    let a16 = B::mul_u8(a8, a8);
    let a32 = B::mul_u8(a16, a16);
    let a64 = B::mul_u8(a32, a32);
    let a128 = B::mul_u8(a64, a64);
    let r = B::mul_u8(a2, a4);
    let r = B::mul_u8(r, a8);
    let r = B::mul_u8(r, a16);
    let r = B::mul_u8(r, a32);
    let r = B::mul_u8(r, a64);
    B::mul_u8(r, a128)
}

// A vector of M = 45 elements is handled as three chunks at offsets 0, 16 and 29. The last two
// overlap, but all operations are lane-wise, so the overlapping lanes always agree.
const C2: usize = M - 16;

type Ch45<B> = [<B as Backend>::Ch; 3];
type Acc45<B> = [<B as Backend>::Acc; 3];

/// # Safety
/// `p` must be valid for reading M bytes.
#[inline(always)]
unsafe fn load45<B: Backend>(p: *const u8) -> Ch45<B> {
    unsafe { [B::load(p), B::load(p.add(16)), B::load(p.add(C2))] }
}

/// # Safety
/// `p` must be valid for writing M bytes.
#[inline(always)]
unsafe fn store45<B: Backend>(p: *mut u8, v: Ch45<B>) {
    unsafe {
        B::store(p, v[0]);
        B::store(p.add(16), v[1]);
        B::store(p.add(C2), v[2]);
    }
}

#[inline(always)]
fn acc45_zero<B: Backend>() -> Acc45<B> {
    [B::acc_zero(); 3]
}

#[inline(always)]
fn madd45<B: Backend>(acc: &mut Acc45<B>, a: &Ch45<B>, c: B::Sc) {
    for t in 0..3 {
        B::madd(&mut acc[t], a[t], c);
    }
}

#[inline(always)]
fn madd45x2<B: Backend>(acc: &mut Acc45<B>, a: &Ch45<B>, c: B::Sc, b: &Ch45<B>, d: B::Sc) {
    for t in 0..3 {
        B::madd2(&mut acc[t], a[t], c, b[t], d);
    }
}

#[inline(always)]
fn reduce45<B: Backend>(acc: Acc45<B>) -> Ch45<B> {
    [B::reduce(acc[0]), B::reduce(acc[1]), B::reduce(acc[2])]
}

/// acc += sum_t coeffs[t] * vec_t, where vec_t is the M-byte vector at `off + M * t` in `base`.
#[inline(always)]
fn row_madd<B: Backend>(acc: &mut Acc45<B>, base: &[u8], off: usize, coeffs: &[u8]) {
    assert!(off + M * coeffs.len() <= base.len());
    let p = unsafe { base.as_ptr().add(off) };
    let pairs = coeffs.len() / 2;
    for t in 0..pairs {
        let x0 = unsafe { load45::<B>(p.add(M * 2 * t)) };
        let x1 = unsafe { load45::<B>(p.add(M * (2 * t + 1))) };
        madd45x2::<B>(
            acc,
            &x0,
            B::sc(coeffs[2 * t]),
            &x1,
            B::sc(coeffs[2 * t + 1]),
        );
    }
    if coeffs.len() % 2 == 1 {
        let t = coeffs.len() - 1;
        let x = unsafe { load45::<B>(p.add(M * t)) };
        madd45::<B>(acc, &x, B::sc(coeffs[t]));
    }
}

/// For j in 0..M: dst[off(j)..][..M] += sum_k cs[k][j] * xs[k].
#[inline(always)]
fn lincomb_kernel<B: Backend>(
    xs: &[Ch45<B>],
    cs: &[[u8; M]],
    dst: &mut [u8],
    off: impl Fn(usize) -> usize,
) {
    assert_eq!(xs.len(), cs.len());
    const J: usize = 3;
    for jb in (0..M).step_by(J) {
        let mut acc = [acc45_zero::<B>(); J];
        let (xs2, xs1) = xs.as_chunks::<2>();
        let (cs2, cs1) = cs.as_chunks::<2>();
        for (x, c) in xs2.iter().zip(cs2) {
            for jj in 0..J {
                let (s0, s1) = (B::sc(c[0][jb + jj]), B::sc(c[1][jb + jj]));
                madd45x2::<B>(&mut acc[jj], &x[0], s0, &x[1], s1);
            }
        }
        for (x, c) in xs1.iter().zip(cs1) {
            for jj in 0..J {
                madd45::<B>(&mut acc[jj], x, B::sc(c[jb + jj]));
            }
        }
        for (jj, a) in acc.into_iter().enumerate() {
            let o = off(jb + jj);
            assert!(o + M <= dst.len());
            let r = reduce45::<B>(a);
            unsafe {
                let p = dst.as_mut_ptr().add(o);
                let d = load45::<B>(p);
                store45::<B>(
                    p,
                    [B::xor(d[0], r[0]), B::xor(d[1], r[1]), B::xor(d[2], r[2])],
                );
            }
        }
    }
}

/// dst = sum_i coeffs[i] * src[i * L..(i + 1) * L].
fn lincomb_long<B: Backend, const L: usize>(dst: &mut [u8; L], src: &[u8], coeffs: &[u8]) {
    const G: usize = 8;
    assert!(L >= 16 && L <= 2048);
    assert!(coeffs.len() * L <= src.len());
    // Chunk offsets, with the last chunk overlapping its predecessor and the list padded to a
    // multiple of G by repeating the last offset.
    let n_chunks = L.div_ceil(16);
    let n_padded = n_chunks.div_ceil(G) * G;
    let mut offs = [0usize; 2048 / 16 + G];
    for (t, o) in offs[..n_padded].iter_mut().enumerate() {
        *o = (16 * t).min(L - 16);
    }
    for g in offs[..n_padded].chunks_exact(G) {
        let mut acc = [B::acc_zero(); G];
        let (c2, c1) = coeffs.as_chunks::<2>();
        for (i, c) in c2.iter().enumerate() {
            let (s0, s1) = (B::sc(c[0]), B::sc(c[1]));
            let b0 = unsafe { src.as_ptr().add(2 * i * L) };
            let b1 = unsafe { b0.add(L) };
            for q in 0..G {
                let (x0, x1) = unsafe { (B::load(b0.add(g[q])), B::load(b1.add(g[q]))) };
                B::madd2(&mut acc[q], x0, s0, x1, s1);
            }
        }
        if let [c] = c1 {
            let s = B::sc(*c);
            let base = unsafe { src.as_ptr().add(2 * c2.len() * L) };
            for q in 0..G {
                B::madd(&mut acc[q], unsafe { B::load(base.add(g[q])) }, s);
            }
        }
        for q in 0..G {
            unsafe { B::store(dst.as_mut_ptr().add(g[q]), B::reduce(acc[q])) };
        }
    }
}

/// sum_{i <= j < V} P1[i][j] v_i v_j
fn eval_p1<B: Backend>(p1: &[u8], v: &[u8]) -> Acc45<B> {
    let mut y = acc45_zero::<B>();
    for i in 0..V {
        let mut inner = acc45_zero::<B>();
        row_madd::<B>(&mut inner, p1, p1_off(i, i), &v[i..V]);
        madd45::<B>(&mut y, &reduce45::<B>(inner), B::sc(v[i]));
    }
    y
}

fn store_target<B: Backend>(acc: Acc45<B>) -> Target {
    let mut out = [0u8; M];
    unsafe { store45::<B>(out.as_mut_ptr(), reduce45::<B>(acc)) };
    out
}

/// P(x) for the expanded public key `pk`, in constant time.
fn eval<B: Backend>(pk: &[u8], x: &Preimage) -> Target {
    assert_eq!(pk.len(), EXPANDED_PUBLIC_KEY_BYTES);
    let mut y = acc45_zero::<B>();
    for i in 0..V {
        let mut inner = acc45_zero::<B>();
        row_madd::<B>(&mut inner, pk, p1_off(i, i), &x[i..V]);
        row_madd::<B>(&mut inner, pk, P1_BYTES + p2_off(i, 0), &x[V..N]);
        madd45::<B>(&mut y, &reduce45::<B>(inner), B::sc(x[i]));
    }
    for a in 0..O {
        let mut inner = acc45_zero::<B>();
        row_madd::<B>(
            &mut inner,
            pk,
            P1_BYTES + P2_BYTES + p3_off(a, a),
            &x[V + a..N],
        );
        madd45::<B>(&mut y, &reduce45::<B>(inner), B::sc(x[V + a]));
    }
    store_target::<B>(y)
}

fn keygen<B: Backend>(sk_seed: &[u8; SECRET_KEY_BYTES]) -> SecretKey {
    // pk_seed || O <- SHAKE256(sk_seed)
    let mut buf = [0u8; PK_SEED_BYTES + V * O];
    shake256(&[sk_seed], &mut buf);
    let pk_seed: [u8; PK_SEED_BYTES] = buf[..PK_SEED_BYTES].try_into().unwrap();
    let o: Box<[u8; V * O]> = Box::new(buf[PK_SEED_BYTES..].try_into().unwrap());
    // Row-major copy of O: ot[k][j] is the coefficient of oil variable j in vinegar variable k.
    let mut ot = [[0u8; M]; V];
    for j in 0..O {
        for k in 0..V {
            ot[k][j] = o[j * V + k];
        }
    }

    // P1 and P2 are the same AES-CTR stream as in the expanded public key.
    let mut expanded = vec![0u8; EXPANDED_PUBLIC_KEY_BYTES].into_boxed_slice();
    expand_p1p2(&pk_seed, &mut expanded[..P1_BYTES + P2_BYTES]);
    let (p1p2, p3) = expanded.split_at_mut(P1_BYTES + P2_BYTES);
    let (p1, p2) = p1p2.split_at(P1_BYTES);

    let mut xs = [[B::zero(); 3]; V];

    // F = P1 O + P2, with P1 upper triangular.
    let mut s = p2.to_vec().into_boxed_slice();
    for i in 0..V {
        for k in i..V {
            xs[k - i] = unsafe { load45::<B>(p1.as_ptr().add(p1_off(i, k))) };
        }
        lincomb_kernel::<B>(
            &xs[..V - i],
            &ot[i..],
            &mut s[p2_off(i, 0)..p2_off(i + 1, 0)],
            |j| M * j,
        );
    }

    // T = O^T F; P3 = UT(T + T^T)
    let mut t = vec![0u8; M * O * O];
    for b in 0..O {
        for k in 0..V {
            xs[k] = unsafe { load45::<B>(s.as_ptr().add(p2_off(k, b))) };
        }
        lincomb_kernel::<B>(&xs, &ot, &mut t, |a| M * (a * O + b));
    }
    for a in 0..O {
        for b in a..O {
            let dst = &mut p3[p3_off(a, b)..p3_off(a, b) + M];
            dst.copy_from_slice(&t[M * (a * O + b)..][..M]);
            if a != b {
                for (d, &x) in dst.iter_mut().zip(&t[M * (b * O + a)..][..M]) {
                    *d ^= x;
                }
            }
        }
    }

    // S = F + P1^T O = (P1 + P1^T) O + P2. The diagonal of P1 is added twice and cancels.
    for i in 0..V {
        for k in 0..=i {
            xs[k] = unsafe { load45::<B>(p1.as_ptr().add(p1_off(k, i))) };
        }
        lincomb_kernel::<B>(
            &xs[..=i],
            &ot[..=i],
            &mut s[p2_off(i, 0)..p2_off(i + 1, 0)],
            |j| M * j,
        );
    }

    let mut public_key: Box<[u8; PUBLIC_KEY_BYTES]> = vec![0u8; PUBLIC_KEY_BYTES]
        .into_boxed_slice()
        .try_into()
        .unwrap();
    public_key[..PK_SEED_BYTES].copy_from_slice(&pk_seed);
    public_key[PK_SEED_BYTES..].copy_from_slice(p3);
    let mut digest = [0u8; PUBLIC_KEY_DIGEST_BYTES];
    shake256(&[&public_key[..]], &mut digest);

    SecretKey {
        sk_seed: *sk_seed,
        o,
        s,
        public_key,
        expanded_public_key: PublicKey { expanded, digest },
    }
}

/// Solve L x = rhs in constant time, where `l` is column-major (column j is `l[j * M..][..M]`).
/// Returns None if L is singular. Matches pqov's gf256mat_gaussian_elim/back_substitute.
fn solve<B: Backend>(l: &[u8; O * M], rhs: &[u8; M]) -> Option<[u8; O]> {
    const W: usize = 48;
    let mut rows = [[0u8; W]; M];
    for (j, row) in rows.iter_mut().enumerate() {
        for c in 0..O {
            row[c] = l[c * M + j];
        }
        row[O] = rhs[j];
    }

    let mut ok = 0xffu8;
    for i in 0..M {
        let t0 = i / 16;
        let mut ai = [B::zero(); 3];
        for t in t0..3 {
            ai[t] = unsafe { B::load(rows[i].as_ptr().add(16 * t)) };
        }
        let mut pivot = rows[i][i];
        for j in i + 1..M {
            let m = ct_is_zero(pivot);
            pivot ^= m & rows[j][i];
            let mv = B::splat(m);
            for t in t0..3 {
                let aj = unsafe { B::load(rows[j].as_ptr().add(16 * t)) };
                ai[t] = B::xor(ai[t], B::and(mv, aj));
            }
        }
        ok &= !ct_is_zero(pivot);
        let inv = B::sc(gf_inv::<B>(pivot));
        for t in t0..3 {
            ai[t] = B::mul(ai[t], inv);
            unsafe { B::store(rows[i].as_mut_ptr().add(16 * t), ai[t]) };
        }
        for j in i + 1..M {
            let f = B::sc(rows[j][i]);
            for t in t0..3 {
                let p = unsafe { rows[j].as_mut_ptr().add(16 * t) };
                unsafe { B::store(p, B::xor(B::load(p), B::mul(ai[t], f))) };
            }
        }
    }

    // Back substitution on the unit upper triangular system.
    let mut x = [0u8; W];
    for (j, row) in rows.iter().enumerate() {
        x[j] = row[O];
    }
    let mut col = [0u8; W];
    for i in (1..M).rev() {
        for j in 0..i {
            col[j] = rows[j][i];
        }
        col[i] = 0;
        let f = B::sc(x[i]);
        for t in 0..3 {
            unsafe {
                let p = x.as_mut_ptr().add(16 * t);
                let c = B::load(col.as_ptr().add(16 * t));
                B::store(p, B::xor(B::load(p), B::mul(c, f)));
            }
        }
    }

    if ok == 0xff {
        Some(x[..O].try_into().unwrap())
    } else {
        None
    }
}

fn derive_preimage<B: Backend>(sk: &SecretKey, target: &Target) -> Result<Preimage, Error> {
    // vinegar <- H(target || sk_seed || DST || ctr)
    let mut prefix = Shake256::new();
    prefix.absorb(target);
    prefix.absorb(&sk.sk_seed);
    prefix.absorb(PREIMAGE_DST);

    let p1 = sk.p1();
    for n_attempt in 0..MAX_ATTEMPT_VINEGAR {
        let mut h = prefix.clone();
        h.absorb(&[n_attempt as u8]);
        let mut vinegar = [0u8; V];
        h.finalize(&mut vinegar);

        // L = sum_i v_i S_i, column-major.
        let mut l = [0u8; O * M];
        lincomb_long::<B, { O * M }>(&mut l, &sk.s, &vinegar);
        let mut rhs = store_target::<B>(eval_p1::<B>(p1, &vinegar));
        for (r, &y) in rhs.iter_mut().zip(target) {
            *r ^= y;
        }
        // Rejection sampling: whether the system is singular is not secret.
        let Some(x) = solve::<B>(&l, &rhs) else {
            continue;
        };

        // w = (v + O x, x)
        let mut ox = [0u8; V];
        lincomb_long::<B, V>(&mut ox, &sk.o[..], &x);
        let mut w = [0u8; N];
        for k in 0..V {
            w[k] = vinegar[k] ^ ox[k];
        }
        w[V..].copy_from_slice(&x);
        return Ok(w);
    }
    Err(Error)
}

#[cfg(test)]
mod tests {
    use super::*;

    fn hex(b: &[u8]) -> String {
        b.iter().map(|x| format!("{x:02x}")).collect()
    }

    fn hash_hex(b: &[u8]) -> String {
        let mut h = [0u8; 32];
        shake256(&[b], &mut h);
        hex(&h)
    }

    struct Kat {
        seed: [u8; 32],
        cpk: &'static str,
        sk: &'static str,
        epk: &'static str,
        preimages: [&'static str; 2],
        eval_x: &'static str,
    }

    fn kats() -> [Kat; 2] {
        let mut seed0 = [0u8; 32];
        for (i, b) in seed0.iter_mut().enumerate() {
            *b = i as u8;
        }
        [
            Kat {
                seed: seed0,
                cpk: "653c9d53d5c0f3f96d8fa74bbd9eeb036230d9dbb8831011989e1b0d20c72bb2",
                sk: "8b25118fbbcc4bde0c2a7e71770aa6aa26808f59cf2b674f82a678c8a64dff0c",
                epk: "6018df56bd1453d3457e39f2959915e19334bf6a38e8aa103b8f2557d212d90b",
                preimages: [
                    "d8fa7835b24395789dff24f126e817fe3f35bf5b3961615a0811bd5902d4a1d8abbba6ab4a04fc225284572bc9f9c57edf892eaa42bea1844682682e555d0823d6a0cf149bfec2e419d6c970b71e5734f1785115146461787800be7d6ed1496bfb555d00fd0e0643cc554e5497e7ac189d60cd6a0b4bf2",
                    "96a26b4e8e316717b88c8439d660892c43ec6e2d76358c8cab5877442636142eddee14a4c9d0112a3d3f3ec85ff8786af6fcae7dfaf2260af6f5cc0c7712375ef9985e138bb7f427cd166e25b8fe4d3c74a6a370b33fa76dbc956e92bff804d4acf2d15089dbdbc7088dfe89f8cb67207046e76e1a03f2",
                ],
                eval_x: "ae8f8eea4504ef9378f436b421f9f4a526cd19d7d9f6ee2688fc7c89ee8fc44e2f3ec83331e06e18fa7bfc89db",
            },
            Kat {
                seed: [0xab; 32],
                cpk: "6596449ed938c173b616fbc09da600d9093421318495020defa3f0b951e11944",
                sk: "b65756a23df65c289ba80b2c36d742de8736755fe94091ec45b8dee1e5c579f5",
                epk: "2b803724a880a51501b3122076788bdc1afe5d32034bcb19380db00efd586238",
                preimages: [
                    "e56cbb6b900e0c47a483ec593fe71825ccd4dec234ef98697c7211976c6dd21d7164abe311c5cd9fec7de1ee2d483f920f9f6a452922e864266f6f13a3c1c7906320419573e5580516954d3fc0db8213577b644f075a1e9ce6b32412916ca54ce0d2bf57881d83d7e410a68cfa7d8da81bc9eb90a79054",
                    "35f06e5a4ac61b27a9688a1101a73621134aeb639330ba1aa3b6294e04b1882a9f3d0450f2c5ca6338870dee8144284990af29459702d8f3a6caf8ac91c46e33e88233cf6c6aa3ed6036f03713b350f059fa42860c360e7c901ecfcde68d2aab865657445e8dedbdea63802a3bece4cdd9affa29e97140",
                ],
                eval_x: "7c09c0eedbf9fbadd03ac69e634ee2cd0719f0753659a6d439365478a5618b2038fd3079a1046e88affaa08b49",
            },
        ]
    }

    fn kat_target(t: usize) -> Target {
        core::array::from_fn(|i| (t * 101 + i * 7 + 3) as u8)
    }

    fn kat_x() -> Preimage {
        core::array::from_fn(|i| (i * 13 + 5) as u8)
    }

    /// Hash of pqov's sk_t: sk_seed || O || P1 || S.
    fn sk_hash(sk: &SecretKey) -> String {
        let mut h = [0u8; 32];
        shake256(&[&sk.sk_seed, &sk.o[..], sk.p1(), &sk.s], &mut h);
        hex(&h)
    }

    fn check_kats<B: Backend>() {
        for kat in kats() {
            let sk = keygen::<B>(&kat.seed);
            assert_eq!(hash_hex(sk.public_key_bytes()), kat.cpk);
            assert_eq!(sk_hash(&sk), kat.sk);
            assert_eq!(hash_hex(sk.expanded_public_key().expanded()), kat.epk);
            assert_eq!(
                sk.expanded_public_key().digest(),
                &PublicKey::new(sk.public_key_bytes()).digest
            );
            let pk = PublicKey::new(sk.public_key_bytes());
            assert_eq!(hash_hex(pk.expanded()), kat.epk);
            assert_eq!(hex(pk.digest()), kat.cpk);
            for (t, expected) in kat.preimages.iter().enumerate() {
                let target = kat_target(t);
                let w = derive_preimage::<B>(&sk, &target).unwrap();
                assert_eq!(hex(&w), *expected);
                assert_eq!(eval::<B>(pk.expanded(), &w), target);
            }
            assert_eq!(hex(&eval::<B>(pk.expanded(), &kat_x())), kat.eval_x);
        }
    }

    #[test]
    fn uov_kat_native() {
        check_kats::<Native>();
    }

    #[test]
    fn uov_kat_soft() {
        check_kats::<soft::Soft>();
    }

    #[test]
    fn uov_public_api() {
        let sk = SecretKey::new(&generate_secret_key_bytes()).unwrap();
        let pk = PublicKey::new(sk.public_key_bytes());
        assert_eq!(pk.expanded(), sk.expanded_public_key().expanded());
        assert_eq!(pk.digest(), sk.expanded_public_key().digest());
        for t in 0..8u8 {
            let target = [t; M];
            let w = sk.derive_preimage(&target).unwrap();
            assert_eq!(pk.eval(&w), target);
        }
    }

    #[test]
    fn uov_for_each_monomial_matches_eval() {
        let sk = SecretKey::new(&[7; 32]).unwrap();
        let pk = sk.expanded_public_key();
        let x = kat_x();
        let mut y = [0u8; M];
        let mut count = 0;
        for_each_monomial(pk.expanded(), |i, j, c| {
            let xij = gf_mul(x[i], x[j]);
            for k in 0..M {
                y[k] ^= gf_mul(c[k], xij);
            }
            count += 1;
        });
        assert_eq!(count, N * (N + 1) / 2);
        assert_eq!(y, pk.eval(&x));
    }

    #[test]
    fn uov_gf_inv() {
        assert_eq!(gf_inv::<Native>(0), 0);
        for a in 1..=255u8 {
            assert_eq!(gf_mul(a, gf_inv::<Native>(a)), 1);
            assert_eq!(gf_inv::<soft::Soft>(a), gf_inv::<Native>(a));
        }
    }

    #[test]
    fn uov_solve_singular() {
        let l = [0u8; O * M];
        assert!(solve::<Native>(&l, &[1; M]).is_none());
    }

    /// Timings: `cargo test --release uov_bench -- --ignored --nocapture`
    #[test]
    #[ignore]
    fn uov_bench() {
        use std::hint::black_box;
        use std::time::Instant;
        let iters = 200;
        let mut seed = [0u8; 32];
        let t0 = Instant::now();
        let mut sk = None;
        for i in 0..iters {
            seed[0] = i as u8;
            sk = Some(black_box(SecretKey::new(black_box(&seed)).unwrap()));
        }
        let keygen_t = t0.elapsed() / iters;
        let sk = sk.unwrap();
        let t0 = Instant::now();
        for _ in 0..iters {
            black_box(PublicKey::new(black_box(sk.public_key_bytes())));
        }
        let expand_t = t0.elapsed() / iters;
        let seed16: [u8; 16] = sk.public_key_bytes()[..16].try_into().unwrap();
        let mut buf = vec![0u8; P1_BYTES + P2_BYTES];
        let t0 = Instant::now();
        for _ in 0..iters {
            expand_p1p2(black_box(&seed16), black_box(&mut buf));
        }
        let aes_t = t0.elapsed() / iters;
        let t0 = Instant::now();
        let mut h = [0u8; 32];
        for _ in 0..iters {
            shake256(&[black_box(&sk.public_key_bytes()[..])], &mut h);
        }
        let shake_t = t0.elapsed() / iters;
        let iters2 = 5000;
        let mut target = [0u8; M];
        let mut w = [0u8; N];
        let t0 = Instant::now();
        for i in 0..iters2 {
            target[0] = i as u8;
            target[1] = (i >> 8) as u8;
            w = black_box(sk.derive_preimage(black_box(&target)).unwrap());
        }
        let derive_t = t0.elapsed() / iters2;
        let pk = sk.expanded_public_key();
        let t0 = Instant::now();
        for i in 0..iters2 {
            w[0] = i as u8;
            black_box(pk.eval(black_box(&w)));
        }
        let eval_t = t0.elapsed() / iters2;
        println!("keygen (incl. digest)    {keygen_t:?}");
        println!("expand_pk (incl. digest) {expand_t:?}");
        println!("  aes p1p2               {aes_t:?}");
        println!("  shake256(cpk)          {shake_t:?}");
        println!("derive_preimage          {derive_t:?}");
        println!("eval                     {eval_t:?}");
    }
}
