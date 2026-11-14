//! 128-bit blocks with carry-less multiplication.
//!
//! The backend is chosen at compile time: NEON + PMULL on aarch64 (`aes` target feature), SSE2 +
//! PCLMULQDQ on x86-64, and a portable fallback otherwise. Bit i of a block (little-endian bytes,
//! least significant bit first) is the coefficient of x^i when a block is viewed as a polynomial.

use core::ops::{BitAnd, BitAndAssign, BitXor, BitXorAssign};

#[cfg(all(target_arch = "aarch64", target_feature = "neon", target_feature = "aes"))]
pub(crate) mod imp {
    use core::arch::aarch64::*;

    pub type Inner = uint8x16_t;

    #[inline(always)]
    pub fn zero() -> Inner {
        unsafe { vdupq_n_u8(0) }
    }
    #[inline(always)]
    pub fn from_u64(lo: u64, hi: u64) -> Inner {
        unsafe { vreinterpretq_u8_u64(vcombine_u64(vcreate_u64(lo), vcreate_u64(hi))) }
    }
    #[inline(always)]
    pub fn lo(x: Inner) -> u64 {
        unsafe { vgetq_lane_u64::<0>(vreinterpretq_u64_u8(x)) }
    }
    #[inline(always)]
    pub fn hi(x: Inner) -> u64 {
        unsafe { vgetq_lane_u64::<1>(vreinterpretq_u64_u8(x)) }
    }
    #[inline(always)]
    pub fn load(p: &[u8; 16]) -> Inner {
        unsafe { vld1q_u8(p.as_ptr()) }
    }
    #[inline(always)]
    pub fn store(x: Inner, p: &mut [u8; 16]) {
        unsafe { vst1q_u8(p.as_mut_ptr(), x) }
    }
    #[inline(always)]
    pub fn xor(a: Inner, b: Inner) -> Inner {
        unsafe { veorq_u8(a, b) }
    }
    #[inline(always)]
    pub fn and(a: Inner, b: Inner) -> Inner {
        unsafe { vandq_u8(a, b) }
    }
    #[inline(always)]
    pub fn splat_u64(x: u64) -> Inner {
        unsafe { vreinterpretq_u8_u64(vdupq_n_u64(x)) }
    }
    #[inline(always)]
    pub fn add32(a: Inner, b: Inner) -> Inner {
        unsafe {
            vreinterpretq_u8_u32(vaddq_u32(vreinterpretq_u32_u8(a), vreinterpretq_u32_u8(b)))
        }
    }
    #[inline(always)]
    pub fn clmul_ll(a: Inner, b: Inner) -> Inner {
        unsafe {
            let a = vreinterpretq_u64_u8(a);
            let b = vreinterpretq_u64_u8(b);
            vreinterpretq_u8_p128(vmull_p64(vgetq_lane_u64::<0>(a), vgetq_lane_u64::<0>(b)))
        }
    }
    #[inline(always)]
    pub fn clmul_hh(a: Inner, b: Inner) -> Inner {
        unsafe {
            vreinterpretq_u8_p128(vmull_high_p64(
                vreinterpretq_p64_u8(a),
                vreinterpretq_p64_u8(b),
            ))
        }
    }
    #[inline(always)]
    pub fn clmul_lh(a: Inner, b: Inner) -> Inner {
        unsafe {
            let a = vreinterpretq_u64_u8(a);
            let b = vreinterpretq_u64_u8(b);
            vreinterpretq_u8_p128(vmull_p64(vgetq_lane_u64::<0>(a), vgetq_lane_u64::<1>(b)))
        }
    }
    #[inline(always)]
    pub fn clmul_hl(a: Inner, b: Inner) -> Inner {
        clmul_lh(b, a)
    }
    /// (0, x.lo)
    #[inline(always)]
    pub fn shl64(x: Inner) -> Inner {
        unsafe { vextq_u8::<8>(vdupq_n_u8(0), x) }
    }
    /// (x.hi, 0)
    #[inline(always)]
    pub fn shr64(x: Inner) -> Inner {
        unsafe { vextq_u8::<8>(x, vdupq_n_u8(0)) }
    }
}

#[cfg(all(
    target_arch = "x86_64",
    target_feature = "sse2",
    target_feature = "pclmulqdq"
))]
pub(crate) mod imp {
    use core::arch::x86_64::*;

    pub type Inner = __m128i;

    #[inline(always)]
    pub fn zero() -> Inner {
        unsafe { _mm_setzero_si128() }
    }
    #[inline(always)]
    pub fn from_u64(lo: u64, hi: u64) -> Inner {
        unsafe { _mm_set_epi64x(hi as i64, lo as i64) }
    }
    #[inline(always)]
    pub fn lo(x: Inner) -> u64 {
        unsafe { _mm_cvtsi128_si64(x) as u64 }
    }
    #[inline(always)]
    pub fn hi(x: Inner) -> u64 {
        unsafe { _mm_cvtsi128_si64(_mm_unpackhi_epi64(x, x)) as u64 }
    }
    #[inline(always)]
    pub fn load(p: &[u8; 16]) -> Inner {
        unsafe { _mm_loadu_si128(p.as_ptr().cast()) }
    }
    #[inline(always)]
    pub fn store(x: Inner, p: &mut [u8; 16]) {
        unsafe { _mm_storeu_si128(p.as_mut_ptr().cast(), x) }
    }
    #[inline(always)]
    pub fn xor(a: Inner, b: Inner) -> Inner {
        unsafe { _mm_xor_si128(a, b) }
    }
    #[inline(always)]
    pub fn and(a: Inner, b: Inner) -> Inner {
        unsafe { _mm_and_si128(a, b) }
    }
    #[inline(always)]
    pub fn splat_u64(x: u64) -> Inner {
        unsafe { _mm_set1_epi64x(x as i64) }
    }
    #[inline(always)]
    pub fn add32(a: Inner, b: Inner) -> Inner {
        unsafe { _mm_add_epi32(a, b) }
    }
    #[inline(always)]
    pub fn clmul_ll(a: Inner, b: Inner) -> Inner {
        unsafe { _mm_clmulepi64_si128::<0x00>(a, b) }
    }
    #[inline(always)]
    pub fn clmul_hh(a: Inner, b: Inner) -> Inner {
        unsafe { _mm_clmulepi64_si128::<0x11>(a, b) }
    }
    #[inline(always)]
    pub fn clmul_lh(a: Inner, b: Inner) -> Inner {
        unsafe { _mm_clmulepi64_si128::<0x10>(a, b) }
    }
    #[inline(always)]
    pub fn clmul_hl(a: Inner, b: Inner) -> Inner {
        unsafe { _mm_clmulepi64_si128::<0x01>(a, b) }
    }
    #[inline(always)]
    pub fn shl64(x: Inner) -> Inner {
        unsafe { _mm_slli_si128::<8>(x) }
    }
    #[inline(always)]
    pub fn shr64(x: Inner) -> Inner {
        unsafe { _mm_srli_si128::<8>(x) }
    }
}

#[cfg(not(any(
    all(target_arch = "aarch64", target_feature = "neon", target_feature = "aes"),
    all(target_arch = "x86_64", target_feature = "sse2", target_feature = "pclmulqdq")
)))]
pub(crate) mod imp {
    pub type Inner = [u64; 2];

    #[inline(always)]
    pub fn zero() -> Inner {
        [0, 0]
    }
    #[inline(always)]
    pub fn from_u64(lo: u64, hi: u64) -> Inner {
        [lo, hi]
    }
    #[inline(always)]
    pub fn lo(x: Inner) -> u64 {
        x[0]
    }
    #[inline(always)]
    pub fn hi(x: Inner) -> u64 {
        x[1]
    }
    #[inline(always)]
    pub fn load(p: &[u8; 16]) -> Inner {
        [
            u64::from_le_bytes(p[..8].try_into().unwrap()),
            u64::from_le_bytes(p[8..].try_into().unwrap()),
        ]
    }
    #[inline(always)]
    pub fn store(x: Inner, p: &mut [u8; 16]) {
        p[..8].copy_from_slice(&x[0].to_le_bytes());
        p[8..].copy_from_slice(&x[1].to_le_bytes());
    }
    #[inline(always)]
    pub fn xor(a: Inner, b: Inner) -> Inner {
        [a[0] ^ b[0], a[1] ^ b[1]]
    }
    #[inline(always)]
    pub fn and(a: Inner, b: Inner) -> Inner {
        [a[0] & b[0], a[1] & b[1]]
    }
    #[inline(always)]
    pub fn splat_u64(x: u64) -> Inner {
        [x, x]
    }
    #[inline(always)]
    pub fn add32(a: Inner, b: Inner) -> Inner {
        let f = |x: u64, y: u64| {
            let lo = (x as u32).wrapping_add(y as u32) as u64;
            let hi = ((x >> 32) as u32).wrapping_add((y >> 32) as u32) as u64;
            lo | (hi << 32)
        };
        [f(a[0], b[0]), f(a[1], b[1])]
    }
    /// The low 64 bits of the carry-less product of x and y, with integer multiplications of
    /// x and y with holes (BearSSL's `bmul64`): each multiplication keeps every fourth bit, so
    /// that the carries of the at most 16 terms of a bit of the low half land in the holes.
    /// Constant time where integer multiplication is.
    #[inline(always)]
    fn bmul64(x: u64, y: u64) -> u64 {
        const M0: u64 = 0x1111_1111_1111_1111;
        const M1: u64 = M0 << 1;
        const M2: u64 = M0 << 2;
        const M3: u64 = M0 << 3;
        let (x0, x1, x2, x3) = (x & M0, x & M1, x & M2, x & M3);
        let (y0, y1, y2, y3) = (y & M0, y & M1, y & M2, y & M3);
        let m = u64::wrapping_mul;
        let z0 = m(x0, y0) ^ m(x1, y3) ^ m(x2, y2) ^ m(x3, y1);
        let z1 = m(x0, y1) ^ m(x1, y0) ^ m(x2, y3) ^ m(x3, y2);
        let z2 = m(x0, y2) ^ m(x1, y1) ^ m(x2, y0) ^ m(x3, y3);
        let z3 = m(x0, y3) ^ m(x1, y2) ^ m(x2, y1) ^ m(x3, y0);
        (z0 & M0) | (z1 & M1) | (z2 & M2) | (z3 & M3)
    }
    /// Constant-time 64x64 -> 128 carry-less multiplication. The high half is the low half of
    /// the product of the bit-reversed operands, reversed.
    #[inline(always)]
    fn clmul64(a: u64, b: u64) -> Inner {
        let lo = bmul64(a, b);
        let hi = bmul64(a.reverse_bits(), b.reverse_bits()).reverse_bits() >> 1;
        [lo, hi]
    }
    #[inline(always)]
    pub fn clmul_ll(a: Inner, b: Inner) -> Inner {
        clmul64(a[0], b[0])
    }
    #[inline(always)]
    pub fn clmul_hh(a: Inner, b: Inner) -> Inner {
        clmul64(a[1], b[1])
    }
    #[inline(always)]
    pub fn clmul_lh(a: Inner, b: Inner) -> Inner {
        clmul64(a[0], b[1])
    }
    #[inline(always)]
    pub fn clmul_hl(a: Inner, b: Inner) -> Inner {
        clmul64(a[1], b[0])
    }
    #[inline(always)]
    pub fn shl64(x: Inner) -> Inner {
        [0, x[0]]
    }
    #[inline(always)]
    pub fn shr64(x: Inner) -> Inner {
        [x[1], 0]
    }
}

/// A 128-bit block.
#[derive(Clone, Copy)]
#[repr(transparent)]
pub struct Block(imp::Inner);

impl Default for Block {
    #[inline(always)]
    fn default() -> Self {
        Self::ZERO
    }
}

impl Block {
    #[allow(dead_code)]
    #[inline(always)]
    pub(crate) fn inner(self) -> imp::Inner {
        self.0
    }
    #[allow(dead_code)]
    #[inline(always)]
    pub(crate) fn from_inner(x: imp::Inner) -> Block {
        Block(x)
    }

    pub const ZERO: Block = Block::from_u128_const(0);
    pub const ONES: Block = Block::from_u128_const(u128::MAX);

    /// Construct a block from a `u128` in a const context.
    pub const fn from_u128_const(x: u128) -> Block {
        // SAFETY: every backend's inner type is 16 bytes of plain data with the same layout as
        // the little-endian byte representation of the block.
        unsafe { core::mem::transmute::<[u8; 16], Block>(x.to_le_bytes()) }
    }

    #[inline(always)]
    pub fn zero() -> Block {
        Block(imp::zero())
    }
    #[inline(always)]
    pub fn from_u64(lo: u64, hi: u64) -> Block {
        Block(imp::from_u64(lo, hi))
    }
    #[inline(always)]
    pub fn from_u128(x: u128) -> Block {
        Block::from_u64(x as u64, (x >> 64) as u64)
    }
    #[inline(always)]
    pub fn to_u128(self) -> u128 {
        (self.lo() as u128) | ((self.hi() as u128) << 64)
    }
    #[inline(always)]
    pub fn from_u32s(x: [u32; 4]) -> Block {
        Block::from_u64(
            x[0] as u64 | ((x[1] as u64) << 32),
            x[2] as u64 | ((x[3] as u64) << 32),
        )
    }
    #[inline(always)]
    pub fn lo(self) -> u64 {
        imp::lo(self.0)
    }
    #[inline(always)]
    pub fn hi(self) -> u64 {
        imp::hi(self.0)
    }
    #[inline(always)]
    pub fn from_bytes(b: &[u8; 16]) -> Block {
        Block(imp::load(b))
    }
    /// Load from the first 16 bytes of a slice.
    #[inline(always)]
    pub fn load(b: &[u8]) -> Block {
        Block::from_bytes(b[..16].try_into().unwrap())
    }
    #[inline(always)]
    pub fn to_bytes(self) -> [u8; 16] {
        let mut out = [0u8; 16];
        imp::store(self.0, &mut out);
        out
    }
    /// Store to the first 16 bytes of a slice.
    #[inline(always)]
    pub fn store(self, out: &mut [u8]) {
        imp::store(self.0, (&mut out[..16]).try_into().unwrap());
    }
    /// All ones if `bit` is 1, zero if it's 0. `bit` must be 0 or 1.
    #[inline(always)]
    pub fn mask(bit: u64) -> Block {
        Block(imp::splat_u64(0u64.wrapping_sub(bit)))
    }
    /// Lane-wise addition of 32-bit integers.
    #[inline(always)]
    pub fn add32(self, other: Block) -> Block {
        Block(imp::add32(self.0, other.0))
    }
    #[inline(always)]
    pub fn clmul_ll(a: Block, b: Block) -> Block {
        Block(imp::clmul_ll(a.0, b.0))
    }
    #[inline(always)]
    pub fn clmul_hh(a: Block, b: Block) -> Block {
        Block(imp::clmul_hh(a.0, b.0))
    }
    /// a.lo * b.hi
    #[inline(always)]
    pub fn clmul_lh(a: Block, b: Block) -> Block {
        Block(imp::clmul_lh(a.0, b.0))
    }
    /// a.hi * b.lo
    #[inline(always)]
    pub fn clmul_hl(a: Block, b: Block) -> Block {
        Block(imp::clmul_hl(a.0, b.0))
    }
    /// Shift left by 64 bits: (0, self.lo).
    #[inline(always)]
    pub fn shl64(self) -> Block {
        Block(imp::shl64(self.0))
    }
    /// Shift right by 64 bits: (self.hi, 0).
    #[inline(always)]
    pub fn shr64(self) -> Block {
        Block(imp::shr64(self.0))
    }
    #[inline(always)]
    pub fn is_zero(self) -> bool {
        (self.lo() | self.hi()) == 0
    }
    #[inline(always)]
    pub fn bit(self, i: usize) -> u64 {
        if i < 64 {
            (self.lo() >> i) & 1
        } else {
            (self.hi() >> (i - 64)) & 1
        }
    }
}

impl PartialEq for Block {
    fn eq(&self, other: &Self) -> bool {
        self.to_u128() == other.to_u128()
    }
}
impl Eq for Block {}

impl core::fmt::Debug for Block {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        write!(f, "Block({:032x})", self.to_u128())
    }
}

impl BitXor for Block {
    type Output = Block;
    #[inline(always)]
    fn bitxor(self, rhs: Block) -> Block {
        Block(imp::xor(self.0, rhs.0))
    }
}
impl BitXorAssign for Block {
    #[inline(always)]
    fn bitxor_assign(&mut self, rhs: Block) {
        self.0 = imp::xor(self.0, rhs.0);
    }
}
impl BitAnd for Block {
    type Output = Block;
    #[inline(always)]
    fn bitand(self, rhs: Block) -> Block {
        Block(imp::and(self.0, rhs.0))
    }
}
impl BitAndAssign for Block {
    #[inline(always)]
    fn bitand_assign(&mut self, rhs: Block) {
        self.0 = imp::and(self.0, rhs.0);
    }
}

/// View blocks as their little-endian bytes.
#[inline(always)]
pub fn as_bytes(b: &[Block]) -> &[u8] {
    // SAFETY: Block is 16 bytes of plain data, and u8 has alignment 1.
    unsafe { core::slice::from_raw_parts(b.as_ptr().cast(), b.len() * 16) }
}

#[inline(always)]
pub fn as_bytes_mut(b: &mut [Block]) -> &mut [u8] {
    // SAFETY: Block is 16 bytes of plain data with no invalid bit patterns, and u8 has alignment 1.
    unsafe { core::slice::from_raw_parts_mut(b.as_mut_ptr().cast(), b.len() * 16) }
}

/// A zeroed vector of blocks.
pub fn zeroed(n: usize) -> Vec<Block> {
    vec![Block::ZERO; n]
}

#[cfg(test)]
mod tests {
    use super::*;

    fn clmul_ref(a: u64, b: u64) -> u128 {
        let mut out = 0u128;
        for i in 0..64 {
            if (b >> i) & 1 == 1 {
                out ^= (a as u128) << i;
            }
        }
        out
    }

    #[test]
    fn clmul() {
        let a = Block::from_u64(0x0123456789abcdef, 0xfedcba9876543210);
        let b = Block::from_u64(0xdeadbeefcafebabe, 0x1122334455667788);
        assert_eq!(Block::clmul_ll(a, b).to_u128(), clmul_ref(a.lo(), b.lo()));
        assert_eq!(Block::clmul_hh(a, b).to_u128(), clmul_ref(a.hi(), b.hi()));
        assert_eq!(Block::clmul_lh(a, b).to_u128(), clmul_ref(a.lo(), b.hi()));
        assert_eq!(Block::clmul_hl(a, b).to_u128(), clmul_ref(a.hi(), b.lo()));
        assert_eq!(a.shl64().to_u128(), (a.lo() as u128) << 64);
        assert_eq!(a.shr64().to_u128(), a.hi() as u128);
        assert_eq!(Block::from_u128_const(5), Block::from_u64(5, 0));
        let bytes: [u8; 16] = core::array::from_fn(|i| i as u8);
        assert_eq!(Block::from_bytes(&bytes).to_u128(), u128::from_le_bytes(bytes));
    }
}
