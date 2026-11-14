//! GF(2^128) = GF(2)[x] / (x^128 + x^7 + x^2 + x + 1), plus the polynomial hashes built on it.

use crate::block::Block;

const MODULUS: Block = Block::from_u128_const(0x87);

/// An unreduced product: lo + mid·x^64 + hi·x^128.
#[derive(Clone, Copy, Default)]
pub struct Wide {
    lo: Block,
    mid: Block,
    hi: Block,
}

impl Wide {
    #[inline(always)]
    pub fn zero() -> Wide {
        Wide { lo: Block::ZERO, mid: Block::ZERO, hi: Block::ZERO }
    }

    #[inline(always)]
    pub fn from(a: Block) -> Wide {
        Wide { lo: a, mid: Block::ZERO, hi: Block::ZERO }
    }

    #[inline(always)]
    pub fn mul(a: Block, b: Block) -> Wide {
        Wide {
            lo: Block::clmul_ll(a, b),
            mid: Block::clmul_lh(a, b) ^ Block::clmul_hl(a, b),
            hi: Block::clmul_hh(a, b),
        }
    }

    #[inline(always)]
    pub fn add_mul(&mut self, a: Block, b: Block) {
        self.lo ^= Block::clmul_ll(a, b);
        self.mid ^= Block::clmul_lh(a, b) ^ Block::clmul_hl(a, b);
        self.hi ^= Block::clmul_hh(a, b);
    }

    /// Add a · b where b has only its low 64 bits set.
    #[inline(always)]
    pub fn add_mul64(&mut self, a: Block, b: Block) {
        self.lo ^= Block::clmul_ll(a, b);
        self.mid ^= Block::clmul_hl(a, b);
    }

    #[inline(always)]
    pub fn add(&mut self, a: Block) {
        self.lo ^= a;
    }

    #[inline(always)]
    pub fn add_wide(&mut self, o: &Wide) {
        self.lo ^= o.lo;
        self.mid ^= o.mid;
        self.hi ^= o.hi;
    }

    #[inline(always)]
    pub fn reduce(self) -> Block {
        let lo = self.lo ^ self.mid.shl64();
        let hi = self.hi ^ self.mid.shr64();
        let x = Block::clmul_hl(hi, MODULUS);
        let lo = lo ^ x.shl64();
        lo ^ Block::clmul_ll(hi ^ x.shr64(), MODULUS)
    }
}

#[inline(always)]
pub fn mul(a: Block, b: Block) -> Block {
    Wide::mul(a, b).reduce()
}

#[inline(always)]
pub fn square(a: Block) -> Block {
    Wide { lo: Block::clmul_ll(a, a), mid: Block::ZERO, hi: Block::clmul_hh(a, a) }.reduce()
}

pub fn pow(a: Block, mut e: u64) -> Block {
    let mut base = a;
    let mut out = Block::from_u64(1, 0);
    while e != 0 {
        if e & 1 == 1 {
            out = mul(out, base);
        }
        base = square(base);
        e >>= 1;
    }
    out
}

const GF8_IN_GF128: [u128; 7] = [
    u128::from_le_bytes([
        0x0d, 0xce, 0x60, 0x55, 0xac, 0xe8, 0x3f, 0xa1, 0x1c, 0x9a, 0x97, 0xa9, 0x55, 0x85, 0x3d,
        0x05,
    ]),
    u128::from_le_bytes([
        0xe1, 0xae, 0x88, 0x34, 0xca, 0x59, 0x77, 0xec, 0x84, 0xbb, 0xbf, 0x9c, 0x43, 0xb7, 0xf4,
        0x4c,
    ]),
    u128::from_le_bytes([
        0xa8, 0x46, 0x39, 0x36, 0xae, 0x02, 0xcf, 0xbf, 0xc6, 0xd2, 0x51, 0x7d, 0x4f, 0x60, 0xad,
        0x35,
    ]),
    u128::from_le_bytes([
        0x49, 0x98, 0x2e, 0x3c, 0x48, 0x30, 0x83, 0x6b, 0xfe, 0x22, 0xa2, 0x40, 0x46, 0x36, 0xcb,
        0x0d,
    ]),
    u128::from_le_bytes([
        0xb4, 0x82, 0x1b, 0x7b, 0x27, 0x49, 0x2b, 0x25, 0xa5, 0xde, 0x88, 0x1a, 0xe1, 0x10, 0x98,
        0x54,
    ]),
    u128::from_le_bytes([
        0x22, 0xff, 0x21, 0x25, 0xef, 0xf2, 0x2b, 0xc7, 0x75, 0x1f, 0x0c, 0x6c, 0x68, 0xa5, 0x81,
        0xd6,
    ]),
    u128::from_le_bytes([
        0xbc, 0xf9, 0x36, 0xe1, 0x94, 0x8e, 0x7a, 0x7a, 0xe0, 0x8f, 0xb7, 0x4f, 0x1a, 0x31, 0x50,
        0x09,
    ]),
];

/// The basis of the embedding of GF(256) (as the AES field) into GF(2^128): x^j ↦ EMBED_BASIS[j].
pub const EMBED_BASIS: [Block; 8] = {
    let mut out = [Block::ZERO; 8];
    out[0] = Block::from_u128_const(1);
    let mut j = 1;
    while j < 8 {
        out[j] = Block::from_u128_const(GF8_IN_GF128[j - 1]);
        j += 1;
    }
    out
};

static EMBED8: [Block; 256] = {
    let mut t = [0u128; 256];
    let mut b: usize = 1;
    while b < 256 {
        let j = b.trailing_zeros() as usize;
        let basis = if j == 0 { 1 } else { GF8_IN_GF128[j - 1] };
        t[b] = t[b & (b - 1)] ^ basis;
        b += 1;
    }
    let mut out = [Block::ZERO; 256];
    let mut i = 0;
    while i < 256 {
        out[i] = Block::from_u128_const(t[i]);
        i += 1;
    }
    out
};

/// Embed a GF(256) element into GF(2^128).
#[inline(always)]
pub fn embed8(b: u8) -> Block {
    EMBED8[b as usize]
}

/// Powers k^1..k^8 of a hash key.
#[derive(Clone)]
pub struct HashKey {
    pows: [Block; 8],
}

impl HashKey {
    pub fn new(k: Block) -> HashKey {
        let mut pows = [k; 8];
        for i in 1..8 {
            pows[i] = mul(pows[i - 1], k);
        }
        HashKey { pows }
    }

    #[inline(always)]
    pub fn pow(&self, i: usize) -> Block {
        self.pows[i - 1]
    }
}

/// Polynomial hash Σ x_i·k^(n-1-i), computed in blocks of 8 so the length needn't be known.
#[derive(Clone)]
pub struct Hasher {
    state: Block,
    buf: [Block; 8],
    n: usize,
}

impl Default for Hasher {
    fn default() -> Self {
        Self::new()
    }
}

impl Hasher {
    pub fn new() -> Hasher {
        Hasher { state: Block::ZERO, buf: [Block::ZERO; 8], n: 0 }
    }

    #[inline(always)]
    pub fn update(&mut self, key: &HashKey, x: Block) {
        self.buf[self.n] = x;
        self.n += 1;
        if self.n == 8 {
            let mut acc = Wide::mul(self.state, key.pows[7]);
            for j in 0..7 {
                acc.add_mul(self.buf[j], key.pows[6 - j]);
            }
            acc.add(self.buf[7]);
            self.state = acc.reduce();
            self.n = 0;
        }
    }

    pub fn finalize(&self, key: &HashKey) -> Block {
        let r = self.n;
        if r == 0 {
            return self.state;
        }
        let mut acc = Wide::mul(self.state, key.pows[r - 1]);
        for j in 0..r - 1 {
            acc.add_mul(self.buf[j], key.pows[r - 2 - j]);
        }
        acc.add(self.buf[r - 1]);
        acc.reduce()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn mul_ref(a: u128, b: u128) -> u128 {
        let mut out = 0u128;
        let mut a = a;
        for i in 0..128 {
            if (b >> i) & 1 == 1 {
                out ^= a;
            }
            let carry = a >> 127;
            a <<= 1;
            if carry == 1 {
                a ^= 0x87;
            }
        }
        out
    }

    #[test]
    fn mul_matches_reference() {
        let mut x = 0x0123456789abcdef_fedcba9876543210u128;
        let mut y = 0xdeadbeefcafebabe_1122334455667788u128;
        for _ in 0..100 {
            assert_eq!(mul(Block::from_u128(x), Block::from_u128(y)).to_u128(), mul_ref(x, y));
            x = mul_ref(x, 0x1234567) ^ 0x55;
            y = y.rotate_left(13) ^ x;
        }
        let m = u128::MAX;
        assert_eq!(mul(Block::from_u128(m), Block::from_u128(m)).to_u128(), mul_ref(m, m));
    }

    #[test]
    fn embed_is_homomorphic() {
        // The embedding must be a field homomorphism from GF(256) with the AES polynomial.
        fn gf256_mul(mut a: u8, mut b: u8) -> u8 {
            let mut r = 0u8;
            while b != 0 {
                if b & 1 == 1 {
                    r ^= a;
                }
                a = (a << 1) ^ if a & 0x80 != 0 { 0x1b } else { 0 };
                b >>= 1;
            }
            r
        }
        for a in 0..=255u8 {
            for b in [1u8, 2, 3, 0x53, 0xca, 0xff] {
                assert_eq!(mul(embed8(a), embed8(b)), embed8(gf256_mul(a, b)));
            }
        }
    }

    #[test]
    fn hasher_is_horner() {
        let k = Block::from_u128(0x1111_2222_3333_4444_5555_6666_7777_8888);
        let key = HashKey::new(k);
        for n in 0..30 {
            let mut h = Hasher::new();
            let mut r = Block::ZERO;
            for i in 0..n {
                let x = Block::from_u128((i as u128 + 1) * 0x9e3779b97f4a7c15);
                h.update(&key, x);
                r = mul(r, k) ^ x;
            }
            assert_eq!(h.finalize(&key), r);
        }
    }
}
