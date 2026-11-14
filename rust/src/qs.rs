//! QuickSilver over GF(2^128), generic over prover and verifier so that each relation's constraints
//! are written once.
//!
//! A committed value of degree d is a polynomial p(X) of degree d whose top coefficient is the
//! value. The prover holds the coefficients; the verifier holds p(Delta). Committed bits are kept
//! separately: the prover holds the d lower coefficients and the bit, which makes products of bits
//! cheaper. Output degrees are explicit const parameters, and must equal the sum of the input
//! degrees (or exceed the input degree, for lifts).

use crate::block::Block;
use crate::gf128::{EMBED_BASIS, HashKey, Wide, mul};
use crate::params::QS_DEGREE;

pub trait Qs {
    type Bit<const D: usize>: Copy;
    type Val<const D: usize>: Copy;

    fn witness_bit(&self, i: usize) -> Self::Bit<1>;
    fn bit_const<const D: usize>(&self, b: bool) -> Self::Bit<D>;
    fn bit_add<const D: usize>(&self, a: &Self::Bit<D>, b: &Self::Bit<D>) -> Self::Bit<D>;
    fn bit_add_one<const D: usize>(&self, a: &Self::Bit<D>) -> Self::Bit<D>;
    fn bit_lift<const D: usize, const E: usize>(&self, a: &Self::Bit<D>) -> Self::Bit<E>;
    fn bit_mul<const A: usize, const B: usize, const C: usize>(
        &self,
        a: &Self::Bit<A>,
        b: &Self::Bit<B>,
    ) -> Self::Bit<C>;
    fn bit_to_val<const D: usize>(&self, a: &Self::Bit<D>) -> Self::Val<D>;
    fn bit_val_mul<const A: usize, const B: usize, const C: usize>(
        &self,
        a: &Self::Bit<A>,
        b: &Self::Val<B>,
    ) -> Self::Val<C>;

    fn val_const<const D: usize>(&self, c: Block) -> Self::Val<D>;
    fn val_add<const D: usize>(&self, a: &Self::Val<D>, b: &Self::Val<D>) -> Self::Val<D>;
    fn val_lift<const D: usize, const E: usize>(&self, a: &Self::Val<D>) -> Self::Val<E>;
    fn val_mul<const A: usize, const B: usize, const C: usize>(
        &self,
        a: &Self::Val<A>,
        b: &Self::Val<B>,
    ) -> Self::Val<C>;
    /// Multiply by a public constant.
    fn val_scale<const D: usize>(&self, c: Block, a: &Self::Val<D>) -> Self::Val<D>;

    /// Combine 8 bits into an element of the GF(256) subfield, bit j being the coefficient of x^j.
    fn combine8<const D: usize>(&self, bits: &[Self::Bit<D>; 8]) -> Self::Val<D>;

    /// Add the constraint x = 0.
    fn add_constraint<const D: usize>(&mut self, x: &Self::Val<D>);

    /// Load witness bits 8i..8i+8 and combine them.
    fn witness_byte(&self, i: usize) -> Self::Val<1> {
        let bits: [Self::Bit<1>; 8] = core::array::from_fn(|j| self.witness_bit(8 * i + j));
        self.combine8(&bits)
    }

    /// Add the constraint x (x + 1) = 0.
    fn add_bit_constraint(&mut self, x: &Self::Bit<1>) {
        let y = self.bit_add_one(x);
        let p = self.bit_mul::<1, 1, 2>(x, &y);
        let v = self.bit_to_val(&p);
        self.add_constraint(&v);
    }
}

/// Polynomial hashes of up to N coefficient streams under two keys, sharing positions.
struct Hashers<const N: usize> {
    k: HashKey,
    k64: HashKey,
    state: [Block; N],
    state64: [Block; N],
    buf: [[Block; 8]; N],
    used: [u8; N],
    n: usize,
}

impl<const N: usize> Hashers<N> {
    fn new(k: Block, k64: Block) -> Self {
        Hashers {
            k: HashKey::new(k),
            k64: HashKey::new(k64),
            state: [Block::ZERO; N],
            state64: [Block::ZERO; N],
            buf: [[Block::ZERO; 8]; N],
            used: [0; N],
            n: 0,
        }
    }

    #[inline(always)]
    fn set(&mut self, s: usize, x: Block) {
        self.buf[s][self.n] = x;
        self.used[s] |= 1 << self.n;
    }

    #[inline(always)]
    fn next(&mut self) {
        self.n += 1;
        if self.n == 8 {
            self.flush(8);
            self.n = 0;
        }
    }

    #[inline(always)]
    fn flush(&mut self, r: usize) {
        for s in 0..N {
            let mut a = Wide::mul(self.state[s], self.k.pow(r));
            let mut a64 = Wide::mul(self.state64[s], self.k64.pow(r));
            let used = self.used[s];
            for j in 0..r {
                if used & (1 << j) != 0 {
                    let x = self.buf[s][j];
                    if j + 1 == r {
                        a.add(x);
                        a64.add(x);
                    } else {
                        a.add_mul(x, self.k.pow(r - 1 - j));
                        a64.add_mul(x, self.k64.pow(r - 1 - j));
                    }
                }
            }
            self.state[s] = a.reduce();
            self.state64[s] = a64.reduce();
            self.used[s] = 0;
        }
    }

    fn finalize(mut self) -> ([Block; N], [Block; N]) {
        if self.n > 0 {
            self.flush(self.n);
        }
        (self.state, self.state64)
    }
}

/// The QuickSilver challenge: hash combination coefficients and the two hash keys.
fn parse_challenge(chal: &[u8]) -> (Block, Block, Block, Block) {
    let hc0 = Block::load(&chal[0..]);
    let hc1 = Block::load(&chal[16..]);
    let k = Block::load(&chal[32..]);
    let k64 = Block::from_u64(u64::from_le_bytes(chal[48..56].try_into().unwrap()), 0);
    (hc0, hc1, k, k64)
}

// ---------------------------------------------------------------------------------------------
// Prover

#[derive(Clone, Copy)]
pub struct PBit<const D: usize> {
    pub mac: [Block; D],
    /// All ones if the bit is set.
    pub v: Block,
}

#[derive(Clone, Copy)]
pub struct PVal<const D: usize> {
    /// Coefficients 0..D.
    pub c: [Block; D],
    /// Coefficient D, the value.
    pub top: Block,
}

pub struct Prover<'a> {
    witness: &'a [u8],
    macs: &'a [Block],
    hc: [Block; 2],
    h: Hashers<QS_DEGREE>,
}

impl<'a> Prover<'a> {
    pub fn new(witness: &'a [u8], macs: &'a [Block], chal: &[u8]) -> Self {
        let (hc0, hc1, k, k64) = parse_challenge(chal);
        Prover { witness, macs, hc: [hc0, hc1], h: Hashers::new(k, k64) }
    }

    /// Returns the check value and writes the proof (QS_DEGREE - 1 blocks).
    pub fn prove(self, u_mask: &[Block], v_mask: &[Block], proof: &mut [u8]) -> [u8; 16] {
        let mut masks = [Block::ZERO; QS_DEGREE];
        for i in 0..QS_DEGREE - 1 {
            masks[i] ^= v_mask[i];
            masks[i + 1] = u_mask[i];
        }
        let hc = self.hc;
        let (h, h64) = self.h.finalize();
        let mut check = [0u8; 16];
        for i in 0..QS_DEGREE {
            let mut acc = Wide::from(masks[i]);
            acc.add_mul(hc[0], h[i]);
            acc.add_mul(hc[1], h64[i]);
            let out = acc.reduce();
            if i == 0 {
                out.store(&mut check);
            } else {
                out.store(&mut proof[16 * (i - 1)..]);
            }
        }
        check
    }
}

/// out[k] = Σ_{i+j=k} a[i] b[j] for k < C.
#[inline(always)]
fn poly_mul_into<const C: usize>(a: &[Block], b: &[Block], acc: &mut [Wide; C]) {
    for (i, &x) in a.iter().enumerate() {
        for (j, &y) in b.iter().enumerate() {
            if i + j < C {
                acc[i + j].add_mul(x, y);
            }
        }
    }
}

const ONE: Block = Block::from_u128_const(1);

impl Qs for Prover<'_> {
    type Bit<const D: usize> = PBit<D>;
    type Val<const D: usize> = PVal<D>;

    #[inline(always)]
    fn witness_bit(&self, i: usize) -> PBit<1> {
        PBit { mac: [self.macs[i]], v: Block::mask(((self.witness[i / 8] >> (i % 8)) & 1) as u64) }
    }

    #[inline(always)]
    fn bit_const<const D: usize>(&self, b: bool) -> PBit<D> {
        PBit { mac: [Block::ZERO; D], v: Block::mask(b as u64) }
    }

    #[inline(always)]
    fn bit_add<const D: usize>(&self, a: &PBit<D>, b: &PBit<D>) -> PBit<D> {
        PBit { mac: core::array::from_fn(|i| a.mac[i] ^ b.mac[i]), v: a.v ^ b.v }
    }

    #[inline(always)]
    fn bit_add_one<const D: usize>(&self, a: &PBit<D>) -> PBit<D> {
        PBit { mac: a.mac, v: a.v ^ Block::ONES }
    }

    #[inline(always)]
    fn bit_lift<const D: usize, const E: usize>(&self, a: &PBit<D>) -> PBit<E> {
        debug_assert!(E >= D);
        let s = E - D;
        PBit { mac: core::array::from_fn(|i| if i >= s { a.mac[i - s] } else { Block::ZERO }), v: a.v }
    }

    #[inline(always)]
    fn bit_mul<const A: usize, const B: usize, const C: usize>(
        &self,
        a: &PBit<A>,
        b: &PBit<B>,
    ) -> PBit<C> {
        debug_assert_eq!(C, A + B);
        let mut acc = [Wide::zero(); C];
        poly_mul_into(&a.mac, &b.mac, &mut acc);
        for i in 0..A {
            acc[i + B].add(a.mac[i] & b.v);
        }
        for j in 0..B {
            acc[j + A].add(b.mac[j] & a.v);
        }
        PBit { mac: acc.map(|w| w.reduce()), v: a.v & b.v }
    }

    #[inline(always)]
    fn bit_to_val<const D: usize>(&self, a: &PBit<D>) -> PVal<D> {
        PVal { c: a.mac, top: a.v & ONE }
    }

    #[inline(always)]
    fn bit_val_mul<const A: usize, const B: usize, const C: usize>(
        &self,
        a: &PBit<A>,
        b: &PVal<B>,
    ) -> PVal<C> {
        debug_assert_eq!(C, A + B);
        let mut acc = [Wide::zero(); C];
        poly_mul_into(&a.mac, &b.c, &mut acc);
        for i in 0..A {
            // a.mac[i] * b.top lands at i + B < C.
            acc[i + B].add_mul(a.mac[i], b.top);
        }
        for j in 0..B {
            acc[j + A].add(b.c[j] & a.v);
        }
        PVal { c: acc.map(|w| w.reduce()), top: b.top & a.v }
    }

    #[inline(always)]
    fn val_const<const D: usize>(&self, c: Block) -> PVal<D> {
        PVal { c: [Block::ZERO; D], top: c }
    }

    #[inline(always)]
    fn val_add<const D: usize>(&self, a: &PVal<D>, b: &PVal<D>) -> PVal<D> {
        PVal { c: core::array::from_fn(|i| a.c[i] ^ b.c[i]), top: a.top ^ b.top }
    }

    #[inline(always)]
    fn val_lift<const D: usize, const E: usize>(&self, a: &PVal<D>) -> PVal<E> {
        debug_assert!(E >= D);
        let s = E - D;
        PVal { c: core::array::from_fn(|i| if i >= s { a.c[i - s] } else { Block::ZERO }), top: a.top }
    }

    #[inline(always)]
    fn val_mul<const A: usize, const B: usize, const C: usize>(
        &self,
        a: &PVal<A>,
        b: &PVal<B>,
    ) -> PVal<C> {
        debug_assert_eq!(C, A + B);
        let mut acc = [Wide::zero(); C];
        poly_mul_into(&a.c, &b.c, &mut acc);
        for i in 0..A {
            acc[i + B].add_mul(a.c[i], b.top);
        }
        for j in 0..B {
            acc[j + A].add_mul(b.c[j], a.top);
        }
        PVal { c: acc.map(|w| w.reduce()), top: mul(a.top, b.top) }
    }

    #[inline(always)]
    fn val_scale<const D: usize>(&self, c: Block, a: &PVal<D>) -> PVal<D> {
        PVal { c: a.c.map(|x| mul(c, x)), top: mul(c, a.top) }
    }

    #[inline(always)]
    fn combine8<const D: usize>(&self, bits: &[PBit<D>; 8]) -> PVal<D> {
        let c = core::array::from_fn(|i| {
            let mut acc = Wide::from(bits[0].mac[i]);
            for j in 1..8 {
                acc.add_mul(bits[j].mac[i], EMBED_BASIS[j]);
            }
            acc.reduce()
        });
        let mut top = bits[0].v & EMBED_BASIS[0];
        for j in 1..8 {
            top ^= bits[j].v & EMBED_BASIS[j];
        }
        PVal { c, top }
    }

    #[inline(always)]
    fn add_constraint<const D: usize>(&mut self, x: &PVal<D>) {
        debug_assert!(D <= QS_DEGREE);
        debug_assert!(x.top.is_zero(), "unsatisfied constraint");
        let s = QS_DEGREE - D;
        for i in 0..D {
            self.h.set(s + i, x.c[i]);
        }
        self.h.next();
    }
}

// ---------------------------------------------------------------------------------------------
// Verifier

pub struct Verifier<'a> {
    keys: &'a [Block],
    /// delta_pow[k] = Delta^k.
    delta_pow: [Block; QS_DEGREE + 1],
    hc: [Block; 2],
    h: Hashers<1>,
}

impl<'a> Verifier<'a> {
    /// `keys` are the corrected, lifted VOLE keys of the witness rows.
    pub fn new(keys: &'a [Block], delta: Block, chal: &[u8]) -> Self {
        let (hc0, hc1, k, k64) = parse_challenge(chal);
        let mut delta_pow = [ONE; QS_DEGREE + 1];
        for i in 1..=QS_DEGREE {
            delta_pow[i] = mul(delta_pow[i - 1], delta);
        }
        Verifier { keys, delta_pow, hc: [hc0, hc1], h: Hashers::new(k, k64) }
    }

    pub fn verify(self, q_mask: &[Block], proof: &[u8]) -> [u8; 16] {
        let dp = self.delta_pow;
        let mut mask = Wide::from(q_mask[0]);
        for i in 1..QS_DEGREE - 1 {
            mask.add_mul(Block::load(&proof[16 * (i - 1)..]) ^ q_mask[i], dp[i]);
        }
        mask.add_mul(Block::load(&proof[16 * (QS_DEGREE - 2)..]), dp[QS_DEGREE - 1]);
        let hc = self.hc;
        let (h, h64) = self.h.finalize();
        mask.add_mul(hc[0], h[0]);
        mask.add_mul(hc[1], h64[0]);
        mask.reduce().to_bytes()
    }
}

impl Qs for Verifier<'_> {
    type Bit<const D: usize> = Block;
    type Val<const D: usize> = Block;

    #[inline(always)]
    fn witness_bit(&self, i: usize) -> Block {
        self.keys[i]
    }

    #[inline(always)]
    fn bit_const<const D: usize>(&self, b: bool) -> Block {
        self.delta_pow[D] & Block::mask(b as u64)
    }

    #[inline(always)]
    fn bit_add<const D: usize>(&self, a: &Block, b: &Block) -> Block {
        *a ^ *b
    }

    #[inline(always)]
    fn bit_add_one<const D: usize>(&self, a: &Block) -> Block {
        *a ^ self.delta_pow[D]
    }

    #[inline(always)]
    fn bit_lift<const D: usize, const E: usize>(&self, a: &Block) -> Block {
        if E == D { *a } else { mul(*a, self.delta_pow[E - D]) }
    }

    #[inline(always)]
    fn bit_mul<const A: usize, const B: usize, const C: usize>(&self, a: &Block, b: &Block) -> Block {
        mul(*a, *b)
    }

    #[inline(always)]
    fn bit_to_val<const D: usize>(&self, a: &Block) -> Block {
        *a
    }

    #[inline(always)]
    fn bit_val_mul<const A: usize, const B: usize, const C: usize>(
        &self,
        a: &Block,
        b: &Block,
    ) -> Block {
        mul(*a, *b)
    }

    #[inline(always)]
    fn val_const<const D: usize>(&self, c: Block) -> Block {
        if D == 0 { c } else { mul(c, self.delta_pow[D]) }
    }

    #[inline(always)]
    fn val_add<const D: usize>(&self, a: &Block, b: &Block) -> Block {
        *a ^ *b
    }

    #[inline(always)]
    fn val_lift<const D: usize, const E: usize>(&self, a: &Block) -> Block {
        if E == D { *a } else { mul(*a, self.delta_pow[E - D]) }
    }

    #[inline(always)]
    fn val_mul<const A: usize, const B: usize, const C: usize>(&self, a: &Block, b: &Block) -> Block {
        mul(*a, *b)
    }

    #[inline(always)]
    fn val_scale<const D: usize>(&self, c: Block, a: &Block) -> Block {
        mul(c, *a)
    }

    #[inline(always)]
    fn combine8<const D: usize>(&self, bits: &[Block; 8]) -> Block {
        let mut acc = Wide::from(bits[0]);
        for j in 1..8 {
            acc.add_mul(bits[j], EMBED_BASIS[j]);
        }
        acc.reduce()
    }

    #[inline(always)]
    fn add_constraint<const D: usize>(&mut self, x: &Block) {
        let y = if D == QS_DEGREE { *x } else { mul(*x, self.delta_pow[QS_DEGREE - D]) };
        self.h.set(0, y);
        self.h.next();
    }
}
