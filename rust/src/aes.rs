//! AES-128 in CTR mode with a fresh key per PRG seed.
//!
//! Hardware AES (aarch64 `aes`, x86-64 AES-NI + SSSE3) runs the key schedule of several keys
//! interleaved with the encryption rounds. WebAssembly has no AES instruction; with `simd128`
//! the same code runs on a constant-time vector-permute round function (one block per vector,
//! so every block can have its own key). Without any of these, the bitsliced `aes` crate is
//! used, several blocks per pass.

use crate::block::Block;

pub const ROUNDS: usize = 10;

/// The PRG input block for counter `ctr` and tweak `tweak`.
#[inline(always)]
pub fn ctr_block(iv: Block, ctr: u32, tweak: u32) -> Block {
    iv.add32(Block::from_u32s([ctr, 0, 0, tweak]))
}

#[cfg(all(target_arch = "aarch64", target_feature = "neon", target_feature = "aes"))]
mod hw {
    use crate::block::Block;
    use core::arch::aarch64::*;

    pub const HW: bool = true;
    /// Whether `round(s, k)` ends in AddRoundKey(k) (AESENC) or starts with it (AESE).
    pub const AESENC: bool = false;

    /// Broadcast RotWord of the last word of the round key into every lane.
    const ROT_DUP: [u8; 16] = [13, 14, 15, 12, 13, 14, 15, 12, 13, 14, 15, 12, 13, 14, 15, 12];

    #[inline(always)]
    pub fn next_round_key(k: Block, rcon: u8) -> Block {
        unsafe {
            let k = k.inner();
            let t = vqtbl1q_u8(k, vld1q_u8(ROT_DUP.as_ptr()));
            // All columns are equal, so ShiftRows does nothing and this is SubWord(RotWord(w3)).
            let t = vaeseq_u8(t, vdupq_n_u8(0));
            let t = veorq_u8(t, vreinterpretq_u8_u32(vdupq_n_u32(rcon as u32)));
            let z = vdupq_n_u8(0);
            let mut k = k;
            k = veorq_u8(k, vextq_u8::<12>(z, k));
            k = veorq_u8(k, vextq_u8::<8>(z, k));
            Block::from_inner(veorq_u8(k, t))
        }
    }

    /// AddRoundKey(k), SubBytes, ShiftRows, MixColumns.
    #[inline(always)]
    pub fn round(s: Block, k: Block) -> Block {
        unsafe { Block::from_inner(vaesmcq_u8(vaeseq_u8(s.inner(), k.inner()))) }
    }

    /// AddRoundKey(k9), SubBytes, ShiftRows, AddRoundKey(k10).
    #[inline(always)]
    pub fn last(s: Block, k9: Block, k10: Block) -> Block {
        unsafe { Block::from_inner(veorq_u8(vaeseq_u8(s.inner(), k9.inner()), k10.inner())) }
    }

    #[inline(always)]
    pub fn first(s: Block, _k0: Block) -> Block {
        s
    }
}

#[cfg(all(
    target_arch = "x86_64",
    target_feature = "sse2",
    target_feature = "ssse3",
    target_feature = "pclmulqdq",
    target_feature = "aes"
))]
mod hw {
    use crate::block::Block;
    use core::arch::x86_64::*;

    pub const HW: bool = true;
    pub const AESENC: bool = true;

    #[inline(always)]
    pub fn next_round_key(k: Block, rcon: u8) -> Block {
        unsafe {
            let k = k.inner();
            let mask = _mm_set_epi8(12, 15, 14, 13, 12, 15, 14, 13, 12, 15, 14, 13, 12, 15, 14, 13);
            let t = _mm_shuffle_epi8(k, mask);
            let t = _mm_aesenclast_si128(t, _mm_set1_epi32(rcon as i32));
            let mut k = k;
            k = _mm_xor_si128(k, _mm_slli_si128::<4>(k));
            k = _mm_xor_si128(k, _mm_slli_si128::<8>(k));
            Block::from_inner(_mm_xor_si128(k, t))
        }
    }

    // The schedule is shifted relative to aarch64: `first` adds k0, `round(s, k)` is a full round
    // ending in AddRoundKey(k_{r+1}), so callers pass k_{r+1} instead of k_r.
    #[inline(always)]
    pub fn first(s: Block, k0: Block) -> Block {
        s ^ k0
    }

    #[inline(always)]
    pub fn round(s: Block, k: Block) -> Block {
        unsafe { Block::from_inner(_mm_aesenc_si128(s.inner(), k.inner())) }
    }

    #[inline(always)]
    pub fn last(s: Block, _k9: Block, k10: Block) -> Block {
        unsafe { Block::from_inner(_mm_aesenclast_si128(s.inner(), k10.inner())) }
    }
}

/// WebAssembly `simd128`: there is no AES instruction, so the S-box is computed with 16-entry
/// table lookups (`i8x16.swizzle`), which are constant time, following Hamburg, "Accelerating
/// AES with Vector Permute Instructions" (CHES 2009).
///
/// GF(2^8) is represented as GF(2^4)[t]/(t^2 + at + a) with a = 2 and GF(2^4) = GF(2)[z]/(z^4 +
/// z + 1). For x = i t + k with norm N = a i^2 + a i k + k^2, the inverse is (i t + (a i + k))/N.
/// With j = i + k, the values
///
///   io = 1/(1/i + a/k) + j = N/(a i + k)
///   jo = 1/(1/j + a/k) + i = N/(a i + (1 + a) k)
///
/// are the inverses of two GF(2^4)-linear functions of the coordinates of 1/x, so SubBytes(x) is
/// `SB_I[io] ^ SB_J[jo] ^ 0x63` for tables that undo that linear map and apply the affine map
/// of the S-box. Infinity (1/0) is 0x80: it survives the additions, and swizzle maps any index
/// above 15 to 0, which is both 1/infinity and the table entry for a zero coordinate. The tables
/// are generated, and checked for all 256 inputs, by tools/gen_aes_tables.py.
#[cfg(all(target_arch = "wasm32", target_feature = "simd128"))]
mod hw {
    use crate::block::Block;
    use core::arch::wasm32::*;

    pub const HW: bool = true;
    pub const AESENC: bool = true;

    const fn table(t: [u8; 16]) -> v128 {
        u8x16(
            t[0], t[1], t[2], t[3], t[4], t[5], t[6], t[7], t[8], t[9], t[10], t[11], t[12], t[13], t[14], t[15],
        )
    }

    /// The isomorphism from the AES field, by nibble: the result is i << 4 | k.
    const IN_LO: v128 = table([
        0x00, 0x01, 0x1c, 0x1d, 0x2d, 0x2c, 0x31, 0x30, 0x27, 0x26, 0x3b, 0x3a, 0x0a, 0x0b, 0x16, 0x17,
    ]);
    const IN_HI: v128 = table([
        0x00, 0x86, 0xfd, 0x7b, 0x8e, 0x08, 0x73, 0xf5, 0x77, 0xf1, 0x8a, 0x0c, 0xf9, 0x7f, 0x04, 0x82,
    ]);
    /// 1/x and a/x in GF(2^4).
    const INV: v128 = table([
        0x80, 0x01, 0x09, 0x0e, 0x0d, 0x0b, 0x07, 0x06, 0x0f, 0x02, 0x0c, 0x05, 0x0a, 0x04, 0x03, 0x08,
    ]);
    const INVA: v128 = table([
        0x80, 0x02, 0x01, 0x0f, 0x09, 0x05, 0x0e, 0x0c, 0x0d, 0x04, 0x0b, 0x0a, 0x07, 0x08, 0x06, 0x03,
    ]);
    /// The S-box output, without the constant 0x63, and twice it.
    const SB_I: v128 = table([
        0x00, 0xcb, 0xd7, 0xb0, 0x21, 0x8d, 0x67, 0xac, 0x7b, 0x5a, 0xea, 0x3d, 0x46, 0xf6, 0x91, 0x1c,
    ]);
    const SB_J: v128 = table([
        0x00, 0x9f, 0x61, 0x16, 0xc2, 0x2a, 0x77, 0xe8, 0x89, 0x4b, 0x5d, 0x3c, 0xb5, 0xa3, 0xd4, 0xfe,
    ]);
    const SB2_I: v128 = table([
        0x00, 0x8d, 0xb5, 0x7b, 0x42, 0x01, 0xce, 0x43, 0xf6, 0xb4, 0xcf, 0x7a, 0x8c, 0xf7, 0x39, 0x38,
    ]);
    const SB2_J: v128 = table([
        0x00, 0x25, 0xc2, 0x2c, 0x9f, 0x54, 0xee, 0xcb, 0x09, 0x96, 0xba, 0x78, 0x71, 0x5d, 0xb3, 0xe7,
    ]);

    /// io and jo for every byte of `x`.
    #[inline(always)]
    fn invert(x: v128) -> (v128, v128) {
        let nib = u8x16_splat(0x0f);
        let y = v128_xor(
            i8x16_swizzle(IN_LO, v128_and(x, nib)),
            i8x16_swizzle(IN_HI, u8x16_shr(x, 4)),
        );
        let k = v128_and(y, nib);
        let i = u8x16_shr(y, 4);
        let j = v128_xor(i, k);
        let ak = i8x16_swizzle(INVA, k);
        let iak = v128_xor(i8x16_swizzle(INV, i), ak);
        let jak = v128_xor(i8x16_swizzle(INV, j), ak);
        (v128_xor(i8x16_swizzle(INV, iak), j), v128_xor(i8x16_swizzle(INV, jak), i))
    }

    #[inline(always)]
    fn shift_rows(s: v128) -> v128 {
        i8x16_shuffle::<0, 5, 10, 15, 4, 9, 14, 3, 8, 13, 2, 7, 12, 1, 6, 11>(s, s)
    }

    #[inline(always)]
    pub fn next_round_key(k: Block, rcon: u8) -> Block {
        let k = k.inner();
        // SubWord(RotWord(w3)) ^ rcon, in every column.
        let t = i8x16_shuffle::<13, 14, 15, 12, 13, 14, 15, 12, 13, 14, 15, 12, 13, 14, 15, 12>(k, k);
        let (io, jo) = invert(t);
        let t = v128_xor(i8x16_swizzle(SB_I, io), i8x16_swizzle(SB_J, jo));
        let t = v128_xor(t, u32x4_splat(0x6363_6363 ^ rcon as u32));
        let z = u64x2(0, 0);
        let k = v128_xor(k, i8x16_shuffle::<16, 16, 16, 16, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11>(k, z));
        let k = v128_xor(k, i8x16_shuffle::<16, 16, 16, 16, 16, 16, 16, 16, 0, 1, 2, 3, 4, 5, 6, 7>(k, z));
        Block::from_inner(v128_xor(k, t))
    }

    #[inline(always)]
    pub fn first(s: Block, k0: Block) -> Block {
        s ^ k0
    }

    /// ShiftRows, SubBytes, MixColumns, AddRoundKey(k), as AESENC.
    #[inline(always)]
    pub fn round(s: Block, k: Block) -> Block {
        let (io, jo) = invert(shift_rows(s.inner()));
        // u is SubBytes without its constant, which MixColumns preserves.
        let u = v128_xor(i8x16_swizzle(SB_I, io), i8x16_swizzle(SB_J, jo));
        let u2 = v128_xor(i8x16_swizzle(SB2_I, io), i8x16_swizzle(SB2_J, jo));
        // Row r of a column of MixColumns is 2 u[r] ^ 3 u[r + 1] ^ u[r + 2] ^ u[r + 3].
        let r1 = i8x16_shuffle::<1, 2, 3, 0, 5, 6, 7, 4, 9, 10, 11, 8, 13, 14, 15, 12>(u, u);
        let r2 = i8x16_shuffle::<2, 3, 0, 1, 6, 7, 4, 5, 10, 11, 8, 9, 14, 15, 12, 13>(u, u);
        let t = v128_xor(v128_xor(u2, u), v128_xor(r1, r2));
        let t = i8x16_shuffle::<1, 2, 3, 0, 5, 6, 7, 4, 9, 10, 11, 8, 13, 14, 15, 12>(t, t);
        let k = v128_xor(k.inner(), u8x16_splat(0x63));
        Block::from_inner(v128_xor(v128_xor(u2, t), k))
    }

    /// ShiftRows, SubBytes, AddRoundKey(k10), as AESENCLAST.
    #[inline(always)]
    pub fn last(s: Block, _k9: Block, k10: Block) -> Block {
        let (io, jo) = invert(shift_rows(s.inner()));
        let u = v128_xor(i8x16_swizzle(SB_I, io), i8x16_swizzle(SB_J, jo));
        Block::from_inner(v128_xor(v128_xor(u, k10.inner()), u8x16_splat(0x63)))
    }
}

#[cfg(not(any(
    all(target_arch = "aarch64", target_feature = "neon", target_feature = "aes"),
    all(
        target_arch = "x86_64",
        target_feature = "sse2",
        target_feature = "ssse3",
        target_feature = "pclmulqdq",
        target_feature = "aes"
    ),
    all(target_arch = "wasm32", target_feature = "simd128")
)))]
mod hw {
    pub const HW: bool = false;
}

const RCON: [u8; 10] = [0x01, 0x02, 0x04, 0x08, 0x10, 0x20, 0x40, 0x80, 0x1b, 0x36];

/// An expanded AES-128 key.
#[derive(Clone)]
pub struct RoundKeys {
    #[cfg(not(any(
        all(target_arch = "aarch64", target_feature = "neon", target_feature = "aes"),
        all(
            target_arch = "x86_64",
            target_feature = "sse2",
            target_feature = "ssse3",
            target_feature = "pclmulqdq",
            target_feature = "aes"
        ),
        all(target_arch = "wasm32", target_feature = "simd128")
    )))]
    soft: ::aes::Aes128Enc,
    #[allow(dead_code)]
    keys: [Block; ROUNDS + 1],
}

#[cfg(any(
    all(target_arch = "aarch64", target_feature = "neon", target_feature = "aes"),
    all(
        target_arch = "x86_64",
        target_feature = "sse2",
        target_feature = "ssse3",
        target_feature = "pclmulqdq",
        target_feature = "aes"
    ),
    all(target_arch = "wasm32", target_feature = "simd128")
))]
mod imp {
    use super::*;

    impl RoundKeys {
        pub fn new(key: Block) -> RoundKeys {
            let mut keys = [key; ROUNDS + 1];
            for r in 0..ROUNDS {
                keys[r + 1] = hw::next_round_key(keys[r], RCON[r]);
            }
            RoundKeys { keys }
        }

        #[inline(always)]
        pub fn encrypt(&self, b: Block) -> Block {
            let k = &self.keys;
            let mut s = hw::first(b, k[0]);
            for r in 0..ROUNDS - 1 {
                s = hw::round(s, k[r + usize::from(hw::AESENC)]);
            }
            hw::last(s, k[ROUNDS - 1], k[ROUNDS])
        }

        /// Encrypt every block of `x` in place.
        #[inline(always)]
        pub fn encrypt_blocks(&self, x: &mut [Block]) {
            let mut chunks = x.chunks_exact_mut(8);
            for chunk in &mut chunks {
                let y: [Block; 8] = core::array::from_fn(|j| self.encrypt(chunk[j]));
                chunk.copy_from_slice(&y);
            }
            for b in chunks.into_remainder() {
                *b = self.encrypt(*b);
            }
        }
    }

    /// Expand `N` keys and call `f(j, x)` for `j = 0, 1, ..., blocks - 1` in order, where `x[i]`
    /// is the CTR output of key `i` for counter `j` and tweak `tweak`.
    #[inline(always)]
    pub fn keygen_ctr_each<const N: usize>(
        keys: &[Block; N],
        iv: Block,
        tweak: u32,
        blocks: usize,
        mut f: impl FnMut(usize, [Block; N]),
    ) {
        if blocks == 0 {
            return;
        }
        let mut rks: [RoundKeys; N] =
            core::array::from_fn(|_| RoundKeys { keys: [Block::ZERO; ROUNDS + 1] });
        let mut out = [[Block::ZERO; 1]; N];
        keygen_ctr(keys, iv, &[tweak; N], 0, Some(&mut rks), &mut out);
        f(0, core::array::from_fn(|i| out[i][0]));
        for j in 1..blocks {
            f(j, encrypt_many(&rks, &[ctr_block(iv, j as u32, tweak); N]));
        }
    }

    /// Encrypt one block under each of `N` keys, interleaving the rounds.
    #[inline(always)]
    pub fn encrypt_many<const N: usize>(rks: &[RoundKeys; N], x: &[Block; N]) -> [Block; N] {
        let off = usize::from(hw::AESENC);
        let mut s: [Block; N] = core::array::from_fn(|i| hw::first(x[i], rks[i].keys[0]));
        for r in 0..ROUNDS - 1 {
            for i in 0..N {
                s[i] = hw::round(s[i], rks[i].keys[r + off]);
            }
        }
        core::array::from_fn(|i| hw::last(s[i], rks[i].keys[ROUNDS - 1], rks[i].keys[ROUNDS]))
    }

    /// Expand `N` keys and encrypt `B` counter blocks under each, with the key schedule
    /// interleaved with encryption. Output `j` of key `i` uses counter `ctr + j` and tweak
    /// `tweaks[i]`.
    #[inline(always)]
    pub fn keygen_ctr<const N: usize, const B: usize>(
        keys: &[Block; N],
        iv: Block,
        tweaks: &[u32; N],
        ctr: u32,
        rks: Option<&mut [RoundKeys; N]>,
        out: &mut [[Block; B]; N],
    ) {
        let mut k = *keys;
        let mut st = [[Block::ZERO; B]; N];
        let mut saved = [[Block::ZERO; ROUNDS + 1]; N];
        for i in 0..N {
            saved[i][0] = k[i];
            for j in 0..B {
                st[i][j] = hw::first(ctr_block(iv, ctr + j as u32, tweaks[i]), k[i]);
            }
        }
        for r in 0..ROUNDS - 1 {
            if hw::AESENC {
                for i in 0..N {
                    k[i] = hw::next_round_key(k[i], RCON[r]);
                    saved[i][r + 1] = k[i];
                }
            }
            for i in 0..N {
                for j in 0..B {
                    st[i][j] = hw::round(st[i][j], k[i]);
                }
            }
            if !hw::AESENC {
                for i in 0..N {
                    k[i] = hw::next_round_key(k[i], RCON[r]);
                    saved[i][r + 1] = k[i];
                }
            }
        }
        // k = k9 here on both architectures.
        let mut k10 = [Block::ZERO; N];
        for i in 0..N {
            k10[i] = hw::next_round_key(k[i], RCON[ROUNDS - 1]);
            saved[i][ROUNDS] = k10[i];
        }
        for i in 0..N {
            for j in 0..B {
                out[i][j] = hw::last(st[i][j], k[i], k10[i]);
            }
        }
        if let Some(rks) = rks {
            for i in 0..N {
                rks[i] = RoundKeys { keys: saved[i] };
            }
        }
    }
}

#[cfg(not(any(
    all(target_arch = "aarch64", target_feature = "neon", target_feature = "aes"),
    all(
        target_arch = "x86_64",
        target_feature = "sse2",
        target_feature = "ssse3",
        target_feature = "pclmulqdq",
        target_feature = "aes"
    ),
    all(target_arch = "wasm32", target_feature = "simd128")
)))]
mod imp {
    use super::*;
    use ::aes::Aes128Enc;
    use ::aes::cipher::{Array, BlockCipherEncrypt, KeyInit};

    impl RoundKeys {
        pub fn new(key: Block) -> RoundKeys {
            RoundKeys {
                soft: Aes128Enc::new(&Array(key.to_bytes())),
                keys: [Block::ZERO; ROUNDS + 1],
            }
        }

        #[inline(always)]
        pub fn encrypt(&self, b: Block) -> Block {
            let mut a = Array(b.to_bytes());
            self.soft.encrypt_block(&mut a);
            Block::from_bytes(&a.0)
        }

        /// Encrypt every block of `x` in place. The bitsliced backend encrypts `PAR` blocks in
        /// about the time of one, but only when it is handed full batches, so the last batch
        /// is padded.
        pub fn encrypt_blocks(&self, x: &mut [Block]) {
            const BUF: usize = 2 * PAR;
            let mut buf = [Array([0u8; 16]); BUF];
            for chunk in x.chunks_mut(BUF) {
                let n = chunk.len().next_multiple_of(PAR);
                for (a, b) in buf.iter_mut().zip(chunk.iter()) {
                    a.0 = b.to_bytes();
                }
                self.soft.encrypt_blocks(&mut buf[..n]);
                for (b, a) in chunk.iter_mut().zip(buf.iter()) {
                    *b = Block::from_bytes(&a.0);
                }
            }
        }
    }

    /// The largest number of blocks the `aes` crate's bitsliced backend encrypts in one pass
    /// (with 64-bit words; it is 2 with 32-bit words, which divides this).
    const PAR: usize = 4;

    /// Expand `N` keys and call `f(j, x)` for `j = 0, 1, ..., blocks - 1` in order, where `x[i]`
    /// is the CTR output of key `i` for counter `j` and tweak `tweak`.
    #[inline(always)]
    pub fn keygen_ctr_each<const N: usize>(
        keys: &[Block; N],
        iv: Block,
        tweak: u32,
        blocks: usize,
        mut f: impl FnMut(usize, [Block; N]),
    ) {
        const W: usize = 2 * PAR;
        let rks: [RoundKeys; N] = core::array::from_fn(|i| RoundKeys::new(keys[i]));
        let mut j = 0;
        while j < blocks {
            let n = W.min(blocks - j);
            let mut y = [[Block::ZERO; W]; N];
            for i in 0..N {
                for d in 0..n {
                    y[i][d] = ctr_block(iv, (j + d) as u32, tweak);
                }
                rks[i].encrypt_blocks(&mut y[i][..n]);
            }
            for d in 0..n {
                f(j + d, core::array::from_fn(|i| y[i][d]));
            }
            j += n;
        }
    }

    pub fn encrypt_many<const N: usize>(rks: &[RoundKeys; N], x: &[Block; N]) -> [Block; N] {
        core::array::from_fn(|i| rks[i].encrypt(x[i]))
    }

    pub fn keygen_ctr<const N: usize, const B: usize>(
        keys: &[Block; N],
        iv: Block,
        tweaks: &[u32; N],
        ctr: u32,
        rks: Option<&mut [RoundKeys; N]>,
        out: &mut [[Block; B]; N],
    ) {
        let expanded: [RoundKeys; N] = core::array::from_fn(|i| RoundKeys::new(keys[i]));
        for i in 0..N {
            out[i] = core::array::from_fn(|j| ctr_block(iv, ctr + j as u32, tweaks[i]));
            expanded[i].encrypt_blocks(&mut out[i]);
        }
        if let Some(rks) = rks {
            *rks = expanded;
        }
    }
}

pub use imp::{encrypt_many, keygen_ctr, keygen_ctr_each};

pub const HARDWARE: bool = hw::HW;

impl RoundKeys {
    /// Fill `out` with CTR output for counters `ctr`, `ctr + 1`, ... and tweak `tweak`.
    pub fn ctr(&self, iv: Block, tweak: u32, ctr: u32, out: &mut [Block]) {
        for (j, o) in out.iter_mut().enumerate() {
            *o = ctr_block(iv, ctr + j as u32, tweak);
        }
        self.encrypt_blocks(out);
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use ::aes::Aes128Enc;
    use ::aes::cipher::{Array, BlockCipherEncrypt, KeyInit};

    fn reference(key: Block, b: Block) -> Block {
        let c = Aes128Enc::new(&Array(key.to_bytes()));
        let mut a = Array(b.to_bytes());
        c.encrypt_block(&mut a);
        Block::from_bytes(&a.0)
    }

    #[test]
    fn matches_aes_crate() {
        let keys: [Block; 3] = core::array::from_fn(|i| {
            Block::from_u64(0x0123456789abcdef ^ i as u64, 0xfedcba9876543210 + 77 * i as u64)
        });
        let iv = Block::from_u64(0xffff_ffff_0000_0001, 0x1234_5678_ffff_fffe);
        let tweaks = [5, 0x8000_0000, u32::MAX];
        let mut out = [[Block::ZERO; 4]; 3];
        let mut rks: [RoundKeys; 3] = core::array::from_fn(|_| RoundKeys::new(Block::ZERO));
        keygen_ctr(&keys, iv, &tweaks, 7, Some(&mut rks), &mut out);
        for i in 0..3 {
            for j in 0..4 {
                let want = reference(keys[i], ctr_block(iv, 7 + j as u32, tweaks[i]));
                assert_eq!(out[i][j], want);
                assert_eq!(rks[i].encrypt(ctr_block(iv, 7 + j as u32, tweaks[i])), want);
                assert_eq!(RoundKeys::new(keys[i]).encrypt(ctr_block(iv, 7 + j as u32, tweaks[i])), want);
            }
            for len in 0..20 {
                let mut v = vec![Block::ZERO; len];
                rks[i].ctr(iv, tweaks[i], 3, &mut v);
                for (j, x) in v.iter().enumerate() {
                    assert_eq!(*x, reference(keys[i], ctr_block(iv, 3 + j as u32, tweaks[i])));
                }
            }
        }
        for blocks in [0, 1, 2, 7, 8, 9, 18] {
            let mut next = 0;
            keygen_ctr_each(&keys, iv, 9, blocks, |j, x| {
                assert_eq!(j, next);
                next += 1;
                for i in 0..3 {
                    assert_eq!(x[i], reference(keys[i], ctr_block(iv, j as u32, 9)));
                }
            });
            assert_eq!(next, blocks);
        }
    }

    /// The round primitives against FIPS 197 Appendix B, and against the `aes` crate on inputs
    /// covering every byte value in every position.
    #[test]
    fn all_byte_values() {
        let key = Block::from_bytes(&[
            0x2b, 0x7e, 0x15, 0x16, 0x28, 0xae, 0xd2, 0xa6, 0xab, 0xf7, 0x15, 0x88, 0x09, 0xcf, 0x4f, 0x3c,
        ]);
        let pt = Block::from_bytes(&[
            0x32, 0x43, 0xf6, 0xa8, 0x88, 0x5a, 0x30, 0x8d, 0x31, 0x31, 0x98, 0xa2, 0xe0, 0x37, 0x07, 0x34,
        ]);
        let ct = [0x39, 0x25, 0x84, 0x1d, 0x02, 0xdc, 0x09, 0xfb, 0xdc, 0x11, 0x85, 0x97, 0x19, 0x6a, 0x0b, 0x32];
        assert_eq!(RoundKeys::new(key).encrypt(pt).to_bytes(), ct);
        for v in 0..=255u8 {
            let k = Block::from_bytes(&core::array::from_fn(|i| v.wrapping_add(17 * i as u8)));
            let b = Block::from_bytes(&core::array::from_fn(|i| v.wrapping_mul(i as u8 | 1) ^ i as u8));
            assert_eq!(RoundKeys::new(k).encrypt(b), reference(k, b));
            assert_eq!(RoundKeys::new(b).encrypt(k), reference(b, k));
        }
    }
}
