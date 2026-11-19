//! AES-128 in CTR mode with a fresh key per PRG seed.
//!
//! Hardware AES (aarch64 `aes`, x86-64 AES-NI + SSSE3) runs the key schedule of several keys
//! interleaved with the encryption rounds. Without it, the `aes` crate is used.

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

#[cfg(not(any(
    all(target_arch = "aarch64", target_feature = "neon", target_feature = "aes"),
    all(
        target_arch = "x86_64",
        target_feature = "sse2",
        target_feature = "ssse3",
        target_feature = "pclmulqdq",
        target_feature = "aes"
    )
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
        )
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
    )
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
                s = hw::round(s, k[r + usize::from(cfg!(target_arch = "x86_64"))]);
            }
            hw::last(s, k[ROUNDS - 1], k[ROUNDS])
        }
    }

    /// Encrypt one block under each of `N` keys, interleaving the rounds.
    #[inline(always)]
    pub fn encrypt_many<const N: usize>(rks: &[RoundKeys; N], x: &[Block; N]) -> [Block; N] {
        let off = usize::from(cfg!(target_arch = "x86_64"));
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
        let x86 = cfg!(target_arch = "x86_64");
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
            if x86 {
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
            if !x86 {
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
    )
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
            for j in 0..B {
                out[i][j] = expanded[i].encrypt(ctr_block(iv, ctr + j as u32, tweaks[i]));
            }
        }
        if let Some(rks) = rks {
            *rks = expanded;
        }
    }
}

pub use imp::{encrypt_many, keygen_ctr};

pub const HARDWARE: bool = hw::HW;

impl RoundKeys {
    /// Fill `out` with CTR output for counters `ctr`, `ctr + 1`, ... and tweak `tweak`.
    pub fn ctr(&self, iv: Block, tweak: u32, ctr: u32, out: &mut [Block]) {
        let mut chunks = out.chunks_exact_mut(8);
        let mut c = ctr;
        for chunk in &mut chunks {
            let blocks: [Block; 8] =
                core::array::from_fn(|j| self.encrypt(ctr_block(iv, c + j as u32, tweak)));
            chunk.copy_from_slice(&blocks);
            c += 8;
        }
        for (j, o) in chunks.into_remainder().iter_mut().enumerate() {
            *o = self.encrypt(ctr_block(iv, c + j as u32, tweak));
        }
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
            let mut v = vec![Block::ZERO; 11];
            rks[i].ctr(iv, tweaks[i], 3, &mut v);
            for (j, x) in v.iter().enumerate() {
                assert_eq!(*x, reference(keys[i], ctr_block(iv, 3 + j as u32, tweaks[i])));
            }
        }
    }
}
