//! SHAKE128/256 sponges over Keccak-f[1600], including a 4-way parallel version.

use keccak::{Backend, BackendClosure, Keccak};

pub type State = [u64; 25];

#[inline(always)]
fn permute(st: &mut State) {
    Keccak::new().with_f1600(|f| f(st));
}

fn permute_x4(sts: &mut [State; 4]) {
    struct C<'a>(&'a mut [State; 4]);
    impl BackendClosure for C<'_> {
        #[inline(always)]
        fn call_once<B: Backend>(self) {
            let par = B::get_par_f1600();
            let (chunks, tail) =
                hybrid_array::Array::<State, B::ParSize1600>::slice_as_chunks_mut(&mut self.0[..]);
            for c in chunks {
                par(c);
            }
            let f = B::get_f1600();
            for s in tail {
                f(s);
            }
        }
    }
    Keccak::new().with_backend(C(sts));
}

#[inline(always)]
fn xor_byte(st: &mut State, pos: usize, b: u8) {
    st[pos / 8] ^= (b as u64) << (8 * (pos % 8));
}

#[inline(always)]
fn get_byte(st: &State, pos: usize) -> u8 {
    (st[pos / 8] >> (8 * (pos % 8))) as u8
}

/// Absorb `data` into a sponge with byte position `pos`, permuting via `perm` when the rate is full.
#[inline(always)]
fn absorb(st: &mut State, pos: &mut usize, rate: usize, mut data: &[u8], perm: &mut impl FnMut(&mut State)) {
    while !data.is_empty() {
        if *pos % 8 == 0 && data.len() >= 8 && *pos + 8 <= rate {
            let words = ((rate - *pos) / 8).min(data.len() / 8);
            for w in 0..words {
                st[*pos / 8 + w] ^= u64::from_le_bytes(data[8 * w..8 * w + 8].try_into().unwrap());
            }
            *pos += 8 * words;
            data = &data[8 * words..];
        } else {
            xor_byte(st, *pos, data[0]);
            *pos += 1;
            data = &data[1..];
        }
        if *pos == rate {
            perm(st);
            *pos = 0;
        }
    }
}

#[inline(always)]
fn squeeze(st: &mut State, pos: &mut usize, rate: usize, mut out: &mut [u8], perm: &mut impl FnMut(&mut State)) {
    while !out.is_empty() {
        if *pos == rate {
            perm(st);
            *pos = 0;
        }
        if *pos % 8 == 0 && out.len() >= 8 && *pos + 8 <= rate {
            let words = ((rate - *pos) / 8).min(out.len() / 8);
            for w in 0..words {
                out[8 * w..8 * w + 8].copy_from_slice(&st[*pos / 8 + w].to_le_bytes());
            }
            *pos += 8 * words;
            out = &mut out[8 * words..];
        } else {
            out[0] = get_byte(st, *pos);
            *pos += 1;
            out = &mut out[1..];
        }
    }
}

/// SHAKE with rate `RATE` bytes (168 for SHAKE128, 136 for SHAKE256).
#[derive(Clone)]
pub struct Shake<const RATE: usize> {
    st: State,
    pos: usize,
    squeezing: bool,
}

pub type Shake128 = Shake<168>;
pub type Shake256 = Shake<136>;

impl<const RATE: usize> Default for Shake<RATE> {
    fn default() -> Self {
        Self::new()
    }
}

impl<const RATE: usize> Shake<RATE> {
    pub fn new() -> Self {
        Shake { st: [0; 25], pos: 0, squeezing: false }
    }

    pub fn update(&mut self, data: &[u8]) -> &mut Self {
        debug_assert!(!self.squeezing);
        absorb(&mut self.st, &mut self.pos, RATE, data, &mut permute);
        self
    }

    pub fn update_byte(&mut self, b: u8) -> &mut Self {
        self.update(&[b])
    }

    fn pad(&mut self) {
        xor_byte(&mut self.st, self.pos, 0x1f);
        xor_byte(&mut self.st, RATE - 1, 0x80);
        permute(&mut self.st);
        self.pos = 0;
        self.squeezing = true;
    }

    /// Squeeze output. The first call finishes absorbing.
    pub fn squeeze(&mut self, out: &mut [u8]) {
        if !self.squeezing {
            self.pad();
        }
        squeeze(&mut self.st, &mut self.pos, RATE, out, &mut permute);
    }

    pub fn finalize<const N: usize>(mut self) -> [u8; N] {
        let mut out = [0u8; N];
        self.squeeze(&mut out);
        out
    }
}

/// Four SHAKE instances whose inputs always have equal lengths.
#[derive(Clone)]
pub struct ShakeX4<const RATE: usize> {
    st: [State; 4],
    pos: usize,
    squeezing: bool,
}

pub type Shake128X4 = ShakeX4<168>;

impl<const RATE: usize> Default for ShakeX4<RATE> {
    fn default() -> Self {
        Self::new()
    }
}

impl<const RATE: usize> ShakeX4<RATE> {
    pub fn new() -> Self {
        ShakeX4 { st: [[0; 25]; 4], pos: 0, squeezing: false }
    }

    /// Absorb a different input into each instance.
    pub fn update(&mut self, data: [&[u8]; 4]) {
        let n = data[0].len();
        debug_assert!(data.iter().all(|d| d.len() == n));
        let mut off = 0;
        while off < n {
            let take = (RATE - self.pos).min(n - off);
            for (st, d) in self.st.iter_mut().zip(data) {
                let mut pos = self.pos;
                absorb(st, &mut pos, RATE + 1, &d[off..off + take], &mut |_| {});
            }
            self.pos += take;
            off += take;
            if self.pos == RATE {
                permute_x4(&mut self.st);
                self.pos = 0;
            }
        }
    }

    /// Absorb the same input into every instance.
    pub fn update_1(&mut self, data: &[u8]) {
        self.update([data; 4]);
    }

    pub fn squeeze(&mut self, out: [&mut [u8]; 4]) {
        if !self.squeezing {
            for st in &mut self.st {
                xor_byte(st, self.pos, 0x1f);
                xor_byte(st, RATE - 1, 0x80);
            }
            permute_x4(&mut self.st);
            self.pos = 0;
            self.squeezing = true;
        }
        let n = out[0].len();
        let mut out = out;
        let mut off = 0;
        while off < n {
            if self.pos == RATE {
                permute_x4(&mut self.st);
                self.pos = 0;
            }
            let take = (RATE - self.pos).min(n - off);
            for (st, o) in self.st.iter_mut().zip(out.iter_mut()) {
                let mut pos = self.pos;
                squeeze(st, &mut pos, RATE + 1, &mut o[off..off + take], &mut |_| {});
            }
            self.pos += take;
            off += take;
        }
    }
}

/// SHAKE128 of the concatenation of `parts`.
pub fn shake128<const N: usize>(parts: &[&[u8]]) -> [u8; N] {
    let mut h = Shake128::new();
    for p in parts {
        h.update(p);
    }
    h.finalize()
}

#[cfg(test)]
mod tests {
    use super::*;

    fn reference(rate: usize, data: &[u8], n: usize) -> Vec<u8> {
        let mut st = [0u64; 25];
        let mut padded = data.to_vec();
        padded.push(0x1f);
        while padded.len() % rate != 0 {
            padded.push(0);
        }
        *padded.last_mut().unwrap() ^= 0x80;
        for chunk in padded.chunks(rate) {
            for (i, &b) in chunk.iter().enumerate() {
                xor_byte(&mut st, i, b);
            }
            permute(&mut st);
        }
        let mut out = Vec::new();
        loop {
            for i in 0..rate {
                if out.len() == n {
                    return out;
                }
                out.push(get_byte(&st, i));
            }
            permute(&mut st);
        }
    }

    fn hex(b: &[u8]) -> String {
        b.iter().map(|x| format!("{x:02x}")).collect()
    }

    #[test]
    fn known_answers() {
        assert_eq!(
            hex(&reference(168, b"", 32)),
            "7f9c2ba4e88f827d616045507605853ed73b8093f6efbc88eb1a6eacfa66ef26"
        );
        assert_eq!(
            hex(&reference(136, b"", 32)),
            "46b9dd2b0ba88d13233b3feb743eeb243fcd52ea62b81b82b50c27646ed5762f"
        );
    }

    #[test]
    fn matches_reference() {
        let data: Vec<u8> = (0..1000u32).map(|i| (i * 7 + 3) as u8).collect();
        for len in [0, 1, 7, 8, 135, 136, 137, 167, 168, 169, 500, 1000] {
            for out_len in [1, 32, 168, 400] {
                let mut h = Shake128::new();
                // Absorb in uneven pieces.
                let (a, b) = data[..len].split_at(len / 3);
                h.update(a).update(b);
                let mut out = vec![0u8; out_len];
                h.squeeze(&mut out[..out_len / 2]);
                h.squeeze(&mut out[out_len / 2..]);
                assert_eq!(out, reference(168, &data[..len], out_len));

                let mut h = Shake256::new();
                h.update(&data[..len]);
                let mut out = vec![0u8; out_len];
                h.squeeze(&mut out);
                assert_eq!(out, reference(136, &data[..len], out_len));

                let mut h = Shake128X4::new();
                let ins: [Vec<u8>; 4] =
                    core::array::from_fn(|k| data[..len].iter().map(|&x| x ^ k as u8).collect());
                let p = len / 2;
                h.update(core::array::from_fn(|k| &ins[k][..p]));
                h.update(core::array::from_fn(|k| &ins[k][p..]));
                let mut outs: [Vec<u8>; 4] = core::array::from_fn(|_| vec![0u8; out_len]);
                let [o0, o1, o2, o3] = &mut outs;
                h.squeeze([o0, o1, o2, o3]);
                for k in 0..4 {
                    assert_eq!(outs[k], reference(168, &ins[k], out_len));
                }
            }
        }
    }
}
