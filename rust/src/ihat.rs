//! VOLE-IHAT: issuance and redemption of anonymous tokens, bound and unbound.

use crate::block::Block;
use crate::circuit::{add_bit_constraints, add_output_constraints, ct_eq_mask, make_dst};
use crate::hash::Shake128;
use crate::keccak800::{
    self, COMMITTED_STATES_BYTES, InputMap, OUTPUT_DEGREE, STATE_BITS, State, qs_byte, qs_input,
    qs_keccak,
};
use crate::params::QS_CHALLENGE_BYTES;
use crate::qs::Qs;
use crate::uov::{self, M, N, Preimage, PublicKey, SecretKey};
use crate::uov_circuit::{Combination, qs_eval_combined_public_map};
use crate::voleith::{self, Dst, Relation};

pub const VERSION: u8 = 0;
const UNBOUND_VERSION: u8 = 1;
pub const MAX_ANCHORS: usize = 64;
pub const NF_BYTES: usize = 24;
pub const CTX_BYTES: usize = 16;
pub const CHALLENGE_DIGEST_BYTES: usize = 32;
pub const SEED_BYTES: usize = 32;
const R_BYTES: usize = 16;
const NF_KEY_BYTES: usize = 16;

pub type Nullifier = [u8; NF_BYTES];
pub type Context = [u8; CTX_BYTES];
pub type ChallengeDigest = [u8; CHALLENGE_DIGEST_BYTES];
pub type Seed = [u8; SEED_BYTES];
pub type Commitment = uov::Target;
pub type IssueResponse = Preimage;
type Opening = [u8; R_BYTES];
type NfKey = [u8; NF_KEY_BYTES];

const COM_DST: Dst = make_dst(b"mous", VERSION, b'c', b'0');
const ISSUE_PROOF_DST: Dst = make_dst(b"mous", VERSION, b'i', b'0');
const ISSUE_SEED_DST: Dst = make_dst(b"mous", VERSION, b's', b'0');
const REDEEM_COMBINE_DST: Dst = make_dst(b"mous", VERSION, b'l', b'0');
const REDEEM_PROOF_DST: Dst = make_dst(b"mous", VERSION, b'r', b'0');
const REDEEM_SEED_DST: Dst = make_dst(b"mous", VERSION, b's', b'1');
const UNBOUND_COM_DST: Dst = make_dst(b"mous", UNBOUND_VERSION, b'c', b'0');
const UNBOUND_DERIVE_DST: Dst = make_dst(b"mous", UNBOUND_VERSION, b'd', b'0');
const UNBOUND_ISSUE_PROOF_DST: Dst = make_dst(b"mous", UNBOUND_VERSION, b'i', b'0');
const UNBOUND_ISSUE_SEED_DST: Dst = make_dst(b"mous", UNBOUND_VERSION, b's', b'0');
const UNBOUND_REDEEM_COMBINE_DST: Dst = make_dst(b"mous", UNBOUND_VERSION, b'l', b'0');
const UNBOUND_REDEEM_PROOF_DST: Dst = make_dst(b"mous", UNBOUND_VERSION, b'r', b'0');
const UNBOUND_REDEEM_SEED_DST: Dst = make_dst(b"mous", UNBOUND_VERSION, b's', b'1');

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Error {
    InvalidAnchorSet,
    InvalidToken,
}

impl core::fmt::Display for Error {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.write_str(match self {
            Error::InvalidAnchorSet => "VOLE-IHAT: invalid Anchor Set",
            Error::InvalidToken => "VOLE-IHAT: invalid token",
        })
    }
}

impl std::error::Error for Error {}

// ---------------------------------------------------------------------------------------------
// Commitments

const COM_OFF_R: usize = 7;
const COM_OFF_CTX_ISS: usize = COM_OFF_R + 25;
const COM_OFF_CTX_RED: usize = COM_OFF_CTX_ISS + CTX_BYTES;
const COM_OFF_NF: usize = COM_OFF_CTX_RED + CTX_BYTES;
const UNBOUND_COM_OFF_R: usize = 7;
const UNBOUND_COM_OFF_CTX_ISS: usize = UNBOUND_COM_OFF_R + 25;
const UNBOUND_COM_OFF_NF_KEY: usize = UNBOUND_COM_OFF_CTX_ISS + CTX_BYTES;
const DERIVE_OFF_NF_KEY: usize = 7;
const DERIVE_OFF_CTX_RED: usize = DERIVE_OFF_NF_KEY + 25;

fn put(state: &mut State, off: usize, b: &[u8]) {
    state[off..off + b.len()].copy_from_slice(b);
}

fn com_state(nf: &Nullifier, ctx_iss: &Context, ctx_red: &Context, r: &Opening) -> State {
    let mut s = [0u8; 100];
    put(&mut s, 0, &COM_DST);
    put(&mut s, COM_OFF_R, r);
    put(&mut s, COM_OFF_CTX_ISS, ctx_iss);
    put(&mut s, COM_OFF_CTX_RED, ctx_red);
    put(&mut s, COM_OFF_NF, nf);
    s
}

fn unbound_com_state(nf_key: &NfKey, ctx_iss: &Context, r: &Opening) -> State {
    let mut s = [0u8; 100];
    put(&mut s, 0, &UNBOUND_COM_DST);
    put(&mut s, UNBOUND_COM_OFF_R, r);
    put(&mut s, UNBOUND_COM_OFF_CTX_ISS, ctx_iss);
    put(&mut s, UNBOUND_COM_OFF_NF_KEY, nf_key);
    s
}

fn derive_state(nf_key: &NfKey, ctx_red: &Context) -> State {
    let mut s = [0u8; 100];
    put(&mut s, 0, &UNBOUND_DERIVE_DST);
    put(&mut s, DERIVE_OFF_NF_KEY, nf_key);
    put(&mut s, DERIVE_OFF_CTX_RED, ctx_red);
    s
}

fn prefix<const K: usize>(s: &State) -> [u8; K] {
    s[..K].try_into().unwrap()
}

pub fn commit(nf: &Nullifier, ctx_iss: &Context, ctx_red: &Context, r: &Opening) -> Commitment {
    prefix(&keccak800::keccak_p800(com_state(nf, ctx_iss, ctx_red, r)))
}

fn unbound_commit(nf_key: &NfKey, ctx_iss: &Context, r: &Opening) -> Commitment {
    prefix(&keccak800::keccak_p800(unbound_com_state(nf_key, ctx_iss, r)))
}

fn derive(nf_key: &NfKey, ctx_red: &Context) -> Nullifier {
    prefix(&keccak800::keccak_p800(derive_state(nf_key, ctx_red)))
}

/// Map `(state offset, witness offset, length)` ranges into an input map.
const fn input_map(ranges: &[(usize, usize, usize)]) -> InputMap {
    let mut map = [-1i32; 100];
    let mut k = 0;
    while k < ranges.len() {
        let (s, w, n) = ranges[k];
        let mut i = 0;
        while i < n {
            map[s + i] = (w + i) as i32;
            i += 1;
        }
        k += 1;
    }
    map
}

// ---------------------------------------------------------------------------------------------
// Shared constraints

const SELECTOR_BYTES: usize = MAX_ANCHORS / 8;

fn encode_selector(b: &mut [u8], i: usize) {
    for u in 0..MAX_ANCHORS {
        b[u / 8] |= (ct_eq_mask(u, i) & (1 << (u % 8))) as u8;
    }
}

fn add_selector_constraints<Q: Qs>(q: &mut Q, n: usize, wit_off_b: usize) -> Vec<Q::Bit<1>> {
    let b: Vec<Q::Bit<1>> = (0..MAX_ANCHORS).map(|u| q.witness_bit(8 * wit_off_b + u)).collect();
    for (u, bu) in b.iter().enumerate() {
        if u < n {
            q.add_bit_constraint(bu);
        } else {
            let v = q.bit_to_val(bu);
            q.add_constraint::<1>(&v);
        }
    }
    let mut pre = b[0];
    for u in 0..MAX_ANCHORS - 1 {
        let p = q.bit_mul::<1, 1, 2>(&pre, &b[u + 1]);
        let v = q.bit_to_val(&p);
        q.add_constraint::<2>(&v);
        pre = q.bit_add(&pre, &b[u + 1]);
    }
    let w = q.bit_add_one(&pre);
    let v = q.bit_to_val(&w);
    q.add_constraint::<1>(&v);
    b
}

/// l(Q(s)) = l(out[0..M]) for the selected Anchor's public map Q, with l derived from chal2.
#[allow(clippy::too_many_arguments)]
fn add_signature_constraint<Q: Qs>(
    q: &mut Q,
    anchors: &[&PublicKey],
    b: &[Q::Bit<1>],
    wit_off_s: usize,
    out: &[Q::Bit<OUTPUT_DEGREE>],
    chal2: &[u8],
    dst: &[u8],
) {
    let l = Combination::new(chal2, dst);
    let s: [Q::Val<1>; N] = core::array::from_fn(|i| q.witness_byte(wit_off_s + i));
    let mut lq = q.val_const::<3>(Block::ZERO);
    for (u, pk) in anchors.iter().enumerate() {
        let lp = qs_eval_combined_public_map(q, pk, &s, &l);
        lq = q.val_add(&lq, &q.bit_val_mul::<1, 2, 3>(&b[u], &lp));
    }
    let mut lout = q.val_const::<OUTPUT_DEGREE>(Block::ZERO);
    for k in 0..M {
        let byte = qs_byte::<Q, OUTPUT_DEGREE>(q, out, k);
        lout = q.val_add(&lout, &q.val_scale(l.coeff(k), &byte));
    }
    let x = q.val_add(&lout, &q.val_lift::<3, OUTPUT_DEGREE>(&lq));
    q.add_constraint::<OUTPUT_DEGREE>(&x);
}

struct RedeemInstance<'a> {
    anchors: &'a [&'a PublicKey],
    nf: Nullifier,
    ctx_iss: Context,
    ctx_red: Context,
    challenge_digest: ChallengeDigest,
}

impl RedeemInstance<'_> {
    fn hash(&self, h: &mut Shake128) {
        h.update(&(MAX_ANCHORS as u32).to_le_bytes());
        h.update(&(self.anchors.len() as u32).to_le_bytes());
        for pk in self.anchors {
            h.update(pk.digest());
        }
        h.update(&self.nf).update(&self.ctx_iss).update(&self.ctx_red).update(&self.challenge_digest);
    }
}

// ---------------------------------------------------------------------------------------------
// Relations

const ISSUE_WIT_OFF_R: usize = 0;
const ISSUE_WIT_OFF_CTX_RED: usize = ISSUE_WIT_OFF_R + R_BYTES;
const ISSUE_WIT_OFF_NF: usize = ISSUE_WIT_OFF_CTX_RED + CTX_BYTES;
const ISSUE_WIT_OFF_STATES: usize = ISSUE_WIT_OFF_NF + NF_BYTES;
const ISSUE_WITNESS_BYTES: usize = ISSUE_WIT_OFF_STATES + COMMITTED_STATES_BYTES;
const COM_TO_WIT: InputMap = input_map(&[
    (COM_OFF_R, ISSUE_WIT_OFF_R, R_BYTES),
    (COM_OFF_CTX_RED, ISSUE_WIT_OFF_CTX_RED, CTX_BYTES),
    (COM_OFF_NF, ISSUE_WIT_OFF_NF, NF_BYTES),
]);

struct IssueRelation {
    t: Commitment,
    ctx_iss: Context,
}

impl Relation for IssueRelation {
    const WITNESS_BYTES: usize = ISSUE_WITNESS_BYTES;
    const DST: Dst = ISSUE_PROOF_DST;

    fn hash_instance(&self, h: &mut Shake128) {
        h.update(&self.t).update(&self.ctx_iss);
    }

    fn constraints<Q: Qs>(&self, q: &mut Q, _chal2: &[u8; QS_CHALLENGE_BYTES]) {
        add_bit_constraints(q, 8 * ISSUE_WITNESS_BYTES);
        let public = com_state(&[0; NF_BYTES], &self.ctx_iss, &[0; CTX_BYTES], &[0; R_BYTES]);
        let input = qs_input(q, &public, &COM_TO_WIT);
        let out = qs_keccak(q, &input, ISSUE_WIT_OFF_STATES, 8 * M);
        add_output_constraints(q, &out, &self.t);
    }
}

fn encode_issue_witness(nf: &Nullifier, ctx_iss: &Context, ctx_red: &Context, r: &Opening) -> Vec<u8> {
    let mut w = vec![0u8; ISSUE_WITNESS_BYTES];
    w[ISSUE_WIT_OFF_R..][..R_BYTES].copy_from_slice(r);
    w[ISSUE_WIT_OFF_CTX_RED..][..CTX_BYTES].copy_from_slice(ctx_red);
    w[ISSUE_WIT_OFF_NF..][..NF_BYTES].copy_from_slice(nf);
    keccak800::encode_committed_states(&mut w[ISSUE_WIT_OFF_STATES..], com_state(nf, ctx_iss, ctx_red, r));
    w
}

const REDEEM_WIT_OFF_R: usize = 0;
const REDEEM_WIT_OFF_S: usize = REDEEM_WIT_OFF_R + R_BYTES;
const REDEEM_WIT_OFF_STATES: usize = REDEEM_WIT_OFF_S + N;
const REDEEM_WIT_OFF_B: usize = REDEEM_WIT_OFF_STATES + COMMITTED_STATES_BYTES;
const REDEEM_WITNESS_BYTES: usize = REDEEM_WIT_OFF_B + SELECTOR_BYTES;
const REDEEM_COM_TO_WIT: InputMap = input_map(&[(COM_OFF_R, REDEEM_WIT_OFF_R, R_BYTES)]);

struct RedeemRelation<'a>(RedeemInstance<'a>);

impl Relation for RedeemRelation<'_> {
    const WITNESS_BYTES: usize = REDEEM_WITNESS_BYTES;
    const DST: Dst = REDEEM_PROOF_DST;

    fn hash_instance(&self, h: &mut Shake128) {
        self.0.hash(h);
    }

    fn constraints<Q: Qs>(&self, q: &mut Q, chal2: &[u8; QS_CHALLENGE_BYTES]) {
        let x = &self.0;
        add_bit_constraints(q, 8 * REDEEM_WIT_OFF_B);
        let b = add_selector_constraints(q, x.anchors.len(), REDEEM_WIT_OFF_B);
        let public = com_state(&x.nf, &x.ctx_iss, &x.ctx_red, &[0; R_BYTES]);
        let input = qs_input(q, &public, &REDEEM_COM_TO_WIT);
        let out = qs_keccak(q, &input, REDEEM_WIT_OFF_STATES, STATE_BITS);
        add_signature_constraint(q, x.anchors, &b, REDEEM_WIT_OFF_S, &out, chal2, &REDEEM_COMBINE_DST);
    }
}

fn encode_redeem_witness(
    nf: &Nullifier,
    ctx_iss: &Context,
    ctx_red: &Context,
    r: &Opening,
    s: &Preimage,
    i: usize,
) -> Vec<u8> {
    let mut w = vec![0u8; REDEEM_WITNESS_BYTES];
    w[REDEEM_WIT_OFF_R..][..R_BYTES].copy_from_slice(r);
    w[REDEEM_WIT_OFF_S..][..N].copy_from_slice(s);
    keccak800::encode_committed_states(&mut w[REDEEM_WIT_OFF_STATES..], com_state(nf, ctx_iss, ctx_red, r));
    encode_selector(&mut w[REDEEM_WIT_OFF_B..], i);
    w
}

const UNBOUND_ISSUE_WIT_OFF_R: usize = 0;
const UNBOUND_ISSUE_WIT_OFF_NF_KEY: usize = UNBOUND_ISSUE_WIT_OFF_R + R_BYTES;
const UNBOUND_ISSUE_WIT_OFF_STATES: usize = UNBOUND_ISSUE_WIT_OFF_NF_KEY + NF_KEY_BYTES;
const UNBOUND_ISSUE_WITNESS_BYTES: usize = UNBOUND_ISSUE_WIT_OFF_STATES + COMMITTED_STATES_BYTES;
const UNBOUND_COM_TO_WIT: InputMap = input_map(&[
    (UNBOUND_COM_OFF_R, UNBOUND_ISSUE_WIT_OFF_R, R_BYTES),
    (UNBOUND_COM_OFF_NF_KEY, UNBOUND_ISSUE_WIT_OFF_NF_KEY, NF_KEY_BYTES),
]);

struct UnboundIssueRelation {
    t: Commitment,
    ctx_iss: Context,
}

impl Relation for UnboundIssueRelation {
    const WITNESS_BYTES: usize = UNBOUND_ISSUE_WITNESS_BYTES;
    const DST: Dst = UNBOUND_ISSUE_PROOF_DST;

    fn hash_instance(&self, h: &mut Shake128) {
        h.update(&self.t).update(&self.ctx_iss);
    }

    fn constraints<Q: Qs>(&self, q: &mut Q, _chal2: &[u8; QS_CHALLENGE_BYTES]) {
        add_bit_constraints(q, 8 * UNBOUND_ISSUE_WITNESS_BYTES);
        let public = unbound_com_state(&[0; NF_KEY_BYTES], &self.ctx_iss, &[0; R_BYTES]);
        let input = qs_input(q, &public, &UNBOUND_COM_TO_WIT);
        let out = qs_keccak(q, &input, UNBOUND_ISSUE_WIT_OFF_STATES, 8 * M);
        add_output_constraints(q, &out, &self.t);
    }
}

fn encode_unbound_issue_witness(nf_key: &NfKey, ctx_iss: &Context, r: &Opening) -> Vec<u8> {
    let mut w = vec![0u8; UNBOUND_ISSUE_WITNESS_BYTES];
    w[UNBOUND_ISSUE_WIT_OFF_R..][..R_BYTES].copy_from_slice(r);
    w[UNBOUND_ISSUE_WIT_OFF_NF_KEY..][..NF_KEY_BYTES].copy_from_slice(nf_key);
    keccak800::encode_committed_states(
        &mut w[UNBOUND_ISSUE_WIT_OFF_STATES..],
        unbound_com_state(nf_key, ctx_iss, r),
    );
    w
}

const UNBOUND_REDEEM_WIT_OFF_R: usize = 0;
const UNBOUND_REDEEM_WIT_OFF_NF_KEY: usize = UNBOUND_REDEEM_WIT_OFF_R + R_BYTES;
const UNBOUND_REDEEM_WIT_OFF_S: usize = UNBOUND_REDEEM_WIT_OFF_NF_KEY + NF_KEY_BYTES;
const UNBOUND_REDEEM_WIT_OFF_COM_STATES: usize = UNBOUND_REDEEM_WIT_OFF_S + N;
const UNBOUND_REDEEM_WIT_OFF_DERIVE_STATES: usize = UNBOUND_REDEEM_WIT_OFF_COM_STATES + COMMITTED_STATES_BYTES;
const UNBOUND_REDEEM_WIT_OFF_B: usize = UNBOUND_REDEEM_WIT_OFF_DERIVE_STATES + COMMITTED_STATES_BYTES;
const UNBOUND_REDEEM_WITNESS_BYTES: usize = UNBOUND_REDEEM_WIT_OFF_B + SELECTOR_BYTES;
const UNBOUND_REDEEM_COM_TO_WIT: InputMap = input_map(&[
    (UNBOUND_COM_OFF_R, UNBOUND_REDEEM_WIT_OFF_R, R_BYTES),
    (UNBOUND_COM_OFF_NF_KEY, UNBOUND_REDEEM_WIT_OFF_NF_KEY, NF_KEY_BYTES),
]);
const UNBOUND_REDEEM_DERIVE_TO_WIT: InputMap =
    input_map(&[(DERIVE_OFF_NF_KEY, UNBOUND_REDEEM_WIT_OFF_NF_KEY, NF_KEY_BYTES)]);

struct UnboundRedeemRelation<'a>(RedeemInstance<'a>);

impl Relation for UnboundRedeemRelation<'_> {
    const WITNESS_BYTES: usize = UNBOUND_REDEEM_WITNESS_BYTES;
    const DST: Dst = UNBOUND_REDEEM_PROOF_DST;

    fn hash_instance(&self, h: &mut Shake128) {
        self.0.hash(h);
    }

    fn constraints<Q: Qs>(&self, q: &mut Q, chal2: &[u8; QS_CHALLENGE_BYTES]) {
        let x = &self.0;
        add_bit_constraints(q, 8 * UNBOUND_REDEEM_WIT_OFF_B);
        let b = add_selector_constraints(q, x.anchors.len(), UNBOUND_REDEEM_WIT_OFF_B);
        let com_public = unbound_com_state(&[0; NF_KEY_BYTES], &x.ctx_iss, &[0; R_BYTES]);
        let com_in = qs_input(q, &com_public, &UNBOUND_REDEEM_COM_TO_WIT);
        let com_out = qs_keccak(q, &com_in, UNBOUND_REDEEM_WIT_OFF_COM_STATES, STATE_BITS);
        let der_public = derive_state(&[0; NF_KEY_BYTES], &x.ctx_red);
        let der_in = qs_input(q, &der_public, &UNBOUND_REDEEM_DERIVE_TO_WIT);
        let der_out = qs_keccak(q, &der_in, UNBOUND_REDEEM_WIT_OFF_DERIVE_STATES, 8 * NF_BYTES);
        add_output_constraints(q, &der_out, &x.nf);
        add_signature_constraint(
            q,
            x.anchors,
            &b,
            UNBOUND_REDEEM_WIT_OFF_S,
            &com_out,
            chal2,
            &UNBOUND_REDEEM_COMBINE_DST,
        );
    }
}

fn encode_unbound_redeem_witness(
    nf_key: &NfKey,
    ctx_iss: &Context,
    ctx_red: &Context,
    r: &Opening,
    s: &Preimage,
    i: usize,
) -> Vec<u8> {
    let mut w = vec![0u8; UNBOUND_REDEEM_WITNESS_BYTES];
    w[UNBOUND_REDEEM_WIT_OFF_R..][..R_BYTES].copy_from_slice(r);
    w[UNBOUND_REDEEM_WIT_OFF_NF_KEY..][..NF_KEY_BYTES].copy_from_slice(nf_key);
    w[UNBOUND_REDEEM_WIT_OFF_S..][..N].copy_from_slice(s);
    keccak800::encode_committed_states(
        &mut w[UNBOUND_REDEEM_WIT_OFF_COM_STATES..],
        unbound_com_state(nf_key, ctx_iss, r),
    );
    keccak800::encode_committed_states(
        &mut w[UNBOUND_REDEEM_WIT_OFF_DERIVE_STATES..],
        derive_state(nf_key, ctx_red),
    );
    encode_selector(&mut w[UNBOUND_REDEEM_WIT_OFF_B..], i);
    w
}

pub const ISSUE_PROOF_BYTES: usize = voleith::proof_bytes::<IssueRelation>();
pub const ISSUE_REQUEST_BYTES: usize = M + ISSUE_PROOF_BYTES;
pub const REDEEM_PROOF_BYTES: usize = voleith::proof_bytes::<RedeemRelation>();
pub const REDEEM_REQUEST_BYTES: usize = NF_BYTES + REDEEM_PROOF_BYTES;
pub const UNBOUND_ISSUE_PROOF_BYTES: usize = voleith::proof_bytes::<UnboundIssueRelation>();
pub const UNBOUND_ISSUE_REQUEST_BYTES: usize = M + UNBOUND_ISSUE_PROOF_BYTES;
pub const UNBOUND_REDEEM_PROOF_BYTES: usize = voleith::proof_bytes::<UnboundRedeemRelation>();
pub const UNBOUND_REDEEM_REQUEST_BYTES: usize = NF_BYTES + UNBOUND_REDEEM_PROOF_BYTES;

const _: () = assert!(ISSUE_PROOF_BYTES == 7272 && REDEEM_PROOF_BYTES == 8751);
const _: () = assert!(UNBOUND_ISSUE_PROOF_BYTES == 6864 && UNBOUND_REDEEM_PROOF_BYTES == 12423);

// ---------------------------------------------------------------------------------------------
// API

fn random_seed() -> Seed {
    let mut s = [0u8; SEED_BYTES];
    getrandom::fill(&mut s).expect("OS random number generator failed");
    s
}

fn xof(dst: &[u8], seed: &Seed) -> Shake128 {
    let mut h = Shake128::new();
    h.update(dst).update(seed);
    h
}

/// A set of Anchor (issuer) public keys.
#[derive(Clone)]
pub struct AnchorSet<'a> {
    keys: Vec<&'a PublicKey>,
}

impl<'a> AnchorSet<'a> {
    pub fn new(keys: impl IntoIterator<Item = &'a PublicKey>) -> Result<Self, Error> {
        let keys: Vec<_> = keys.into_iter().collect();
        if keys.is_empty() || keys.len() > MAX_ANCHORS {
            return Err(Error::InvalidAnchorSet);
        }
        for u in 0..keys.len() {
            for v in u + 1..keys.len() {
                if keys[u].digest() == keys[v].digest() {
                    return Err(Error::InvalidAnchorSet);
                }
            }
        }
        Ok(AnchorSet { keys })
    }

    pub fn len(&self) -> usize {
        self.keys.len()
    }

    pub fn is_empty(&self) -> bool {
        self.keys.is_empty()
    }

    /// Index of the Anchor whose public map takes s to t, without branching on the index.
    fn find_issuer(&self, t: &Commitment, s: &Preimage) -> Result<usize, Error> {
        let mut i = 0usize;
        let mut found = 0usize;
        for (u, pk) in self.keys.iter().enumerate() {
            let tu = pk.eval(s);
            let diff = t.iter().zip(&tu).fold(0u8, |d, (a, b)| d | (a ^ b));
            let m = ct_eq_mask(diff as usize, 0);
            i = (i & !m) | (u & m);
            found |= m;
        }
        if found == 0 { Err(Error::InvalidToken) } else { Ok(i) }
    }
}

#[derive(Clone)]
pub struct PendingToken {
    nf: Nullifier,
    r: Opening,
    t: Commitment,
}

#[derive(Clone)]
pub struct Token {
    nf: Nullifier,
    r: Opening,
    s: Preimage,
}

pub fn issue_request(ctx_iss: &Context, ctx_red: &Context) -> (PendingToken, Vec<u8>) {
    issue_request_with_seed(ctx_iss, ctx_red, &random_seed())
}

pub fn issue_request_with_seed(ctx_iss: &Context, ctx_red: &Context, seed: &Seed) -> (PendingToken, Vec<u8>) {
    let mut x = xof(&ISSUE_SEED_DST, seed);
    let mut nf = [0u8; NF_BYTES];
    let mut r = [0u8; R_BYTES];
    let mut rho = [0u8; 16];
    x.squeeze(&mut nf);
    x.squeeze(&mut r);
    x.squeeze(&mut rho);

    let t = commit(&nf, ctx_iss, ctx_red, &r);
    let w = encode_issue_witness(&nf, ctx_iss, ctx_red, &r);
    let proof = voleith::prove(&IssueRelation { t, ctx_iss: *ctx_iss }, &w, &rho);
    let mut req = Vec::with_capacity(ISSUE_REQUEST_BYTES);
    req.extend_from_slice(&t);
    req.extend_from_slice(&proof);
    (PendingToken { nf, r, t }, req)
}

pub fn issue_response(sk: &SecretKey, request: &[u8], ctx_iss: &Context) -> Option<IssueResponse> {
    if request.len() != ISSUE_REQUEST_BYTES {
        return None;
    }
    let t: Commitment = request[..M].try_into().unwrap();
    if !voleith::verify(&IssueRelation { t, ctx_iss: *ctx_iss }, &request[M..]) {
        return None;
    }
    sk.derive_preimage(&t).ok()
}

impl PendingToken {
    pub fn finalize_issue(self, pk: &PublicKey, response: &IssueResponse) -> Option<Token> {
        (pk.eval(response) == self.t).then_some(Token { nf: self.nf, r: self.r, s: *response })
    }
}

fn expand_redeem_seed(dst: &[u8], seed: &Seed) -> [u8; 16] {
    let mut rho = [0u8; 16];
    xof(dst, seed).squeeze(&mut rho);
    rho
}

impl Token {
    pub fn redeem_request(
        self,
        anchors: &AnchorSet,
        ctx_iss: &Context,
        ctx_red: &Context,
        challenge_digest: &ChallengeDigest,
    ) -> Result<Vec<u8>, Error> {
        self.redeem_request_with_seed(anchors, ctx_iss, ctx_red, challenge_digest, &random_seed())
    }

    pub fn redeem_request_with_seed(
        self,
        anchors: &AnchorSet,
        ctx_iss: &Context,
        ctx_red: &Context,
        challenge_digest: &ChallengeDigest,
        seed: &Seed,
    ) -> Result<Vec<u8>, Error> {
        let i = anchors.find_issuer(&commit(&self.nf, ctx_iss, ctx_red, &self.r), &self.s)?;
        let w = encode_redeem_witness(&self.nf, ctx_iss, ctx_red, &self.r, &self.s, i);
        let rel = RedeemRelation(RedeemInstance {
            anchors: &anchors.keys,
            nf: self.nf,
            ctx_iss: *ctx_iss,
            ctx_red: *ctx_red,
            challenge_digest: *challenge_digest,
        });
        let proof = voleith::prove(&rel, &w, &expand_redeem_seed(&REDEEM_SEED_DST, seed));
        let mut req = Vec::with_capacity(REDEEM_REQUEST_BYTES);
        req.extend_from_slice(&self.nf);
        req.extend_from_slice(&proof);
        Ok(req)
    }
}

pub fn finalize_redeem(
    anchors: &AnchorSet,
    request: &[u8],
    ctx_iss: &Context,
    ctx_red: &Context,
    challenge_digest: &ChallengeDigest,
) -> Option<Nullifier> {
    if request.len() != REDEEM_REQUEST_BYTES {
        return None;
    }
    let nf: Nullifier = request[..NF_BYTES].try_into().unwrap();
    let rel = RedeemRelation(RedeemInstance {
        anchors: &anchors.keys,
        nf,
        ctx_iss: *ctx_iss,
        ctx_red: *ctx_red,
        challenge_digest: *challenge_digest,
    });
    voleith::verify(&rel, &request[NF_BYTES..]).then_some(nf)
}

#[derive(Clone)]
pub struct PendingUnboundToken {
    nf_key: NfKey,
    r: Opening,
    t: Commitment,
}

#[derive(Clone)]
pub struct UnboundToken {
    nf_key: NfKey,
    r: Opening,
    s: Preimage,
}

pub fn unbound_issue_request(ctx_iss: &Context) -> (PendingUnboundToken, Vec<u8>) {
    unbound_issue_request_with_seed(ctx_iss, &random_seed())
}

pub fn unbound_issue_request_with_seed(ctx_iss: &Context, seed: &Seed) -> (PendingUnboundToken, Vec<u8>) {
    let mut x = xof(&UNBOUND_ISSUE_SEED_DST, seed);
    let mut nf_key = [0u8; NF_KEY_BYTES];
    let mut r = [0u8; R_BYTES];
    let mut rho = [0u8; 16];
    x.squeeze(&mut nf_key);
    x.squeeze(&mut r);
    x.squeeze(&mut rho);

    let t = unbound_commit(&nf_key, ctx_iss, &r);
    let w = encode_unbound_issue_witness(&nf_key, ctx_iss, &r);
    let proof = voleith::prove(&UnboundIssueRelation { t, ctx_iss: *ctx_iss }, &w, &rho);
    let mut req = Vec::with_capacity(UNBOUND_ISSUE_REQUEST_BYTES);
    req.extend_from_slice(&t);
    req.extend_from_slice(&proof);
    (PendingUnboundToken { nf_key, r, t }, req)
}

pub fn unbound_issue_response(sk: &SecretKey, request: &[u8], ctx_iss: &Context) -> Option<IssueResponse> {
    if request.len() != UNBOUND_ISSUE_REQUEST_BYTES {
        return None;
    }
    let t: Commitment = request[..M].try_into().unwrap();
    if !voleith::verify(&UnboundIssueRelation { t, ctx_iss: *ctx_iss }, &request[M..]) {
        return None;
    }
    sk.derive_preimage(&t).ok()
}

impl PendingUnboundToken {
    pub fn finalize_issue(self, pk: &PublicKey, response: &IssueResponse) -> Option<UnboundToken> {
        (pk.eval(response) == self.t).then_some(UnboundToken { nf_key: self.nf_key, r: self.r, s: *response })
    }
}

impl UnboundToken {
    pub fn redeem_request(
        &self,
        anchors: &AnchorSet,
        ctx_iss: &Context,
        ctx_red: &Context,
        challenge_digest: &ChallengeDigest,
    ) -> Result<Vec<u8>, Error> {
        self.redeem_request_with_seed(anchors, ctx_iss, ctx_red, challenge_digest, &random_seed())
    }

    pub fn redeem_request_with_seed(
        &self,
        anchors: &AnchorSet,
        ctx_iss: &Context,
        ctx_red: &Context,
        challenge_digest: &ChallengeDigest,
        seed: &Seed,
    ) -> Result<Vec<u8>, Error> {
        let i = anchors.find_issuer(&unbound_commit(&self.nf_key, ctx_iss, &self.r), &self.s)?;
        let nf = derive(&self.nf_key, ctx_red);
        let w = encode_unbound_redeem_witness(&self.nf_key, ctx_iss, ctx_red, &self.r, &self.s, i);
        let rel = UnboundRedeemRelation(RedeemInstance {
            anchors: &anchors.keys,
            nf,
            ctx_iss: *ctx_iss,
            ctx_red: *ctx_red,
            challenge_digest: *challenge_digest,
        });
        let proof = voleith::prove(&rel, &w, &expand_redeem_seed(&UNBOUND_REDEEM_SEED_DST, seed));
        let mut req = Vec::with_capacity(UNBOUND_REDEEM_REQUEST_BYTES);
        req.extend_from_slice(&nf);
        req.extend_from_slice(&proof);
        Ok(req)
    }
}

pub fn unbound_finalize_redeem(
    anchors: &AnchorSet,
    request: &[u8],
    ctx_iss: &Context,
    ctx_red: &Context,
    challenge_digest: &ChallengeDigest,
) -> Option<Nullifier> {
    if request.len() != UNBOUND_REDEEM_REQUEST_BYTES {
        return None;
    }
    let nf: Nullifier = request[..NF_BYTES].try_into().unwrap();
    let rel = UnboundRedeemRelation(RedeemInstance {
        anchors: &anchors.keys,
        nf,
        ctx_iss: *ctx_iss,
        ctx_red: *ctx_red,
        challenge_digest: *challenge_digest,
    });
    voleith::verify(&rel, &request[NF_BYTES..]).then_some(nf)
}

/// Internals exposed for known-answer tests.
#[doc(hidden)]
pub mod testing {
    use super::*;

    pub fn issue_witness(t: &PendingToken, ctx_iss: &Context, ctx_red: &Context) -> Vec<u8> {
        encode_issue_witness(&t.nf, ctx_iss, ctx_red, &t.r)
    }
    pub fn pending_nf_r(t: &PendingToken) -> (Nullifier, [u8; 16], Commitment) {
        (t.nf, t.r, t.t)
    }
    pub fn redeem_witness(t: &Token, ctx_iss: &Context, ctx_red: &Context, i: usize) -> Vec<u8> {
        encode_redeem_witness(&t.nf, ctx_iss, ctx_red, &t.r, &t.s, i)
    }
    pub fn unbound_issue_witness(t: &PendingUnboundToken, ctx_iss: &Context) -> Vec<u8> {
        encode_unbound_issue_witness(&t.nf_key, ctx_iss, &t.r)
    }
    pub fn pending_unbound(t: &PendingUnboundToken) -> ([u8; 16], [u8; 16], Commitment) {
        (t.nf_key, t.r, t.t)
    }
    pub fn unbound_redeem_witness(t: &UnboundToken, ctx_iss: &Context, ctx_red: &Context, i: usize) -> Vec<u8> {
        encode_unbound_redeem_witness(&t.nf_key, ctx_iss, ctx_red, &t.r, &t.s, i)
    }
    pub fn derive_nf(t: &UnboundToken, ctx_red: &Context) -> Nullifier {
        derive(&t.nf_key, ctx_red)
    }
}
