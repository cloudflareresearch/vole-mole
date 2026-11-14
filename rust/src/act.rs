//! VOLE-ACT: anonymous credit tokens.

use crate::block::Block;
use crate::circuit::{add_bit_constraints, add_output_constraints, make_dst};
use crate::hash::Shake128;
use crate::keccak800::{self, COMMITTED_STATES_BYTES, InputMap, OUTPUT_DEGREE, State, qs_byte, qs_input, qs_keccak};
use crate::params::QS_CHALLENGE_BYTES;
use crate::qs::Qs;
use crate::uov::{self, M, N, Preimage, PublicKey, SecretKey};
use crate::uov_circuit::{Combination, qs_eval_combined_public_map};
use crate::voleith::{self, Dst, Relation};

pub const VERSION: u8 = 0;
pub type Credits = u64;
pub const CREDIT_BYTES: usize = 8;
const CREDIT_BITS: usize = 64;
pub const NF_BYTES: usize = 24;
pub const CTX_BYTES: usize = 16;
pub const COMMITMENT_BYTES: usize = 32;
pub const SEED_BYTES: usize = 32;
const R_BYTES: usize = 16;

pub type Nullifier = [u8; NF_BYTES];
pub type Context = [u8; CTX_BYTES];
pub type Seed = [u8; SEED_BYTES];
pub type Commitment = [u8; COMMITMENT_BYTES];
pub type IssueResponse = Preimage;
type Opening = [u8; R_BYTES];

const COM_DST: Dst = make_dst(b"rata", VERSION, b'c', b'0');
const ISSUE_PROOF_DST: Dst = make_dst(b"rata", VERSION, b'i', b'0');
const ISSUE_SEED_DST: Dst = make_dst(b"rata", VERSION, b's', b'0');
const SPEND_COMBINE_DST: Dst = make_dst(b"rata", VERSION, b'l', b'0');
const SPEND_PROOF_DST: Dst = make_dst(b"rata", VERSION, b'p', b'0');
const SPEND_SEED_DST: Dst = make_dst(b"rata", VERSION, b's', b'1');
const TAG_DST: Dst = make_dst(b"rata", VERSION, b't', b'0');

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Error {
    ZeroInitialCredit,
    WrongIssuer,
    InsufficientBalance,
    ChangeOverflow,
}

impl core::fmt::Display for Error {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.write_str(match self {
            Error::ZeroInitialCredit => "VOLE-ACT: initial credit must be positive",
            Error::WrongIssuer => "VOLE-ACT: token wasn't issued by this Issuer for this issuance context",
            Error::InsufficientBalance => "VOLE-ACT: insufficient balance",
            Error::ChangeOverflow => "VOLE-ACT: change exceeds the largest credit value",
        })
    }
}

impl std::error::Error for Error {}

// ---------------------------------------------------------------------------------------------
// Commitment and tag

const COM_OFF_R: usize = 7;
const COM_OFF_CTX: usize = COM_OFF_R + 25;
const COM_OFF_T: usize = COM_OFF_CTX + CTX_BYTES;
const COM_OFF_NF: usize = COM_OFF_T + CREDIT_BYTES;
const TAG_OFF_C: usize = 7 + 25;
const TAG_OFF_X: usize = TAG_OFF_C + COMMITMENT_BYTES;

fn com_state(nf: &Nullifier, ctx_iss: &Context, t: Credits, r: &Opening) -> State {
    let mut s = [0u8; 100];
    s[..7].copy_from_slice(&COM_DST);
    s[COM_OFF_R..][..R_BYTES].copy_from_slice(r);
    s[COM_OFF_CTX..][..CTX_BYTES].copy_from_slice(ctx_iss);
    s[COM_OFF_T..][..CREDIT_BYTES].copy_from_slice(&t.to_le_bytes());
    s[COM_OFF_NF..][..NF_BYTES].copy_from_slice(nf);
    s
}

fn tag_state(c: &Commitment, x: Credits) -> State {
    let mut s = [0u8; 100];
    s[..7].copy_from_slice(&TAG_DST);
    s[TAG_OFF_C..][..COMMITMENT_BYTES].copy_from_slice(c);
    s[TAG_OFF_X..][..CREDIT_BYTES].copy_from_slice(&x.to_le_bytes());
    s
}

pub fn commit(nf: &Nullifier, ctx_iss: &Context, t: Credits, r: &Opening) -> Commitment {
    keccak800::keccak_p800(com_state(nf, ctx_iss, t, r))[..COMMITMENT_BYTES].try_into().unwrap()
}

pub fn tag(c: &Commitment, x: Credits) -> uov::Target {
    keccak800::keccak_p800(tag_state(c, x))[..M].try_into().unwrap()
}

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
// Issuance

const ISSUE_WIT_OFF_R: usize = 0;
const ISSUE_WIT_OFF_NF: usize = ISSUE_WIT_OFF_R + R_BYTES;
const ISSUE_WIT_OFF_STATES: usize = ISSUE_WIT_OFF_NF + NF_BYTES;
const ISSUE_WITNESS_BYTES: usize = ISSUE_WIT_OFF_STATES + COMMITTED_STATES_BYTES;
const ISSUE_COM_TO_WIT: InputMap =
    input_map(&[(COM_OFF_R, ISSUE_WIT_OFF_R, R_BYTES), (COM_OFF_NF, ISSUE_WIT_OFF_NF, NF_BYTES)]);

struct IssueRelation {
    c: Commitment,
    t_init: Credits,
    ctx_iss: Context,
}

impl Relation for IssueRelation {
    const WITNESS_BYTES: usize = ISSUE_WITNESS_BYTES;
    const DST: Dst = ISSUE_PROOF_DST;

    fn hash_instance(&self, h: &mut Shake128) {
        h.update(&self.c).update(&self.t_init.to_le_bytes()).update(&self.ctx_iss);
    }

    fn constraints<Q: Qs>(&self, q: &mut Q, _chal2: &[u8; QS_CHALLENGE_BYTES]) {
        add_bit_constraints(q, 8 * ISSUE_WITNESS_BYTES);
        let public = com_state(&[0; NF_BYTES], &self.ctx_iss, self.t_init, &[0; R_BYTES]);
        let input = qs_input(q, &public, &ISSUE_COM_TO_WIT);
        let out = qs_keccak(q, &input, ISSUE_WIT_OFF_STATES, 8 * COMMITMENT_BYTES);
        add_output_constraints(q, &out, &self.c);
    }
}

fn encode_issue_witness(nf: &Nullifier, ctx_iss: &Context, t_init: Credits, r: &Opening) -> Vec<u8> {
    let mut w = vec![0u8; ISSUE_WITNESS_BYTES];
    w[ISSUE_WIT_OFF_R..][..R_BYTES].copy_from_slice(r);
    w[ISSUE_WIT_OFF_NF..][..NF_BYTES].copy_from_slice(nf);
    keccak800::encode_committed_states(&mut w[ISSUE_WIT_OFF_STATES..], com_state(nf, ctx_iss, t_init, r));
    w
}

// ---------------------------------------------------------------------------------------------
// Spending

const SPEND_WIT_OFF_R: usize = 0;
const SPEND_WIT_OFF_T: usize = SPEND_WIT_OFF_R + R_BYTES;
const SPEND_WIT_OFF_X: usize = SPEND_WIT_OFF_T + CREDIT_BYTES;
const SPEND_WIT_OFF_C: usize = SPEND_WIT_OFF_X + CREDIT_BYTES;
const SPEND_WIT_OFF_NF_NEXT: usize = SPEND_WIT_OFF_C + COMMITMENT_BYTES;
const SPEND_WIT_OFF_T_NEXT: usize = SPEND_WIT_OFF_NF_NEXT + NF_BYTES;
const SPEND_WIT_OFF_R_NEXT: usize = SPEND_WIT_OFF_T_NEXT + CREDIT_BYTES;
const SPEND_WIT_OFF_S: usize = SPEND_WIT_OFF_R_NEXT + R_BYTES;
const SPEND_WIT_OFF_K1: usize = SPEND_WIT_OFF_S + N;
const SPEND_WIT_OFF_K2: usize = SPEND_WIT_OFF_K1 + CREDIT_BYTES;
const SPEND_WIT_OFF_COM_STATES: usize = SPEND_WIT_OFF_K2 + CREDIT_BYTES;
const SPEND_WIT_OFF_TAG_STATES: usize = SPEND_WIT_OFF_COM_STATES + COMMITTED_STATES_BYTES;
const SPEND_WIT_OFF_COM_NEXT_STATES: usize = SPEND_WIT_OFF_TAG_STATES + COMMITTED_STATES_BYTES;
const SPEND_WITNESS_BYTES: usize = SPEND_WIT_OFF_COM_NEXT_STATES + COMMITTED_STATES_BYTES;

const SPEND_COM_TO_WIT: InputMap =
    input_map(&[(COM_OFF_R, SPEND_WIT_OFF_R, R_BYTES), (COM_OFF_T, SPEND_WIT_OFF_T, CREDIT_BYTES)]);
const SPEND_TAG_TO_WIT: InputMap = input_map(&[
    (TAG_OFF_C, SPEND_WIT_OFF_C, COMMITMENT_BYTES),
    (TAG_OFF_X, SPEND_WIT_OFF_X, CREDIT_BYTES),
]);
const SPEND_COM_NEXT_TO_WIT: InputMap = input_map(&[
    (COM_OFF_NF, SPEND_WIT_OFF_NF_NEXT, NF_BYTES),
    (COM_OFF_T, SPEND_WIT_OFF_T_NEXT, CREDIT_BYTES),
    (COM_OFF_R, SPEND_WIT_OFF_R_NEXT, R_BYTES),
]);

/// The carries k_1..k_64 of a + b, with k_(i+1) at bit i.
fn carries(a: u64, b: u64) -> u64 {
    let (mut k, mut out) = (0u64, 0u64);
    for i in 0..CREDIT_BITS {
        let (ai, bi) = ((a >> i) & 1, (b >> i) & 1);
        k = (ai & bi) | (ai & k) | (bi & k);
        out |= k << i;
    }
    out
}

/// Ripple-carry adder over committed bits, with carries from the witness. Returns 65 sum bits.
fn add_credits<Q: Qs>(
    q: &mut Q,
    a: impl Fn(&Q, usize) -> Q::Bit<1>,
    b: impl Fn(&Q, usize) -> Q::Bit<1>,
    wit_off_carries: usize,
) -> Vec<Q::Bit<1>> {
    let mut sum = Vec::with_capacity(CREDIT_BITS + 1);
    let mut k = q.bit_const::<1>(false);
    for i in 0..CREDIT_BITS {
        let (ai, bi) = (a(q, i), b(q, i));
        sum.push(q.bit_add(&q.bit_add(&ai, &bi), &k));
        let next = q.witness_bit(8 * wit_off_carries + i);
        let ab = q.bit_mul::<1, 1, 2>(&ai, &bi);
        let ak = q.bit_mul::<1, 1, 2>(&ai, &k);
        let bk = q.bit_mul::<1, 1, 2>(&bi, &k);
        let maj = q.bit_add(&q.bit_add(&ab, &ak), &bk);
        let x = q.bit_add(&maj, &q.bit_lift::<1, 2>(&next));
        let v = q.bit_to_val(&x);
        q.add_constraint::<2>(&v);
        k = next;
    }
    sum.push(k);
    sum
}

struct SpendRelation<'a> {
    pk: &'a PublicKey,
    nf: Nullifier,
    d: Credits,
    c_next: Commitment,
    ctx_iss: Context,
}

impl Relation for SpendRelation<'_> {
    const WITNESS_BYTES: usize = SPEND_WITNESS_BYTES;
    const DST: Dst = SPEND_PROOF_DST;

    fn hash_instance(&self, h: &mut Shake128) {
        h.update(self.pk.digest())
            .update(&self.nf)
            .update(&self.d.to_le_bytes())
            .update(&self.c_next)
            .update(&self.ctx_iss);
    }

    fn constraints<Q: Qs>(&self, q: &mut Q, chal2: &[u8; QS_CHALLENGE_BYTES]) {
        add_bit_constraints(q, 8 * SPEND_WITNESS_BYTES);

        let wit = |off: usize| move |q: &Q, i: usize| q.witness_bit(8 * off + i);
        let sum1 = add_credits(q, wit(SPEND_WIT_OFF_T), wit(SPEND_WIT_OFF_X), SPEND_WIT_OFF_K1);
        let d = self.d;
        let sum2 = add_credits(
            q,
            wit(SPEND_WIT_OFF_T_NEXT),
            move |q: &Q, i| q.bit_const::<1>((d >> i) & 1 == 1),
            SPEND_WIT_OFF_K2,
        );
        for (a, b) in sum1.iter().zip(&sum2) {
            let v = q.bit_to_val(&q.bit_add(a, b));
            q.add_constraint::<1>(&v);
        }

        // V1: Com() and Tag().
        let public = com_state(&self.nf, &self.ctx_iss, 0, &[0; R_BYTES]);
        let input = qs_input(q, &public, &SPEND_COM_TO_WIT);
        let com_out = qs_keccak(q, &input, SPEND_WIT_OFF_COM_STATES, 8 * COMMITMENT_BYTES);
        for (i, o) in com_out.iter().enumerate() {
            let ci = q.witness_bit(8 * SPEND_WIT_OFF_C + i);
            let x = q.bit_add(o, &q.bit_lift::<1, OUTPUT_DEGREE>(&ci));
            let v = q.bit_to_val(&x);
            q.add_constraint::<OUTPUT_DEGREE>(&v);
        }

        let input = qs_input(q, &tag_state(&[0; COMMITMENT_BYTES], 0), &SPEND_TAG_TO_WIT);
        let tag_out = qs_keccak(q, &input, SPEND_WIT_OFF_TAG_STATES, 8 * M);

        let l = Combination::new(chal2, &SPEND_COMBINE_DST);
        let s: [Q::Val<1>; N] = core::array::from_fn(|i| q.witness_byte(SPEND_WIT_OFF_S + i));
        let lp = qs_eval_combined_public_map(q, self.pk, &s, &l);
        let mut ly = q.val_const::<OUTPUT_DEGREE>(Block::ZERO);
        for k in 0..M {
            let byte = qs_byte::<Q, OUTPUT_DEGREE>(q, &tag_out, k);
            ly = q.val_add(&ly, &q.val_scale(l.coeff(k), &byte));
        }
        let x = q.val_add(&ly, &q.val_lift::<2, OUTPUT_DEGREE>(&lp));
        q.add_constraint::<OUTPUT_DEGREE>(&x);

        // V2: Com() of the updated state.
        let public = com_state(&[0; NF_BYTES], &self.ctx_iss, 0, &[0; R_BYTES]);
        let input = qs_input(q, &public, &SPEND_COM_NEXT_TO_WIT);
        let out = qs_keccak(q, &input, SPEND_WIT_OFF_COM_NEXT_STATES, 8 * COMMITMENT_BYTES);
        add_output_constraints(q, &out, &self.c_next);
    }
}

struct SpendState {
    nf: Nullifier,
    t: Credits,
    r: Opening,
    x: Credits,
    s: Preimage,
    nf_next: Nullifier,
    t_next: Credits,
    r_next: Opening,
}

fn encode_spend_witness(st: &SpendState, d: Credits, ctx_iss: &Context) -> Vec<u8> {
    let mut w = vec![0u8; SPEND_WITNESS_BYTES];
    let mut put = |off: usize, b: &[u8]| w[off..off + b.len()].copy_from_slice(b);
    let com_in = com_state(&st.nf, ctx_iss, st.t, &st.r);
    let c: Commitment = keccak800::keccak_p800(com_in)[..COMMITMENT_BYTES].try_into().unwrap();
    put(SPEND_WIT_OFF_R, &st.r);
    put(SPEND_WIT_OFF_T, &st.t.to_le_bytes());
    put(SPEND_WIT_OFF_X, &st.x.to_le_bytes());
    put(SPEND_WIT_OFF_C, &c);
    put(SPEND_WIT_OFF_NF_NEXT, &st.nf_next);
    put(SPEND_WIT_OFF_T_NEXT, &st.t_next.to_le_bytes());
    put(SPEND_WIT_OFF_R_NEXT, &st.r_next);
    put(SPEND_WIT_OFF_S, &st.s);
    put(SPEND_WIT_OFF_K1, &carries(st.t, st.x).to_le_bytes());
    put(SPEND_WIT_OFF_K2, &carries(st.t_next, d).to_le_bytes());
    keccak800::encode_committed_states(&mut w[SPEND_WIT_OFF_COM_STATES..], com_in);
    keccak800::encode_committed_states(&mut w[SPEND_WIT_OFF_TAG_STATES..], tag_state(&c, st.x));
    keccak800::encode_committed_states(
        &mut w[SPEND_WIT_OFF_COM_NEXT_STATES..],
        com_state(&st.nf_next, ctx_iss, st.t_next, &st.r_next),
    );
    w
}

pub const ISSUE_PROOF_BYTES: usize = voleith::proof_bytes::<IssueRelation>();
pub const ISSUE_REQUEST_BYTES: usize = COMMITMENT_BYTES + ISSUE_PROOF_BYTES;
pub const SPEND_PROOF_BYTES: usize = voleith::proof_bytes::<SpendRelation>();
pub const SPEND_REQUEST_BYTES: usize = NF_BYTES + CREDIT_BYTES + COMMITMENT_BYTES + SPEND_PROOF_BYTES;
pub const SPEND_RESPONSE_BYTES: usize = CREDIT_BYTES + N;
const _: () = assert!(ISSUE_PROOF_BYTES == 7000 && SPEND_PROOF_BYTES == 17319);

const REQ_OFF_D: usize = NF_BYTES;
const REQ_OFF_C_NEXT: usize = REQ_OFF_D + CREDIT_BYTES;
const REQ_OFF_PROOF: usize = REQ_OFF_C_NEXT + COMMITMENT_BYTES;

// ---------------------------------------------------------------------------------------------
// API

fn random_seed() -> Seed {
    let mut s = [0u8; SEED_BYTES];
    getrandom::fill(&mut s).expect("OS random number generator failed");
    s
}

/// (nf, r, rho) from a seed.
fn expand_seed(dst: &[u8], seed: &Seed) -> (Nullifier, Opening, [u8; 16]) {
    let mut h = Shake128::new();
    h.update(dst).update(seed);
    let (mut nf, mut r, mut rho) = ([0u8; NF_BYTES], [0u8; R_BYTES], [0u8; 16]);
    h.squeeze(&mut nf);
    h.squeeze(&mut r);
    h.squeeze(&mut rho);
    (nf, r, rho)
}

#[derive(Clone)]
pub struct Token {
    nf: Nullifier,
    t: Credits,
    r: Opening,
    x: Credits,
    s: Preimage,
}

#[derive(Clone)]
pub struct PendingToken {
    nf: Nullifier,
    r: Opening,
    t_init: Credits,
    c: Commitment,
}

#[derive(Clone)]
pub struct PendingSpend {
    nf: Nullifier,
    t: Credits,
    r: Opening,
    c: Commitment,
}

pub struct SpendResponseResult {
    pub response: Vec<u8>,
    pub nf: Nullifier,
    pub d: Credits,
}

pub fn issue_request(t_init: Credits, ctx_iss: &Context) -> Result<(PendingToken, Vec<u8>), Error> {
    issue_request_with_seed(t_init, ctx_iss, &random_seed())
}

pub fn issue_request_with_seed(
    t_init: Credits,
    ctx_iss: &Context,
    seed: &Seed,
) -> Result<(PendingToken, Vec<u8>), Error> {
    if t_init == 0 {
        return Err(Error::ZeroInitialCredit);
    }
    let (nf, r, rho) = expand_seed(&ISSUE_SEED_DST, seed);
    let c = commit(&nf, ctx_iss, t_init, &r);
    let w = encode_issue_witness(&nf, ctx_iss, t_init, &r);
    let proof = voleith::prove(&IssueRelation { c, t_init, ctx_iss: *ctx_iss }, &w, &rho);
    let mut req = Vec::with_capacity(ISSUE_REQUEST_BYTES);
    req.extend_from_slice(&c);
    req.extend_from_slice(&proof);
    Ok((PendingToken { nf, r, t_init, c }, req))
}

pub fn issue_response(
    sk: &SecretKey,
    request: &[u8],
    t_init: Credits,
    ctx_iss: &Context,
) -> Result<Option<IssueResponse>, Error> {
    if t_init == 0 {
        return Err(Error::ZeroInitialCredit);
    }
    if request.len() != ISSUE_REQUEST_BYTES {
        return Ok(None);
    }
    let c: Commitment = request[..COMMITMENT_BYTES].try_into().unwrap();
    if !voleith::verify(&IssueRelation { c, t_init, ctx_iss: *ctx_iss }, &request[COMMITMENT_BYTES..]) {
        return Ok(None);
    }
    Ok(sk.derive_preimage(&tag(&c, 0)).ok())
}

impl PendingToken {
    pub fn finalize_issue(self, pk: &PublicKey, response: &IssueResponse) -> Option<Token> {
        (pk.eval(response) == tag(&self.c, 0)).then_some(Token {
            nf: self.nf,
            t: self.t_init,
            r: self.r,
            x: 0,
            s: *response,
        })
    }
}

impl Token {
    pub fn credit(&self) -> Credits {
        self.t
    }

    pub fn refund(&self) -> Credits {
        self.x
    }

    pub fn spend_request(self, pk: &PublicKey, d: Credits, ctx_iss: &Context) -> Result<(PendingSpend, Vec<u8>), Error> {
        self.spend_request_with_seed(pk, d, ctx_iss, &random_seed())
    }

    pub fn spend_request_with_seed(
        self,
        pk: &PublicKey,
        d: Credits,
        ctx_iss: &Context,
        seed: &Seed,
    ) -> Result<(PendingSpend, Vec<u8>), Error> {
        if pk.eval(&self.s) != tag(&commit(&self.nf, ctx_iss, self.t, &self.r), self.x) {
            return Err(Error::WrongIssuer);
        }
        let (lo, overflow) = self.t.overflowing_add(self.x);
        if !overflow && d > lo {
            return Err(Error::InsufficientBalance);
        }
        if overflow && d <= lo {
            return Err(Error::ChangeOverflow);
        }
        let t_next = lo.wrapping_sub(d);

        let (nf_next, r_next, rho) = expand_seed(&SPEND_SEED_DST, seed);
        let c_next = commit(&nf_next, ctx_iss, t_next, &r_next);
        let st = SpendState { nf: self.nf, t: self.t, r: self.r, x: self.x, s: self.s, nf_next, t_next, r_next };
        let w = encode_spend_witness(&st, d, ctx_iss);
        let rel = SpendRelation { pk, nf: self.nf, d, c_next, ctx_iss: *ctx_iss };
        let proof = voleith::prove(&rel, &w, &rho);

        let mut req = Vec::with_capacity(SPEND_REQUEST_BYTES);
        req.extend_from_slice(&self.nf);
        req.extend_from_slice(&d.to_le_bytes());
        req.extend_from_slice(&c_next);
        req.extend_from_slice(&proof);
        Ok((PendingSpend { nf: nf_next, t: t_next, r: r_next, c: c_next }, req))
    }
}

pub fn spend_response(sk: &SecretKey, request: &[u8], ctx_iss: &Context, refund: Credits) -> Option<SpendResponseResult> {
    if request.len() != SPEND_REQUEST_BYTES {
        return None;
    }
    let nf: Nullifier = request[..NF_BYTES].try_into().unwrap();
    let d = u64::from_le_bytes(request[REQ_OFF_D..REQ_OFF_C_NEXT].try_into().unwrap());
    let c_next: Commitment = request[REQ_OFF_C_NEXT..REQ_OFF_PROOF].try_into().unwrap();
    let rel = SpendRelation { pk: sk.expanded_public_key(), nf, d, c_next, ctx_iss: *ctx_iss };
    if !voleith::verify(&rel, &request[REQ_OFF_PROOF..]) {
        return None;
    }
    let s = sk.derive_preimage(&tag(&c_next, refund)).ok()?;
    let mut response = Vec::with_capacity(SPEND_RESPONSE_BYTES);
    response.extend_from_slice(&refund.to_le_bytes());
    response.extend_from_slice(&s);
    Some(SpendResponseResult { response, nf, d })
}

impl PendingSpend {
    pub fn finalize_spend(self, pk: &PublicKey, response: &[u8]) -> Option<Token> {
        if response.len() != SPEND_RESPONSE_BYTES {
            return None;
        }
        let x = u64::from_le_bytes(response[..CREDIT_BYTES].try_into().unwrap());
        let s: Preimage = response[CREDIT_BYTES..].try_into().unwrap();
        (pk.eval(&s) == tag(&self.c, x)).then_some(Token { nf: self.nf, t: self.t, r: self.r, x, s })
    }
}

/// Internals exposed for known-answer tests.
#[doc(hidden)]
pub mod testing {
    use super::*;

    pub fn pending(t: &PendingToken) -> (Nullifier, [u8; 16], Commitment) {
        (t.nf, t.r, t.c)
    }
    pub fn issue_witness(t: &PendingToken, ctx_iss: &Context) -> Vec<u8> {
        encode_issue_witness(&t.nf, ctx_iss, t.t_init, &t.r)
    }
    pub fn token_nf(t: &Token) -> Nullifier {
        t.nf
    }
    pub fn pending_spend(p: &PendingSpend) -> (Nullifier, Credits, [u8; 16]) {
        (p.nf, p.t, p.r)
    }
    pub fn spend_witness(tok: &Token, p: &PendingSpend, d: Credits, ctx_iss: &Context) -> Vec<u8> {
        let st = SpendState {
            nf: tok.nf,
            t: tok.t,
            r: tok.r,
            x: tok.x,
            s: tok.s,
            nf_next: p.nf,
            t_next: p.t,
            r_next: p.r,
        };
        encode_spend_witness(&st, d, ctx_iss)
    }
}
