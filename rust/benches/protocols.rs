//! Benchmarks mirroring tests/ihat/bench_ihat.cpp and tests/act/bench_act.cpp.

use criterion::{BenchmarkId, Criterion, criterion_group, criterion_main};
use std::hint::black_box;
use std::time::Duration;
use vole_mole::uov::{PublicKey, SecretKey};
use vole_mole::{act, ihat};

fn filled<const N: usize>(start: u8) -> [u8; N] {
    core::array::from_fn(|i| start.wrapping_add(i as u8))
}

fn seed_from_counter(i: u64) -> [u8; 32] {
    let mut s = [0u8; 32];
    s[..8].copy_from_slice(&i.to_le_bytes());
    s
}

fn key_pair() -> SecretKey {
    SecretKey::new(&filled(0x60)).unwrap()
}

fn distinct_public_key(u: usize) -> PublicKey {
    let mut b: [u8; 32] = filled(0x80);
    b[0] = u as u8;
    b[1] = (u >> 8) as u8;
    PublicKey::new(SecretKey::new(&b).unwrap().public_key_bytes())
}

fn bench_ihat(c: &mut Criterion) {
    let ctx_iss: ihat::Context = filled(0x10);
    let ctx_red: ihat::Context = filled(0x20);
    let cd: ihat::ChallengeDigest = filled(0x70);
    let sk = key_pair();
    let pk = sk.expanded_public_key();
    let others: Vec<PublicKey> = (0..ihat::MAX_ANCHORS - 1).map(distinct_public_key).collect();
    let anchor_set = |n: usize| ihat::AnchorSet::new(others[..n - 1].iter().chain([pk])).unwrap();

    let mut g = c.benchmark_group("ihat");
    g.sample_size(30).measurement_time(Duration::from_secs(3));

    let mut i = 0u64;
    g.bench_function("IssueRequest", |b| {
        b.iter(|| {
            i += 1;
            black_box(ihat::issue_request_with_seed(&ctx_iss, &ctx_red, &seed_from_counter(i)))
        })
    });
    let (pending, req) = ihat::issue_request_with_seed(&ctx_iss, &ctx_red, &seed_from_counter(0));
    g.bench_function("IssueResponse", |b| {
        b.iter(|| black_box(ihat::issue_response(&sk, &req, &ctx_iss).unwrap()))
    });
    let resp = ihat::issue_response(&sk, &req, &ctx_iss).unwrap();
    g.bench_function("FinalizeIssue", |b| {
        b.iter(|| black_box(pending.clone().finalize_issue(pk, &resp).unwrap()))
    });

    let token = {
        let (p, r) = ihat::issue_request_with_seed(&ctx_iss, &ctx_red, &[0; 32]);
        p.finalize_issue(pk, &ihat::issue_response(&sk, &r, &ctx_iss).unwrap()).unwrap()
    };
    for n in [1, 8, ihat::MAX_ANCHORS] {
        let anchors = anchor_set(n);
        let mut i = 0u64;
        g.bench_with_input(BenchmarkId::new("RedeemRequest", n), &n, |b, _| {
            b.iter(|| {
                i += 1;
                black_box(
                    token
                        .clone()
                        .redeem_request_with_seed(&anchors, &ctx_iss, &ctx_red, &cd, &seed_from_counter(i))
                        .unwrap(),
                )
            })
        });
        let rreq = token
            .clone()
            .redeem_request_with_seed(&anchors, &ctx_iss, &ctx_red, &cd, &seed_from_counter(0))
            .unwrap();
        g.bench_with_input(BenchmarkId::new("FinalizeRedeem", n), &n, |b, _| {
            b.iter(|| black_box(ihat::finalize_redeem(&anchors, &rreq, &ctx_iss, &ctx_red, &cd).unwrap()))
        });
    }

    // Unbound tokens.
    let mut i = 0u64;
    g.bench_function("UnboundIssueRequest", |b| {
        b.iter(|| {
            i += 1;
            black_box(ihat::unbound_issue_request_with_seed(&ctx_iss, &seed_from_counter(i)))
        })
    });
    let (pending, req) = ihat::unbound_issue_request_with_seed(&ctx_iss, &seed_from_counter(0));
    g.bench_function("UnboundIssueResponse", |b| {
        b.iter(|| black_box(ihat::unbound_issue_response(&sk, &req, &ctx_iss).unwrap()))
    });
    let resp = ihat::unbound_issue_response(&sk, &req, &ctx_iss).unwrap();
    let token = pending.finalize_issue(pk, &resp).unwrap();
    for n in [1, 8, ihat::MAX_ANCHORS] {
        let anchors = anchor_set(n);
        let mut i = 0u64;
        g.bench_with_input(BenchmarkId::new("UnboundRedeemRequest", n), &n, |b, _| {
            b.iter(|| {
                i += 1;
                black_box(
                    token
                        .redeem_request_with_seed(&anchors, &ctx_iss, &ctx_red, &cd, &seed_from_counter(i))
                        .unwrap(),
                )
            })
        });
        let rreq = token
            .redeem_request_with_seed(&anchors, &ctx_iss, &ctx_red, &cd, &seed_from_counter(0))
            .unwrap();
        g.bench_with_input(BenchmarkId::new("UnboundFinalizeRedeem", n), &n, |b, _| {
            b.iter(|| black_box(ihat::unbound_finalize_redeem(&anchors, &rreq, &ctx_iss, &ctx_red, &cd).unwrap()))
        });
    }
    g.finish();
}

fn bench_act(c: &mut Criterion) {
    const T_INIT: u64 = 1000;
    const D: u64 = 1;
    let ctx_iss: act::Context = filled(0x10);
    let sk = key_pair();
    let pk = sk.expanded_public_key();

    let mut g = c.benchmark_group("act");
    g.sample_size(30).measurement_time(Duration::from_secs(3));

    let mut i = 0u64;
    g.bench_function("IssueRequest", |b| {
        b.iter(|| {
            i += 1;
            black_box(act::issue_request_with_seed(T_INIT, &ctx_iss, &seed_from_counter(i)).unwrap())
        })
    });
    let (pending, req) = act::issue_request_with_seed(T_INIT, &ctx_iss, &seed_from_counter(0)).unwrap();
    g.bench_function("IssueResponse", |b| {
        b.iter(|| black_box(act::issue_response(&sk, &req, T_INIT, &ctx_iss).unwrap().unwrap()))
    });
    let resp = act::issue_response(&sk, &req, T_INIT, &ctx_iss).unwrap().unwrap();
    g.bench_function("FinalizeIssue", |b| {
        b.iter(|| black_box(pending.clone().finalize_issue(pk, &resp).unwrap()))
    });

    let token = {
        let (p, r) = act::issue_request_with_seed(T_INIT, &ctx_iss, &[0; 32]).unwrap();
        p.finalize_issue(pk, &act::issue_response(&sk, &r, T_INIT, &ctx_iss).unwrap().unwrap()).unwrap()
    };
    let mut i = 0u64;
    g.bench_function("SpendRequest", |b| {
        b.iter(|| {
            i += 1;
            black_box(token.clone().spend_request_with_seed(pk, D, &ctx_iss, &seed_from_counter(i)).unwrap())
        })
    });
    let (pend, sreq) = token.clone().spend_request_with_seed(pk, D, &ctx_iss, &seed_from_counter(0)).unwrap();
    g.bench_function("SpendResponse", |b| {
        b.iter(|| black_box(act::spend_response(&sk, &sreq, &ctx_iss, 0).unwrap()))
    });
    let sresp = act::spend_response(&sk, &sreq, &ctx_iss, 0).unwrap().response;
    g.bench_function("FinalizeSpend", |b| {
        b.iter(|| black_box(pend.clone().finalize_spend(pk, &sresp).unwrap()))
    });
    g.finish();
}

criterion_group!(benches, bench_ihat, bench_act);
criterion_main!(benches);
