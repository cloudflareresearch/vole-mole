mod common;

use common::*;
use vole_mole::ihat::{self, AnchorSet, testing};
use vole_mole::uov::{M, SecretKey};

fn keys(r: &Record) -> Vec<SecretKey> {
    all(r, "anchor_sk")
        .iter()
        .map(|h| SecretKey::new(&arr(h)).unwrap())
        .collect()
}

#[test]
fn ihat_kat() {
    let recs = records(include_str!("../testdata/ihat_kat.txt"));
    assert_eq!(recs.len(), 3);
    for (case, r) in recs.iter().enumerate() {
        let seed = arr(get(r, "issue_seed"));
        let redeem_seed = arr(get(r, "redeem_seed"));
        let ctx_iss = arr(get(r, "ctx_iss"));
        let ctx_red = arr(get(r, "ctx_red"));
        let cd = arr(get(r, "challenge_digest"));
        let issuer: usize = get(r, "issuer").parse().unwrap();
        let sks = keys(r);
        assert_eq!(sks.len(), get(r, "anchor_count").parse::<usize>().unwrap());
        let anchors = AnchorSet::new(sks.iter().map(|sk| sk.expanded_public_key())).unwrap();

        let (pending, req) = ihat::issue_request_with_seed(&ctx_iss, &ctx_red, &seed);
        let (nf, opening, t) = testing::pending_nf_r(&pending);
        assert_eq!(nf.to_vec(), unhex(get(r, "nf")), "case {case}: nf");
        assert_eq!(opening.to_vec(), unhex(get(r, "r")), "case {case}: r");
        assert_eq!(
            t.to_vec(),
            unhex(get(r, "commitment")),
            "case {case}: commitment"
        );
        let w = testing::issue_witness(&pending, &ctx_iss, &ctx_red);
        assert_eq!(
            w,
            unhex(get(r, "issue_witness")),
            "case {case}: issue_witness"
        );
        check_request(
            &format!("case {case}: issue_request"),
            &req,
            &unhex(get(r, "issue_request")),
            M,
            w.len(),
        );

        let resp =
            ihat::issue_response(&sks[issuer], &req, &ctx_iss).expect("issue proof verifies");
        assert_eq!(
            resp.to_vec(),
            unhex(get(r, "issue_response")),
            "case {case}: issue_response"
        );
        let token = pending
            .finalize_issue(sks[issuer].expanded_public_key(), &resp)
            .unwrap();

        let rw = testing::redeem_witness(&token, &ctx_iss, &ctx_red, issuer);
        assert_eq!(
            rw,
            unhex(get(r, "redeem_witness")),
            "case {case}: redeem_witness"
        );
        let rreq = token
            .redeem_request_with_seed(&anchors, &ctx_iss, &ctx_red, &cd, &redeem_seed)
            .unwrap();
        check_request(
            &format!("case {case}: redeem_request"),
            &rreq,
            &unhex(get(r, "redeem_request")),
            ihat::NF_BYTES,
            rw.len(),
        );
        let got = ihat::finalize_redeem(&anchors, &rreq, &ctx_iss, &ctx_red, &cd)
            .expect("redeem proof verifies");
        assert_eq!(got.to_vec(), unhex(get(r, "redeemed_nf")));
        // A different challenge digest must fail.
        let mut cd2 = cd;
        cd2[0] ^= 1;
        assert!(ihat::finalize_redeem(&anchors, &rreq, &ctx_iss, &ctx_red, &cd2).is_none());
    }
}

#[test]
fn unbound_ihat_kat() {
    let recs = records(include_str!("../testdata/unbound_ihat_kat.txt"));
    assert_eq!(recs.len(), 3);
    for (case, r) in recs.iter().enumerate() {
        let seed = arr(get(r, "issue_seed"));
        let ctx_iss = arr(get(r, "ctx_iss"));
        let issuer: usize = get(r, "issuer").parse().unwrap();
        let sks = keys(r);
        let anchors = AnchorSet::new(sks.iter().map(|sk| sk.expanded_public_key())).unwrap();

        let (pending, req) = ihat::unbound_issue_request_with_seed(&ctx_iss, &seed);
        let (nf_key, opening, t) = testing::pending_unbound(&pending);
        assert_eq!(
            nf_key.to_vec(),
            unhex(get(r, "nf_key")),
            "case {case}: nf_key"
        );
        assert_eq!(opening.to_vec(), unhex(get(r, "r")), "case {case}: r");
        assert_eq!(
            t.to_vec(),
            unhex(get(r, "commitment")),
            "case {case}: commitment"
        );
        let w = testing::unbound_issue_witness(&pending, &ctx_iss);
        assert_eq!(
            w,
            unhex(get(r, "issue_witness")),
            "case {case}: issue_witness"
        );
        check_request(
            &format!("case {case}: issue_request"),
            &req,
            &unhex(get(r, "issue_request")),
            M,
            w.len(),
        );

        let resp = ihat::unbound_issue_response(&sks[issuer], &req, &ctx_iss)
            .expect("issue proof verifies");
        assert_eq!(
            resp.to_vec(),
            unhex(get(r, "issue_response")),
            "case {case}: issue_response"
        );
        let token = pending
            .finalize_issue(sks[issuer].expanded_public_key(), &resp)
            .unwrap();

        let n: usize = get(r, "redemption_count").parse().unwrap();
        let seeds = all(r, "redeem_seed");
        let ctxs = all(r, "ctx_red");
        let cds = all(r, "challenge_digest");
        let nfs = all(r, "nf");
        let wits = all(r, "redeem_witness");
        let reqs = all(r, "redeem_request");
        assert_eq!(reqs.len(), n);
        for j in 0..n {
            let ctx_red = arr(ctxs[j]);
            let cd = arr(cds[j]);
            assert_eq!(testing::derive_nf(&token, &ctx_red).to_vec(), unhex(nfs[j]));
            let rw = testing::unbound_redeem_witness(&token, &ctx_iss, &ctx_red, issuer);
            assert_eq!(rw, unhex(wits[j]), "case {case}.{j}: redeem_witness");
            let rreq = token
                .redeem_request_with_seed(&anchors, &ctx_iss, &ctx_red, &cd, &arr(seeds[j]))
                .unwrap();
            check_request(
                &format!("case {case}.{j}: redeem_request"),
                &rreq,
                &unhex(reqs[j]),
                ihat::NF_BYTES,
                rw.len(),
            );
            let got = ihat::unbound_finalize_redeem(&anchors, &rreq, &ctx_iss, &ctx_red, &cd)
                .expect("verifies");
            assert_eq!(got.to_vec(), unhex(nfs[j]));
        }
    }
}
