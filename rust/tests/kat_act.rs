mod common;

use common::*;
use vole_mole::act::{self, testing};
use vole_mole::uov::SecretKey;

#[test]
fn act_kat() {
    let recs = records(include_str!("../testdata/act_kat.txt"));
    let mut it = recs.iter();
    let mut cases = 0;
    while let Some(r) = it.next() {
        let seed = arr(get(r, "issue_seed"));
        let ctx_iss = arr(get(r, "ctx_iss"));
        let t_init: u64 = get(r, "t_init").parse().unwrap();
        let sk = SecretKey::new(&arr(get(r, "issuer_sk"))).unwrap();
        let pk = sk.expanded_public_key();

        let (pending, req) = act::issue_request_with_seed(t_init, &ctx_iss, &seed).unwrap();
        let (nf, opening, c) = testing::pending(&pending);
        assert_eq!(nf.to_vec(), unhex(get(r, "nf")), "case {cases}: nf");
        assert_eq!(opening.to_vec(), unhex(get(r, "r")), "case {cases}: r");
        assert_eq!(
            c.to_vec(),
            unhex(get(r, "commitment")),
            "case {cases}: commitment"
        );
        let w = testing::issue_witness(&pending, &ctx_iss);
        assert_eq!(
            w,
            unhex(get(r, "issue_witness")),
            "case {cases}: issue_witness"
        );
        check_request(
            &format!("case {cases}: issue_request"),
            &req,
            &unhex(get(r, "issue_request")),
            act::COMMITMENT_BYTES,
            w.len(),
        );
        let resp = act::issue_response(&sk, &req, t_init, &ctx_iss)
            .unwrap()
            .expect("issue proof verifies");
        assert_eq!(
            resp.to_vec(),
            unhex(get(r, "issue_response")),
            "case {cases}: issue_response"
        );
        let mut token = pending.finalize_issue(pk, &resp).unwrap();

        let n: usize = get(r, "spend_count").parse().unwrap();
        for j in 0..n {
            let s = it.next().unwrap();
            let d: u64 = get(s, "d").parse().unwrap();
            let refund: u64 = get(s, "refund").parse().unwrap();
            let prev = token.clone();
            let (pend, sreq) = token
                .spend_request_with_seed(pk, d, &ctx_iss, &arr(get(s, "spend_seed")))
                .unwrap();
            let (nf_next, t_next, r_next) = testing::pending_spend(&pend);
            assert_eq!(
                nf_next.to_vec(),
                unhex(get(s, "nf_next")),
                "case {cases}.{j}: nf_next"
            );
            assert_eq!(t_next, get(s, "t_next").parse::<u64>().unwrap());
            assert_eq!(r_next.to_vec(), unhex(get(s, "r_next")));
            let sw = testing::spend_witness(&prev, &pend, d, &ctx_iss);
            assert_eq!(
                sw,
                unhex(get(s, "spend_witness")),
                "case {cases}.{j}: spend_witness"
            );
            check_request(
                &format!("case {cases}.{j}: spend_request"),
                &sreq,
                &unhex(get(s, "spend_request")),
                act::NF_BYTES + act::CREDIT_BYTES + act::COMMITMENT_BYTES,
                sw.len(),
            );
            let sr =
                act::spend_response(&sk, &sreq, &ctx_iss, refund).expect("spend proof verifies");
            assert_eq!(sr.nf, testing::token_nf(&prev));
            assert_eq!(sr.d, d);
            assert_eq!(
                sr.response,
                unhex(get(s, "spend_response")),
                "case {cases}.{j}: spend_response"
            );
            token = pend.finalize_spend(pk, &sr.response).unwrap();
            assert_eq!(token.credit(), t_next);
            assert_eq!(token.refund(), refund);
        }
        cases += 1;
    }
    assert_eq!(cases, 3);
}
