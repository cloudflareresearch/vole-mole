#![allow(dead_code)]

pub type Record = Vec<(String, String)>;

/// Parse a KAT file into records of key/value lines separated by blank lines.
pub fn records(text: &str) -> Vec<Record> {
    let mut out = vec![];
    let mut cur: Record = vec![];
    for line in text.lines() {
        if line.starts_with('#') {
            continue;
        }
        if line.trim().is_empty() {
            if !cur.is_empty() {
                out.push(std::mem::take(&mut cur));
            }
            continue;
        }
        let (k, v) = line.split_once(' ').unwrap_or((line, ""));
        cur.push((k.to_string(), v.to_string()));
    }
    if !cur.is_empty() {
        out.push(cur);
    }
    out
}

pub fn unhex(s: &str) -> Vec<u8> {
    assert!(s.len() % 2 == 0);
    (0..s.len()).step_by(2).map(|i| u8::from_str_radix(&s[i..i + 2], 16).unwrap()).collect()
}

pub fn get<'a>(r: &'a Record, k: &str) -> &'a str {
    &r.iter().find(|(key, _)| key == k).unwrap_or_else(|| panic!("missing {k}")).1
}

pub fn all<'a>(r: &'a Record, k: &str) -> Vec<&'a str> {
    r.iter().filter(|(key, _)| key == k).map(|(_, v)| v.as_str()).collect()
}

pub fn arr<const N: usize>(s: &str) -> [u8; N] {
    unhex(s).try_into().unwrap()
}

/// Proof field names and offsets for a witness length, for locating mismatches.
fn field(witness_bytes: usize, off: usize) -> String {
    let p = vole_mole::params::Params::new(witness_bytes);
    let fields = [
        ("corrections", p.off_corrections),
        ("cmult", p.off_cmult),
        ("vole_check", p.off_vole_check),
        ("correction", p.off_correction),
        ("qs_proof", p.off_qs_proof),
        ("open", p.off_open),
        ("delta", p.off_delta),
        ("iv_pre", p.off_iv_pre),
        ("ctr", p.off_ctr),
    ];
    let (name, start) = fields.iter().rev().find(|(_, s)| *s <= off).unwrap();
    format!("{name}+{}", off - start)
}

/// Assert that a request (prefix || proof) matches, naming the first differing proof field.
pub fn check_request(what: &str, got: &[u8], want: &[u8], prefix: usize, witness_bytes: usize) {
    assert_eq!(got.len(), want.len(), "{what}: length");
    if let Some(i) = got.iter().zip(want).position(|(a, b)| a != b) {
        let loc = if i < prefix { format!("prefix+{i}") } else { field(witness_bytes, i - prefix) };
        panic!("{what}: first difference at byte {i} ({loc})");
    }
}
