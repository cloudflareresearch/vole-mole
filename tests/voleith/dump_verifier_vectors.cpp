// Dump test vectors for the executable Lean model of the VOLEitH verifier (see
// lean/VoleMole/Verifier/, lean/docs/verifier-plan.md and `lake exe verifier_vectors` in lean/).
//
// Usage: dump_verifier_vectors OUTPUT_DIR (normally lean/vectors). Run explicitly, never as part of
// the test suite. All inputs are deterministic, so rerunning it reproduces the same files.
//
// File format (as tests/arith/dump_arith_vectors.cpp): lines `KEY VALUE` separated by a single
// space; blank lines and lines starting with '#' are comments; a record is `record GROUP NAME`,
// then KEY VALUE lines, then `end`. Byte strings are lowercase hex (`-` if empty), numbers decimal.
//
// verifier_prims.txt: the primitives.
//
//   record aes NAME      key, pt, ct = AES-128_key(pt) (aes_keygen_ecb), rk = the 11 round keys.
//   record prg NAME      key, iv, tweak, counter, out: aes_ctr_prg<s128>::init with one key and 4
//                        blocks starting at `counter` (block j = AES_key(iv + (counter + j, 0, 0,
//                        tweak)), lane-wise 32-bit addition).
//   record shake NAME    secpar, input, out (hash_state: init(secpar), update(input) in pieces,
//                        finalize). Records named x4_* are hash_state_x4 outputs (lane 0 of
//                        update_4 on four distinct inputs), which must equal hash_state's.
//
// verifier_bavc.txt: the one-tree BAVC of the Moussaka issuance parameters (FAEST-EM-128f: s128,
// tau = 17, delta_bits = 120, AES-CTR tree PRG and leaf hash, T_OPEN = 105), for a fixed seed and
// iv. Leaves are listed in "spec order": leaf j of small VOLE i (concatenated over i = 0..16, the
// first vector having 2^8 leaves and the others 2^7), i.e., with faest-arch-opt's in-memory
// permutation (vole_permute_key_index_inv of j ^ Delta_i) undone.
//
//   record bavc commit   seed, iv, tree (all COMMIT_NODES nodes, heap order: children of node n
//                        are 2n + 1 and 2n + 2), leaves, hashed_leaves (32 bytes per leaf),
//                        check (hash_hashed_leaves, the VOLE commitment check value).
//   record bavc open     delta (16 bytes; the first SHAKE-derived candidate whose opening fits),
//                        opening (OPEN_SIZE bytes), leaves (the verifier's: the hidden leaf
//                        j = Delta_i of each vector is zero), hashed_leaves, check.
//
// verifier_kat.txt: intermediate values of the verification of the first Moussaka issuance KAT
// proof (tests/moussaka/moussaka_kat.txt, record 0, `issue_request` = t || proof), following
// voleith_vole_reconstruct and voleith_verify_commit step by step.
//
//   record kat moussaka_issue_0
//     t, ctx_iss, proof    the instance and the proof
//     mu                   H_2^0(t || ctx_iss || DST || 8), 32 bytes
//     iv                   H_4(iv_pre || mu || 4), 16 bytes
//     leaves, hashed_leaves  the BAVC verification of the opening at Delta (spec order, as above)
//     q_columns            the small-VOLE keys before the CRT lift: column c (0 <= c < 128) is
//                          VOLE_COL_STRIDE bytes, row r is bit r % 8 of byte r / 8 of the column
//     vole_commit_check    hash_hashed_leaves
//     q_rows               the VOLE_CORRECTION_ROWS rows of q after the CRT lift and the
//                          transpose, before the correction d (16 bytes each)
//     q_mask               the CRT_NUM_MASK mask rows (16 bytes each)
//     delta_lifted         crt_lift_delta(Delta)
//     chal1, chal2         H_2^1 and H_2^2
//     qs_check             the verifier's QuickSilver check value
//     delta_check          H_2^3(chal2 || qs_check || qs_proof || ctr || 11), compared with Delta
//     accept               1 if voleith_verify accepts

#include "vole_mole/moussaka.hpp"

#include "moussaka/commit.hpp" // internal
#include "moussaka/issue.hpp"  // internal
#include "voleith.hpp"         // internal

#include "aes.hpp"                        // from faest-arch-opt
#include "aes_defs.hpp"                   // from faest-arch-opt
#include "block.hpp"                      // from faest-arch-opt
#include "crt_vole_helpers.inc"           // from faest-arch-opt
#include "faest_sig.hpp"                  // from faest-arch-opt
#include "hash.hpp"                       // from faest-arch-opt
#include "kos_vole_check.hpp"             // from faest-arch-opt
#include "parameters.hpp"                 // from faest-arch-opt
#include "prgs.hpp"                       // from faest-arch-opt
#include "quicksilver.hpp"                // from faest-arch-opt
#include "util.hpp"                       // from faest-arch-opt
#include "vole_commit.hpp"                // from faest-arch-opt
#include "vole_commit.inc"                // from faest-arch-opt
#include "vole_key_index_permutation.hpp" // from faest-arch-opt

#include <algorithm>
#include <array>
#include <cstddef>
#include <cstdint>
#include <cstdlib>
#include <cstring>
#include <fstream>
#include <iostream>
#include <optional>
#include <span>
#include <sstream>
#include <string>
#include <string_view>
#include <utility>
#include <vector>

namespace {

using namespace vole_mole;
using P = moussaka::detail::IssueParams;
using CP = P::CONSTS;
using VC = CP::VEC_COM;
using BAVC = P::bavc_t;
constexpr auto S = faest::secpar::s128;

std::string hex(std::span<const uint8_t> bytes) {
    if (bytes.empty()) {
        return "-";
    }
    static constexpr std::string_view DIGITS = "0123456789abcdef";
    std::string out;
    out.reserve(2 * bytes.size());
    for (const uint8_t b : bytes) {
        out.push_back(DIGITS[b >> 4]);
        out.push_back(DIGITS[b & 15]);
    }
    return out;
}

template <typename T> std::span<const uint8_t> bytes_of(const T* p, size_t n) {
    return {reinterpret_cast<const uint8_t*>(p), n * sizeof(T)};
}

std::vector<uint8_t> unhex(const std::string& s) {
    std::vector<uint8_t> out(s.size() / 2);
    for (size_t i = 0; i < out.size(); ++i) {
        out[i] = static_cast<uint8_t>(std::stoi(s.substr(2 * i, 2), nullptr, 16));
    }
    return out;
}

// Deterministic test bytes: SHAKE128(label), n bytes.
std::vector<uint8_t> test_bytes(const std::string& label, size_t n) {
    std::vector<uint8_t> out(n);
    faest::hash_state h;
    h.init(S);
    h.update(label.data(), label.size());
    h.finalize(out.data(), out.size());
    return out;
}

faest::block128 load_block(std::span<const uint8_t> b) { return faest::block128::load(b.data()); }

void dump_aes(std::ostream& out, const std::string& name, std::span<const uint8_t, 16> key,
              std::span<const uint8_t, 16> pt) {
    // E_key(pt) is the first block of aes_ctr_prg with iv = pt, tweak = 0 and counter = 0.
    using PRG = faest::aes_ctr_prg<S>;
    const faest::block128 k = faest::block128::load(key.data());
    faest::aes_round_keys<S> rk;
    faest::aes_keygen<S>(&rk, k);
    PRG::expanded_key_t expanded;
    faest::block128 data;
    PRG::init<1, 1>(&k, &expanded, faest::block128::load(pt.data()), uint32_t{0}, uint32_t{0},
                    &data);
    out << "record aes " << name << "\n";
    out << "key " << hex(key) << "\n";
    out << "pt " << hex(pt) << "\n";
    out << "ct " << hex(bytes_of(&data, 1)) << "\n";
    out << "rk " << hex(bytes_of(&rk.keys[0], std::size(rk.keys))) << "\n";
    out << "end\n\n";
}

void dump_prg(std::ostream& out, const std::string& name, std::span<const uint8_t> key,
              std::span<const uint8_t> iv, uint32_t tweak, uint32_t counter) {
    using PRG = faest::aes_ctr_prg<S>;
    constexpr size_t BLOCKS = 4;
    const faest::block128 k = load_block(key);
    PRG::expanded_key_t expanded;
    std::array<faest::block128, BLOCKS> output{};
    PRG::init<1, BLOCKS>(&k, &expanded, load_block(iv), &tweak, &counter, output.data());
    out << "record prg " << name << "\n";
    out << "key " << hex(key) << "\n";
    out << "iv " << hex(iv) << "\n";
    out << "tweak " << tweak << "\n";
    out << "counter " << counter << "\n";
    out << "out " << hex(bytes_of(output.data(), output.size())) << "\n";
    out << "end\n\n";
}

std::vector<uint8_t> shake(faest::secpar s, std::span<const uint8_t> input, size_t out_len) {
    // Absorb in uneven pieces, as the C++ does (many update calls).
    faest::hash_state h;
    h.init(s);
    size_t pos = 0;
    for (size_t piece = 1; pos < input.size(); piece = 2 * piece + 1) {
        const size_t n = std::min(piece, input.size() - pos);
        h.update(input.subspan(pos, n));
        pos += n;
    }
    std::vector<uint8_t> out(out_len);
    h.finalize(out);
    return out;
}

void dump_shake(std::ostream& out, const std::string& name, faest::secpar s,
                std::span<const uint8_t> input, size_t out_len) {
    out << "record shake " << name << "\n";
    out << "secpar " << faest::secpar_to_bits(s) << "\n";
    out << "input " << hex(input) << "\n";
    out << "out " << hex(shake(s, input, out_len)) << "\n";
    out << "end\n\n";
}

void dump_shake_x4(std::ostream& out, const std::string& name, faest::secpar s, size_t in_len,
                   size_t out_len) {
    std::array<std::vector<uint8_t>, 4> inputs;
    std::array<std::vector<uint8_t>, 4> outputs;
    for (size_t i = 0; i < 4; ++i) {
        inputs[i] = test_bytes(name + std::to_string(i), in_len);
        outputs[i].resize(out_len);
    }
    faest::hash_state_x4 h;
    h.init(s);
    h.update_4(inputs[0].data(), inputs[1].data(), inputs[2].data(), inputs[3].data(), in_len);
    h.update_1_byte(5);
    h.finalize_4(outputs[0].data(), outputs[1].data(), outputs[2].data(), outputs[3].data(),
                 out_len);
    for (size_t i = 0; i < 4; ++i) {
        std::vector<uint8_t> single = inputs[i];
        single.push_back(5);
        if (shake(s, single, out_len) != outputs[i]) {
            std::cerr << "hash_state_x4 disagrees with hash_state\n";
            std::exit(1);
        }
    }
    std::vector<uint8_t> input0 = inputs[0];
    input0.push_back(5);
    out << "record shake " << name << "\n";
    out << "secpar " << faest::secpar_to_bits(s) << "\n";
    out << "input " << hex(input0) << "\n";
    out << "out " << hex(outputs[0]) << "\n";
    out << "end\n\n";
}

void dump_prims(const std::string& dir) {
    std::ofstream out(dir + "/verifier_prims.txt");
    out << "# Generated by tests/voleith/dump_verifier_vectors.cpp. Do not edit.\n\n";
    for (size_t i = 0; i < 4; ++i) {
        const auto key = test_bytes("aes key " + std::to_string(i), 16);
        const auto pt = test_bytes("aes pt " + std::to_string(i), 16);
        dump_aes(out, std::to_string(i), std::span<const uint8_t, 16>(key.data(), 16),
                 std::span<const uint8_t, 16>(pt.data(), 16));
    }
    // IVs whose lanes 0 and 3 overflow, to pin down the counter/tweak arithmetic.
    const auto key = test_bytes("prg key", 16);
    std::vector<uint8_t> iv_wrap(16, 0xff);
    iv_wrap[4] = 0x01;
    dump_prg(out, "wrap", key, iv_wrap, (uint32_t{1} << 31) + 5, 0xfffffffe);
    dump_prg(out, "random", key, test_bytes("prg iv", 16), 2303, 0);
    dump_prg(out, "vole", key, test_bytes("prg iv 2", 16), (uint32_t{1} << 31) + 16, 6);
    for (const size_t n : {0, 1, 135, 136, 167, 168, 169, 500}) {
        dump_shake(out, "s128_" + std::to_string(n), faest::secpar::s128,
                   test_bytes("shake " + std::to_string(n), n), 200);
        dump_shake(out, "s256_" + std::to_string(n), faest::secpar::s256,
                   test_bytes("shake " + std::to_string(n), n), 200);
    }
    dump_shake_x4(out, "x4_s128", faest::secpar::s128, 300, 40);
}

// Leaves of the BAVC in spec order (see the file comment).
std::vector<faest::block128> spec_order_leaves(const faest::block128* leaves,
                                               std::span<const uint8_t> delta_bytes) {
    std::vector<faest::block128> out;
    size_t offset = 0;
    size_t delta_pos = 0;
    for (size_t i = 0; i < P::tau_v; ++i) {
        const size_t k = i < VC::NUM_MAX_K ? VC::MAX_K : VC::MIN_K;
        size_t delta_i = 0;
        for (size_t d = 0; d < k; ++d) {
            delta_i |= static_cast<size_t>(delta_bytes[delta_pos + d] & 1) << d;
        }
        delta_pos += k;
        for (size_t j = 0; j < (size_t{1} << k); ++j) {
            out.push_back(
                leaves[offset + faest::vole_permute_key_index_inv<CP::VOLE_WIDTH_SHIFT, VC::MAX_K>(
                                    j ^ delta_i)]);
        }
        offset += size_t{1} << k;
    }
    return out;
}

void dump_bavc(const std::string& dir) {
    std::ofstream out(dir + "/verifier_bavc.txt");
    out << "# Generated by tests/voleith/dump_verifier_vectors.cpp. Do not edit.\n\n";

    const auto seed_bytes = test_bytes("bavc seed", 16);
    const auto iv_bytes = test_bytes("bavc iv", 16);
    const faest::block128 seed = load_block(seed_bytes);
    const faest::block128 iv = load_block(iv_bytes);

    std::vector<faest::block128> tree(BAVC::COMMIT_NODES);
    std::vector<faest::block128> leaves(BAVC::COMMIT_LEAVES);
    std::vector<uint8_t> hashed(BAVC::COMMIT_LEAVES * P::leaf_hash_t::hash_len);
    BAVC::commit(seed, iv, tree.data(), leaves.data(), hashed.data());
    std::array<uint8_t, CP::VOLE_COMMIT_CHECK_SIZE> check{};
    faest::detail::hash_hashed_leaves<P>(hashed.data(), check.data());

    const std::vector<uint8_t> zero_delta(P::delta_bits_v, 0);
    const auto prover_leaves = spec_order_leaves(leaves.data(), zero_delta);
    out << "record bavc commit\n";
    out << "seed " << hex(seed_bytes) << "\n";
    out << "iv " << hex(iv_bytes) << "\n";
    out << "tree " << hex(bytes_of(tree.data(), tree.size())) << "\n";
    out << "leaves " << hex(bytes_of(prover_leaves.data(), prover_leaves.size())) << "\n";
    out << "hashed_leaves " << hex(hashed) << "\n";
    out << "check " << hex(check) << "\n";
    out << "end\n\n";

    // The first candidate Delta = SHAKE128("bavc delta" || ctr) (top 8 bits cleared) that opens.
    for (uint32_t ctr = 0;; ++ctr) {
        auto delta = test_bytes("bavc delta " + std::to_string(ctr), 16);
        delta[15] = 0;
        std::vector<uint8_t> delta_bytes(P::delta_bits_v);
        faest::expand_bits_to_bytes(delta_bytes.data(), P::delta_bits_v, delta.data());
        std::vector<uint8_t> opening(BAVC::OPEN_SIZE);
        if (!BAVC::open(tree.data(), hashed.data(), delta_bytes.data(), opening.data())) {
            continue;
        }
        std::vector<faest::block128> v_leaves(BAVC::COMMIT_LEAVES);
        std::vector<uint8_t> v_hashed(BAVC::COMMIT_LEAVES * P::leaf_hash_t::hash_len);
        if (!BAVC::verify(iv, opening.data(), delta_bytes.data(), v_leaves.data(),
                          v_hashed.data())) {
            std::cerr << "BAVC verify failed\n";
            std::exit(1);
        }
        std::array<uint8_t, CP::VOLE_COMMIT_CHECK_SIZE> v_check{};
        faest::detail::hash_hashed_leaves<P>(v_hashed.data(), v_check.data());
        const auto spec_leaves = spec_order_leaves(v_leaves.data(), delta_bytes);
        out << "record bavc open\n";
        out << "delta " << hex(delta) << "\n";
        out << "opening " << hex(opening) << "\n";
        out << "leaves " << hex(bytes_of(spec_leaves.data(), spec_leaves.size())) << "\n";
        out << "hashed_leaves " << hex(v_hashed) << "\n";
        out << "check " << hex(v_check) << "\n";
        out << "end\n\n";
        break;
    }
}

// The first `issue_request` and `ctx_iss` of the Moussaka KAT file.
std::optional<std::pair<std::vector<uint8_t>, std::vector<uint8_t>>> read_moussaka_kat() {
    std::ifstream in(std::string(VOLE_MOLE_TEST_DATA_DIR) + "/moussaka/moussaka_kat.txt");
    std::string line;
    std::vector<uint8_t> request;
    std::vector<uint8_t> ctx_iss;
    while (std::getline(in, line)) {
        std::istringstream fields(line);
        std::string key;
        std::string value;
        fields >> key >> value;
        if (key == "ctx_iss" && ctx_iss.empty()) {
            ctx_iss = unhex(value);
        } else if (key == "issue_request") {
            request = unhex(value);
            return std::make_pair(request, ctx_iss);
        }
    }
    return std::nullopt;
}

void dump_kat(const std::string& dir) {
    using Relation = moussaka::detail::IssueRelation;
    using OC = P::OWF_CONSTS;

    const auto kat = read_moussaka_kat();
    if (!kat) {
        std::cerr << "cannot read the Moussaka KAT file\n";
        std::exit(1);
    }
    const auto& [request, ctx_iss_bytes] = *kat;
    Relation::instance x{};
    std::memcpy(x.t.data(), request.data(), x.t.size());
    std::memcpy(x.ctx_iss.data(), ctx_iss_bytes.data(), x.ctx_iss.size());
    if (request.size() != moussaka::ISSUE_REQUEST_BYTES) {
        std::cerr << "unexpected issue_request length\n";
        std::exit(1);
    }
    const std::span<const uint8_t, moussaka::ISSUE_PROOF_BYTES> proof_bytes(
        request.data() + x.t.size(), moussaka::ISSUE_PROOF_BYTES);
    const faest::faest_signature<P> proof = proof_bytes.data();

    std::ofstream out(dir + "/verifier_kat.txt");
    out << "# Generated by tests/voleith/dump_verifier_vectors.cpp. Do not edit.\n\n";
    out << "record kat moussaka_issue_0\n";
    out << "t " << hex(x.t) << "\n";
    out << "ctx_iss " << hex(x.ctx_iss) << "\n";
    out << "proof " << hex(proof_bytes) << "\n";

    const auto mu = detail::hash_mu<Relation>(&x);
    out << "mu " << hex(bytes_of(&mu, 1)) << "\n";

    faest::block128 iv;
    faest::hash_state hasher;
    hasher.init(S);
    hasher.update(proof.iv_pre());
    hasher.update(&mu, sizeof(mu));
    hasher.update_byte(4);
    hasher.finalize(&iv, sizeof(iv));
    out << "iv " << hex(bytes_of(&iv, 1)) << "\n";

    faest::block128 delta = load_block(proof.delta());
    std::vector<uint8_t> delta_bytes(P::delta_bits_v);
    faest::expand_bits_to_bytes(delta_bytes.data(), P::delta_bits_v, proof.delta().data());

    // The BAVC verification on its own, for the leaves in spec order.
    {
        std::vector<faest::block128> v_leaves(BAVC::COMMIT_LEAVES);
        std::vector<uint8_t> v_hashed(BAVC::COMMIT_LEAVES * P::leaf_hash_t::hash_len);
        if (!BAVC::verify(iv, proof.veccom_open().data(), delta_bytes.data(), v_leaves.data(),
                          v_hashed.data())) {
            std::cerr << "BAVC verify of the KAT proof failed\n";
            std::exit(1);
        }
        const auto spec_leaves = spec_order_leaves(v_leaves.data(), delta_bytes);
        out << "leaves " << hex(bytes_of(spec_leaves.data(), spec_leaves.size())) << "\n";
        out << "hashed_leaves " << hex(v_hashed) << "\n";
    }

    // Plain VOLE reconstruction, for the columns before the CRT lift.
    std::array<uint8_t, CP::VOLE_COMMIT_CHECK_SIZE> vole_commit_check{};
    {
        auto data = faest::vole_commit_data<P, true>::alloc();
        if (!data || !faest::vole_reconstruct<P>(iv, *data, delta_bytes.data(),
                                                 proof.vole_commitment_corrections(),
                                                 proof.veccom_open(), vole_commit_check)) {
            std::cerr << "vole_reconstruct failed\n";
            std::exit(1);
        }
        out << "q_columns "
            << hex(bytes_of(data->q_columns().data(), P::secpar_bits * CP::VOLE_COL_BLOCKS))
            << "\n";
        out << "vole_commit_check " << hex(vole_commit_check) << "\n";
    }

    // The CRT reconstruction, as voleith_vole_reconstruct.
    auto allocated = faest::vole_commit_data<P, true>::alloc();
    if (!allocated) {
        std::cerr << "allocation failed\n";
        std::exit(1);
    }
    auto& data = *allocated;
    if (!faest::crt_vole_reconstruct<P>(iv, data, delta, proof.vole_commitment_corrections(),
                                        proof.veccom_open(), vole_commit_check,
                                        proof.vole_commitment_cmult())) {
        std::cerr << "crt_vole_reconstruct failed\n";
        std::exit(1);
    }
    out << "q_rows " << hex(bytes_of(data.q().data(), CP::VOLE_CORRECTION_ROWS)) << "\n";
    out << "q_mask " << hex(bytes_of(data.q_mask().data(), CP::CRT_NUM_MASK)) << "\n";
    delta = faest::crt_lift_delta<P>(delta);
    out << "delta_lifted " << hex(bytes_of(&delta, 1)) << "\n";

    std::array<uint8_t, CP::VOLE_CHECK::CHALLENGE_BYTES> chal1{};
    hasher.init(S);
    hasher.update(&mu, sizeof(mu));
    hasher.update(vole_commit_check);
    hasher.update(proof.vole_commitment_corrections());
    hasher.update(proof.vole_commitment_cmult());
    hasher.update(proof.iv_pre());
    hasher.update_byte(8 + 1);
    hasher.finalize(chal1);
    out << "chal1 " << hex(chal1) << "\n";

    std::array<uint8_t, CP::QS::CHALLENGE_BYTES> chal2{};
    hasher.init(S);
    hasher.update(chal1);
    faest::kos_vole_check_receiver<P>(delta, data.q().subspan<0, CP::VOLE_CORRECTION_ROWS>(),
                                      data.q_mask(), chal1, proof.vole_check_proof(), hasher);
    hasher.update(proof.correction());
    hasher.update_byte(8 + 2);
    hasher.finalize(chal2);
    out << "chal2 " << hex(chal2) << "\n";

    {
        const auto d = proof.correction();
        const auto q = data.q();
        for (size_t i = 0; i < CP::VOLE_CORRECTION_ROWS; ++i) {
            if (((d[i / 8] >> (i % 8)) & 1) != 0) {
                q[i] = q[i] ^ delta;
            }
        }
    }
    faest::quicksilver_state<S, true, OC::QS_DEGREE> qs(data.q().data(), Relation::NUM_CONSTRAINTS,
                                                        delta, chal2.data());
    Relation::constraints(&qs, x, std::span<const uint8_t, CP::QS::CHALLENGE_BYTES>(chal2));
    std::array<uint8_t, CP::QS::CHECK_BYTES> qs_check{};
    qs.verify(data.q_mask().data(), proof.qs_proof().data(), qs_check.data());
    out << "qs_check " << hex(qs_check) << "\n";

    std::array<uint8_t, 16> delta_check{};
    hasher.init(S);
    hasher.update(chal2);
    hasher.update(qs_check);
    hasher.update(proof.qs_proof());
    hasher.update(proof.grinding_ctr());
    hasher.update_byte(8 + 3);
    hasher.finalize(delta_check);
    out << "delta_check " << hex(delta_check) << "\n";

    const bool accept = moussaka::detail::verify_issue_proof(proof_bytes, x.t, x.ctx_iss);
    out << "accept " << (accept ? 1 : 0) << "\n";
    out << "end\n";
    if (!accept || std::memcmp(delta_check.data(), proof.delta().data(), 16) != 0) {
        std::cerr << "the KAT proof does not verify\n";
        std::exit(1);
    }
}

} // namespace

int main(int argc, char** argv) {
    if (argc != 2) {
        std::cerr << "Usage: dump_verifier_vectors OUTPUT_DIR\n";
        return 1;
    }
    const std::string dir = argv[1];
    dump_prims(dir);
    dump_bavc(dir);
    dump_kat(dir);
    return 0;
}
