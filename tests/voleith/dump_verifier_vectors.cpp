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
// verifier_keys.txt: lines `key SK PK`, the compressed UOV public key PK of each compact secret key
// SK in the Moussaka and Ratatouille KAT files.
//
// verifier_kat.txt: the CRT tables, then one record per relation with the intermediate values of
// the verification of a KAT proof (Moussaka issuance and redemption, Ratatouille issuance and
// spend, PomFRIT redemption; see dump_moussaka etc. for which KAT record), following
// voleith_vole_reconstruct and voleith_verify_commit step by step.
//
//   record crt tables      n_mult; m_i (17 little-endian uint64: the CRT moduli M_i, bit j is the
//                          coefficient of X^j); m_tree; the row tables of the lifts, each row a
//                          little-endian bit vector padded to whole uint64s: w_crt (120 rows x 128
//                          bits), w_tree (120 x 128), w_gate (n_mult x 128), g (120 x 320).
//   record kat NAME
//     witness_bytes, qs_degree, n_mask, vole_col_blocks, vole_rows, correction_rows  parameters
//     dst, inst_enc        the relation's DST and the bytes its hash_instance absorbs
//     delayed              1 for delayed instance binding (PomFRIT): chal1 uses mu1 = H(DST || 12)
//     binder1, binder2     the chal1 and chal2 binders
//     proof                the proof
//     mu                   H(inst_enc || DST || 8), 32 bytes; mu1 is the mu used for iv and chal1
//     iv                   H_4(iv_pre || mu1 || 4), 16 bytes
//     leaves, hashed_leaves  the BAVC verification of the opening at Delta (spec order, as above)
//     q_columns            the small-VOLE keys before the CRT lift: column c (0 <= c < 128) is
//                          VOLE_COL_STRIDE bytes, row r is bit r % 8 of byte r / 8 of the column
//     vole_commit_check    hash_hashed_leaves
//     gate_hashes          the n_mult 32-bit gate hashes of lift_and_hash_vq (little endian)
//     r_tilde              compute_r_tilde of the mask rows (n_mask blocks)
//     q_rows               the VOLE_CORRECTION_ROWS rows of q after the CRT lift and the
//                          transpose, before the correction d (16 bytes each)
//     q_mask               the CRT_NUM_MASK mask rows (16 bytes each)
//     delta_lifted         crt_lift_delta(Delta)
//     chal1, chal2         H_2^1 and H_2^2
//     qs_check             the verifier's QuickSilver check value
//     delta_check          H_2^3(chal2 || qs_check || qs_proof || ctr || 11), compared with Delta
//     accept               1 if voleith_verify (or PomFRIT's two-step verification) accepts

#include "vole_mole/moussaka.hpp"
#include "vole_mole/ratatouille.hpp"
#include "vole_mole/uov.hpp"

#include "dst.hpp"                // internal
#include "moussaka/commit.hpp"    // internal
#include "moussaka/issue.hpp"     // internal
#include "moussaka/redeem.hpp"    // internal
#include "pomfrit/redeem.hpp"     // internal
#include "ratatouille/commit.hpp" // internal
#include "ratatouille/issue.hpp"  // internal
#include "ratatouille/spend.hpp"  // internal
#include "uov/public_key.hpp"     // internal
#include "voleith.hpp"            // internal

#include "aes.hpp"                        // from faest-arch-opt
#include "aes_defs.hpp"                   // from faest-arch-opt
#include "block.hpp"                      // from faest-arch-opt
#include "crt_constants.hpp"              // from faest-arch-opt
#include "crt_vole_helpers.inc"           // from faest-arch-opt
#include "faest_sig.hpp"                  // from faest-arch-opt
#include "hash.hpp"                       // from faest-arch-opt
#include "kos_vole_check.hpp"             // from faest-arch-opt
#include "parameters.hpp"                 // from faest-arch-opt
#include "prgs.hpp"                       // from faest-arch-opt
#include "quicksilver.hpp"                // from faest-arch-opt
#include "transpose_secpar.hpp"           // from faest-arch-opt
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
#include <set>
#include <span>
#include <sstream>
#include <string>
#include <string_view>
#include <type_traits>
#include <utility>
#include <variant>
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

// A KAT file as a flat list of (key, value) lines, in order.
using KatLines = std::vector<std::pair<std::string, std::string>>;

KatLines read_kat(const std::string& relative_path) {
    std::ifstream in(std::string(VOLE_MOLE_TEST_DATA_DIR) + "/" + relative_path);
    if (!in.is_open()) {
        std::cerr << "cannot read " << relative_path << "\n";
        std::exit(1);
    }
    KatLines lines;
    std::string line;
    while (std::getline(in, line)) {
        if (line.empty() || line[0] == '#') {
            continue;
        }
        std::istringstream fields(line);
        std::string key;
        std::string value;
        fields >> key >> value;
        lines.emplace_back(key, value);
    }
    return lines;
}

// The value of the n-th line with the given key (n counted from 0), starting at line `from`.
std::string kat_value(const KatLines& lines, const std::string& key, size_t n = 0,
                      size_t from = 0) {
    for (size_t i = from; i < lines.size(); ++i) {
        if (lines[i].first == key && n-- == 0) {
            return lines[i].second;
        }
    }
    std::cerr << "KAT key not found: " << key << "\n";
    std::exit(1);
}

// Index of the n-th line with the given key.
size_t kat_index(const KatLines& lines, const std::string& key, size_t n) {
    for (size_t i = 0; i < lines.size(); ++i) {
        if (lines[i].first == key && n-- == 0) {
            return i;
        }
    }
    std::cerr << "KAT key not found: " << key << "\n";
    std::exit(1);
}

template <size_t N> std::array<uint8_t, N> to_array(const std::vector<uint8_t>& v) {
    if (v.size() != N) {
        std::cerr << "unexpected length " << v.size() << ", wanted " << N << "\n";
        std::exit(1);
    }
    std::array<uint8_t, N> out{};
    std::ranges::copy(v, out.begin());
    return out;
}

template <typename T> void append(std::vector<uint8_t>& out, const T& bytes) {
    out.insert(out.end(), std::begin(bytes), std::end(bytes));
}

void dump_crt_tables(std::ostream& out) {
    using C = faest::CRT_CONSTANTS<S, P::tau_v, P::delta_bits_v>;
    out << "record crt tables\n";
    out << "n_mult " << CP::CRT_NUM_MULT << "\n";
    out << "m_i " << hex(bytes_of(C::M_i.data(), C::M_i.size())) << "\n";
    out << "m_tree " << hex(C::M_TREE) << "\n";
    out << "w_crt " << hex(bytes_of(C::W_CRT_LIFT_ROW_TAB.data(), C::W_CRT_LIFT_ROW_TAB.size()))
        << "\n";
    out << "w_tree " << hex(bytes_of(C::W_TREE_LIFT_ROW_TAB.data(), C::W_TREE_LIFT_ROW_TAB.size()))
        << "\n";
    out << "w_gate " << hex(bytes_of(C::W_GATE_LIFT_ROW_TAB.data(), C::W_GATE_LIFT_ROW_TAB.size()))
        << "\n";
    out << "g " << hex(bytes_of(C::G_LIFT_ROW_TAB.data(), C::G_LIFT_ROW_TAB.size())) << "\n";
    out << "end\n\n";
}

// Verify `proof_bytes` for instance `x` step by step, as voleith_vole_reconstruct and
// voleith_verify_commit do, and dump the intermediate values (see the file comment). inst_enc are
// the bytes Relation::hash_instance absorbs (checked against hash_mu).
template <typename Relation>
void dump_verification(std::ostream& out, const std::string& name,
                       std::span<const uint8_t> proof_in, const typename Relation::instance& x,
                       std::span<const uint8_t> inst_enc, bool delayed,
                       std::span<const uint8_t> binder1, std::span<const uint8_t> binder2) {
    using RP = detail::relation_params<Relation>;
    using RCP = RP::CONSTS;
    using OC = RP::OWF_CONSTS;
    static_assert(std::is_same_v<typename RP::bavc_t, BAVC>);
    constexpr size_t N_MULT = RCP::CRT_NUM_MULT;
    constexpr size_t PADDED_N_MULT = ((N_MULT + 15) / 16) * 16;

    if (proof_in.size() != detail::PROOF_BYTES<Relation>) {
        std::cerr << name << ": unexpected proof length\n";
        std::exit(1);
    }
    const detail::const_proof_span<Relation> proof_bytes(proof_in.data(), proof_in.size());
    const faest::faest_signature<RP> proof = proof_bytes.data();

    out << "record kat " << name << "\n";
    out << "witness_bytes " << OC::WITNESS_BITS / 8 << "\n";
    out << "qs_degree " << OC::QS_DEGREE << "\n";
    out << "n_mask " << RCP::CRT_NUM_MASK << "\n";
    out << "vole_col_blocks " << RCP::VOLE_COL_BLOCKS << "\n";
    out << "vole_rows " << RCP::VOLE_ROWS << "\n";
    out << "correction_rows " << RCP::VOLE_CORRECTION_ROWS << "\n";
    out << "dst " << hex(Relation::DST) << "\n";
    out << "inst_enc " << hex(inst_enc) << "\n";
    out << "delayed " << (delayed ? 1 : 0) << "\n";
    out << "binder1 " << hex(binder1) << "\n";
    out << "binder2 " << hex(binder2) << "\n";
    out << "proof " << hex(proof_bytes) << "\n";

    const auto mu = detail::hash_mu<Relation>(&x);
    {
        std::vector<uint8_t> input(inst_enc.begin(), inst_enc.end());
        append(input, Relation::DST);
        input.push_back(8);
        if (shake(S, input, sizeof(mu)) !=
            std::vector<uint8_t>(bytes_of(&mu, 1).begin(), bytes_of(&mu, 1).end())) {
            std::cerr << name << ": inst_enc does not match hash_instance\n";
            std::exit(1);
        }
    }
    const auto mu1 = detail::hash_mu<Relation>(delayed ? nullptr : &x);
    out << "mu " << hex(bytes_of(&mu, 1)) << "\n";
    out << "mu1 " << hex(bytes_of(&mu1, 1)) << "\n";

    faest::block128 iv;
    faest::hash_state hasher;
    hasher.init(S);
    hasher.update(proof.iv_pre());
    hasher.update(&mu1, sizeof(mu1));
    hasher.update_byte(4);
    hasher.finalize(&iv, sizeof(iv));
    out << "iv " << hex(bytes_of(&iv, 1)) << "\n";

    faest::block128 delta = load_block(proof.delta());
    std::vector<uint8_t> delta_bytes(RP::delta_bits_v);
    faest::expand_bits_to_bytes(delta_bytes.data(), RP::delta_bits_v, proof.delta().data());

    // The BAVC verification on its own, for the leaves in spec order.
    {
        std::vector<faest::block128> v_leaves(BAVC::COMMIT_LEAVES);
        std::vector<uint8_t> v_hashed(BAVC::COMMIT_LEAVES * RP::leaf_hash_t::hash_len);
        if (!BAVC::verify(iv, proof.veccom_open().data(), delta_bytes.data(), v_leaves.data(),
                          v_hashed.data())) {
            std::cerr << name << ": BAVC verify failed\n";
            std::exit(1);
        }
        const auto spec_leaves = spec_order_leaves(v_leaves.data(), delta_bytes);
        out << "leaves " << hex(bytes_of(spec_leaves.data(), spec_leaves.size())) << "\n";
        out << "hashed_leaves " << hex(v_hashed) << "\n";
    }

    // Plain VOLE reconstruction, for the columns before the CRT lift, and the gate hashes.
    std::array<uint8_t, RCP::VOLE_COMMIT_CHECK_SIZE> vole_commit_check{};
    {
        auto data = faest::vole_commit_data<RP, true>::alloc();
        if (!data || !faest::vole_reconstruct<RP>(iv, *data, delta_bytes.data(),
                                                  proof.vole_commitment_corrections(),
                                                  proof.veccom_open(), vole_commit_check)) {
            std::cerr << name << ": vole_reconstruct failed\n";
            std::exit(1);
        }
        out << "q_columns "
            << hex(bytes_of(data->q_columns().data(), RP::secpar_bits * RCP::VOLE_COL_BLOCKS))
            << "\n";
        out << "vole_commit_check " << hex(vole_commit_check) << "\n";
        std::array<uint32_t, PADDED_N_MULT> hashes{};
        faest::detail::lift_and_hash_vq<RP, true>(iv, data->q_columns().data(), std::monostate{},
                                                  std::span(hashes).template subspan<0, N_MULT>(),
                                                  std::monostate{});
        out << "gate_hashes " << hex(bytes_of(hashes.data(), N_MULT)) << "\n";
        // r_tilde from the transposed, CRT-lifted rows (compute_r_tilde reads only mask rows,
        // which the lift leaves unchanged).
        faest::crt_lift_q<RP>(data->q_columns().data(), RCP::VOLE_COL_BLOCKS,
                              RCP::VOLE_CORRECTION_BYTES);
        faest::transpose_secpar<S>(data->q_columns().data(), data->q().data(), RCP::VOLE_COL_STRIDE,
                                   RCP::VOLE_ROWS_PADDED);
        std::array<faest::block128, RCP::CRT_NUM_MASK> r_tilde{};
        faest::detail::compute_r_tilde<RP>(data->q().data(), r_tilde.data());
        out << "r_tilde " << hex(bytes_of(r_tilde.data(), r_tilde.size())) << "\n";
    }

    // The CRT reconstruction, as voleith_vole_reconstruct.
    auto allocated = faest::vole_commit_data<RP, true>::alloc();
    if (!allocated) {
        std::cerr << "allocation failed\n";
        std::exit(1);
    }
    auto& data = *allocated;
    if (!faest::crt_vole_reconstruct<RP>(iv, data, delta, proof.vole_commitment_corrections(),
                                         proof.veccom_open(), vole_commit_check,
                                         proof.vole_commitment_cmult())) {
        std::cerr << name << ": crt_vole_reconstruct failed\n";
        std::exit(1);
    }
    out << "q_rows " << hex(bytes_of(data.q().data(), RCP::VOLE_CORRECTION_ROWS)) << "\n";
    out << "q_mask " << hex(bytes_of(data.q_mask().data(), RCP::CRT_NUM_MASK)) << "\n";
    delta = faest::crt_lift_delta<RP>(delta);
    out << "delta_lifted " << hex(bytes_of(&delta, 1)) << "\n";

    std::array<uint8_t, RCP::VOLE_CHECK::CHALLENGE_BYTES> chal1{};
    hasher.init(S);
    hasher.update(&mu1, sizeof(mu1));
    hasher.update(vole_commit_check);
    hasher.update(proof.vole_commitment_corrections());
    hasher.update(proof.vole_commitment_cmult());
    hasher.update(proof.iv_pre());
    hasher.update(binder1);
    hasher.update_byte(8 + 1);
    hasher.finalize(chal1);
    out << "chal1 " << hex(chal1) << "\n";

    std::array<uint8_t, RCP::QS::CHALLENGE_BYTES> chal2{};
    hasher.init(S);
    hasher.update(chal1);
    faest::kos_vole_check_receiver<RP>(delta,
                                       data.q().template subspan<0, RCP::VOLE_CORRECTION_ROWS>(),
                                       data.q_mask(), chal1, proof.vole_check_proof(), hasher);
    if (delayed) {
        hasher.update(&mu, sizeof(mu));
    }
    hasher.update(binder2);
    hasher.update(proof.correction());
    hasher.update_byte(8 + 2);
    hasher.finalize(chal2);
    out << "chal2 " << hex(chal2) << "\n";

    {
        const auto d = proof.correction();
        const auto q = data.q();
        // Witness rows only (dedicated label rows, if any, get no d).
        for (size_t i = 0; i < OC::WITNESS_BITS; ++i) {
            if (((d[i / 8] >> (i % 8)) & 1) != 0) {
                q[i] = q[i] ^ delta;
            }
        }
    }
    faest::quicksilver_state<S, true, OC::QS_DEGREE> qs(data.q().data(), Relation::NUM_CONSTRAINTS,
                                                        delta, chal2.data());
    Relation::constraints(&qs, x, std::span<const uint8_t, RCP::QS::CHALLENGE_BYTES>(chal2));
    std::array<uint8_t, RCP::QS::CHECK_BYTES> qs_check{};
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

    auto pending =
        detail::voleith_vole_reconstruct<Relation>(proof_bytes, delayed ? nullptr : &x, binder1);
    const bool accept = pending && detail::voleith_verify_commit<Relation>(
                                       proof_bytes, x, std::move(*pending), binder2);
    out << "accept " << (accept ? 1 : 0) << "\n";
    out << "end\n\n";
    if (!accept || std::memcmp(delta_check.data(), proof.delta().data(), 16) != 0) {
        std::cerr << name << ": the KAT proof does not verify\n";
        std::exit(1);
    }
}

std::array<uint8_t, 4> u32le(size_t v) {
    const auto u = static_cast<uint32_t>(v);
    return {static_cast<uint8_t>(u), static_cast<uint8_t>(u >> 8), static_cast<uint8_t>(u >> 16),
            static_cast<uint8_t>(u >> 24)};
}

void dump_moussaka(std::ostream& out) {
    namespace md = moussaka::detail;
    const auto kat = read_kat("moussaka/moussaka_kat.txt");

    // Issuance: record 0. issue_request = t || proof.
    {
        const auto request = unhex(kat_value(kat, "issue_request"));
        md::IssueRelation::instance x{};
        std::copy_n(request.begin(), x.t.size(), x.t.begin());
        x.ctx_iss = to_array<moussaka::CTX_BYTES>(unhex(kat_value(kat, "ctx_iss")));
        std::vector<uint8_t> enc;
        append(enc, x.t);
        append(enc, x.ctx_iss);
        dump_verification<md::IssueRelation>(
            out, "moussaka_issue_0", std::span(request).subspan(x.t.size()), x, enc, false, {}, {});
    }

    // Redemption: record 1 (three anchors). redeem_request = nf || proof.
    {
        const size_t start = kat_index(kat, "issue_seed", 1);
        const size_t anchor_count = std::stoul(kat_value(kat, "anchor_count", 0, start));
        std::vector<uov::SecretKey> sks;
        for (size_t u = 0; u < anchor_count; ++u) {
            sks.emplace_back(
                to_array<uov::SECRET_KEY_BYTES>(unhex(kat_value(kat, "anchor_sk", u, start))));
        }
        std::vector<moussaka::AnchorRef> anchors;
        for (const auto& sk : sks) {
            anchors.emplace_back(sk.expanded_public_key());
        }
        const auto request = unhex(kat_value(kat, "redeem_request", 0, start));
        md::RedeemRelation::instance x{
            anchors,
            {},
            to_array<moussaka::CTX_BYTES>(unhex(kat_value(kat, "ctx_iss", 0, start))),
            to_array<moussaka::CTX_BYTES>(unhex(kat_value(kat, "ctx_red", 0, start))),
            to_array<moussaka::CHALLENGE_DIGEST_BYTES>(
                unhex(kat_value(kat, "challenge_digest", 0, start)))};
        std::copy_n(request.begin(), x.nf.size(), x.nf.begin());
        std::vector<uint8_t> enc;
        append(enc, u32le(moussaka::MAX_ANCHORS));
        append(enc, u32le(anchors.size()));
        for (const uov::PublicKey& pk : anchors) {
            append(enc, uov::detail::PublicKeyAccess::digest(pk));
        }
        append(enc, x.nf);
        append(enc, x.ctx_iss);
        append(enc, x.ctx_red);
        append(enc, x.challenge_digest);
        dump_verification<md::RedeemRelation>(out, "moussaka_redeem_1",
                                              std::span(request).subspan(x.nf.size()), x, enc,
                                              false, {}, {});
    }
}

void dump_ratatouille(std::ostream& out) {
    namespace rd = ratatouille::detail;
    const auto kat = read_kat("ratatouille/ratatouille_kat.txt");
    const uov::SecretKey sk(to_array<uov::SECRET_KEY_BYTES>(unhex(kat_value(kat, "issuer_sk"))));
    const auto ctx_iss = to_array<ratatouille::CTX_BYTES>(unhex(kat_value(kat, "ctx_iss")));

    // Issuance: record 0. issue_request = c || proof.
    {
        const auto request = unhex(kat_value(kat, "issue_request"));
        rd::IssueRelation::instance x{};
        std::copy_n(request.begin(), x.c.size(), x.c.begin());
        x.t_init = std::stoull(kat_value(kat, "t_init"));
        x.ctx_iss = ctx_iss;
        std::vector<uint8_t> enc;
        append(enc, x.c);
        append(enc, rd::encode_credits(x.t_init));
        append(enc, x.ctx_iss);
        dump_verification<rd::IssueRelation>(out, "ratatouille_issue_0",
                                             std::span(request).subspan(x.c.size()), x, enc, false,
                                             {}, {});
    }

    // First spend of record 0. spend_request = nf || <d> || c' || proof.
    {
        const auto request = unhex(kat_value(kat, "spend_request"));
        const uov::PublicKey& pk = sk.expanded_public_key();
        rd::SpendRelation::instance x{pk, {}, 0, {}, ctx_iss};
        size_t off = 0;
        std::copy_n(request.begin(), x.nf.size(), x.nf.begin());
        off += x.nf.size();
        x.d = rd::decode_credits(std::span<const uint8_t, ratatouille::CREDIT_BYTES>(
            request.data() + off, ratatouille::CREDIT_BYTES));
        off += ratatouille::CREDIT_BYTES;
        std::copy_n(request.begin() + static_cast<std::ptrdiff_t>(off), x.c_next.size(),
                    x.c_next.begin());
        off += x.c_next.size();
        std::vector<uint8_t> enc;
        append(enc, uov::detail::PublicKeyAccess::digest(pk));
        append(enc, x.nf);
        append(enc, rd::encode_credits(x.d));
        append(enc, x.c_next);
        append(enc, x.ctx_iss);
        dump_verification<rd::SpendRelation>(
            out, "ratatouille_spend_0", std::span(request).subspan(off), x, enc, false, {}, {});
    }
}

void dump_pomfrit(std::ostream& out) {
    namespace pd = pomfrit::detail;
    using Relation = pd::RedeemRelation;
    const auto kat = read_kat("pomfrit/pomfrit_kat.txt");
    const uov::PublicKey pk(to_array<uov::PUBLIC_KEY_BYTES>(unhex(kat_value(kat, "pk"))));
    // The second signature (non-empty msg). signature = proof || refresher_com || refresher.
    const auto sig = unhex(kat_value(kat, "signature", 1));
    const auto msg = unhex(kat_value(kat, "msg", 1));
    constexpr size_t PROOF = detail::PROOF_BYTES<Relation>;
    constexpr size_t REFRESHER = 2 * detail::relation_params<Relation>::secpar_bytes;
    const std::span<const uint8_t> proof(sig.data(), PROOF);
    const std::span<const uint8_t> refresher_com(sig.data() + PROOF, REFRESHER);
    const std::span<const uint8_t> refresher(sig.data() + PROOF + REFRESHER, REFRESHER);
    const faest::faest_signature<detail::relation_params<Relation>> view = proof.data();

    // h = H(TARGET_DST || dig(pk) || chal1 || u_tilde || d[0..M) || msg), as hash_to_target.
    const auto chal1 = unhex(kat_value(kat, "chal1", 1));
    Relation::instance x{&pk, {}};
    {
        faest::hash_state h;
        h.init(S);
        h.update(detail::POMFRIT_TARGET_DST);
        h.update(uov::detail::PublicKeyAccess::digest(pk));
        h.update(chal1);
        h.update(view.vole_check_proof());
        h.update(view.correction().subspan(0, uov::M));
        h.update(msg);
        h.finalize(x.h);
    }
    std::vector<uint8_t> enc;
    append(enc, uov::detail::PublicKeyAccess::digest(pk));
    append(enc, x.h);
    dump_verification<Relation>(out, "pomfrit_redeem_1", proof, x, enc, true, refresher_com,
                                refresher);
}

// The compressed public keys of all UOV secret keys in the Moussaka and Ratatouille KAT files.
void dump_keys(const std::string& dir) {
    std::ofstream out(dir + "/verifier_keys.txt");
    out << "# Generated by tests/voleith/dump_verifier_vectors.cpp. Do not edit.\n";
    out << "# key SK PK: a compact UOV secret key and its compressed public key.\n\n";
    std::set<std::string> seen;
    for (const auto* path : {"moussaka/moussaka_kat.txt", "ratatouille/ratatouille_kat.txt"}) {
        for (const auto& [key, value] : read_kat(path)) {
            if ((key != "anchor_sk" && key != "issuer_sk") || !seen.insert(value).second) {
                continue;
            }
            const uov::SecretKey sk(to_array<uov::SECRET_KEY_BYTES>(unhex(value)));
            out << "key " << value << " " << hex(sk.public_key_bytes()) << "\n";
        }
    }
}

void dump_kats(const std::string& dir) {
    std::ofstream out(dir + "/verifier_kat.txt");
    out << "# Generated by tests/voleith/dump_verifier_vectors.cpp. Do not edit.\n\n";
    dump_crt_tables(out);
    dump_moussaka(out);
    dump_ratatouille(out);
    dump_pomfrit(out);
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
    dump_kats(dir);
    dump_keys(dir);
    return 0;
}
