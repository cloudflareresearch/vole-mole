// The binary part of the mdoc proof (see mdoc_relation.hpp for the whole statement), in FAEST's
// VOLEitH (src/voleith.hpp).
//
//   Instance: the statement (through mu), the time "now", the disclosed attributes, the link
//             challenges, and the link values Z_n, Z_p (issuer), Z_q, Z_n', Z_p' (device)
//   Witness:  the issuer's signed message (COSE Sig_structure of the MSO) in MAX_BLOCKS padded
//             blocks and their SHA-256 values, the index of its last block, its digest e, the
//             selectors of the fields of the MSO and their dates, the issuer's X = x(R), the device
//             key Q, the device's X' = x(R'), and for each attribute, its padded
//             IssuerSignedItemBytes, their SHA-256 values, and the selectors of its fields; the
//             masks rho_n, rho_p, rho_q, rho_n', rho_p'; and carries
//
// The constraints, which are those of Longfellow's mdoc circuit (version 7, lib/circuits/mdoc/
// mdoc_hash.h), except where noted:
//
//   1. The message starts with the 18 bytes COSE_PREFIX, and e = H_t, the SHA-256 chaining value
//      after block t, for a one-hot t over the MAX_BLOCKS blocks; the blocks after t are zero.
//      (Longfellow reads the message length from the padding of block t, and checks that each
//      field below starts before it. Here a field can't start in the padding or the zero blocks
//      instead: each pattern below starts with a byte in [0x58, 0x6d] followed by a nonzero byte,
//      the padding is 0x80, zeros, and a 64-bit length below 2^15, and zero blocks follow.)
//   2. At secret offsets (each a one-hot block index and a one-hot offset in the block; see
//      select_ops.hpp), the message has the patterns
//        - 69 "validFrom" C0 74 <validFrom>, with validFrom <= now (20 bytes, as big-endian
//          integers, i.e., lexicographically),
//        - 6A "validUntil" C0 74 <validUntil>, with now <= validUntil,
//        - 6D "deviceKeyInfo" A1 69 "deviceKey" A4 01 02 20 01 21 58 20 <x_Q> 22 58 20 <y_Q>,
//          where x_Q, y_Q < p are the device key's coordinates (big endian),
//        - 6C "valueDigests",
//        - for each attribute, 58 20 <SHA-256 of its IssuerSignedItemBytes>.
//   3. For each attribute, its IssuerSignedItemBytes, in 2 padded blocks (so 56 to 119 bytes, of
//      length L, from the padding), are D8 18 58 xx A4, followed by 4 fields in slots j < 4 at
//      positions pos_0 = 5 < pos_1 < pos_2 < pos_3 < pos_4 = L, with pos_{j+1} = pos_j + len_j. A
//      one-hot sigma_f assigns each field f (digestID, random, elementIdentifier, elementValue) to
//      a slot, where it has the pattern
//        - 68 "digestID" <H>, with H the header of an unsigned integer of 1, 2, 3, or 5 bytes, and
//          len = 9 + that length (Longfellow allows any major type with such a header),
//        - 66 "random" <H> <N>, with H a byte string header of length n < 24 (ai = n) or n = N
//          (ai = 24), and len = 7 + (1 or 2) + n (Longfellow allows any string type),
//        - 71 "elementIdentifier" <public tstr>, and len its length,
//        - 6C "elementValue" <public value>, and len its length.
//      The patterns' first bytes differ, so no two fields share a slot, and sigma is a
//      permutation.
//   4. X < p, x_Q < p, y_Q < p, and X' < p (not part of Longfellow's hash circuit, whose signature
//      circuit takes these values as field elements).
//   5. The link sums Z_n = c_1 e + c_2 X + rho_n, Z_p = c_3 X + rho_p (as binary.hpp), and, with a
//      second link challenge, Z_q = c_x x_Q + c_y y_Q + rho_q (as rr_binary.hpp) and
//      Z_n' = c_2' X' + rho_n', Z_p' = c_3' X' + rho_p' (as hk_binary.hpp).
//
// As in binary.hpp, the carries of the link sums are committed after the link challenge, with a
// budget. The witness may be derived from a short key with a PRG (BinPrg).

#ifndef VOLE_MOLE_ECDSA_POK_MDOC_BINARY_HPP
#define VOLE_MOLE_ECDSA_POK_MDOC_BINARY_HPP

#include "dst.hpp"
#include "ecdsa_pok/bin_ops.hpp"
#include "ecdsa_pok/binary.hpp"
#include "ecdsa_pok/hk_binary.hpp"
#include "ecdsa_pok/link.hpp"
#include "ecdsa_pok/rr_binary.hpp"
#include "ecdsa_pok/select_ops.hpp"
#include "ecdsa_pok/sha256_circuit.hpp"
#include "qs_bit.hpp"
#include "sha256/sha256.hpp"
#include "voleith.hpp"
#include "witness_prg.hpp"

#include "hash.hpp"       // from faest-arch-opt
#include "parameters.hpp" // from faest-arch-opt

#include <algorithm>
#include <array>
#include <cstddef>
#include <cstdint>
#include <span>
#include <stdexcept>
#include <type_traits>
#include <utility>
#include <vector>

namespace vole_mole::ecdsa_pok::detail::mdoc {

constexpr size_t MAX_ATTRIBUTES = 4;

// The link values, in this order in the proof: the issuer's Z_n, Z_p, and the device's Z_q, Z_n',
// Z_p'.
enum LinkValue : size_t { Z_N = 0, Z_P = 1, Z_Q = 2, Z_DN = 3, Z_DP = 4, NUM_Z = 5 };
constexpr std::array<size_t, NUM_Z> Z_COLS = {ZN_COLS, ZP_COLS, rr::Z_COLS, hk::Z_COLS, hk::Z_COLS};
using LinkValues = std::array<uint8_t, NUM_Z * Z_BYTES>;
inline std::span<uint8_t, Z_BYTES> z_at(std::span<uint8_t, NUM_Z * Z_BYTES> z, size_t i) {
    return std::span<uint8_t, Z_BYTES>(z.data() + i * Z_BYTES, Z_BYTES);
}

// The issuer's signed message: at most MAX_BLOCKS SHA-256 blocks (as Longfellow's version 7).
constexpr size_t MAX_BLOCKS = 40;
constexpr size_t SIG_BYTES = 64 * MAX_BLOCKS;
// 84 6A "Signature1" 43 A1 01 26 40 59: the COSE Sig_structure ["Signature1", {1: -7}, h'',
// payload] with a payload of 256 to 65535 bytes.
constexpr std::array<uint8_t, 18> COSE_PREFIX = {0x84, 0x6A, 'S',  'i',  'g',  'n',
                                                 'a',  't',  'u',  'r',  'e',  '1',
                                                 0x43, 0xA1, 0x01, 0x26, 0x40, 0x59};

// The patterns of the MSO (see above), up to their secret parts.
constexpr std::array<uint8_t, 12> VALID_FROM = {0x69, 'v', 'a', 'l', 'i',  'd',
                                                'F',  'r', 'o', 'm', 0xC0, 0x74};
constexpr std::array<uint8_t, 13> VALID_UNTIL = {0x6A, 'v', 'a', 'l', 'i',  'd', 'U',
                                                 'n',  't', 'i', 'l', 0xC0, 0x74};
constexpr std::array<uint8_t, 33> DEVICE_KEY = {
    0x6D, 'd', 'e', 'v', 'i', 'c', 'e', 'K', 'e',  'y',  'I',  'n',  'f',  'o',  0xA1, 0x69, 'd',
    'e',  'v', 'i', 'c', 'e', 'K', 'e', 'y', 0xA4, 0x01, 0x02, 0x20, 0x01, 0x21, 0x58, 0x20};
constexpr std::array<uint8_t, 3> DEVICE_KEY_Y = {0x22, 0x58, 0x20};
constexpr std::array<uint8_t, 13> VALUE_DIGESTS = {0x6C, 'v', 'a', 'l', 'u', 'e', 'D',
                                                   'i',  'g', 'e', 's', 't', 's'};
constexpr std::array<uint8_t, 2> DIGEST = {0x58, 0x20};
constexpr size_t DATE_BYTES = 20;

// The windows of the MSO: validFrom, validUntil, deviceKeyInfo, valueDigests, then the
// attributes' digests.
enum Window : size_t { W_FROM = 0, W_UNTIL = 1, W_KEY = 2, W_DIGESTS = 3, W_ATTR = 4 };
constexpr size_t window_bytes(size_t w) {
    return w == W_FROM      ? VALID_FROM.size() + DATE_BYTES
           : w == W_UNTIL   ? VALID_UNTIL.size() + DATE_BYTES
           : w == W_KEY     ? DEVICE_KEY.size() + 32 + DEVICE_KEY_Y.size() + 32
           : w == W_DIGESTS ? VALUE_DIGESTS.size()
                            : DIGEST.size() + 32;
}
constexpr size_t BLOCK_BYTES = 64;

// IssuerSignedItemBytes: 2 padded blocks, D8 18 58 xx A4, then the fields from offset 5.
constexpr size_t ITEM_BYTES = 128;
constexpr size_t ITEM_FIRST = 5;                         // offset of the first field
constexpr size_t ITEM_MAX_LEN = ITEM_BYTES - 9;          // 119
constexpr size_t ITEM_SLOTS = ITEM_MAX_LEN - ITEM_FIRST; // positions of slots 1, 2, 3: [5, 119)
constexpr size_t POS_BITS = 10;                          // width of position sums
constexpr std::array<uint8_t, 9> DIGEST_ID = {0x68, 'd', 'i', 'g', 'e', 's', 't', 'I', 'D'};
constexpr std::array<uint8_t, 7> RANDOM = {0x66, 'r', 'a', 'n', 'd', 'o', 'm'};
constexpr std::array<uint8_t, 18> ELEMENT_ID = {0x71, 'e', 'l', 'e', 'm', 'e', 'n', 't', 'I',
                                                'd',  'e', 'n', 't', 'i', 'f', 'i', 'e', 'r'};
constexpr std::array<uint8_t, 13> ELEMENT_VALUE = {0x6C, 'e', 'l', 'e', 'm', 'e', 'n',
                                                   't',  'V', 'a', 'l', 'u', 'e'};
enum Field : size_t { F_DIGEST_ID = 0, F_RANDOM = 1, F_ID = 2, F_VALUE = 3 };
// The digestID's lengths (key and header) by header length 1, 2, 3, 5.
constexpr std::array<uint8_t, 4> DIGEST_ID_LENS = {10, 11, 12, 14};

// The public values of the binary relation besides mu.
struct BinPublic {
    std::array<uint8_t, DATE_BYTES> now;
    // For each attribute, the patterns 71 "elementIdentifier" <tstr> and 6C "elementValue" <value>
    // (each of at most ITEM_MAX_LEN - ITEM_FIRST bytes).
    std::vector<std::vector<uint8_t>> ei, ev;
};

// The values the prover commits to (PlainOps only).
struct ItemValues {
    std::array<uint8_t, ITEM_BYTES> buf; // padded
    size_t len;                          // L
    std::array<size_t, 4> slot_pos;      // pos_0 = 5, pos_1, pos_2, pos_3
    std::array<size_t, 4> slot_of;       // the slot of each field
    std::array<size_t, 4> slot_len;      // len_j
    size_t id_class;                     // index into DIGEST_ID_LENS
    size_t rnd_len;                      // the random field's length
    bool rnd_long;                       // ai = 24
    uint8_t rnd_n;                       // the random value's length
};

struct MdocValues {
    std::array<uint8_t, SIG_BYTES> sig; // the padded message, then zeros
    std::vector<sha256::Trace> traces;  // MAX_BLOCKS
    size_t last;                        // index of the last block
    std::array<uint8_t, DATE_BYTES> valid_from, valid_until;
    std::vector<size_t> windows;    // offsets of the windows
    std::array<uint8_t, 32> x;      // issuer's X, little endian
    std::array<uint8_t, 32> qx, qy; // device key, little endian
    std::array<uint8_t, 32> xd;     // device's X', little endian
    std::vector<ItemValues> items;
    std::array<uint8_t, Z_BYTES> rho_n, rho_p, rho_q, rho_dn, rho_dp;
};

template <typename Ops> struct MdocWires {
    PrefixWires<Ops> issuer;   // e, X, rho_n, rho_p
    rr::PrefixWires<Ops> dev;  // x_Q, y_Q, rho_q
    hk::PrefixWires<Ops> dsig; // X', rho_n', rho_p'
    // Indices in the witness of the first bit of: t, and each window's block selector (for
    // tests).
    size_t t_bit = 0;
    std::vector<size_t> window_bits;
};

namespace impl {

template <typename Ops> using Wires = std::vector<typename Ops::Wire>;

template <typename Ops> void push_byte(Ops& ops, Wires<Ops>& v, uint8_t b) {
    for (size_t i = 0; i < 8; ++i) {
        v.push_back(((b >> i) & 1) ? ops.one() : ops.zero());
    }
}
template <typename Ops> void push_bytes(Ops& ops, Wires<Ops>& v, std::span<const uint8_t> b) {
    for (const uint8_t x : b) {
        push_byte(ops, v, x);
    }
}
template <typename Ops> Wires<Ops> commit_bits(Ops& ops, size_t n, const uint8_t* v) {
    Wires<Ops> out;
    out.reserve(n);
    for (size_t i = 0; i < n; ++i) {
        out.push_back(ops.commit(v && ((v[i / 8] >> (i % 8)) & 1)));
    }
    return out;
}
template <typename Ops> Wires<Ops> commit_value(Ops& ops, size_t n, uint64_t v, bool plain) {
    Wires<Ops> out;
    for (size_t i = 0; i < n; ++i) {
        out.push_back(ops.commit(plain && ((v >> i) & 1)));
    }
    return out;
}
// A one-hot vector of n bits with bit `k` set.
template <typename Ops> Wires<Ops> commit_onehot(Ops& ops, size_t n, size_t k, bool plain) {
    Wires<Ops> out;
    for (size_t i = 0; i < n; ++i) {
        out.push_back(ops.commit(plain && i == k));
    }
    assert_onehot(ops, std::span<const typename Ops::Wire>(out));
    return out;
}
// The big-endian bytes (as wires, least significant bit first) of the 256-bit integer with
// little-endian bits v.
template <typename V> void push_be256(V& out, const V& v) {
    for (size_t j = 0; j < 32; ++j) {
        for (size_t i = 0; i < 8; ++i) {
            out.push_back(v[8 * (31 - j) + i]);
        }
    }
}
// SHA-256 digest words as the integer e (little-endian bits): word w holds bits 32 (7 - w) + i.
template <typename Ops> Wires<Ops> digest_int(const std::array<Word<Ops>, 8>& h) {
    Wires<Ops> out(256);
    for (size_t w = 0; w < 8; ++w) {
        for (size_t i = 0; i < 32; ++i) {
            out[32 * (7 - w) + i] = h[w].w[i];
        }
    }
    return out;
}
template <typename Ops> typename Ops::Wire xor_of(Ops& ops, std::span<const typename Ops::Wire> v) {
    typename Ops::Wire acc = ops.zero();
    for (const auto& w : v) {
        acc = ops.add(acc, w);
    }
    return acc;
}

// A window of `bytes` bytes of buf at a secret offset (a one-hot block and offset in the block),
// equal to `pattern`.
template <typename Ops>
void window(Ops& ops, const Wires<Ops>& buf, const Wires<Ops>& pattern, size_t pos, bool plain) {
    const size_t w = pattern.size() / 8;
    const Wires<Ops> hi = commit_onehot(ops, MAX_BLOCKS, pos / BLOCK_BYTES, plain);
    const Wires<Ops> lo = commit_onehot(ops, BLOCK_BYTES, pos % BLOCK_BYTES, plain);
    std::vector<SelTerm<typename Ops::Wire>> terms;
    for (size_t h = 0; h < MAX_BLOCKS; ++h) {
        for (size_t l = 0; l < BLOCK_BYTES; ++l) {
            if (BLOCK_BYTES * h + l + w <= SIG_BYTES) {
                terms.push_back({hi[h], lo[l], BLOCK_BYTES * h + l});
            }
        }
    }
    assert_window(ops, std::span<const typename Ops::Wire>(buf),
                  std::span<const SelTerm<typename Ops::Wire>>(terms),
                  std::span<const typename Ops::Wire>(pattern));
}

// Monomials for assert_poly.
template <typename Ops> struct Poly {
    std::vector<Monomial<typename Ops::Wire>> m;
    using W = typename Ops::Wire;
    Poly& one(Ops& ops) {
        m.push_back({{ops.zero(), ops.zero(), ops.zero()}, 0});
        return *this;
    }
    Poly& add(const W& a) {
        m.push_back({{a, a, a}, 1});
        return *this;
    }
    Poly& add(const W& a, const W& b) {
        m.push_back({{a, b, b}, 2});
        return *this;
    }
    Poly& add(const W& a, const W& b, const W& c) {
        m.push_back({{a, b, c}, 3});
        return *this;
    }
    void check(Ops& ops) { assert_poly(ops, std::span<const Monomial<W>>(m)); }
};

// c (b - v) = 0 for each bit b of the low 5 bits of h, i.e., c implies that ai = v.
template <typename Ops>
void implies_ai(Ops& ops, const typename Ops::Wire& c, const Wires<Ops>& h, uint8_t v) {
    for (size_t i = 0; i < 5; ++i) {
        Poly<Ops> p;
        p.add(c, h[i]);
        if ((v >> i) & 1) {
            p.add(c);
        }
        p.check(ops);
    }
}

// The checks of one attribute (see 3. above), returning its digest as big-endian bytes.
template <size_t LOG, typename Ops>
Wires<Ops> item_circuit(Ops& ops, std::span<const uint8_t> ei, std::span<const uint8_t> ev,
                        const ItemValues* v) {
    using Wire = typename Ops::Wire;
    const bool plain = v != nullptr;
    // The buffer: constants D8 18 58, committed byte 3, constant A4, committed bytes [5, 120), and
    // the 64-bit bit length 8 L from the 7 committed bits of L.
    Wires<Ops> buf;
    buf.reserve(8 * ITEM_BYTES);
    push_bytes(ops, buf, std::array<uint8_t, 3>{0xD8, 0x18, 0x58});
    for (Wire& w : commit_bits(ops, 8, plain ? &v->buf[3] : nullptr)) {
        buf.push_back(w);
    }
    push_byte(ops, buf, 0xA4);
    for (Wire& w :
         commit_bits(ops, 8 * (120 - ITEM_FIRST), plain ? &v->buf[ITEM_FIRST] : nullptr)) {
        buf.push_back(w);
    }
    const Wires<Ops> len = commit_value(ops, 7, plain ? v->len : 0, plain);
    for (size_t i = 0; i < 6; ++i) {
        push_byte(ops, buf, 0);
    }
    // Byte 126 holds bits 8, 9 of 8 L (bits 5, 6 of L); byte 127 holds bits 3..7 (bits 0..4 of L).
    for (size_t i = 0; i < 8; ++i) {
        buf.push_back(i < 2 ? len[5 + i] : ops.zero());
    }
    for (size_t i = 0; i < 8; ++i) {
        buf.push_back(i >= 3 ? len[i - 3] : ops.zero());
    }

    // The digest.
    ShaCircuit<Ops> sha{ops};
    std::array<Word<Ops>, 8> h;
    for (size_t i = 0; i < 8; ++i) {
        h[i] = Word<Ops>::constant(sha256::IV[i]);
    }
    for (size_t b = 0; b < 2; ++b) {
        h = sha.compress(h, std::span<const Wire, 512>(buf.data() + 512 * b, 512));
    }
    Wires<Ops> digest;
    push_be256(digest, digest_int(h));

    // Slots 1, 2, 3: one-hot positions in [5, 119), and their positions as integers.
    std::array<Wires<Ops>, 4> slot;
    std::array<Wires<Ops>, 4> pos;
    for (size_t j = 0; j < 4; ++j) {
        pos[j].resize(POS_BITS, ops.zero());
        if (j == 0) {
            for (size_t b = 0; b < POS_BITS; ++b) {
                pos[0][b] = ((ITEM_FIRST >> b) & 1) ? ops.one() : ops.zero();
            }
            continue;
        }
        slot[j] = commit_onehot(ops, ITEM_SLOTS, plain ? v->slot_pos[j] - ITEM_FIRST : 0, plain);
        for (size_t k = 0; k < ITEM_SLOTS; ++k) {
            for (size_t b = 0; b < 7; ++b) {
                if (((ITEM_FIRST + k) >> b) & 1) {
                    pos[j][b] = ops.add(pos[j][b], slot[j][k]);
                }
            }
        }
    }
    // sigma_f: the slot of field f.
    std::array<Wires<Ops>, 4> sigma;
    for (size_t f = 0; f < 4; ++f) {
        sigma[f] = commit_onehot(ops, 4, plain ? v->slot_of[f] : 0, plain);
    }

    // digestID: its header H and class c.
    const Wires<Ops> hd =
        commit_value(ops, 8, plain ? v->buf[v->slot_pos[v->slot_of[F_DIGEST_ID]] + 9] : 0, plain);
    const Wires<Ops> cls = commit_onehot(ops, 4, plain ? v->id_class : 0, plain);
    for (size_t i = 5; i < 8; ++i) {
        ops.assert_eq(hd[i], false); // major type 0
    }
    Poly<Ops>().add(cls[0], hd[4], hd[3]).check(ops); // ai < 24
    implies_ai(ops, cls[1], hd, 24);
    implies_ai(ops, cls[2], hd, 25);
    implies_ai(ops, cls[3], hd, 26);
    Wires<Ops> len_id(POS_BITS, ops.zero());
    for (size_t c = 0; c < 4; ++c) {
        for (size_t b = 0; b < POS_BITS; ++b) {
            if ((DIGEST_ID_LENS[c] >> b) & 1) {
                len_id[b] = ops.add(len_id[b], cls[c]);
            }
        }
    }

    // random: its header H, the next byte N, the flag f (ai = 24), its length n, and the field's
    // length 8 + f + n.
    const size_t rpos = plain ? v->slot_pos[v->slot_of[F_RANDOM]] : 0;
    const Wires<Ops> hr = commit_value(ops, 8, plain ? v->buf[rpos + 7] : 0, plain);
    const Wires<Ops> nn = commit_value(ops, 8, plain ? v->buf[rpos + 8] : 0, plain);
    const Wire flag = ops.commit(plain && v->rnd_long);
    const Wires<Ops> nval = commit_value(ops, 8, plain ? v->rnd_n : 0, plain);
    const Wires<Ops> len_rnd = commit_value(ops, POS_BITS, plain ? v->rnd_len : 0, plain);
    ops.assert_eq(hr[7], false); // major type 2
    ops.assert_eq(hr[6], true);
    ops.assert_eq(hr[5], false);
    implies_ai(ops, flag, hr, 24);
    Poly<Ops>().add(hr[4], hr[3]).add(flag, hr[4], hr[3]).check(ops); // not f implies ai < 24
    for (size_t b = 0; b < 8; ++b) {
        // n = f N + (1 - f) ai
        Poly<Ops> p;
        p.add(nval[b]).add(flag, nn[b]);
        if (b < 5) {
            p.add(hr[b]).add(flag, hr[b]);
        }
        p.check(ops);
    }
    {
        ColSum<Ops> s(ops, POS_BITS);
        s.add_const(8, 0);
        s.add(flag, 0);
        for (size_t b = 0; b < 8; ++b) {
            s.add(nval[b], b);
        }
        for (size_t b = 0; b < POS_BITS; ++b) {
            s.sub(len_rnd[b], b);
        }
        s.template assert_zero<LOG>();
    }

    // The fields' lengths, by slot: len_j = sum_f sigma_f[j] len_f.
    std::array<Wires<Ops>, 4> len_f;
    len_f[F_DIGEST_ID] = len_id;
    len_f[F_RANDOM] = len_rnd;
    for (const size_t f : {F_ID, F_VALUE}) {
        const size_t l = f == F_ID ? ei.size() : ev.size();
        for (size_t b = 0; b < POS_BITS; ++b) {
            len_f[f].push_back(((l >> b) & 1) ? ops.one() : ops.zero());
        }
    }
    std::array<Wires<Ops>, 4> len_slot;
    for (size_t j = 0; j < 4; ++j) {
        len_slot[j] = commit_value(ops, POS_BITS, plain ? v->slot_len[j] : 0, plain);
        for (size_t b = 0; b < POS_BITS; ++b) {
            Poly<Ops> p;
            p.add(len_slot[j][b]);
            for (size_t f = 0; f < 4; ++f) {
                p.add(sigma[f][j], len_f[f][b]);
            }
            p.check(ops);
        }
    }
    // pos_{j+1} = pos_j + len_j, with pos_4 = L.
    for (size_t j = 0; j < 4; ++j) {
        ColSum<Ops> s(ops, POS_BITS);
        for (size_t b = 0; b < POS_BITS; ++b) {
            s.add(pos[j][b], b);
            s.add(len_slot[j][b], b);
            if (j < 3) {
                s.sub(pos[j + 1][b], b);
            } else if (b < 7) {
                s.sub(len[b], b);
            }
        }
        s.template assert_zero<LOG>();
    }

    // The fields' patterns at their slots.
    for (size_t f = 0; f < 4; ++f) {
        Wires<Ops> pat;
        if (f == F_DIGEST_ID) {
            push_bytes(ops, pat, DIGEST_ID);
            pat.insert(pat.end(), hd.begin(), hd.end());
        } else if (f == F_RANDOM) {
            push_bytes(ops, pat, RANDOM);
            pat.insert(pat.end(), hr.begin(), hr.end());
            pat.insert(pat.end(), nn.begin(), nn.end());
        } else {
            push_bytes(ops, pat, f == F_ID ? ei : ev);
        }
        const size_t w = pat.size() / 8;
        std::vector<SelTerm<Wire>> terms;
        if (ITEM_FIRST + w <= ITEM_BYTES) {
            terms.push_back({sigma[f][0], ops.one(), ITEM_FIRST});
        }
        for (size_t j = 1; j < 4; ++j) {
            for (size_t k = 0; k < ITEM_SLOTS; ++k) {
                if (ITEM_FIRST + k + w <= ITEM_BYTES) {
                    terms.push_back({sigma[f][j], slot[j][k], ITEM_FIRST + k});
                }
            }
        }
        assert_window(ops, std::span<const Wire>(buf), std::span<const SelTerm<Wire>>(terms),
                      std::span<const Wire>(pat));
    }
    return digest;
}

} // namespace impl

// The prefix circuit (everything but the carries of the link sums), with counters of size LOG.
// vals is null except for PlainOps.
template <size_t LOG, typename Ops>
MdocWires<Ops> prefix_circuit(Ops& ops, const BinPublic& pub, const MdocValues* vals) {
    using namespace impl;
    using Wire = typename Ops::Wire;
    const bool plain = vals != nullptr;
    const size_t na = pub.ei.size();
    MdocWires<Ops> out;

    // 1. The message, its SHA-256 chaining values, and e.
    Wires<Ops> msg;
    msg.reserve(8 * SIG_BYTES);
    push_bytes(ops, msg, COSE_PREFIX);
    for (Wire& w : commit_bits(ops, 8 * (SIG_BYTES - COSE_PREFIX.size()),
                               plain ? &vals->sig[COSE_PREFIX.size()] : nullptr)) {
        msg.push_back(w);
    }
    ShaCircuit<Ops> sha{ops};
    std::array<Word<Ops>, 8> h;
    for (size_t i = 0; i < 8; ++i) {
        h[i] = Word<Ops>::constant(sha256::IV[i]);
    }
    std::vector<Wires<Ops>> chain;
    for (size_t b = 0; b < MAX_BLOCKS; ++b) {
        h = sha.compress(h, std::span<const Wire, 512>(msg.data() + 512 * b, 512));
        chain.push_back(digest_int(h));
    }
    out.t_bit = ops.next;
    const Wires<Ops> t = commit_onehot(ops, MAX_BLOCKS, plain ? vals->last : 0, plain);
    std::array<uint8_t, 32> e_le{};
    if (plain) {
        const auto& s = vals->traces[vals->last].out;
        for (size_t w = 0; w < 8; ++w) {
            for (size_t i = 0; i < 32; ++i) {
                set_bit(e_le, 32 * (7 - w) + i, ((s[w] >> i) & 1) != 0);
            }
        }
    }
    out.issuer.e = commit_bits(ops, 256, plain ? e_le.data() : nullptr);
    assert_select(ops, std::span<const Wire>(t), std::span<const Wires<Ops>>(chain),
                  std::span<const Wire>(out.issuer.e));
    {
        // The blocks after t are zero: block b is after t iff t_{b'} = 1 for some b' < b.
        Wires<Ops> after;
        std::vector<Wires<Ops>> blocks;
        Wire acc = ops.zero();
        for (size_t b = 1; b < MAX_BLOCKS; ++b) {
            acc = ops.add(acc, t[b - 1]);
            after.push_back(acc);
            blocks.emplace_back(msg.begin() + static_cast<ptrdiff_t>(512 * b),
                                msg.begin() + static_cast<ptrdiff_t>(512 * (b + 1)));
        }
        assert_and_zero(ops, std::span<const Wire>(after), std::span<const Wires<Ops>>(blocks));
    }

    // 4. X, x_Q, y_Q < p.
    out.issuer.x = rr::canonical_coordinate<LOG>(ops, plain ? &vals->x : nullptr);
    out.dev.x = rr::canonical_coordinate<LOG>(ops, plain ? &vals->qx : nullptr);
    out.dev.y = rr::canonical_coordinate<LOG>(ops, plain ? &vals->qy : nullptr);
    out.dsig.x = rr::canonical_coordinate<LOG>(ops, plain ? &vals->xd : nullptr);

    // 2. The dates, and their comparisons with now (20-byte big-endian integers).
    const Wires<Ops> from =
        commit_bits(ops, 8 * DATE_BYTES, plain ? vals->valid_from.data() : nullptr);
    const Wires<Ops> until =
        commit_bits(ops, 8 * DATE_BYTES, plain ? vals->valid_until.data() : nullptr);
    // now as constant wires (rather than ColSum constants, so that the number of carries doesn't
    // depend on it).
    Wires<Ops> now;
    push_bytes(ops, now, pub.now);
    auto leq = [&](const Wires<Ops>& a, const Wires<Ops>& b) {
        // b - a + 2^160 >= 2^160.
        ColSum<Ops> s(ops, 8 * DATE_BYTES + 1);
        for (size_t j = 0; j < DATE_BYTES; ++j) {
            for (size_t i = 0; i < 8; ++i) {
                const size_t col = 8 * (DATE_BYTES - 1 - j) + i;
                s.add(b[8 * j + i], col);
                s.sub(a[8 * j + i], col);
            }
        }
        s.add_const(1, 8 * DATE_BYTES);
        s.template reduce<LOG>([&](size_t col, const Wire& w) {
            if (col == 8 * DATE_BYTES) {
                ops.assert_eq(w, true);
            }
        });
    };
    leq(from, now);
    leq(now, until);

    // 3. The attributes.
    std::vector<Wires<Ops>> digests;
    for (size_t a = 0; a < na; ++a) {
        digests.push_back(
            item_circuit<LOG>(ops, pub.ei[a], pub.ev[a], plain ? &vals->items[a] : nullptr));
    }

    // 2. The windows of the MSO.
    for (size_t w = 0; w < W_ATTR + na; ++w) {
        Wires<Ops> pat;
        switch (w) {
        case W_FROM:
            push_bytes(ops, pat, VALID_FROM);
            pat.insert(pat.end(), from.begin(), from.end());
            break;
        case W_UNTIL:
            push_bytes(ops, pat, VALID_UNTIL);
            pat.insert(pat.end(), until.begin(), until.end());
            break;
        case W_KEY:
            push_bytes(ops, pat, DEVICE_KEY);
            push_be256(pat, out.dev.x);
            push_bytes(ops, pat, DEVICE_KEY_Y);
            push_be256(pat, out.dev.y);
            break;
        case W_DIGESTS:
            push_bytes(ops, pat, VALUE_DIGESTS);
            break;
        default:
            push_bytes(ops, pat, DIGEST);
            pat.insert(pat.end(), digests[w - W_ATTR].begin(), digests[w - W_ATTR].end());
        }
        out.window_bits.push_back(ops.next);
        window(ops, msg, pat, plain ? vals->windows[w] : 0, plain);
    }

    // The masks.
    out.issuer.rho_n = commit_bits(ops, RHO_N_BITS, plain ? vals->rho_n.data() : nullptr);
    out.issuer.rho_p = commit_bits(ops, RHO_P_BITS, plain ? vals->rho_p.data() : nullptr);
    out.dev.rho = commit_bits(ops, rr::RHO_BITS, plain ? vals->rho_q.data() : nullptr);
    out.dsig.rho_n = commit_bits(ops, hk::RHO_BITS, plain ? vals->rho_dn.data() : nullptr);
    out.dsig.rho_p = commit_bits(ops, hk::RHO_BITS, plain ? vals->rho_dp.data() : nullptr);
    return out;
}

// The link carries' budget: the issuer's (binary.hpp) and the device's (rr_binary.hpp and
// hk_binary.hpp).
template <size_t LOG>
constexpr size_t LINK_BUDGET =
    detail::LINK_BUDGET<LOG> + rr::LINK_BUDGET<LOG> + hk::LINK_BUDGET<LOG>;

// The link circuit: the link sums, with carries in [first, first + LINK_BUDGET<LOG>). Throws
// std::runtime_error if the budget is exceeded (which happens with negligible probability).
template <size_t LOG, typename Ops>
void link_circuit(Ops& ops, const MdocWires<Ops>& in, const LinkChallenge& chal,
                  const LinkChallenge& dchal, std::span<uint8_t, NUM_Z * Z_BYTES> z, bool record) {
    const size_t first = ops.next;
    detail::link_sums<LOG>(ops, in.issuer, chal, z_at(z, Z_N), z_at(z, Z_P), record);
    rr::link_sums<LOG>(ops, in.dev, dchal, z_at(z, Z_Q), record);
    hk::link_sums<LOG>(ops, in.dsig, dchal, z_at(z, Z_DN), z_at(z, Z_DP), record);
    if (ops.next > first + LINK_BUDGET<LOG>) {
        throw std::runtime_error("ecdsa_pok: link carry budget exceeded");
    }
    while (ops.next < first + LINK_BUDGET<LOG>) {
        ops.assert_eq(ops.commit(false), false);
    }
}

// Counts of the circuits (checked by test_mdoc.cpp against CountOps): the prefix's committed bits
// and the constraints (besides the bit constraints), by number of attributes and counter size.
struct Counts {
    size_t prefix_bits, constraints;
};
// Index LOG - 2, then number of attributes - 1.
constexpr std::array<std::array<Counts, MAX_ATTRIBUTES>, 2> COUNTS = {{
    {{{809544, 817142}, {848136, 854401}, {886728, 891660}, {925320, 928919}}},
    {{{809544, 799454}, {848136, 836713}, {886728, 873972}, {925320, 911231}}},
}};
constexpr Counts counts(size_t log, size_t na) { return COUNTS[log - 2][na - 1]; }

constexpr size_t prefix_bytes(size_t log, size_t na) {
    return (counts(log, na).prefix_bits + 7) / 8;
}
template <Shape SH> constexpr size_t witness_bits(size_t na) {
    return 8 * prefix_bytes(SH.small_log, na) + LINK_BUDGET<SH.link_log>;
}
template <Shape SH> constexpr size_t circuit_constraints(size_t na) {
    return counts(SH.small_log, na).constraints;
}

template <Shape SH> Counts count_circuit(const BinPublic& pub) {
    CountOps ops;
    const auto wires = prefix_circuit<SH.small_log>(ops, pub, nullptr);
    Counts out{ops.next, 0};
    ops.next = 8 * ((out.prefix_bits + 7) / 8);
    const LinkChallenge chal = derive_link_challenge(Digest{});
    LinkValues z{};
    link_circuit<SH.link_log>(ops, wires, chal, chal, z, false);
    out.constraints = ops.constraints;
    return out;
}

// owf IDs 0xb0 + 4 prg + (na - 1).
constexpr faest::owf owf_for(size_t na, BinPrg prg) {
    return static_cast<faest::owf>(((0xb0u + 4 * std::to_underlying(prg) + (na - 1)) << 8) |
                                   faest::owf_flag_witness_bits_check);
}
constexpr bool is_mdoc_owf(faest::owf o) {
    const auto v = std::to_underlying(o);
    const auto hi = v >> 8;
    return (v & 0xff) == faest::owf_flag_witness_bits_check && hi >= 0xb0 && hi < 0xbc;
}
constexpr BinPrg prg_of_owf(faest::owf o) {
    return static_cast<BinPrg>(((std::to_underlying(o) >> 8) - 0xb0) / 4);
}
constexpr size_t na_of_owf(faest::owf o) { return ((std::to_underlying(o) >> 8) - 0xb0) % 4 + 1; }

} // namespace vole_mole::ecdsa_pok::detail::mdoc

template <faest::owf O>
    requires(vole_mole::ecdsa_pok::detail::mdoc::is_mdoc_owf(O))
struct faest::OWF_CONSTANTS<faest::secpar::s128, O>
    : vole_mole::detail::RelationConstants<
          vole_mole::ecdsa_pok::detail::mdoc::witness_bits<vole_mole::ecdsa_pok::detail::SHAPE<
              vole_mole::ecdsa_pok::detail::mdoc::prg_of_owf(O)>>(
              vole_mole::ecdsa_pok::detail::mdoc::na_of_owf(O)),
          vole_mole::ecdsa_pok::detail::BIN_QS_DEGREE<
              vole_mole::ecdsa_pok::detail::mdoc::prg_of_owf(O)>,
          typename vole_mole::ecdsa_pok::detail::bin_prg<
              vole_mole::ecdsa_pok::detail::mdoc::prg_of_owf(O)>::type> {};

namespace vole_mole::ecdsa_pok::detail::mdoc {

template <size_t NA, bool SMALL, BinPrg PRG>
using BinParams =
    faest::parameter_set<faest::secpar::s128, SMALL ? 11 : 17, mdoc::owf_for(NA, PRG),
                         faest::prg::aes_ctr, faest::prg::aes_ctr, faest::leaf_hash::aes_ctr,
                         SMALL ? 7 : 8, {faest::bavc::one_tree, SMALL ? 103u : 105u}, true, true>;

template <size_t NA, bool SMALL, BinPrg PRG> struct BinRelation {
    using params = BinParams<NA, SMALL, PRG>;
    static constexpr Shape SH = SHAPE<PRG>;
    static constexpr bool DERIVED = PRG != BinPrg::none;

    struct instance {
        const Digest* mu;
        const BinPublic* pub;
        const LinkChallenge* chal;
        const LinkChallenge* dchal;
        LinkValues z;
    };

    static constexpr size_t RELATION_WITNESS_BITS = witness_bits<SH>(NA);
    static constexpr size_t WITNESS_PREFIX_BYTES = prefix_bytes(SH.small_log, NA);
    static constexpr std::span<const uint8_t> DST = vole_mole::detail::ECDSA_MDOC_BINARY_DST;
    static constexpr std::span<const uint8_t> WITNESS_PRG_DST =
        vole_mole::detail::ECDSA_MDOC_BINARY_PRG_DST;
    static constexpr size_t NUM_CONSTRAINTS = vole_mole::detail::qs_batches(
        (DERIVED ? 0 : RELATION_WITNESS_BITS) + circuit_constraints<SH>(NA));

    static void hash_instance(faest::hash_state& hasher, const instance& x) {
        hasher.update(*x.mu);
        hasher.update(x.chal->digest);
        hasher.update(x.dchal->digest);
        hasher.update(x.z);
    }

    template <typename QS>
    static void constraints(QS* qs, const instance& x,
                            std::span<const uint8_t, params::CONSTS::QS::CHALLENGE_BYTES> chal2) {
        static_assert(QS::max_degree == BIN_QS_DEGREE<PRG>);
        SelQsOps<QS> ops(qs, chal2, vole_mole::detail::ECDSA_MDOC_SELECT_DST);
        if constexpr (!DERIVED) {
            for (size_t i = 0; i < RELATION_WITNESS_BITS; ++i) {
                ops.assert_bit(qs->get_witness_bit(i));
            }
        }
        const auto wires = prefix_circuit<SH.small_log>(ops, *x.pub, nullptr);
        ops.next = 8 * WITNESS_PREFIX_BYTES;
        auto z = x.z;
        link_circuit<SH.link_log>(ops, wires, *x.chal, *x.dchal, z, false);
        ops.finish();
    }
};

} // namespace vole_mole::ecdsa_pok::detail::mdoc

#endif
