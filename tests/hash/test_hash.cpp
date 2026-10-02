// Tests for the TurboSHAKE option of faest-arch-opt's hash_state and hash_state_x4. (Their SHAKE
// mode is covered by the FAEST known answers in voleith/test_voleith.cpp.)

#include "test.hpp"

#include "hash.hpp" // from faest-arch-opt

#include <gtest/gtest.h>

#include <algorithm>
#include <array>
#include <cstddef>
#include <cstdint>
#include <span>
#include <string>
#include <vector>

using faest::secpar;
using faest::xof;
using vole_mole::test::to_hex;

namespace {

// ptn(n) from RFC 9861, Section 5: the pattern 00 01 02 .. F9 FA, repeated and truncated to n
// bytes.
std::vector<uint8_t> ptn(size_t n) {
    std::vector<uint8_t> out(n);
    for (size_t i = 0; i < n; ++i) {
        out[i] = static_cast<uint8_t>(i % 0xfb);
    }
    return out;
}

std::string turboshake(secpar s, const std::vector<uint8_t>& msg, size_t out_len) {
    faest::hash_state hasher;
    hasher.init(s, xof::turboshake);
    hasher.update(msg.data(), msg.size());
    std::vector<uint8_t> out(out_len);
    hasher.finalize(out.data(), out.size());
    return to_hex(out);
}

struct KnownAnswer {
    secpar s;
    size_t msg_len;
    size_t out_len;
    const char* want;
};

// TurboSHAKE128 and TurboSHAKE256 with D = 1F, from RFC 9861, Section 5.
const KnownAnswer KNOWN_ANSWERS[] = {
    {secpar::s128, 0, 32, "1e415f1c5983aff2169217277d17bb538cd945a397ddec541f1ce41af2c1b74c"},
    {secpar::s128, 0, 64,
     "1e415f1c5983aff2169217277d17bb538cd945a397ddec541f1ce41af2c1b74c"
     "3e8ccae2a4dae56c84a04c2385c03c15e8193bdf58737363321691c05462c8df"},
    {secpar::s128, 1, 32, "55cedd6f60af7bb29a4042ae832ef3f58db7299f893ebb9247247d856958daa9"},
    {secpar::s128, 17, 32, "9c97d036a3bac819db70ede0ca554ec6e4c2a1a4ffbfd9ec269ca6a111161233"},
    {secpar::s128, 17 * 17, 32, "96c77c279e0126f7fc07c9b07f5cdae1e0be60bdbe10620040e75d7223a624d2"},
    {secpar::s128, 17 * 17 * 17, 32,
     "d4976eb56bcf118520582b709f73e1d6853e001fdaf80e1b13e0d0599d5fb372"},
    {secpar::s256, 0, 64,
     "367a329dafea871c7802ec67f905ae13c57695dc2c6663c61035f59a18f8e7db"
     "11edc0e12e91ea60eb6b32df06dd7f002fbafabb6e13ec1cc20d995547600db0"},
    {secpar::s256, 17, 64,
     "b3bab0300e6a191fbe6137939835923578794ea54843f5011090fa2f3780a9e5"
     "cb22c59d78b40a0fbff9e672c0fbe0970bd2c845091c6044d687054da5d8e9c7"},
    {secpar::s256, 17 * 17, 64,
     "66b810db8e90780424c0847372fdc95710882fde31c6df75beb9d4cd9305cfca"
     "e35e7b83e8b7e6eb4b78605880116316fe2c078a09b94ad7b8213c0a738b65c0"},
};

} // namespace

TEST(TurboShake, KnownAnswers) {
    for (const auto& ka : KNOWN_ANSWERS) {
        EXPECT_EQ(turboshake(ka.s, ptn(ka.msg_len), ka.out_len), ka.want)
            << "secpar " << faest::secpar_to_bits(ka.s) << ", |M| = " << ka.msg_len;
    }
}

// Absorbing in pieces is the same as absorbing at once.
TEST(TurboShake, Incremental) {
    const auto msg = ptn(17 * 17 * 17);
    faest::hash_state hasher;
    hasher.init(secpar::s128, xof::turboshake);
    for (size_t i = 0; i < msg.size(); i += 100) {
        hasher.update(msg.data() + i, std::min<size_t>(100, msg.size() - i));
    }
    std::array<uint8_t, 32> out;
    hasher.finalize(out);
    EXPECT_EQ(to_hex(out), "d4976eb56bcf118520582b709f73e1d6853e001fdaf80e1b13e0d0599d5fb372");
}

// Squeezing many blocks; from RFC 9861: TurboSHAKE128(M=``, D=`1F`, 10032), last 32 bytes.
TEST(TurboShake, LongOutput) {
    faest::hash_state hasher;
    hasher.init(secpar::s128, xof::turboshake);
    std::vector<uint8_t> out(10032);
    hasher.finalize(out.data(), out.size());
    EXPECT_EQ(to_hex(std::span(out).last<32>()),
              "a3b9b0385900ce761f22aed548e754da10a5242d62e8c658e3f3a923a7555607");
}

// The four lanes of hash_state_x4 each compute the same hash as hash_state, for both XOFs.
TEST(HashX4, MatchesHashState) {
    for (const xof x : {xof::shake, xof::turboshake}) {
        for (const secpar s : {secpar::s128, secpar::s256}) {
            // Distinct messages per lane (of equal length, as hash_state_x4 requires), longer than
            // a block.
            std::array<std::vector<uint8_t>, 4> msgs;
            for (size_t j = 0; j < 4; ++j) {
                msgs[j] = ptn(300);
                msgs[j][0] = static_cast<uint8_t>(j);
            }
            const uint8_t suffix = 0x42;

            faest::hash_state_x4 hasher_x4;
            hasher_x4.init(s, x);
            hasher_x4.update_4(msgs[0].data(), msgs[1].data(), msgs[2].data(), msgs[3].data(),
                               msgs[0].size());
            hasher_x4.update_1_byte(suffix);
            std::array<std::array<uint8_t, 200>, 4> got;
            hasher_x4.finalize_4(got[0].data(), got[1].data(), got[2].data(), got[3].data(),
                                 got[0].size());

            for (size_t j = 0; j < 4; ++j) {
                faest::hash_state hasher;
                hasher.init(s, x);
                hasher.update(msgs[j]);
                hasher.update_byte(suffix);
                std::array<uint8_t, 200> want;
                hasher.finalize(want);
                EXPECT_EQ(to_hex(got[j]), to_hex(want))
                    << "xof " << static_cast<int>(x) << ", secpar " << faest::secpar_to_bits(s)
                    << ", lane " << j;
            }
        }
    }
}

// TurboSHAKE and SHAKE differ.
TEST(TurboShake, DiffersFromShake) {
    faest::hash_state shake;
    shake.init(secpar::s128, xof::shake);
    std::array<uint8_t, 32> out;
    shake.finalize(out);
    // SHAKE128(``)
    EXPECT_EQ(to_hex(out), "7f9c2ba4e88f827d616045507605853ed73b8093f6efbc88eb1a6eacfa66ef26");
    EXPECT_NE(to_hex(out), turboshake(secpar::s128, {}, 32));
}
