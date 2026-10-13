// A split MQ PRG: c independent instances of the MQ PRG (see prg.hpp), each with its own key and
// public map, whose outputs are concatenated.
//
// The committed evaluation of one instance with n key bits and N outputs costs about N n^2 / 16
// table lookups, and n grows like sqrt(N) (see key_bits.hpp), so the cost grows like N^2. Splitting
// the N outputs over c instances reduces it to about N n_c^2 / 16 with n_c = key_bits(N / c), i.e.,
// by roughly a factor c, at the cost of a total key of c n_c bits, which grows like sqrt(c).
//
// Layout: The N / 8 output bytes are split into c consecutive parts: parts 0, ..., c - 2 have
// ceil(N / 8 / c) bytes, and part c - 1 has the rest. Instance t outputs part t and has
// key_bits(8 * |part t|) key bits; the key is the concatenation of the instance keys, in order.
// The public map of instance t is derived (see PublicMap) from the DST dst || le32(t).
//
// Security: If each instance is a PRG, then so is their concatenation (with independent keys), by
// a hybrid argument that loses a factor c. Recovering the key of one instance reveals its part of
// the output, so each instance must be secure on its own.

#ifndef VOLE_MOLE_MQ_SPLIT_HPP
#define VOLE_MOLE_MQ_SPLIT_HPP

#include "mq/prg.hpp"

#include <cstddef>
#include <cstdint>
#include <span>
#include <tuple>
#include <utility>
#include <vector>

namespace vole_mole::mq::detail {

template <size_t NUM_OUTPUTS, size_t NUM_INSTANCES> struct SplitLayout {
    static_assert(NUM_OUTPUTS % 8 == 0 && NUM_OUTPUTS > 0);
    static_assert(NUM_INSTANCES >= 1);
    static constexpr size_t OUTPUT_BYTES = NUM_OUTPUTS / 8;
    // Size of the parts 0, ..., c - 2.
    static constexpr size_t PART_BYTES = (OUTPUT_BYTES + NUM_INSTANCES - 1) / NUM_INSTANCES;
    static_assert(PART_BYTES * (NUM_INSTANCES - 1) < OUTPUT_BYTES,
                  "too many instances: the last part would be empty");

    static constexpr size_t output_bytes(size_t t) {
        return t + 1 < NUM_INSTANCES ? PART_BYTES : OUTPUT_BYTES - (NUM_INSTANCES - 1) * PART_BYTES;
    }
    static constexpr size_t output_offset(size_t t) { return t * PART_BYTES; } // in bytes
    static constexpr size_t instance_key_bits(size_t t) { return key_bits(8 * output_bytes(t)); }
    static constexpr size_t key_offset(size_t t) { // in bits
        size_t off = 0;
        for (size_t u = 0; u < t; ++u) {
            off += instance_key_bits(u);
        }
        return off;
    }
    static constexpr size_t KEY_BITS = key_offset(NUM_INSTANCES);
};

// The total key length of a split PRG with `num_instances` instances and `num_outputs` outputs.
template <size_t NUM_OUTPUTS, size_t NUM_INSTANCES>
constexpr size_t split_key_bits = SplitLayout<NUM_OUTPUTS, NUM_INSTANCES>::KEY_BITS;

template <size_t NUM_OUTPUTS, size_t NUM_INSTANCES> class SplitMap {
    using Layout = SplitLayout<NUM_OUTPUTS, NUM_INSTANCES>;

  public:
    static constexpr size_t num_outputs_v = NUM_OUTPUTS;
    static constexpr size_t num_instances_v = NUM_INSTANCES;
    static constexpr size_t KEY_BITS = Layout::KEY_BITS;
    static constexpr size_t KEY_BYTES = KEY_BITS / 8;
    static constexpr size_t OUTPUT_BYTES = Layout::OUTPUT_BYTES;
    static_assert(KEY_BITS % 8 == 0);

    template <size_t t>
    using InstanceMap = PublicMap<Layout::instance_key_bits(t), 8 * Layout::output_bytes(t)>;

    explicit SplitMap(std::span<const uint8_t> dst)
        : maps_(make_maps(dst, std::make_index_sequence<NUM_INSTANCES>())) {}

    template <size_t t> const InstanceMap<t>& instance() const { return std::get<t>(maps_); }

    // Evaluate the PRG on a plaintext key.
    void eval(std::span<const uint8_t, KEY_BYTES> key, std::span<uint8_t, OUTPUT_BYTES> out) const {
        for_each_instance([&]<size_t t>() {
            mq::detail::eval(
                instance<t>(),
                key.template subspan<Layout::key_offset(t) / 8, Layout::instance_key_bits(t) / 8>(),
                out.template subspan<Layout::output_offset(t), Layout::output_bytes(t)>());
        });
    }

    // Evaluate the PRG on a committed key and add `e` (see mq::detail::qs_eval).
    template <typename QS>
    std::vector<qs_bit<QS, DEGREE>> qs_eval(std::span<const qs_bit<QS, 1>, KEY_BITS> key,
                                            std::span<const uint8_t, OUTPUT_BYTES> e) const {
        std::vector<qs_bit<QS, DEGREE>> out;
        out.reserve(NUM_OUTPUTS);
        for_each_instance([&]<size_t t>() {
            const auto w = mq::detail::qs_eval<QS>(
                instance<t>(),
                key.template subspan<Layout::key_offset(t), Layout::instance_key_bits(t)>(),
                e.template subspan<Layout::output_offset(t), Layout::output_bytes(t)>());
            out.insert(out.end(), w.begin(), w.end());
        });
        return out;
    }

  private:
    template <size_t... t> using Maps = std::tuple<InstanceMap<t>...>;

    template <size_t t> static InstanceMap<t> make_map(std::span<const uint8_t> dst) {
        // dst || le32(t)
        std::vector<uint8_t> instance_dst(dst.begin(), dst.end());
        for (size_t i = 0; i < 4; ++i) {
            instance_dst.push_back(static_cast<uint8_t>(t >> (8 * i)));
        }
        return InstanceMap<t>(instance_dst);
    }
    template <size_t... t>
    static Maps<t...> make_maps(std::span<const uint8_t> dst, std::index_sequence<t...>) {
        return Maps<t...>(make_map<t>(dst)...);
    }

    template <typename F> static void for_each_instance(F&& f) {
        [&]<size_t... t>(std::index_sequence<t...>) {
            (f.template operator()<t>(), ...);
        }(std::make_index_sequence<NUM_INSTANCES>());
    }

    decltype(make_maps(std::span<const uint8_t>(),
                       std::make_index_sequence<NUM_INSTANCES>())) maps_;
};

} // namespace vole_mole::mq::detail

#endif
