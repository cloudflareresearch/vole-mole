// The PRGs from which a relation's witness may be derived (see "Derived
// witnesses" in voleith.hpp).
//
// A witness PRG is a type with a member template Map<N>: the public map of the
// PRG with N output bits, derived from a DST. It provides KEY_BITS and
// KEY_BYTES (the length of the key from which the N witness bits are derived),
// a constructor from the DST, eval (on a plaintext key), and qs_eval (on a
// committed key, adding the public vector e). Its outputs have degree
// mq::detail::DEGREE = 2 in the key. name() describes the PRG (e.g., in the KAT
// files).

#ifndef VOLE_MOLE_WITNESS_PRG_HPP
#define VOLE_MOLE_WITNESS_PRG_HPP

#include "mq/local.hpp"
#include "mq/split.hpp"

#include <cstddef>
#include <string>
#include <type_traits>

namespace vole_mole::detail {

// Commit to the witness directly rather than deriving it.
struct NoPrg {
    static std::string name() { return "none"; }
};

// The dense MQ PRG (see mq/prg.hpp), split into `instances` independent
// instances (see mq/split.hpp).
template <size_t instances> struct MqPrg {
    static_assert(instances >= 1);
    template <size_t N> using Map = mq::detail::SplitMap<N, instances>;
    static std::string name() { return "MQ, " + std::to_string(instances) + " instances"; }
};

// The local PRG (see mq/local.hpp) with LOCAL_LINEAR_TERMS = 16 linear terms
// and `ands` products per output; for ands = 1, this is Goldreich's PRG with
// the predicate XOR_16-AND_2. Its key is much shorter than that of the MQ PRG
// for the same cost (each output costs `ands` products and a few additions of
// committed bits), but its security rests on a different, less studied
// assumption, and its key length (local_key_bits) is a rough estimate that
// hasn't been checked against the literature on attacks on local PRGs (see
// tools/local_key_bits.py). Experimental.
template <size_t ands = 1> struct LocalPrg {
    template <size_t N>
    using Map = mq::detail::LocalMap<mq::detail::local_key_bits(N, ands), N,
                                     mq::detail::LOCAL_LINEAR_TERMS, ands>;
    static std::string name() { return "local, " + std::to_string(ands) + " products"; }
};

// Whether witnesses are derived with Prg.
template <typename Prg> constexpr bool derives_witness = !std::is_same_v<Prg, NoPrg>;

} // namespace vole_mole::detail

#endif
