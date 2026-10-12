// The PRGs from which a relation's witness may be derived (see "Derived witnesses" in voleith.hpp).
//
// A witness PRG is a type with a member template Map<N>: the public map of the PRG with N output
// bits, derived from a DST. It provides KEY_BITS and KEY_BYTES (the length of the key from which
// the N witness bits are derived), a constructor from the DST, eval (on a plaintext key), and
// qs_eval (on a committed key, adding the public vector e). Its outputs have degree
// mq::detail::DEGREE = 2 in the key. name() describes the PRG (e.g., in the KAT files).

#ifndef VOLE_MOLE_WITNESS_PRG_HPP
#define VOLE_MOLE_WITNESS_PRG_HPP

#include "mq/split.hpp"

#include <cstddef>
#include <string>
#include <type_traits>

namespace vole_mole::detail {

// Commit to the witness directly rather than deriving it.
struct NoPrg {
    static std::string name() { return "none"; }
};

// The dense MQ PRG (see mq/prg.hpp), split into `instances` independent instances (see
// mq/split.hpp).
template <size_t instances> struct MqPrg {
    static_assert(instances >= 1);
    template <size_t N> using Map = mq::detail::SplitMap<N, instances>;
    static std::string name() { return "MQ, " + std::to_string(instances) + " instances"; }
};

// Whether witnesses are derived with Prg.
template <typename Prg> constexpr bool derives_witness = !std::is_same_v<Prg, NoPrg>;

} // namespace vole_mole::detail

#endif
