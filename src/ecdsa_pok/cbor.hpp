// A minimal CBOR (RFC 8949) decoder, for the mdoc prover to find its witness in a DeviceResponse
// (see mdoc_relation.hpp). It decodes definite-length items only, and records where each item is in
// the input. It isn't used by the verifier.

#ifndef VOLE_MOLE_ECDSA_POK_CBOR_HPP
#define VOLE_MOLE_ECDSA_POK_CBOR_HPP

#include <cstddef>
#include <cstdint>
#include <optional>
#include <span>
#include <string_view>
#include <vector>

namespace vole_mole::ecdsa_pok::detail::cbor {

enum class Major : uint8_t {
    uint = 0,
    nint = 1,
    bytes = 2,
    text = 3,
    array = 4,
    map = 5,
    tag = 6,
    simple = 7
};

struct Item {
    Major major;
    uint64_t arg; // the value (uint, nint, simple), length (bytes, text), count, or tag number
    size_t start; // offset of the header
    size_t body;  // offset of the content (strings) or first child
    size_t end;   // offset after the item
    std::vector<Item> children; // array elements, map keys and values (alternating), tag content

    std::span<const uint8_t> content(std::span<const uint8_t> in) const {
        return in.subspan(body, end - body);
    }
    bool is_text(std::span<const uint8_t> in, std::string_view s) const {
        if (major != Major::text || end - body != s.size()) {
            return false;
        }
        for (size_t i = 0; i < s.size(); ++i) {
            if (in[body + i] != static_cast<uint8_t>(s[i])) {
                return false;
            }
        }
        return true;
    }
    // The value of the map entry whose key is the text s.
    const Item* get(std::span<const uint8_t> in, std::string_view s) const {
        if (major != Major::map) {
            return nullptr;
        }
        for (size_t i = 0; i + 1 < children.size(); i += 2) {
            if (children[i].is_text(in, s)) {
                return &children[i + 1];
            }
        }
        return nullptr;
    }
    // The value of the map entry whose key is the integer k.
    const Item* get_int(int64_t k) const {
        if (major != Major::map) {
            return nullptr;
        }
        for (size_t i = 0; i + 1 < children.size(); i += 2) {
            const Item& c = children[i];
            if ((k >= 0 && c.major == Major::uint && c.arg == static_cast<uint64_t>(k)) ||
                (k < 0 && c.major == Major::nint && c.arg == static_cast<uint64_t>(-1 - k))) {
                return &children[i + 1];
            }
        }
        return nullptr;
    }
    // The map entry's key for get(in, s).
    const Item* key(std::span<const uint8_t> in, std::string_view s) const {
        if (major != Major::map) {
            return nullptr;
        }
        for (size_t i = 0; i + 1 < children.size(); i += 2) {
            if (children[i].is_text(in, s)) {
                return &children[i];
            }
        }
        return nullptr;
    }
    const Item* at(size_t i) const {
        return major == Major::array && i < children.size() ? &children[i] : nullptr;
    }
};

namespace impl {

inline bool decode(std::span<const uint8_t> in, size_t& pos, Item& out, int depth) {
    if (depth > 32 || pos >= in.size()) {
        return false;
    }
    out.start = pos;
    const uint8_t h = in[pos++];
    out.major = static_cast<Major>(h >> 5);
    const uint8_t ai = h & 31;
    if (ai < 24) {
        out.arg = ai;
    } else if (ai <= 27) {
        const size_t n = size_t{1} << (ai - 24);
        if (in.size() - pos < n) {
            return false;
        }
        out.arg = 0;
        for (size_t i = 0; i < n; ++i) {
            out.arg = (out.arg << 8) | in[pos++];
        }
    } else {
        return false; // reserved or indefinite length
    }
    out.body = pos;
    switch (out.major) {
    case Major::bytes:
    case Major::text:
        if (out.arg > in.size() - pos) {
            return false;
        }
        pos += static_cast<size_t>(out.arg);
        break;
    case Major::array:
    case Major::map: {
        const uint64_t n = out.major == Major::map ? 2 * out.arg : out.arg;
        if (n > in.size() - pos) {
            return false;
        }
        out.children.resize(static_cast<size_t>(n));
        for (auto& c : out.children) {
            if (!decode(in, pos, c, depth + 1)) {
                return false;
            }
        }
        break;
    }
    case Major::tag:
        out.children.resize(1);
        if (!decode(in, pos, out.children[0], depth + 1)) {
            return false;
        }
        break;
    default:
        break;
    }
    out.end = pos;
    return true;
}

} // namespace impl

// Decode the single item in `in` (with nothing after it, unless allow_trailing).
inline std::optional<Item> decode(std::span<const uint8_t> in, bool allow_trailing = false) {
    Item out;
    size_t pos = 0;
    if (!impl::decode(in, pos, out, 0) || (!allow_trailing && pos != in.size())) {
        return std::nullopt;
    }
    return out;
}

} // namespace vole_mole::ecdsa_pok::detail::cbor

#endif
