// Mdocs from Longfellow's tests (mdoc_vectors.txt), for the tests and benchmarks of the mdoc proof.

#pragma once

#include "ecdsa_pok/mdoc_relation.hpp" // internal

#include <algorithm>
#include <fstream>
#include <map>
#include <sstream>
#include <string>
#include <vector>

namespace mdoc_vectors {

namespace md = vole_mole::ecdsa_pok::detail::mdoc;

inline std::vector<uint8_t> from_hex(const std::string& s) {
    std::vector<uint8_t> out;
    for (size_t i = 0; i + 1 < s.size(); i += 2) {
        out.push_back(static_cast<uint8_t>(std::stoi(s.substr(i, 2), nullptr, 16)));
    }
    return out;
}

struct Vector {
    md::Request req; // without attributes
    std::vector<uint8_t> mdoc;
};

inline const std::map<int, Vector>& vectors() {
    static const std::map<int, Vector> out = [] {
        std::map<int, Vector> v;
        std::ifstream f(std::string(VOLE_MOLE_TEST_DATA_DIR) + "/ecdsa_pok/mdoc_vectors.txt");
        std::string line;
        int cur = -1;
        auto coord = [](std::string s) {
            s = s.substr(2); // 0x
            s.insert(0, 64 - s.size(), '0');
            return from_hex(s);
        };
        while (std::getline(f, line)) {
            if (line.empty() || line[0] == '#') {
                continue;
            }
            std::istringstream ss(line);
            std::string k, val;
            ss >> k >> val;
            if (k == "vector") {
                cur = std::stoi(val);
                v[cur].req.issuer_pk[0] = 0x04;
            } else if (k == "pkx") {
                const auto b = coord(val);
                std::ranges::copy(b, v[cur].req.issuer_pk.begin() + 1);
            } else if (k == "pky") {
                const auto b = coord(val);
                std::ranges::copy(b, v[cur].req.issuer_pk.begin() + 33);
            } else if (k == "transcript") {
                v[cur].req.transcript = from_hex(val);
            } else if (k == "now") {
                std::copy_n(val.begin(), md::DATE_BYTES, v[cur].req.now.begin());
            } else if (k == "doctype") {
                v[cur].req.doc_type = val;
            } else if (k == "mdoc") {
                v[cur].mdoc = from_hex(val);
            }
        }
        return v;
    }();
    return out;
}

inline const md::Attribute AGE_OVER_18{"age_over_18", {0xF5}};
inline const md::Attribute NOT_OVER_18{"age_over_18", {0xF4}};
inline const md::Attribute FAMILY_NAME{"family_name",
                                       {0x6A, 'M', 'u', 's', 't', 'e', 'r', 'm', 'a', 'n', 'n'}};
inline const md::Attribute BIRTH_DATE{
    "birth_date", {0xD9, 0x03, 0xEC, 0x6A, '1', '9', '7', '1', '-', '0', '9', '-', '0', '1'}};
inline const md::Attribute HEIGHT{"height", {0x18, 0xAF}};
inline const md::Attribute BIRTH_YEAR{"age_birth_year", {0x19, 0x07, 0xB0}};

inline md::Request request(int v, std::vector<md::Attribute> attrs) {
    md::Request r = vectors().at(v).req;
    r.attributes = std::move(attrs);
    return r;
}

} // namespace mdoc_vectors
