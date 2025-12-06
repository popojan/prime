// Prime DNA - Universal gap/2 encoding
// Works for arbitrary prime ranges with automatic type selection

#pragma once

#include <vector>
#include <cstdint>
#include <fstream>
#include <stdexcept>
#include <algorithm>

#ifdef USE_FLINT
#include <flint/fmpz.h>
#endif

namespace prime_dna {

// Type codes for serialization
enum class GapType : uint8_t {
    UINT8 = 1,
    UINT16 = 2,
    UINT32 = 4
};

// Universal DNA: stores gap/2 values with automatic type selection
class PrimeDNAUniversal {
public:
    uint64_t first_prime = 2;
    uint32_t max_half_gap = 0;
    GapType gap_type = GapType::UINT8;

    // Storage (only one is used based on gap_type)
    std::vector<uint8_t> gaps8;
    std::vector<uint16_t> gaps16;
    std::vector<uint32_t> gaps32;

    void encode(const std::vector<uint64_t>& primes) {
        if (primes.size() < 2) {
            first_prime = primes.empty() ? 2 : primes[0];
            return;
        }

        first_prime = primes[0];

        // First pass: find max half-gap
        max_half_gap = 0;
        for (size_t i = 1; i < primes.size(); ++i) {
            uint64_t gap = primes[i] - primes[i-1];
            uint32_t half = static_cast<uint32_t>(gap / 2);
            max_half_gap = std::max(max_half_gap, half);
        }

        // Select type
        if (max_half_gap <= 255) {
            gap_type = GapType::UINT8;
        } else if (max_half_gap <= 65535) {
            gap_type = GapType::UINT16;
        } else {
            gap_type = GapType::UINT32;
        }

        // Second pass: store
        // Note: first gap (2→3) is 1 (odd!), rest are even
        // We store raw gap for first, then gap/2 for rest
        size_t n = primes.size() - 1;

        switch (gap_type) {
            case GapType::UINT8:
                gaps8.clear();
                gaps8.reserve(n);
                // First gap stored as-is (handles 2→3 = 1)
                gaps8.push_back(static_cast<uint8_t>(primes[1] - primes[0]));
                for (size_t i = 2; i < primes.size(); ++i) {
                    gaps8.push_back(static_cast<uint8_t>((primes[i] - primes[i-1]) / 2));
                }
                break;

            case GapType::UINT16:
                gaps16.clear();
                gaps16.reserve(n);
                gaps16.push_back(static_cast<uint16_t>(primes[1] - primes[0]));
                for (size_t i = 2; i < primes.size(); ++i) {
                    gaps16.push_back(static_cast<uint16_t>((primes[i] - primes[i-1]) / 2));
                }
                break;

            case GapType::UINT32:
                gaps32.clear();
                gaps32.reserve(n);
                gaps32.push_back(static_cast<uint32_t>(primes[1] - primes[0]));
                for (size_t i = 2; i < primes.size(); ++i) {
                    gaps32.push_back(static_cast<uint32_t>((primes[i] - primes[i-1]) / 2));
                }
                break;
        }
    }

    std::vector<uint64_t> decode() const {
        std::vector<uint64_t> primes;
        size_t n = count();
        primes.reserve(n);

        uint64_t p = first_prime;
        primes.push_back(p);

        // First gap is raw, rest are gap/2
        switch (gap_type) {
            case GapType::UINT8:
                if (!gaps8.empty()) {
                    p += gaps8[0];  // First gap raw
                    primes.push_back(p);
                    for (size_t i = 1; i < gaps8.size(); ++i) {
                        p += 2 * static_cast<uint64_t>(gaps8[i]);
                        primes.push_back(p);
                    }
                }
                break;

            case GapType::UINT16:
                if (!gaps16.empty()) {
                    p += gaps16[0];
                    primes.push_back(p);
                    for (size_t i = 1; i < gaps16.size(); ++i) {
                        p += 2 * static_cast<uint64_t>(gaps16[i]);
                        primes.push_back(p);
                    }
                }
                break;

            case GapType::UINT32:
                if (!gaps32.empty()) {
                    p += gaps32[0];
                    primes.push_back(p);
                    for (size_t i = 1; i < gaps32.size(); ++i) {
                        p += 2 * static_cast<uint64_t>(gaps32[i]);
                        primes.push_back(p);
                    }
                }
                break;
        }

        return primes;
    }

    size_t count() const {
        switch (gap_type) {
            case GapType::UINT8: return gaps8.size() + 1;
            case GapType::UINT16: return gaps16.size() + 1;
            case GapType::UINT32: return gaps32.size() + 1;
        }
        return 1;
    }

    size_t gap_count() const {
        switch (gap_type) {
            case GapType::UINT8: return gaps8.size();
            case GapType::UINT16: return gaps16.size();
            case GapType::UINT32: return gaps32.size();
        }
        return 0;
    }

    size_t storage_bytes() const {
        size_t header = sizeof(first_prime) + sizeof(max_half_gap) + sizeof(gap_type);
        switch (gap_type) {
            case GapType::UINT8: return header + gaps8.size();
            case GapType::UINT16: return header + gaps16.size() * 2;
            case GapType::UINT32: return header + gaps32.size() * 4;
        }
        return header;
    }

    double bits_per_prime() const {
        return 8.0 * storage_bytes() / count();
    }

    void save(const std::string& filename) const {
        std::ofstream out(filename, std::ios::binary);
        if (!out) throw std::runtime_error("Cannot open file");

        // Header
        uint64_t n = gap_count();
        out.write(reinterpret_cast<const char*>(&n), sizeof(n));
        out.write(reinterpret_cast<const char*>(&first_prime), sizeof(first_prime));
        out.write(reinterpret_cast<const char*>(&max_half_gap), sizeof(max_half_gap));
        out.write(reinterpret_cast<const char*>(&gap_type), sizeof(gap_type));

        // Data
        switch (gap_type) {
            case GapType::UINT8:
                out.write(reinterpret_cast<const char*>(gaps8.data()), gaps8.size());
                break;
            case GapType::UINT16:
                out.write(reinterpret_cast<const char*>(gaps16.data()), gaps16.size() * 2);
                break;
            case GapType::UINT32:
                out.write(reinterpret_cast<const char*>(gaps32.data()), gaps32.size() * 4);
                break;
        }
    }

    void load(const std::string& filename) {
        std::ifstream in(filename, std::ios::binary);
        if (!in) throw std::runtime_error("Cannot open file");

        uint64_t n;
        in.read(reinterpret_cast<char*>(&n), sizeof(n));
        in.read(reinterpret_cast<char*>(&first_prime), sizeof(first_prime));
        in.read(reinterpret_cast<char*>(&max_half_gap), sizeof(max_half_gap));
        in.read(reinterpret_cast<char*>(&gap_type), sizeof(gap_type));

        gaps8.clear();
        gaps16.clear();
        gaps32.clear();

        switch (gap_type) {
            case GapType::UINT8:
                gaps8.resize(n);
                in.read(reinterpret_cast<char*>(gaps8.data()), n);
                break;
            case GapType::UINT16:
                gaps16.resize(n);
                in.read(reinterpret_cast<char*>(gaps16.data()), n * 2);
                break;
            case GapType::UINT32:
                gaps32.resize(n);
                in.read(reinterpret_cast<char*>(gaps32.data()), n * 4);
                break;
        }
    }

    // Info string
    std::string info() const {
        std::string type_str;
        switch (gap_type) {
            case GapType::UINT8: type_str = "uint8"; break;
            case GapType::UINT16: type_str = "uint16"; break;
            case GapType::UINT32: type_str = "uint32"; break;
        }
        return std::to_string(count()) + " primes, " +
               std::to_string(storage_bytes()) + " bytes, " +
               type_str + " gaps (max=" + std::to_string(max_half_gap) + ")";
    }
};

} // namespace prime_dna
