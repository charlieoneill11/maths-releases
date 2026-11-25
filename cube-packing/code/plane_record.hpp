#pragma once

#include <array>
#include <cstdint>
#include <istream>
#include <limits>
#include <ostream>
#include <stdexcept>

using PlaneRecord = std::array<std::uint16_t, 15>;

constexpr bool coordinates_fit(int side) {
    return (side + 8LL) * (side + 8LL) <= std::numeric_limits<int>::max();
}

// Big-endian fields preserve the numeric lexicographic order used in orbit reduction.
template<int Side>
bool read_record(std::istream& input, PlaneRecord& record) {
    constexpr int width = Side <= 255 ? 1 : 2;
    std::array<unsigned char, 15 * width> bytes{};
    if (!input.read(reinterpret_cast<char*>(bytes.data()), bytes.size())) {
        if (input.eof() && input.gcount() == 0) return false;
        throw std::runtime_error("partial or unreadable plane record");
    }
    for (std::size_t i = 0; i < record.size(); ++i) {
        unsigned value = bytes[i * width];
        if constexpr (width == 2) value = 256 * value + bytes[i * width + 1];
        if (value >= Side) throw std::runtime_error("plane coordinate outside torus");
        record[i] = static_cast<std::uint16_t>(value);
    }
    return true;
}

template<int Side>
void write_record(std::ostream& output, const PlaneRecord& record) {
    constexpr int width = Side <= 255 ? 1 : 2;
    std::array<unsigned char, 15 * width> bytes{};
    for (std::size_t i = 0; i < record.size(); ++i) {
        if constexpr (width == 2) bytes[i * width] = record[i] >> 8;
        bytes[(i + 1) * width - 1] = static_cast<unsigned char>(record[i]);
    }
    if (!output.write(reinterpret_cast<const char*>(bytes.data()), bytes.size()))
        throw std::runtime_error("failed writing plane record");
}
