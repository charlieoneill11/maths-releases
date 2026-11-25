// c++ -O3 -std=c++17 interval_witness_codec.cpp -o interval_witness_codec
// interval_witness_codec pack < canonical.txt > shard.iw
// interval_witness_codec unpack < shard.iw | ./check_witnesses FIRST LAST
//
// IW format version 1. Integer fields are unsigned little-endian. File header:
// "I11WIT", byte 1, byte 0, first base (8 bytes). Each nonempty block has
// count (2 bytes), stride code (1), first witness (13), and, if count > 1,
// last witness (13). Stride = 2^(code & 127) times (code & 128 ? 3 : 1).
// In stride units relative to the first witness, the predictor at position i
// is floor(i * span / (count-1)). Each interior difference from its predictor
// uses zigzag then unsigned base-128 little-endian varint. Blocks have 2048
// records except the final block, which can be shorter. The mandatory footer
// holds zero count (2), total record count (8), then IEEE CRC-32 (4) over all
// preceding bytes, including the count fields. No trailing bytes are allowed.
// CRC detects accidental corruption. Consumers must check decoder exit status
// before accepting the stream. Add -DPOWER_WITNESS_SQUARES for square-cell
// archives with magic "I2SWIT" and 0 < m < 2^50. Primality and interval membership are checked
// by the separate proof verifier. The codec accepts strictly increasing odd
// witnesses 1 < p < 2^100 and consecutive bases 0 < n < 2^45.
#include <algorithm>
#include <array>
#include <charconv>
#include <cstdint>
#include <cstring>
#include <iostream>
#include <stdexcept>
#include <string>
#include <vector>

using Wide = unsigned __int128;
constexpr unsigned BLOCK = 2048;
constexpr Wide PRIME_LIMIT = Wide{1} << 100;
#ifdef POWER_WITNESS_SQUARES
constexpr uint64_t BASE_LIMIT = uint64_t{1} << 50;
constexpr std::array<uint8_t, 8> MAGIC{'I','2','S','W','I','T',1,0};
#else
constexpr uint64_t BASE_LIMIT = uint64_t{1} << 45;
constexpr std::array<uint8_t, 8> MAGIC{'I','1','1','W','I','T',1,0};
#endif

void require(bool condition, const char* error) {
    if (!condition) throw std::runtime_error(error);
}

std::array<uint32_t, 256> make_crc_table() {
    std::array<uint32_t, 256> table{};
    for (unsigned i = 0; i < table.size(); ++i) {
        uint32_t value = i;
        for (unsigned bit = 0; bit < 8; ++bit)
            value = (value >> 1) ^ ((value & 1) ? 0xedb88320u : 0u);
        table[i] = value;
    }
    return table;
}
const auto CRC_TABLE = make_crc_table();

class Binary {
    uint32_t crc_ = 0xffffffffu;

    void update(uint8_t byte) { crc_ = CRC_TABLE[(crc_ ^ byte) & 255] ^ (crc_ >> 8); }

public:
    uint32_t checksum() const { return ~crc_; }

    void put(uint8_t byte) {
        require(std::cout.rdbuf()->sputc(static_cast<char>(byte)) != std::char_traits<char>::eof(),
                "binary write failed");
        update(byte);
    }

    uint8_t get() {
        const int value = std::cin.rdbuf()->sbumpc();
        require(value != std::char_traits<char>::eof(), "truncated binary input");
        const auto byte = static_cast<uint8_t>(value);
        update(byte);
        return byte;
    }

    void write_le(Wide value, unsigned bytes) {
        for (unsigned i = 0; i < bytes; ++i) {
            put(static_cast<uint8_t>(value));
            value >>= 8;
        }
    }

    Wide read_le(unsigned bytes) {
        Wide result = 0;
        for (unsigned i = 0; i < bytes; ++i) result |= Wide(get()) << (8*i);
        return result;
    }

    void write_var(Wide value) {
        while (value >= 128) {
            put(static_cast<uint8_t>(value) | 128);
            value >>= 7;
        }
        put(static_cast<uint8_t>(value));
    }

    Wide read_var() {
        Wide value = 0;
        for (unsigned shift = 0; shift < 101; shift += 7) {
            const uint8_t byte = get();
            value |= Wide(byte & 127) << shift;
            if (!(byte & 128)) {
                require((!shift || byte) && value < 2*PRIME_LIMIT, "invalid offset varint");
                return value;
            }
        }
        throw std::runtime_error("offset varint too long");
    }
};

bool valid_prime_field(Wide p) { return p > 1 && (p & 1) && p < PRIME_LIMIT; }

unsigned trailing_zeros(Wide positive) {
    const auto low = static_cast<uint64_t>(positive);
    return low ? __builtin_ctzll(low) : 64+__builtin_ctzll(static_cast<uint64_t>(positive >> 64));
}

bool read_row(uint64_t& n, Wide& p) {
    char line[64]{};
    if (!std::cin.getline(line, sizeof(line))) {
        require(std::cin.eof() && !std::cin.bad() && std::cin.gcount() == 0,
                "invalid or overlong decimal input");
        return false;
    }
    const std::size_t length = static_cast<std::size_t>(std::cin.gcount()) - (std::cin.eof() ? 0 : 1);
    const char* end = line+length;
    const char* space = std::find(static_cast<const char*>(line), end, ' ');
    require(space != end && space != line && line[0] != '0', "invalid decimal base");
    auto parsed = std::from_chars(static_cast<const char*>(line), space, n);
    require(parsed.ec == std::errc() && parsed.ptr == space && n > 0 && n < BASE_LIMIT,
            "base outside supported range");
    const char* start = space+1;
    require(start != end && *start != '0' && end-start <= 31, "invalid decimal witness");
    p = 0;
    for (const char* digit = start; digit != end; ++digit) {
        require(*digit >= '0' && *digit <= '9', "invalid decimal witness");
        p = p*10 + unsigned(*digit-'0');
    }
    require(valid_prime_field(p), "witness outside supported range");
    return true;
}

void write_block(Binary& file, const std::vector<Wide>& values) {
    unsigned shift = 100;
    bool same_residue = true;
    const unsigned residue = values.front() % 3;
    for (Wide p : values) {
        shift = std::min(shift, trailing_zeros(p-1));
        if (p % 3 != residue) same_residue = false;
    }
    const Wide stride = (Wide{1} << shift) * (same_residue ? 3 : 1);
    file.write_le(values.size(), 2);
    file.put(static_cast<uint8_t>(shift) | (same_residue ? 128 : 0));
    file.write_le(values.front(),13);
    if (values.size() == 1) return;
    file.write_le(values.back(),13);
    const Wide span = (values.back()-values.front())/stride;
    const auto last = static_cast<unsigned>(values.size()-1);
    for (unsigned i = 1; i < last; ++i) {
        const Wide actual = (values[i]-values.front())/stride;
        const Wide predicted = (i*span)/last;
        file.write_var(actual >= predicted ? 2*(actual-predicted) : 2*(predicted-actual)-1);
    }
}

void pack() {
    Binary file;
    uint64_t first = 0, n = 0, count = 0;
    Wide p = 0, previous = 0;
    std::vector<Wide> block;
    block.reserve(BLOCK);
    while (read_row(n,p)) {
        if (count == 0) {
            first = n;
            for (uint8_t byte : MAGIC) file.put(byte);
            file.write_le(first,8);
        }
        require(n == first+count && p > previous, "nonconsecutive base or nonincreasing witness");
        block.push_back(p);
        previous = p;
        ++count;
        if (block.size() == BLOCK) {
            write_block(file,block);
            block.clear();
        }
    }
    require(count != 0, "empty witness stream");
    if (!block.empty()) write_block(file,block);
    file.write_le(0,2);
    file.write_le(count,8);
    file.write_le(file.checksum(),4);
}

void write_row(uint64_t base, Wide p, std::string& out) {
    char digits[40];
    auto index = std::to_chars(digits,digits+sizeof(digits),base);
    out.append(digits,index.ptr);
    out.push_back(' ');
    // A 100-bit witness needs at most four groups of nine digits.
    uint32_t groups[4];
    unsigned size = 0;
    do {
        groups[size++] = static_cast<uint32_t>(p % 1000000000);
        p /= 1000000000;
    } while (p);
    auto high = std::to_chars(digits,digits+sizeof(digits),groups[--size]);
    out.append(digits,high.ptr);
    while (size) {
        auto group = std::to_chars(digits,digits+sizeof(digits),groups[--size]);
        out.append(9-(group.ptr-digits),'0');
        out.append(digits,group.ptr);
    }
    out.push_back('\n');
}

void unpack() {
    Binary file;
    for (uint8_t byte : MAGIC) require(file.get() == byte, "wrong archive magic or version");
    const auto first = static_cast<uint64_t>(file.read_le(8));
    require(first > 0 && first < BASE_LIMIT, "invalid first base");
    uint64_t count = 0;
    Wide previous = 0;
    bool final_block = false;
    std::string output;
    output.reserve(BLOCK*50);
    while (true) {
        const unsigned size = static_cast<unsigned>(file.read_le(2));
        if (size == 0) break;
        require(!final_block && size <= BLOCK && size <= BASE_LIMIT-first-count, "invalid block size or range");
        final_block = size != BLOCK;
        const uint8_t code = file.get();
        const unsigned shift = code & 127;
        require(shift > 0 && shift < 100, "invalid stride");
        const Wide twos = Wide{1} << shift;
        const Wide stride = twos * ((code & 128) ? 3 : 1);
        const Wide start = file.read_le(13);
        require(valid_prime_field(start) && start > previous && (start-1)%twos == 0,
                "invalid block start");
        write_row(first+count,start,output);
        previous = start;
        if (size > 1) {
            const Wide end = file.read_le(13);
            require(valid_prime_field(end) && end > start && (end-start)%stride == 0,
                    "invalid block endpoint");
            const Wide span = (end-start)/stride;
            require(span >= size-1, "block cannot be strictly increasing");
            for (unsigned i = 1; i+1 < size; ++i) {
                const Wide encoded = file.read_var();
                const Wide predicted = (i*span)/(size-1);
                const bool negative = encoded & 1;
                const Wide distance = (encoded >> 1) + negative;
                require(distance <= (negative ? predicted : span-predicted), "offset outside block");
                const Wide actual = negative ? predicted-distance : predicted+distance;
                const Wide value = start+actual*stride;
                require(previous < value && value < end, "nonincreasing decoded witness");
                write_row(first+count+i,value,output);
                previous = value;
            }
            write_row(first+count+size-1,end,output);
            previous = end;
        }
        std::cout.write(output.data(),static_cast<std::streamsize>(output.size()));
        require(bool(std::cout), "decimal write failed");
        output.clear();
        count += size;
    }
    require(count > 0 && file.read_le(8) == count, "wrong footer count");
    const uint32_t expected = file.checksum();
    require(file.read_le(4) == expected, "archive CRC-32 mismatch");
    require(std::cin.rdbuf()->sgetc() == std::char_traits<char>::eof(), "trailing data after archive");
}

int main(int argc, char** argv) try {
    require(argc == 2, "usage: interval_witness_codec pack|unpack");
    std::ios::sync_with_stdio(false);
    std::cin.tie(nullptr);
    if (std::strcmp(argv[1],"pack") == 0) pack();
    else if (std::strcmp(argv[1],"unpack") == 0) unpack();
    else throw std::runtime_error("usage: interval_witness_codec pack|unpack");
    std::cout.flush();
    require(bool(std::cout), "output flush failed");
    return 0;
} catch (const std::exception& error) {
    std::cerr << error.what() << '\n';
    return 1;
}
