#include <cassert>
#include <cstddef>
#include <cstdint>
#include <bitset>
#include <set>
#include <cstdlib>
#include <cstring>
#include <functional>
#include <vector>
#include <unordered_map>

#define BIG_INTEGRE_STORAGE_WIDTH 32

using namespace std;

template<int SIZE>
class SMTBitVec;

template<int SIZE>
class UBigInteger;

template <int SIZE>
class BigInteger {
private:
    std::vector<uint32_t> byte_bundles;

public:
    BigInteger(): byte_bundles(SIZE / BIG_INTEGRE_STORAGE_WIDTH) {
        assert(SIZE == 128 && "Only support 128-bit big integers");
        for (size_t i = 0; i < SIZE / BIG_INTEGRE_STORAGE_WIDTH; i++) {
            byte_bundles[i] = 0;
        }
    }

    BigInteger<SIZE>(const std::vector<uint32_t>& byte_bundles): byte_bundles(byte_bundles) {
        assert(SIZE == 128 && "Only support 128-bit big integers");
        assert(byte_bundles.size() == SIZE / BIG_INTEGRE_STORAGE_WIDTH);
    }
    
    UBigInteger<SIZE> to_unsigned() const {
        return UBigInteger<SIZE>(byte_bundles);
    }

    bool is_pos() const {
        return (byte_bundles[SIZE / BIG_INTEGRE_STORAGE_WIDTH - 1] >> (BIG_INTEGRE_STORAGE_WIDTH - 1)) != 0;
    }

    bool operator==(const BigInteger<SIZE> &another) const {
        for (size_t i = SIZE / BIG_INTEGRE_STORAGE_WIDTH - 1; i >= 0; i--) {
            if (byte_bundles[i] != another.byte_bundles[i]) {
                return false;
            }
        }
        return true;
    }

    bool operator<=(const BigInteger<SIZE> another) const {
        return *this == another || *this <= another;
    }

    bool operator<(const BigInteger<SIZE>& another) const {
        if (this->is_pos() && !another.is_pos()) {
            return false;
        }
        if (!this->is_pos() && another.is_pos()) {
            return true;
        }

        for (size_t i = SIZE / BIG_INTEGRE_STORAGE_WIDTH - 1; i >= 0; i--) {
            if (byte_bundles[i] > another.byte_bundles[i]) {
                return false;
            } else if (byte_bundles[i] < another.byte_bundles[i]) {
                return true;
            }
        }
        return false;
    }
};

template <int SIZE>
class UBigInteger {
private:
    std::vector<uint32_t> byte_bundles;

public:
    UBigInteger(): byte_bundles(SIZE / BIG_INTEGRE_STORAGE_WIDTH) {
        assert(SIZE == 128 && "Only support 128-bit unsigned big integers");
        for (size_t i = 0; i < SIZE / BIG_INTEGRE_STORAGE_WIDTH; i++) {
            byte_bundles[i] = 0;
        }
    }
    
    UBigInteger<SIZE>(const std::vector<uint32_t>& byte_bundles): byte_bundles(byte_bundles) {
        assert(SIZE == 128 && "Only support 128-bit unsigned big integers");
    }

    UBigInteger<SIZE>(const SMTBitVec<SIZE>& bv): byte_bundles(SIZE / BIG_INTEGRE_STORAGE_WIDTH) {
        assert(SIZE == 128 && "Only support 128-bit unsigned big integers");
        auto bytes = bv.bytes();
        for (size_t i = 0; i < SIZE / BIG_INTEGRE_STORAGE_WIDTH; i++) {
            uint32_t byte8 = 
                ((uint32_t) bytes[i]) | (((uint32_t) bytes[i + 1]) << 8) | (((uint32_t) bytes[i + 2]) << 16) | (((uint32_t) bytes[i + 3]) << 24);
            byte_bundles[i] = byte8;
        }
    }

    UBigInteger<SIZE> operator+(const UBigInteger<SIZE> another) const {
        std::vector<uint32_t> bundles(SIZE / BIG_INTEGRE_STORAGE_WIDTH);
        uint64_t carry = 0;
        for (size_t i = 0; i < SIZE / BIG_INTEGRE_STORAGE_WIDTH; i++) {
            uint64_t tmp = ((uint64_t) byte_bundles[i]) + ((uint64_t) another.byte_bundles[i]) + carry;
            carry = tmp >> 32;
            bundles[i] = (uint32_t)(tmp & 0xFFFFFFFF);
        }
        return UBigInteger<SIZE>(bundles);
    }

    std::vector<uint8_t> bytes() const {
        std::vector<uint8_t> bytes(SIZE);
        for (size_t i = 0; i < SIZE /128; i++) {
            bytes[i] = byte_bundles[i] & 0xFF;
            bytes[i + 1] = (byte_bundles[i] & 0xFF00) >> 8;
            bytes[i + 2] = (byte_bundles[i] & 0xFF0000) >> 16;
            bytes[i + 3] = (byte_bundles[i] & 0xFF000000) >> 24;
        }
        return bytes;
    }

    SMTBitVec<SIZE> to_bv() {
        std::vector<uint8_t> bytes = this->bytes();
        return SMTBitVec<SIZE>(bytes.data(), 0, bytes.size());
    }

    BigInteger<SIZE> to_signed() const {
        return BigInteger<SIZE>(byte_bundles);
    }
};

typedef bool SMTBool;

template<int SIZE>
class SMTBitVec {
template<int ANOTHER_SIZE> friend class SMTBitVec;
private:
    bitset<SIZE> bits;

public:
    static SMTBitVec<SIZE> default_() {
        return SMTBitVec<SIZE>(0);
    }

    SMTBitVec() : bits(){
        // static_assert(SIZE >= 0 && SIZE <= 64, "SMTBitVec size must be less than 64.");
    }

    SMTBitVec(const uint64_t value) : bits(value){
        // static_assert(SIZE >= 0 && SIZE <= 64, "SMTBitVec size must be less than 64.");
    }

    static SMTBitVec<1> from_bool(const bool value) {
        static_assert(SIZE == 1, "SMTBitVec size must be 1.");
        return SMTBitVec<1>(value);
    }

    static SMTBitVec<SIZE> from_hex_str(const char* hex_str) {
        size_t str_len = strlen(hex_str);
        assert(str_len % 2 == 0);
        char tmp_store[3] = {0};

        std::vector<uint8_t> bytes(str_len / 2);
        for (size_t i = 0; i < str_len; i += 2) {
            tmp_store[0] = hex_str[i];
            tmp_store[1] = hex_str[i + 1];
            uint8_t byte = (uint8_t) strtol(tmp_store, NULL, 16);
            bytes[i / 2] = byte;
        }
        return SMTBitVec<SIZE>(bytes.data(), 0, bytes.size());
    }

    SMTBitVec(const bitset<SIZE>& value) : bits(value) {
        // static_assert(SIZE >= 0 && SIZE <= 64, "SMTBitVec size must be less than 64.");
    }

    SMTBitVec(const SMTBitVec<SIZE>& value) : bits(value.bits) {
        // static_assert(SIZE >= 0 && SIZE <= 64, "SMTBitVec size must be less than 64.");
    }

    SMTBitVec(const uint8_t* buffer, size_t from_bit, size_t buffer_size_in_bytes): bits() {
        // static_assert(SIZE >= 0 && SIZE <= 64, "SMTBitVec size must be less than 64.");

        size_t from_byte = from_bit / 8;
        size_t from_bit_in_byte = from_bit % 8;
        size_t to_byte = (from_bit + SIZE - 1) / 8;
        size_t to_bit_in_byte = (from_bit + SIZE - 1) % 8;

        if (from_byte >= buffer_size_in_bytes) {
            exit(1);
        }

        if (from_byte == to_byte) {
            uint8_t byte = buffer[from_byte] >> from_bit_in_byte;
            for (int i = 0; i < SIZE; i++) {
                bits[i] = byte & 1;
                byte >>= 1;
            }
        } else {
            uint8_t byte = buffer[from_byte] >> from_bit_in_byte;
            for (int i = 0; i < 8 - from_bit_in_byte; i++) {
                bits[i] = byte & 1;
                byte >>= 1;
            }
            for (int i = 1; i < to_byte - from_byte; i++) {
                byte = buffer[from_byte + i];
                for (int j = 0; j < 8; j++) {
                    bits[i * 8 + j] = byte & 1;
                    byte >>= 1;
                }
            }
            byte = buffer[to_byte];
            for (int i = 0; i <= to_bit_in_byte; i++) {
                bits[(to_byte - from_byte) * 8 + i] = byte & 1;
                byte >>= 1;
            }
        }
    }

    uint64_t raw_value() const {
        assert(SIZE >= 0 && SIZE <= 64 && "SMTBitVec size must be less than 64.");
        return (uint64_t) bits.to_ullong();
    }

    UBigInteger<SIZE> big_raw_value() const {
        assert(SIZE > 64);
        return UBigInteger<SIZE>(*this);
    }

    BigInteger<SIZE> big_signed_value() const {
        return big_raw_value().to_signed();
    }

    bool raw_bool() const {
        static_assert(SIZE == 1, "SMTBitVec size must be 1.");
        return bits[0];
    }

    static constexpr size_t size() {
        return SIZE;
    }

    const std::vector<uint8_t> bytes() const {
        // static_assert(SIZE <= 64, "SMTBitVec size must be less than 64.");
        std::vector<uint8_t> bytes(size() / 8 + (size() % 8 == 0 ? 0 : 1));
        if (size() <= 64) {
            uint64_t value = raw_value();
            for (size_t i = 0; i < size() / 8 + (size() % 8 == 0 ? 0 : 1); i++) {
                bytes[i] = value & 0xFF;
                value >>= 8;
            }
        } else {
            std::bitset<SIZE> mask(0xFF);
            std::bitset<SIZE> bits = this->bits;
            for (size_t i = 0; i < size() / 8 + (size() % 8 == 0 ? 0 : 1); i++) {
                bytes[i] = (bits & mask).to_ullong();
                bits >>= 8;
            }
        }
        return bytes;
    }

    template<int ANOTHER_SIZE>
    SMTBitVec<SIZE + ANOTHER_SIZE> concat(SMTBitVec<ANOTHER_SIZE> another) const {
        bitset<SIZE + ANOTHER_SIZE> bits(0);
        for (int i = 0; i < SIZE; i++) {
            bits[i] = this->bits[i];
        }
        for (int i = 0; i < ANOTHER_SIZE; i++) {
            bits[i + SIZE] = another.bits[i];
        }
        return SMTBitVec<SIZE + ANOTHER_SIZE>(bits);
    }

    template<int FROM, int TO>
    SMTBitVec<TO + 1 - FROM> extract() const {
        static_assert(FROM >= 0 && TO >= FROM && TO < SIZE, "Invalid extract range.");
        bitset<TO + 1 - FROM> bits(0);
        for (int i = 0; i < TO + 1 - FROM; i++) {
            bits[i] = this->bits[i + FROM];
        }
        return bits;
    }

    template<int TIMES>
    SMTBitVec<SIZE * TIMES> repeat() const {
        static_assert(TIMES >= 0, "Invalid repeat times.");
        bitset<SIZE * TIMES> bits(0);
        for (int i = 0; i < SIZE * TIMES; i++) {
            bits[i] = this->bits[i % SIZE];
        }
        return SMTBitVec<SIZE * TIMES>(bits);
    }

    SMTBitVec<SIZE> operator&(const SMTBitVec<SIZE>& another) const {
        bitset<SIZE> bits = this->bits & another.bits;
        return SMTBitVec<SIZE>(bits);
    }

    SMTBitVec<SIZE> operator|(const SMTBitVec<SIZE>& another) const {
        bitset<SIZE> bits = this->bits | another.bits;
        return SMTBitVec<SIZE>(bits);
    }

    SMTBitVec<SIZE> operator~() const {
        bitset<SIZE> bits = ~this->bits;
        return SMTBitVec<SIZE>(bits);
    }

    SMTBitVec<SIZE> operator-() const {
        int64_t num = signed_value();
        return SMTBitVec<SIZE>((uint64_t) -num);
    }

    SMTBitVec<SIZE> operator+(const SMTBitVec<SIZE>& another) const {
        if (SIZE > 64) {
            return (big_raw_value() + another.big_raw_value()).to_bv();
        }

        uint64_t num1 = raw_value();
        uint64_t num2 = another.raw_value();
        return SMTBitVec<SIZE>(num1 + num2);
    }

    SMTBitVec<SIZE> operator*(const SMTBitVec<SIZE>& another) const {
        uint64_t num1 = raw_value();
        uint64_t num2 = another.raw_value();
        return SMTBitVec<SIZE>(num1 * num2);
    }

    SMTBitVec<SIZE> operator/(const SMTBitVec<SIZE>& another) const {
        uint64_t num1 = raw_value();
        uint64_t num2 = another.raw_value();
        if (num2 == 0) {
            return SMTBitVec<SIZE>(1);
        }
        uint64_t num3 = num1 / num2;
        return SMTBitVec<SIZE>(num3);
    }

    SMTBitVec<SIZE> operator%(const SMTBitVec<SIZE>& another) const {
        uint64_t num1 = raw_value();
        uint64_t num2 = another.raw_value();
        if (num2 == 0) {
            return SMTBitVec<SIZE>(raw_value());
        }
        uint64_t num3 = num1 % num2;
        return SMTBitVec<SIZE>(num3);
    }

    SMTBitVec<SIZE> shl(const SMTBitVec<SIZE>& shift_bv) const {
        uint64_t shift = shift_bv.raw_value();
        bitset<SIZE> bits = this->bits << shift;
        return SMTBitVec<SIZE>(bits);
    }

    SMTBitVec<SIZE> lshr(const SMTBitVec<SIZE>& shift_bv) const {
        uint64_t shift = shift_bv.raw_value();
        bitset<SIZE> bits = this->bits >> shift;
        return SMTBitVec<SIZE>(bits);
    }

    bool operator<(const SMTBitVec<SIZE>& another) const {
        uint64_t num1 = raw_value();
        uint64_t num2 = another.raw_value();
        return num1 < num2;
    }

    bool operator==(const SMTBitVec<SIZE>& another) const {
        uint64_t num1 = raw_value();
        uint64_t num2 = another.raw_value();
        return num1 == num2;
    }

    SMTBitVec<SIZE> operator-(const SMTBitVec<SIZE>& another) const {
        uint64_t num1 = raw_value();
        uint64_t num2 = another.raw_value();
        return SMTBitVec<SIZE>(num1 - num2);
    }

    int64_t signed_value() const {
        assert(SIZE >= 0 && SIZE <= 64 && "SMTBitVec size must be less than 64.");
        uint64_t num = raw_value();
        bool is_neg = bits[SIZE - 1];
        if (is_neg) {
            num = ((0xFFFFFFFFFFFFFFFF >> SIZE) << SIZE) | num;
        }
        return (int64_t) num;
    }

    SMTBitVec<SIZE> sdiv(const SMTBitVec<SIZE>& another) const {
        int64_t num1 = signed_value();
        int64_t num2 = another.signed_value();
        if (num2 == 0) {
            return SMTBitVec<SIZE>(1);
        }
        int64_t num3 = num1 / num2;
        return SMTBitVec<SIZE>((uint64_t) (num3));
    }

    SMTBitVec<SIZE> srem(const SMTBitVec<SIZE>& another) const {
        int64_t num1 = signed_value();
        int64_t num2 = another.signed_value();
        if (num2 == 0) {
            return SMTBitVec<SIZE>(raw_value());
        }
        int64_t num3 = num1 % num2;
        return SMTBitVec<SIZE>((uint64_t) (num3));
    }
    
    SMTBitVec<SIZE> smod(const SMTBitVec<SIZE>& another) const {
        int64_t num1 = signed_value();
        int64_t num2 = another.signed_value();
        if (num2 == 0) {
            int64_t rem = num1;
            int64_t rem_abs = rem < 0 ? -rem : rem;
            return SMTBitVec<SIZE>((uint64_t) rem_abs);
        } else {
            int64_t rem = num1 % num2;
            int64_t num2_abs = num2 < 0 ? -num2 : num2;
            int64_t rem_abs = rem < 0 ? -rem : rem;
            return SMTBitVec<SIZE>((uint64_t) (rem < 0 ? (num2_abs - rem_abs) : rem_abs));
        }
    }


    SMTBitVec<SIZE> ashr(const SMTBitVec<SIZE>& shift_bv) const {
        uint64_t shift = shift_bv.raw_value();
        int64_t num = signed_value();
        return SMTBitVec<SIZE>((uint64_t) (num >> shift));
    }

    bool operator<=(const SMTBitVec<SIZE>& another) const {
        uint64_t num1 = raw_value();
        uint64_t num2 = another.raw_value();
        return num1 <= num2;
    }

    bool operator>(const SMTBitVec<SIZE>& another) const {
        uint64_t num1 = raw_value();
        uint64_t num2 = another.raw_value();
        return num1 > num2;
    }

    bool operator>=(const SMTBitVec<SIZE>& another) const {
        uint64_t num1 = raw_value();
        uint64_t num2 = another.raw_value();
        return num1 >= num2;
    }

    bool slt(const SMTBitVec<SIZE>& another) const {
        if (SIZE > 64) {
            return this->big_signed_value() < another.big_signed_value();
        }

        int64_t num1 = signed_value();
        int64_t num2 = another.signed_value();
        return num1 < num2;
    }

    bool sle(const SMTBitVec<SIZE>& another) const {
        int64_t num1 = signed_value();
        int64_t num2 = another.signed_value();
        return num1 <= num2;
    }

    bool sgt(const SMTBitVec<SIZE>& another) const {
        int64_t num1 = signed_value();
        int64_t num2 = another.signed_value();
        return num1 > num2;
    }

    bool sge(const SMTBitVec<SIZE>& another) const {
        int64_t num1 = signed_value();
        int64_t num2 = another.signed_value();
        return num1 >= num2;
    }

    template<int PADDING_SIZE>
    SMTBitVec<SIZE + PADDING_SIZE> sign_ext() const {
        // static_assert(SIZE >= 0 && SIZE <= 64, "SMTBitVec size must be less than 64.");
        // static_assert(PADDING_SIZE >= 0 && PADDING_SIZE + SIZE <= 64, "SMTBitVec size must be less than 64.");
        bitset<SIZE + PADDING_SIZE> retval(0);
        bool is_neg = bits[SIZE - 1];
        for (int i = 0; i < SIZE; i++) {
            retval[i] = this->bits[i];
        }
        if (is_neg) {
            for (int i = SIZE; i < SIZE + PADDING_SIZE; i++) {
                retval[i] = 1;
            }
        }
        return SMTBitVec<SIZE + PADDING_SIZE>(retval);
    }

    template<int PADDING_SIZE>
    SMTBitVec<SIZE + PADDING_SIZE> zero_ext() const {
        // static_assert(SIZE >= 0 && SIZE <= 64, "SMTBitVec size must be less than 64.");
        // static_assert(PADDING_SIZE >= 0 && PADDING_SIZE + SIZE <= 64, "SMTBitVec size must be less than 64.");
        bitset<SIZE + PADDING_SIZE> bits(0);
        for (int i = 0; i < SIZE; i++) {
            bits[i] = this->bits[i];
        }
        return SMTBitVec<SIZE + PADDING_SIZE>(bits);
    }

    template<int SHIFT>
    SMTBitVec<SIZE> rotate_left() const {
        SMTBitVec<SHIFT> leftmost = this->extract<SIZE - SHIFT, SIZE - 1>();
        SMTBitVec<SIZE> tmp = this->shl(SHIFT);
        return tmp | (leftmost.template zero_ext<SIZE - SHIFT>());
    }

    template<int SHIFT>
    SMTBitVec<SIZE> rotate_right() const {
        SMTBitVec<SHIFT> rightmost = this->extract<0, SHIFT - 1>();
        SMTBitVec<SIZE> tmp = this->lshr(SHIFT);
        return tmp | (rightmost.template zero_ext<SIZE - SHIFT>().shl(SIZE - SHIFT));
    }
};

template<typename D, typename R>
class SMTArray {
private:
    vector<R> data;
    size_t upper_bound;
public:
    SMTArray(const D& upper_bound) : upper_bound((size_t) upper_bound.raw_value()) {
        data.resize(upper_bound.raw_value());
    }

    R get(const D& index) const {
        uint64_t idx = index.raw_value();
        if (idx > upper_bound) {
            return R::default_();
        }
        return data[idx];
    }

    void write(const D& index, R value) {
        uint64_t idx = index.raw_value();
        if (idx > upper_bound) {
            // for (uint64_t i = upper_bound; i < idx; i++) {
            //     data.push_back(R::default_());
            // }
            // data.push_back(value);
            // upper_bound = idx;
            // return;
            exit(0);
        }
        data[idx] = value;
    }

    R select(const D& index) const {
        return get(index);
    }

    SMTArray<D, R> store(const D& index, R value) const {
        SMTArray<D, R> retval(*this);
        retval.write(index, value);
        return retval;
    }

    size_t size() const {
        return data.size() * upper_bound;
    }
};

template<int N>
class hash<SMTBitVec<N>> {
public:
    size_t operator()(const SMTBitVec<N>& bv) const {
        return hash<uint64_t>()(bv.raw_value());
    }
};

template<typename D, typename R>
class SMTConstArray {
private:
    unordered_map<D, R> data;
    R initial_value;
public:
    SMTConstArray(R initial_value) : initial_value(initial_value), data() {}
    
    R get(const D& index) const {
        auto it = data.find(index);
        if (it == data.end()) {
            return initial_value;
        } else {
            return it->second;
        }
    }

    void write(const D& index, R value) {
        data[index] = value;
    }

    R select(const D& index) const {
        return get(index);
    }

    SMTConstArray<D, R> store(const D& index, R value) const {
        SMTConstArray<D, R> retval(*this);
        retval.write(index, value);
        return retval;
    }
};


class MemoryProxy {
private:
    struct {
        uint64_t offset_value;
        uint64_t offset_neg;
    };
    uint64_t min_addr;
    uint8_t* memory_space;
    size_t size;

public:
    MemoryProxy(uint64_t min_addr, size_t size) {
        this->size = size;
        this->memory_space = new uint8_t[size];
        if ((uint64_t) this->memory_space > min_addr) {
            this->offset_value = (uint64_t) this->memory_space - min_addr;
            this->offset_neg = false;
        } else {
            this->offset_value = min_addr - (uint64_t) this->memory_space;
            this->offset_neg = true;
        }
        this->min_addr = min_addr;
    }

    ~MemoryProxy() {
        delete[] memory_space;
    }

    void memset(uint64_t addr, SMTBool value) {
        if (addr + 1 > min_addr + size) {
            assert(false);
        }
        memory_space[addr - min_addr] = (uint8_t) value;
    }

    void memset(uint64_t addr, const char* hex_bytes) {
        size_t len = strlen(hex_bytes);
        assert(len % 2 == 0);
        if (addr + len / 2 > min_addr + size) {
            assert(false);
        }

        uint8_t buffer[len / 2];

        char tmp_store[3] = {0};

        for (size_t i = 0; i < len; i += 2) {
            tmp_store[0] = hex_bytes[i];
            tmp_store[1] = hex_bytes[i + 1];
            uint8_t byte = (uint8_t) strtol(tmp_store, NULL, 16);
            buffer[i / 2] = byte;
        }

        memcpy(memory_space + addr - min_addr, buffer, len / 2);
    }

    template<int N>
    void memset(uint64_t addr, SMTBitVec<N> bitvec) {
        if (addr + bitvec.size() / 8 + (bitvec.size() % 8 == 0 ? 0 : 1) > min_addr + size) {
            assert(false);
        }
        auto bytes = bitvec.bytes();
        for (uint64_t i = 0; i < bytes.size(); i++) {
            memory_space[addr - min_addr + i] = bytes[i];
        }
    }

    uint64_t proxy_addr(uint64_t original_addr) const {
        if (original_addr == 0) {
            return 0;
        }
        return offset_neg ? original_addr - offset_value
                          : original_addr + offset_value;
    }

    uint64_t original_addr(uint64_t proxy_addr) const {
        if (proxy_addr == 0) {
            return 0;
        }
        return offset_neg ? proxy_addr + offset_value
                          : proxy_addr - offset_value;
    }
};


class InputBuffer {
private:
    const uint8_t* buffer;
    size_t size;

public:
    InputBuffer(const uint8_t* buffer, size_t size) {
        this->buffer = buffer;
        this->size = size;
    }

    template<int N>
    SMTBitVec<N> read_bv(size_t from_bit, const std::set<uint8_t> virtual_bytes) {
        assert(from_bit % 8 == 0);
        size_t from_byte = from_bit / 8;
        size_t byte_num = N / 8 + (N % 8 == 0 ? 0 : 1);
        uint8_t* bytes = new uint8_t[byte_num];
        size_t ptr = from_byte;
        for (size_t i = 0; i < byte_num; i++) {
            if (virtual_bytes.count(i) > 0) {
                bytes[i] = 0;
            } else {
                assert(ptr < size);
                bytes[i] = buffer[ptr];
                ptr++;
            }
        }
        SMTBitVec<N> r = SMTBitVec<N>(bytes, 0, byte_num);
        delete[] bytes;
        return r;
    }

    SMTBool read_bool(size_t from_bit, const std::set<uint8_t> virtual_bytes) {
        if (!virtual_bytes.empty()) {
            assert(virtual_bytes.size() == 1 && virtual_bytes.count(0) == 1);
            return SMTBool(false);
        }
        return static_cast<SMTBool>(buffer[from_bit / 8] & (1 << (from_bit % 8)));
    }

    template<int D, int R>
    SMTArray<SMTBitVec<D>, SMTBitVec<R>> read_bv_arr(size_t from_bit, size_t upper_bound, const std::set<uint8_t> virtual_bytes) {
        SMTArray<SMTBitVec<D>, SMTBitVec<R>> result(upper_bound + 1);
        assert(from_bit % 8 == 0);
        size_t from_byte = from_bit / 8;
        size_t byte_num = (upper_bound + 1) * R / 8 + ((upper_bound + 1) * R % 8 == 0 ? 0 : 1);
        uint8_t* bytes = new uint8_t[byte_num];
        size_t ptr = from_byte;
        for (size_t i = 0; i < byte_num; i++) {
            if (virtual_bytes.count(i) > 0) {
                bytes[i] = 0;
            } else {
                assert(ptr < size);
                bytes[i] = buffer[ptr];
                ptr++;
            }
        }
        for (size_t i = 0; i <= upper_bound; i++) {
            result.write(SMTBitVec<D>(i), SMTBitVec<R>(bytes, i * R, byte_num));
        }
        return result;
    }
};

class Output {
private:
    vector<uint8_t> buffer;
    std::string filename;
public:
    Output(std::string filename, size_t sz) : filename(filename), buffer(sz) {}

    void insert_byte(size_t byte_offset, uint8_t byte) {
        buffer[byte_offset] = byte;
    }

    template<int N>
    void record_bitvec(size_t start_bits, const SMTBitVec<N>& bitvec) {
        assert(start_bits % 8 == 0);
        size_t sz_in_bytes = N / 8 + (N % 8 == 0 ? 0 : 1);
        for (size_t i = 0; i < sz_in_bytes; i++) {
            insert_byte(start_bits / 8 + i, bitvec.bytes()[i]);
        }
    }

    void record_bool(size_t start_bits, const bool b) {
        assert(start_bits % 8 == 0);
        uint8_t to_append = b ? 1 : 0;
        // append_byte(to_append);
        insert_byte(start_bits / 8, to_append);
    }

    void dump() {
        if (buffer.empty()) {
            return;
        }
        FILE* fp = fopen(filename.c_str(), "wb");
        fwrite(buffer.data(), 1, buffer.size(), fp);
        fclose(fp);
    }
};

extern "C" size_t LLVMFuzzerCustomMutatorNeg(uint8_t *data, size_t size, size_t max_size, unsigned int seed) {
    for (size_t i = 0; i < size; i++) {
        int8_t byte = (int8_t) data[i];
        data[i] = -byte;
    }
    return size;
}