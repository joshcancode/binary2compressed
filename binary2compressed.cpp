// Credit from ocornut's binary_to_compressed.cpp
// Helper tool to turn a file into a C array, if you want to embed file data in your source code.

// Usage:
//   binary_to_compressed_c.exe [-base85] [-nocompress] <inputfile> <symbolname>
// Usage example:
//   # binary_to_compressed_c.exe myfont.ttf MyFont > myfont.cpp

#define _CRT_SECURE_NO_WARNINGS

#include <assert.h>
#include <cstdint>
#include <errno.h>
#include <stdio.h>
#include <string>

namespace stb
{
    std::uint32_t adler32(std::uint32_t adler32, std::uint8_t* buffer, std::uint32_t bufferLength) noexcept;
    std::uint32_t compress(std::uint8_t* out, std::uint8_t* input, std::uint32_t length) noexcept;
    int compressChunk(std::uint8_t* start, std::uint8_t* end, int length, int* pendingLiterals, std::uint8_t** cHash, std::uint32_t mask) noexcept;
    int compressInner(std::uint8_t* input, std::uint32_t length) noexcept;
    void out(std::uint32_t v) noexcept;
    void shiftOut(std::uint32_t v, int level = 0) noexcept;
    void write(std::uint8_t v) noexcept;
}

// ---------- Compressor ---------- //

std::uint32_t stb::adler32(std::uint32_t adler32, std::uint8_t* buffer, std::uint32_t bufferLength) noexcept
{
    constexpr int adlerBase = 65521; // Largest prime smaller than 65536

    std::uint32_t blockLength = bufferLength % 5552;
    std::uint32_t s1 = adler32 & 0xFFFF;
    std::uint32_t s2 = adler32 >> 16;

    std::uint32_t i = 0;

    while (bufferLength != 0) {
        for (i = 0; i + 7 < blockLength; i += 8) {
            for (int j = 0; j < 8; ++j) {
                s1 += buffer[j];
                s2 += s1;
            }

            buffer += 8;
        }

        for (; i < blockLength; ++i) {
            s1 += *buffer++;
            s2 += s1;
        }

        s1 %= adlerBase;
        s2 %= adlerBase;
        bufferLength -= blockLength;
        blockLength = 5552;
    }

    return (s2 << 16) + s1;
}

static std::uint32_t matchLength(std::uint8_t* m1, std::uint8_t* m2, std::uint32_t maxLength) noexcept
{
    std::uint32_t i = 0;
    for (i = 0; i < maxLength; ++i) {
        if (m1[i] != m2[i])
            break;
    }

    return i;
}

static std::uint8_t* stb__out;
static std::uint32_t stb__outbytes;
static std::FILE* stb__outfile;

void stb::write(std::uint8_t v) noexcept
{
    std::fputc(v, stb__outfile);
    ++stb__outbytes;
}

void stb::out(std::uint32_t v) noexcept
{
    do {
        if (stb__out)
            *stb__out++ = static_cast<std::uint8_t>(v);
        else
            write(static_cast<std::uint8_t>(v));
    } while (0);
}

void stb::shiftOut(std::uint32_t v, int level) noexcept
{
    if (level >= 2)
        out(v >> 24);

    if (level >= 1)
        out(v >> 16);

    out(v >> 8);
    out(v);
}

static void outLiterals(std::uint8_t* in, int numlit)
{
    while (numlit > 65536) {
        outLiterals(in, 65536);
        in += 65536;
        numlit -= 65536;
    }

    if (numlit == 0);
    else if (numlit <= 32)
        stb::out(0x000020 + numlit - 1);
    else if (numlit <= 2048)
        stb::shiftOut(0x000800 + numlit - 1);
    else
        stb::shiftOut(0x070000 + numlit - 1, 1);

    if (stb__out) {
        std::memcpy(stb__out, in, numlit);
        stb__out += numlit;
    }
    else
        std::fwrite(in, 1, numlit, stb__outfile);
}

static int stb_not_crap(int best, int dist)
{
    return (best > 2 && dist <= 0x00100) || (best > 5 && dist <= 0x04000) || (best > 7 && dist <= 0x80000);
}

// note that you can play with the hashing functions all you
// want without needing to change the decompressor
#define stb__hc(q,h,c)      (((h) << 7) + ((h) >> 25) + q[c])
#define stb__hc2(q,h,c,d)   (((h) << 14) + ((h) >> 18) + (q[c] << 7) + q[d])
#define stb__hc3(q,c,d,e)   ((q[c] << 14) + (q[d] << 7) + q[e])

static int stb__window = 0x40000; // 256K
static unsigned int stb__running_adler;
static std::uint32_t stb__hashsize = 32768;

int stb::compressChunk(std::uint8_t* start, std::uint8_t* end, int length, int* pendingLiterals, std::uint8_t** cHash, std::uint32_t mask) noexcept
{
    auto scramble = [&](unsigned int h) -> int {
        return (h + (h >> 16) & mask);
    };

    int window = stb__window;
    std::uint32_t match_max;
    std::uint8_t* lit_start = start - *pendingLiterals;
    std::uint8_t* q = start;

    // stop short of the end so we don't scan off the end doing
    // the hashing; this means we won't compress the last few bytes
    // unless they were part of something longer
    while (q < start + length && q + 12 < end) {
        int m;
        std::uint32_t h1, h2, h3, h4, h;
        std::uint8_t* t;
        int best = 2, dist = 0;

        if (q + 65536 > end)
            match_max = end - q;
        else
            match_max = 65536;

#define stb__nc(b,d)  ((d) <= window && ((b) > 9 || stb_not_crap(b,d)))

#define STB__TRY(t,p)  /* avoid retrying a match we already tried */ \
    if (p ? dist != q-t : 1)                             \
    if ((m = matchLength(t, q, match_max)) > best)     \
    if (stb__nc(m,q-(t)))                                \
    best = m, dist = q - (t)

        // rather than search for all matches, only try 4 candidate locations,
        // chosen based on 4 different hash functions of different lengths.
        // this strategy is inspired by LZO; hashing is unrolled here using the
        // 'hc' macro
        h = stb__hc3(q, 0, 1, 2); h1 = scramble(h);
        t = cHash[h1]; if (t) STB__TRY(t, 0);
        h = stb__hc2(q, h, 3, 4); h2 = scramble(h);
        h = stb__hc2(q, h, 5, 6);        t = cHash[h2]; if (t) STB__TRY(t, 1);
        h = stb__hc2(q, h, 7, 8); h3 = scramble(h);
        h = stb__hc2(q, h, 9, 10);        t = cHash[h3]; if (t) STB__TRY(t, 1);
        h = stb__hc2(q, h, 11, 12); h4 = scramble(h);
        t = cHash[h4]; if (t) STB__TRY(t, 1);

        // because we use a shared hash table, can only update it
        // _after_ we've probed all of them
        cHash[h1] = cHash[h2] = cHash[h3] = cHash[h4] = q;

        if (best > 2)
            assert(dist > 0);

        // see if our best match qualifies
        if (best < 3) // fast path literals
            ++q;
        else if (best > 2 && best <= 0x80 && dist <= 0x100) {
            outLiterals(lit_start, q - lit_start); lit_start = (q += best);
            stb::out(0x80 + best - 1);
            stb::out(dist - 1);
        }
        else if (best > 5 && best <= 0x100 && dist <= 0x4000) {
            outLiterals(lit_start, q - lit_start); lit_start = (q += best);
            stb::shiftOut(0x4000 + dist - 1);
            stb::out(best - 1);
        }
        else if (best > 7 && best <= 0x100 && dist <= 0x80000) {
            outLiterals(lit_start, q - lit_start); lit_start = (q += best);
            stb::shiftOut(0x180000 + dist - 1, 1);
            stb::out(best - 1);
        }
        else if (best > 8 && best <= 0x10000 && dist <= 0x80000) {
            outLiterals(lit_start, q - lit_start); lit_start = (q += best);
            stb::shiftOut(0x100000 + dist - 1, 1);
            stb::shiftOut(best - 1);
        }
        else if (best > 9 && dist <= 0x1000000) {
            if (best > 65536) best = 65536;
            outLiterals(lit_start, q - lit_start); lit_start = (q += best);
            if (best <= 0x100) {
                stb::out(0x06);
                stb::shiftOut(dist - 1, 1);
                stb::out(best - 1);
            }
            else {
                stb::out(0x04);
                stb::shiftOut(dist - 1, 1);
                stb::shiftOut(best - 1);
            }
        }
        else // fallback literals if no match was a balanced tradeoff
            ++q;
    }

    // if we didn't get all the way, add the rest to literals
    if (q - start < length)
        q = start + length;

    // the literals are everything from lit_start to q
    *pendingLiterals = (q - lit_start);

    stb__running_adler = stb::adler32(stb__running_adler, start, q - start);
    return q - start;
}

int stb::compressInner(std::uint8_t* input, std::uint32_t length) noexcept
{
    std::uint8_t** chash = static_cast<std::uint8_t**>(std::malloc(stb__hashsize * sizeof(std::uint8_t*)));
    if (chash == NULL)
        return 0;

    for (std::uint32_t i = 0; i < stb__hashsize; ++i)
        chash[i] = NULL;

    // stream signature
    stb::out(0x57);
    stb::out(0xbc);
    stb::shiftOut(0);

    stb::shiftOut(0, 2); // 64-bit length requires 32-bit leading 0
    stb::shiftOut(length, 2);
    stb::shiftOut(stb__window, 2);

    stb__running_adler = 1;

    int literals = 0;
    int hashLength = compressChunk(input, input + length, length, &literals, chash, stb__hashsize - 1);
    assert(hashLength == length);

    outLiterals(input + length - literals, literals);

    std::free(chash);

    stb::shiftOut(0x05fa); // end opcode
    stb::shiftOut(stb__running_adler, 2);

    return 1;
}

std::uint32_t stb::compress(std::uint8_t* out, std::uint8_t* input, std::uint32_t length) noexcept
{
    stb__out = out;
    stb__outfile = NULL;

    compressInner(input, length);

    return stb__out - out;
}

char encode85Byte(unsigned int x)
{
    x = (x % 85) + 35;
    return x >= '\\' ? x + 1 : x;
}

bool binaryToCompressed(const char* fileName, const char* symbol, bool useBase85Encoding, bool useCompression)
{
    // Read the font file using rb, since this is not a text file
    FILE* stream = std::fopen(fileName, "rb");
    if (!stream) {
        std::perror("An error has occured");
        return false;
    }

    // Calculate the size of the font file data, and check for any errors with the file
    std::uint32_t dataSize = 0;
    if (std::fseek(stream, 0L, SEEK_END) != 0 || (dataSize = static_cast<std::uint32_t>(std::ftell(stream))) == -1 || std::fseek(stream, 0L, SEEK_SET) != 0) {
        std::fclose(stream);
        return false;
    }

    // Read the file and write to our newly allocated data. We will also check that the size we calculated matches the actual data size
    char* data = new char[dataSize + 4];
    if (fread_s(data, dataSize + 4, 1, dataSize, stream) != dataSize) {
        std::fclose(stream);
        delete[] data;
        return false;
    }

    // We are done making sure the font file is valid, close the file and reset the memory stored in data
    std::fclose(stream);
    std::memset(static_cast<char*>(data + dataSize), 0, 4);

    // Compress our data
    const std::uint32_t maxLength = dataSize + 512 + (dataSize >> 2) + sizeof(int); // Total guess, might need to be fixed
    char* compressed = useCompression ? new char[maxLength] : data;
    const std::uint32_t compressedSize = useCompression ? stb::compress(reinterpret_cast<std::uint8_t*>(compressed), reinterpret_cast<std::uint8_t*>(data), dataSize) : dataSize;

    if (useCompression)
        std::memset(static_cast<char*>(compressed + compressedSize), 0, maxLength - compressedSize);

    // Output as Base85 encoded
    FILE* out = stdout;
    std::fprintf(out, "// File: '%s' (%d bytes)\n", fileName, dataSize);

    const char* nameSuffix = useCompression ? "_compressed" : "_";

    if (useBase85Encoding) {
        std::fprintf(out, "static const char %s%sdata_base85[%d + 1] =\n\t\"", symbol, nameSuffix, ((compressedSize + 3) / 4) * 5);
        char previousChar = NULL;

        for (std::uint32_t i = 0; i < compressedSize; i += 4) {
            // This is made a little more complicated by the fact that ??X sequences are interpreted as trigraphs by old C/C++ compilers. So we need to escape pairs of ??.
            std::uint32_t d = *reinterpret_cast<std::uint32_t*>(compressed + i);

            for (int n = 0; n < 5; ++n, d /= 85) {
                const char c = encode85Byte(d);
                std::fprintf(out, (c == '?' && previousChar == '?') ? "\\%c" : "%c", c);
                previousChar = c;
            }

            if ((i % 112) == 108)
                std::fprintf(out, "\"\n\t\"");
        }
        std::fprintf(out, "\";");
    }
    else {
        std::fprintf(out, "constexpr unsigned int %s%sSize = %d;\n", symbol, nameSuffix, compressedSize);
        std::fprintf(out, "constexpr unsigned int %s%sData[%d / 4] = {\n\t", symbol, nameSuffix, ((compressedSize + 3) / 4) * 4);

        // The number of columns per line
        constexpr int columns = 12;
        int column = 0;

        for (std::uint32_t i = 0; i < compressedSize; i += 4) {
            if (compressedSize - i == 3)
                std::fprintf(out, "0x%08x", *reinterpret_cast<unsigned int*>(compressed + i));
            else
                std::fprintf(out, (column++ % columns) == 0 ? "\n\t0x%08x, " : "0x%08x, ", *reinterpret_cast<unsigned int*>(compressed + i));
        }

        std::fprintf(out, "\n};");
    }

    // De-allocate the memory we've occupied
    if (useCompression)
        delete[] compressed;

    delete[] data;
    return true;
}

int main(int argc, char** argv)
{
    if (argc < 3) {
        std::printf("Syntax: %s [-base85] [-nocompress] <inputfile> <symbolname>\n", argv[0]);
        return EXIT_SUCCESS;
    }

    bool base85Encoding = false;
    bool compression = true;
    int arg = 1;

    if (argv[arg][0] == '-') {
        if (std::strcmp(argv[arg], "-base85") == 0)
            base85Encoding = true;
        else if (std::strcmp(argv[arg], "-nocompress") == 0)
            compression = false;
        else {
            std::fprintf(stderr, "Unknown argument: '%s'\n", argv[arg]);
            return EXIT_FAILURE;
        }

        ++arg;
    }

    if (binaryToCompressed(argv[arg], argv[arg + 1], base85Encoding, compression))
        return EXIT_SUCCESS;

    std::fprintf(stderr, "Error opening or reading file: '%s'\n", argv[arg]);
    return EXIT_FAILURE;
}