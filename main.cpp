#include <cryptopp/integer.h>
#include <cryptopp/modarith.h>
#include <cryptopp/osrng.h>
#include <cryptopp/rsa.h>

#include <exception>
#include <fstream>
#include <sstream>
#include <iomanip>
#include <iostream>
#include <unordered_map>
#include <vector>

using CryptoPP::Integer;

class Server
{
    private:
    CryptoPP::RSA::PrivateKey privateKey;
    CryptoPP::AutoSeededRandomPool prng;

    public:
    const int keysize;
    CryptoPP::RSA::PublicKey publicKey;
    std::string PS;

    Server(int keysize) : keysize(keysize)
    {
        privateKey.GenerateRandomWithKeySize(prng, keysize);
        publicKey = CryptoPP::RSA::PublicKey(privateKey);
    }

    bool isPkcsConforming(const Integer& c)
    {
        Integer m = privateKey.CalculateInverse(prng, c);
        if (m.BitCount() != keysize - 14) return false;
        int sz = m.ByteCount();

        if (m.GetByte(sz - 1) != 2) return false;
        for (int i = 0; i < 8; ++i)
            if (m.GetByte(sz - 2 - i) == 0) return false;
        for (int i = sz - 10; i >= 0; --i)
            if (m.GetByte(i) == 0) return true;
        return false;
    }

    Integer PkcsEncrypt(const std::string& s)
    {
        int max_size = publicKey.GetModulus().ByteCount() - 11;
        if (s.length() > max_size)
            throw std::overflow_error("message too long, max size is " + std::to_string(max_size));

        int pad = publicKey.GetModulus().ByteCount() - 3 - s.length();
        uint16_t rnd;
        Integer res = Integer::Power2(keysize) - 1;
        int sz = res.ByteCount();
        res.SetByte(sz - 2, 2);

        for (int i = 0; i < pad; ++i)
        {
            do
            {
                rnd = random() % 256;
            } while (rnd == 0);
            res.SetByte(sz - 3 - i, rnd);
        }
        res.SetByte(sz - 3 - pad, 0);

        for (int i = 0; i < s.length(); ++i)
            res.SetByte((sz - 4 - pad) - i, s[i]);

        res.SetByte(sz - 1, 0);

        return publicKey.ApplyFunction(res);
    }
};

// helper class to help messuring times
// only used for debbuging, has no actual effect
class ProgressBar
{
    int guess;
    const std::string name;
    const clock_t begin;
    std::ostream& os;
    int counter = 0, last = -1;

    public:
    ProgressBar(const std::string& name, int guess, std::ostream& os)
    : name(name), guess(guess), os(os), begin(clock())
    {
    }

    int get_counter() const
    {
        return counter;
    }

    void advance()
    {
        counter++;
        int per = (counter * 100) / guess;
        if (per <= last) return;
        last = per;

        os << name << ": " << per << "%";
        
        if (per >= 10 && counter < guess)
        {
            double remain = clock() - begin;
            remain /= CLOCKS_PER_SEC;
            remain *= 1 - double(counter) / guess;
            os << " remaining time " << remain << " seconds";
        }
        os << std::endl;
    }
};

class Intervals
{
    public:
    typedef std::pair<Integer, Integer> II;
    std::vector<II> arr;

    // turn the set of non-disjoint intervals in "arr" to a set of disjoint intervals
    void sort()
    {
        std::sort(arr.begin(), arr.end(),
                  [](const II& i1, const II& i2) { return i1.first > i2.first; });

        int index = 0;
        for (int i = 0; i < arr.size(); ++i)
        {
            if (index != 0 && arr[index - 1].first <= arr[i].second)
            {
                while (index != 0 && arr[index - 1].first <= arr[i].second)
                {
                    arr[index - 1].second = std::max(arr[index - 1].second, arr[i].second);
                    arr[index - 1].first = std::min(arr[index - 1].first, arr[i].first);
                    --index;
                }
            }
            else
                arr[index] = arr[i];

            ++index;
        }

        while (arr.size() > index)
            arr.pop_back();
    }

    // returns the first element
    II& front()
    {
        return arr.front();
    }

    // returns the sum of sizes of intervals
    // i.e the number of integers that belongs to some interval
    Integer size() const
    {
        Integer res = 0;
        for (const II& p : arr)
            res += p.second - p.first + 1;
        return res;
    }

    // returns the number of disjoint intervals
    int count() const
    {
        return arr.size();
    }

    // inserts an elment to the set of intervals
    void insert(const Integer& a, const Integer& b)
    {
        arr.push_back(std::make_pair(a, b));
    }
};

Integer div_ceil(const Integer& n, const Integer& m)
{
    Integer res = n / m;
    if (n.Modulo(m).IsZero()) return res;
    return res + 1;
}

std::string PkcsDecode(const Integer& m, int keysize)
{
    if (m.BitCount() != keysize - 14) throw std::invalid_argument("invalid message length");
    std::vector<char> res;
    uint16_t c;

    int i;
    for (i = m.ByteCount() - 2; i >= 0 && m.GetByte(i) != 0; --i)
        ;
    if (i < 0) return "";
    --i;

    for (; i >= 0; --i)
        res.push_back(m.GetByte(i));
    res.push_back(0);
    return res.data();
}

Integer BleichenbacherAttack(Server& srv, const Integer& c, std::ostream& out)
{
    static int attack_count = 1;
    int keysize = srv.publicKey.GetModulus().BitCount();
    std::stringstream ss;
    ProgressBar pb("Attack progress bar #" + std::to_string(attack_count++), 15*keysize, ss);

    // basic variables
    Integer n = srv.publicKey.GetModulus();
    CryptoPP::ModularArithmetic modN = n;
    Integer B = Integer::Power2(n.BitCount() - 16);
    Integer s;
    // the current range of intervals we search in
    Intervals M;

    // algorithm
    // step 1 is skipped (since c is PCKS#1 conforming)
    M.insert(2 * B, 3 * B - 1);

    // step 2.a
    s = div_ceil(n, 3 * B);
    while (s < n && !srv.isPkcsConforming(modN.Multiply(srv.publicKey.ApplyFunction(s), c)))
    {
        s += 1;
        pb.advance();
    }
    pb.advance();

    for (int i = 1; M.size() > 1; ++i)
    {
        // step 2.b
        if (i != 1 && M.count() > 1)
        {
            s += 1;
            while (s < n && !srv.isPkcsConforming(modN.Multiply(srv.publicKey.ApplyFunction(s), c)))
            {
                s += 1;
                pb.advance();
            }
            pb.advance();
        }

        // step 2.c
        else if (i != 1)
        {
            Integer a = M.front().first, b = M.front().second;
            bool stop_flag = false;
            for (Integer r = div_ceil(2 * b * s - 4 * B, n); !stop_flag; ++r)
            {
                Integer begin = div_ceil(2 * B + r * n, b), end = div_ceil(3 * B + r * n, a) - 1;
                for (Integer st = begin; !stop_flag && st <= end; ++st)
                {
                    if (srv.isPkcsConforming(modN.Multiply(srv.publicKey.ApplyFunction(st), c)))
                    {
                        stop_flag = true;
                        s = st;
                        break;
                    }
                    pb.advance();
                }
            }
        }

        // step 3
        Intervals M_res;
        for (const auto& p : M.arr)
        {
            Integer a = p.first, b = p.second;
            Integer begin = div_ceil(a * s - 3 * B + 1, n), end = (b * s - 2 * B) / n;
            for (Integer r = begin; r <= end; ++r)
            {
                Integer na = std::max(a, div_ceil(2 * B + r * n, s)),
                        nb = std::min(b, (3 * B - 1 + r * n) / s);
                M_res.insert(na, nb);
            }
        }
        M_res.sort();
        M = M_res;
    }
    out << pb.get_counter();
    if (M.size() != 1) throw std::runtime_error("algorithmic impossibility");
    return M.front().first;
}

int main(int argc, char* argv[])
{
    std::ofstream log_file, data_file;
    log_file.open("log.txt");
    log_file << "index, keysize, messages" << std::endl;

    for (int i = 1; i < (1 << 20); ++i)
    {
        int keysize = rand() % (384 - 128) + 128;
        keysize *= 8;
        Server srv(keysize);

        Integer c = srv.PkcsEncrypt("hello world! my name is ofer! this is my secret");
        log_file << i << "," << keysize << ",";
        Integer attack_res = BleichenbacherAttack(srv, c, log_file);
        log_file << std::endl;
    }
    data_file.close();
    log_file.close();
    return 0;
}