#include <cryptopp/integer.h>
#include <cryptopp/modarith.h>
#include <cryptopp/osrng.h>
#include <cryptopp/rsa.h>

#include <exception>
#include <iomanip>
#include <iostream>
#include <sstream>
#include <unordered_map>
#include <vector>

using CryptoPP::Integer;

uint16_t hex2int(char c)
{
    if (c >= 'a' && c <= 'f') return 10 + (c - 'a');
    if (c >= 'A' && c <= 'F') return 10 + (c - 'A');
    if (c >= '0' && c <= '9') return c - '0';
    throw std::range_error(
    "hexadecimal chars must be in the range \"A\"-\"F\", \"a\"-\"f\" or \"0\"-\"9\"");
}

class Server
{
    public:
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

// helper class to help messuring times
// only used for debbuging, has no actual effect
class Timer
{
    private:
    std::string name;
    clock_t begin_all;
    std::unordered_map<std::string, clock_t> M;
    std::vector<std::string> stack;
    std::ostream& os;
    static int counter;

    public:
    Timer(const std::string& name, std::ostream& os) : begin_all(clock()), name(name), os(os)
    {
        begin("all");
    }

    Timer() : Timer("Timer #" + std::to_string(counter++), std::clog) {}

    void push(const std::string& s)
    {
        begin(s);
        stack.push_back(s);
    }

    void pop()
    {
        end(stack.back());
        stack.pop_back();
    }

    void begin(const std::string& s)
    {
        M[s] = clock();
        os << name << ": began " << s << std::endl;
    }

    void end(const std::string& s)
    {
        double secs = (clock() - M[s]) / CLOCKS_PER_SEC;
        os << name << ": finised " << s << ", took " << secs << " seconds" << std::endl;
        M.erase(s);
    }

    ~Timer()
    {
        end("all");
    }
};
int Timer::counter = 1;

class Intervals
{
    public:
    typedef std::pair<Integer, Integer> II;
    std::vector<II> arr;

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

    II& front()
    {
        return arr.front();
    }
    // returns the sum of sizes of intervals
    // i.e the number of elemnts that belungs to some interval
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

    void insert(const Integer& a, const Integer& b)
    {
        if (a > b) throw std::runtime_error("algorithmic impossibility");
        arr.push_back(std::make_pair(a, b));
    }
};

Integer div_ceil(const Integer& n, const Integer& m)
{
    Integer res = n / m;
    if (n % m == 0) return res;
    return res + 1;
}

Integer BleichenbacherAttack(Server& srv, const Integer& c, std::ostream& out)
{   
    static int count = 1;
    // begin attack
    Timer tick("Attack timer #" + std::to_string(count++), out);
    Integer n = srv.publicKey.GetModulus();

    CryptoPP::ModularArithmetic ma(n);
    Integer B = Integer::Power2(n.BitCount() - 16);
    Integer s;

    // the current range ogf intervals we search in
    Intervals M;
    M.insert(2 * B, 3 * B - 1);
    // the current interval size
    Integer size = M.size();
    // the best interval size so far
    Integer min_size = size;


    tick.push("step 2.a");
    s = div_ceil(n,3*B);
    while (s < n && !srv.isPkcsConforming(ma.Multiply(srv.publicKey.ApplyFunction(s), c)))
        s += 1;
    tick.pop();

    for (int i = 1; M.size() > 1; ++i)
    {
        if (i != 1 && M.count() > 1)
        {
            tick.push("step 2.b for i=" + std::to_string(i));
            s += 1;
            while (s < n && !srv.isPkcsConforming(ma.Multiply(srv.publicKey.ApplyFunction(s), c)))
                s += 1;
            tick.pop();
        }
        else if(i != 1)
        {
            tick.push("step 2.c for i=" + std::to_string(i));
            Integer a = M.front().first, b = M.front().second;
            bool stop_flag = false;
            for (Integer r = div_ceil(2 * b * s - 4 * B, n); !stop_flag; ++r)
            {
                Integer begin = div_ceil(2 * B + r * n, b), end = div_ceil(3 * B + r * n, a) - 1;
                for (Integer st = begin; !stop_flag && st <= end; ++st)
                {
                    if (srv.isPkcsConforming(ma.Multiply(srv.publicKey.ApplyFunction(st), c)))
                    {
                        stop_flag = true;
                        s = st;
                        break;
                    }
                }
            }
            tick.pop();
        }
        
        if (s <= 0 || s >= n) throw std::runtime_error("algorithmic impossibility");

        tick.push("step 3 for i=" + std::to_string(i));
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
        tick.pop();

        size = M.size();   
        if (size > min_size) throw std::runtime_error("algorithmic impossibility");
        min_size = std::min(min_size, size);
    }

    if (M.size() != 1) throw std::runtime_error("algorithmic impossibility");
    
    return M.front().first,;
}

int main(int argc, char* argv[])
{
    Server srv(2048);
    Integer c = srv.PkcsEncrypt("hello world! my name is ofer! this is my secret");
    Integer attack_res = BleichenbacherAttack(srv, c, std::cout);
    std::cout << PkcsDecode(attack_res,srv.keysize) << std::endl;

    return 0;
}