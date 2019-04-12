#include <cryptopp/integer.h>
#include <cryptopp/modarith.h>
#include <cryptopp/osrng.h>
#include <cryptopp/rsa.h>

#include <iomanip>
#include <iostream>
#include <set>
#include <sstream>
#include <unordered_map>
#include <vector>

using CryptoPP::Integer;

#define dout std::cout << "\tdebug: "

uint16_t hex2int(char c)
{
    if (c >= 'a' && c <= 'f') return 10 + (c - 'a');
    if (c >= 'A' && c <= 'F') return 10 + (c - 'A');
    if (c >= '0' && c <= '9') return c - '0';
    throw "wtf";
}


const int keysize = 256; // keysize is 3072 bits


class Server
{
    private:
    CryptoPP::RSA::PrivateKey privateKey;
    CryptoPP::AutoSeededRandomPool prng;

    public:
    CryptoPP::RSA::PublicKey publicKey;
    std::string PS;

    Server()
    {
        privateKey.GenerateRandomWithKeySize(prng, keysize * 8);
        publicKey = CryptoPP::RSA::PublicKey(privateKey);
    }

    bool isPkcsConforming(const Integer& c)
    {
        Integer m = privateKey.CalculateInverse(prng, c);

        std::stringstream _s;
        _s << std::hex << m;
        std::string s = _s.str();
        s.pop_back();

        if (s.length() < 21 || s.length() % 2 == 0) return false;
        if (s[0] != '2') return false;
        for (int i = 1; i < 2 * 8 + 1; i += 2)
            if (s[i] == '0' && s[i + 1] == '0') return false;
        for (int i = 2 * 8 + 1; i < s.length(); i += 2)
            if (s[i] == '0' && s[i + 1] == '0') return true;
        return false;
    }
};

Integer PkcsEncode(const std::string& s)
{
    int pad = keysize - 3 - s.length();
    if (pad < 8) throw "wtf";
    uint16_t rnd;

    std::stringstream ss;
    ss << "0x0002";
    for (int i = 0; i < pad; ++i)
    {
        do
        {
            rnd = random() % 256;
        } while (rnd == 0);
        if (rnd < 16) ss << "0";
        ss << std::hex << rnd;
    }
    ss << "00";

    for (uint16_t c : s)
    {
        if (c < 16) ss << "0";
        ss << std::hex << c;
    }

    return Integer(ss.str().c_str());
}

std::string PkcsDecode(const Integer& m)
{
    std::stringstream _s;
    std::string s;
    uint16_t c;

    _s << std::hex << m;
    s = _s.str();
    s.pop_back();
    if (s.length() <= 2 * 10 || s.length() % 2 == 0) throw "wtf";

    int begin = 1;
    while (begin < s.length() && (s[begin] != '0' || s[begin + 1] != '0'))
        begin += 2;
    if (begin >= s.length()) throw "wtf";

    std::string res((s.length() - begin) / 2, '0');
    for (int i = begin; i < s.length(); i += 2)
        res[(i - begin) / 2] = hex2int(s[i + 1]) + 16 * hex2int(s[i]);

    return res;
}

//helper class to help messuring times of the attack
//only used fo rdebbuging, has no actual effect
class Timer
{
    private:
    std::string name;
    clock_t begin_all;
    std::unordered_map<std::string, clock_t> M;
    std::vector<std::string> stack;
    std::ostream& os;

    public:
    Timer(const std::string& name, std::ostream& os) : begin_all(clock()), name(name), os(os)
    {
        begin("all");
    }

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

//helper class to help handling the concept of a set of disjoint intervals
class Intervals
{
    typedef std::pair<Integer, Integer> II;
    std::set<II> intervals;

    public:

    //returns the intervals themself (as a const set)
    const std::set<II>& get_intervals() const
    {
        return intervals;
    }
    //returns the sum of sizes of intervals
    //i.e the number of elemnts that belungs to some interval
    Integer size() const
    {
        Integer res = 0;
        for (const II& p : intervals)
            res += p.second - p.first + 1;
        return res;
    }

    //returns the number of disjoint intervals
    int count() const
    {
        return intervals.size();
    }

    //inserts an interval to the set
    void insert(II p)
    {
        auto it = intervals.begin();
        while (it != intervals.end())
        {
            bool not_intersacting = it->first > p.second || it->second < p.first;
            if (!not_intersacting)
            {
                p.first = std::min(p.first, it->first);
                p.second = std::max(p.second, it->second);
                intervals.erase(it);
            }
            else
            {
                it++;
            }
        }
        intervals.insert(p);
    }
};

template <typename T>
T div_ceil(const T& n, const T& m)
{
    T res = n / m;
    if (n % m == 0) return res;
    return res + 1;
}
int main(int argc, char* argv[])
{

    Server srv;
    Integer m_secret = PkcsEncode("hell0");
    Integer c0 = srv.publicKey.ApplyFunction(m_secret);

    // begin attack
    Timer tick("Attack timer", std::cout);
    Integer n = srv.publicKey.GetModulus();
    CryptoPP::ModularArithmetic ma(n);
    Integer B = Integer::Power2(8 * (keysize - 2));
    Intervals M;
    Integer s = -1;
    M.insert(std::make_pair(2 * B, 3 * B - 1));
    Integer last, sz;
    for (int i = 1; M.size() > 1; ++i)
    {
        if (i > 1)
        {
            sz = M.size();
            if (sz.BitCount() < 100) dout << "interval size: " << std::hex << sz << std::endl;
            dout << "size decreased? " << std::boolalpha << (sz < last) << std::endl;
            last = sz;
        }

        if (i == 1 || M.count() > 1)
        {
            if (i == 1)
                tick.push("step 2.a");
            else
                tick.push("step 2.b for i=" + std::to_string(i));

            s = (i == 1) ? div_ceil(n, 3 * B) : s + 1;
            while (!srv.isPkcsConforming(ma.Multiply(srv.publicKey.ApplyFunction(s), c0)))
                s += 1;

            tick.pop();
        }

        else
        {
            tick.push("step 2.c for i=" + std::to_string(i));
            Integer a = M.get_intervals().begin()->first, b = M.get_intervals().begin()->second;
            bool stop_flag = false;
            for (Integer r = div_ceil(2 * b * s - 4 * B, n); !stop_flag; ++r)
            {
                Integer begin = div_ceil(2 * B + r * n, b), end = div_ceil(3 * B + r * n, a) - 1;
                for (Integer st = begin; !stop_flag && st <= end; ++st)
                {
                    if (srv.isPkcsConforming(ma.Multiply(srv.publicKey.ApplyFunction(st), c0)))
                    {
                        stop_flag = true;
                        s = st;
                        break;
                    }
                }
            }
            tick.pop();
        }

        tick.push("step 3 for i=" + std::to_string(i));
        Intervals M_res;
        for (const auto& p : M.get_intervals())
        {
            Integer a = p.first, b = p.second;
            Integer begin = div_ceil(a * s - 3 * B + 1, n), end = (b * s - 2 * B) / n;
            for (Integer r = begin; r <= end; ++r)
                M_res.insert(std::make_pair(std::max(a, div_ceil(2 * B - r * n, s)),
                                            std::min(b, (3 * B - 1 + r * n) / s)));
        }
        M = M_res;
        tick.pop();
    }

    Integer m = M.get_intervals().begin()->first;
    std::string result = PkcsDecode(m);

    std::cout << result << std::endl;


    return 0;
}