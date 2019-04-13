#include <cryptopp/integer.h>
#include <cryptopp/modarith.h>
#include <cryptopp/osrng.h>
#include <cryptopp/rsa.h>

#include <exception>
#include <fstream>
#include <sstream>

#include <iomanip>
#include <iostream>
#include <mutex>
#include <thread>
#include <unordered_map>
#include <vector>

using CryptoPP::Integer;

class Server
{
    private:
    CryptoPP::RSA::PrivateKey privateKey;
    CryptoPP::AutoSeededRandomPool prng;

    public:
    int keysize;
    CryptoPP::RSA::PublicKey publicKey;

    Server(int keysize) : keysize(keysize)
    {
        privateKey.GenerateRandomWithKeySize(prng, keysize);
        publicKey = CryptoPP::RSA::PublicKey(privateKey);
    }

    Server(const Server& srv)
    : publicKey(srv.publicKey), privateKey(srv.privateKey), keysize(srv.keysize)
    {
    }

    Server& operator=(const Server& srv)
    {
        publicKey = srv.publicKey;
        privateKey = srv.privateKey;
        keysize = srv.keysize;
        return *this;
    }

    bool is_pkcs_conforming(const Integer& c)
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

    Integer pkcs_encrypt(const std::string& s)
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
class Timer
{
    private:
    std::string name;
    static int counter;
    const clock_t begin_all;


    std::unordered_map<std::string, clock_t> M;
    std::vector<std::string> stack;
    std::ostream& os;

    public:
    Timer(const std::string& name, std::ostream& os) : begin_all(clock()), name(name), os(os)
    {
        os << "Begining \"" << name << "\"" << std::endl;
    }

    Timer() : Timer("Timer #" + std::to_string(counter++), std::clog)
    {
    }

    void push(const std::string& s, bool force_print = false)
    {
        begin(s, force_print);
        stack.push_back(s);
    }

    void pop()
    {
        end(stack.back());
        stack.pop_back();
    }

    void begin(const std::string& s, bool force_print = false)
    {
        M[s] = clock();
        if (force_print) os << name << ": began " << s << std::endl;
    }

    void end(const std::string& s)
    {
        double secs = double(clock() - M[s]) / CLOCKS_PER_SEC;
        if (secs > 6e-2)
            os << name << ": finised " << s << ", took " << secs << " seconds" << std::endl;
        M.erase(s);
    }

    ~Timer()
    {
        double secs = double(clock() - begin_all) / CLOCKS_PER_SEC;
        os << "\"" << name << "\" finished, took " << secs << " seconds" << std::endl;
    }
};
int Timer::counter = 1;

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

std::string pkcs_decode(const Integer& m, int keysize)
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

namespace parallel_search
{
Integer s;
std::mutex lock, glb_lock;
bool run_flag;
const int THREAD_NUM = 4;

void thread_search(Server srv, Integer c, Integer begin, int offset)
{
    Integer n = srv.publicKey.GetModulus();
    CryptoPP::ModularArithmetic modN = n;
    for (Integer i = begin; parallel_search::run_flag && i < n; i += offset)
    {
        if (srv.is_pkcs_conforming(modN.Multiply(srv.publicKey.ApplyFunction(i), c)))
        {
            parallel_search::lock.lock();
            if (parallel_search::run_flag)
            {
                parallel_search::s = i;
                parallel_search::run_flag = false;
            }
            parallel_search::lock.unlock();
        }
    }
}

Integer parallel_search(const Server& srv, const Integer& c, const Integer& begin, int threadnum = parallel_search::THREAD_NUM)
{
    parallel_search::glb_lock.lock();
    parallel_search::run_flag = true;
    std::vector<std::thread> run_threads;


    for (int i = 1; i < threadnum; ++i)
        run_threads.push_back(std::thread(thread_search, srv, c, begin + i, threadnum));
    thread_search(srv, c, begin, threadnum);

    for (std::thread& th : run_threads)
        if (th.joinable()) th.join();

    Integer res = parallel_search::s;
    parallel_search::glb_lock.unlock();
    return res;
}
} // namespace parallel_search


Integer bleichenbacher_attack(Server& srv, const Integer& c)
{
    static int attack_count = 1;
    Timer tick("Attack timer #" + std::to_string(attack_count++), std::clog);

    int keysize = srv.publicKey.GetModulus().BitCount();
    // basic variables
    Integer n = srv.publicKey.GetModulus();
    CryptoPP::ModularArithmetic modN = n;
    Integer B = Integer::Power2(keysize - 16);
    Integer s;
    // the current range of intervals we search in
    Intervals M;

    // algorithm
    // step 1 is skipped (since c is PCKS#1 conforming)
    M.insert(2 * B, 3 * B - 1);

    // step 2.a
    tick.push("step 2.a", true);
    s = parallel_search::parallel_search(srv, c, div_ceil(n, 3 * B));
    tick.pop();

    for (int i = 1; M.size() > 1; ++i)
    {
        // step 2.b
        if (i != 1 && M.count() > 1)
        {
            tick.push("step 2.b for i=" + std::to_string(i), true);
            s = parallel_search::parallel_search(srv, c, s + 1);
            tick.pop();
        }

        // step 2.c
        else if (i != 1)
        {
            tick.push("step 2.c for i=" + std::to_string(i));
            Integer a = M.front().first, b = M.front().second;
            bool stop_flag = false;
            for (Integer r = div_ceil(2 * b * s - 4 * B, n); !stop_flag; ++r)
            {
                Integer begin = div_ceil(2 * B + r * n, b), end = div_ceil(3 * B + r * n, a) - 1;
                for (Integer st = begin; !stop_flag && st <= end; ++st)
                {
                    if (srv.is_pkcs_conforming(modN.Multiply(srv.publicKey.ApplyFunction(st), c)))
                    {
                        stop_flag = true;
                        s = st;
                        break;
                    }
                }
            }
            tick.pop();
        }

        // step 3
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
    }

    if (M.size() != 1) throw std::runtime_error("algorithmic impossibility");
    return M.front().first;
}


int main(int argc, char* argv[])
{
    int keysize = rand() % (512 - 128) + 128;
    keysize *= 8;
    Server srv(keysize);

    Integer c = srv.pkcs_encrypt("hello world! my name is ofer! this is my secret");
    Integer res = bleichenbacher_attack(srv, c);
    std::string message = pkcs_decode(res, srv.keysize);

    std::cout << message << std::endl;


    return 0;
}