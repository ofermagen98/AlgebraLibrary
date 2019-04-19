#include <cryptopp/integer.h>
#include <cryptopp/modarith.h>
#include <cryptopp/osrng.h>
#include <cryptopp/rsa.h>
using CryptoPP::Integer;

#include <fstream>
#include <iostream>

#include <exception>

#include <unordered_map>
#include <vector>

#include <ctime>
#include <mutex>
#include <thread>
using std::chrono::steady_clock;

class Server
{
    private:
    CryptoPP::RSA::PrivateKey privateKey;

    public:
    int keysize;
    CryptoPP::RSA::PublicKey publicKey;

    Server(int keysize) : keysize(keysize)
    {
        CryptoPP::AutoSeededRandomPool prng;
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

    bool is_pkcs_conforming(const Integer& c) const
    {
        CryptoPP::AutoSeededRandomPool prng;
        Integer m = privateKey.CalculateInverse(prng, c);
        int sz = m.ByteCount();
        if (sz * 8 != keysize - 8) return false;
        if (m.GetByte(sz - 1) != 2) return false;
        for (int i = sz - 2; i > sz - 10; --i)
            if (m.GetByte(i) == 0) return false;
        for (int i = sz - 10; i >= 0; --i)
            if (m.GetByte(i) == 0) return true;
        return false;
    }

    Integer pkcs_encrypt(const std::string& s) const
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
class Logger
{
    std::string name = "";
    std::ostream& os;

    public:
    Logger(std::ostream& os) : os(os)
    {
    }

    void set_name(const std::string& s)
    {
        name = s;
        os << "Begining \"" << name << "\"" << std::endl;
    }

    std::ostream& debug(int t = 0)
    {
        for (int i = 0; i < t; ++i)
            os << "\t";
        return os << name << " debug: ";
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


class Attacker
{

    // static id counter for all attackers
    static int id;
    static std::mutex id_mutex;
    // limitat number of messages each attacker can send
    const static int limitation = 20000;
    // counts the number of message this attacker sent
    int message_counter;
    const Server& srv;
    const Integer& c;
    const std::atomic_bool* const pkill;
    std::string name;

    protected:
    Logger clog;
    const Integer n, B;

    inline bool is_good_pivot(const Integer& s)
    {
        ++message_counter;
        if (message_counter > limitation)
            throw std::runtime_error("message limitation was reached");
        return srv.is_pkcs_conforming(srv.publicKey.ApplyFunction(s).Times(c).Modulo(srv.publicKey.GetModulus()));
    }

    inline bool not_killed() const
    {
        return pkill == nullptr || !*pkill;
    }

    public:
    Attacker(const Server& srv, const Integer& c, const std::string& name, const std::atomic_bool* pkill)
    : pkill(pkill), clog(std::clog), srv(srv), n(srv.publicKey.GetModulus()),
      B(Integer::Power2(n.BitCount() - 16)), c(c), name(name)
    {
    }

    std::ostream& debug(int t = 0)
    {
        return clog.debug(t);
    }

    void reset()
    {
        std::lock_guard<std::mutex> lock(Attacker::id_mutex);
        clog.set_name(name + " (" + std::to_string(id++) + ")");
        message_counter = 0;
    }
};
int Attacker::id = 1;
std::mutex Attacker::id_mutex;


class BleichenbacherAttacker : public Attacker
{
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

        const II& front() const
        {
            return arr.front();
        }

        II enclose() const
        {
            II res = front();
            for (const II& p : arr)
            {
                if (p.first < res.first) res.first = p.first;
                if (p.second > res.second) res.second = p.second;
            }
            return res;
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
            arr.push_back(std::make_pair(std::move(a), std::move(b)));
        }
    };

    Intervals M;

    BleichenbacherAttacker(const Server& srv, const Integer& c, std::atomic_bool* pkill = nullptr)
    : Attacker(srv, c, "Bleichenbacher Attacker", pkill)
    {
        M.insert(2 * B, 3 * B - 1);
    }

    // step 3
    void interval_divsion(const Integer& s)
    {
        Intervals res;
        for (const auto& p : M.arr)
        {
            const Integer& a = p.first;
            const Integer& b = p.second;
            Integer begin = div_ceil(a * s - 3 * B + 1, n), end = (b * s - 2 * B) / n;
            for (Integer r = begin; r <= end; ++r)
            {
                Integer na = std::max(a, div_ceil(2 * B + r * n, s)),
                        nb = std::min(b, (3 * B - 1 + r * n) / s);
                res.insert(std::move(na), std::move(nb));
            }
        }
        res.sort();
        M = res;
    }

    // step 2.c
    void repivot(Integer& s, const Intervals::II& range)
    {
        const Integer& a = range.first;
        const Integer& b = range.second;
        for (Integer r = div_ceil(2 * b * s - 4 * B, n);; ++r)
            for (s = div_ceil(2 * B + r * n, b); s < div_ceil(3 * B + r * n, a); ++s)
                if (is_good_pivot(s)) return;
    }

    // step 2.a
    // step 2.b
    void incremental_search(Integer& s)
    {
        while (!is_good_pivot(s))
        {
            ++s;
        }
    }
};

class BlindingAttacker : public Attacker
{

    public:
    BlindingAttacker(const Server& srv, const Integer& c, const std::atomic_bool* pkill = nullptr)
    : Attacker(srv, c, "Blinding Attacker", pkill)
    {
    }

    Integer blind()
    {
        Integer s = 0;
        CryptoPP::AutoSeededRandomPool prng;
        do
        {
            s.Randomize(prng, 2, n - 1);
        } while (!is_good_pivot(s) && not_killed());
        return s;
    }
};

std::vector<Integer> res_vector;
std::atomic_bool thread_kill_flag;
std::mutex res_vector_mutex;
const int blindings_num = 5;
void blinding_thread(const Server* srv, const Integer* c)
{
    BlindingAttacker attacker(*srv, *c, &thread_kill_flag);
    Integer blind_value;

    while (!thread_kill_flag)
    {
        attacker.reset();
        try
        {
            blind_value = attacker.blind();
            if (thread_kill_flag) break;
            attacker.debug(1) << "found blinding value!" << std::endl;
            {
                std::lock_guard<std::mutex> lock(res_vector_mutex);
                res_vector.push_back(blind_value);
                std::clog << "Number of blindings found " << res_vector.size() << std::endl;
                if (res_vector.size() >= blindings_num) thread_kill_flag = true;
            }
        }
        catch (std::exception& e)
        {
            attacker.debug(1) << "was killed before it found blinding value" << std::endl;
        }
    }
}

int main(int argc, char* argv[])
{
    Server srv(2048);
    Integer c = srv.pkcs_encrypt("He11o w0r1d! My n4me is 0fer! This is my secret");
    thread_kill_flag = false;
    std::vector<std::thread> v;
    for (int i = 0; i < 3; ++i)
        v.push_back(std::move(std::thread(blinding_thread, &srv, &c)));
    blinding_thread(&srv, &c);
    for (auto& t : v)
        if (t.joinable()) t.join();
    return 0;
}