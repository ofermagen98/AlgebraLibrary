#include <cryptopp/integer.h>
#include <cryptopp/modarith.h>
#include <cryptopp/osrng.h>
#include <cryptopp/rsa.h>

#include <chrono>
#include <exception>

#include <fstream>
#include <iostream>
#include <mutex>
#include <thread>
#include <vector>

#include "Fraction.h"
#include "matrix.h"
#include "vector.h"

using AlgebraTAU::Fraction;
using CryptoPP::Integer;
const int max_message_count = 1<<16;
typedef std::pair<Integer, Integer> II;

template <typename T>
inline T div_ceil(const T& x, const T& y)
{
    return ((x + y - 1) / y);
}

class Server
{
    //TODO change!
    private:
    CryptoPP::RSA::PrivateKey privateKey;

    public:
    std::ostream& print(std::ostream& os) const
    {
        os << std::hex << publicKey.GetModulus() << std::endl;
        os << std::hex << publicKey.GetPublicExponent() << std::endl;
        os << std::hex << privateKey.GetPrivateExponent() << std::endl;
        return os;
    }
    int keysize;

    public:
    CryptoPP::RSA::PublicKey publicKey;

    Server(std::istream& is)
    {
        Integer n, e, d, x;
        is >> n;
        is >> e;
        is >> d;

        CryptoPP::InvertibleRSAFunction params;
        params.Initialize(n, e, d);
        publicKey = CryptoPP::RSA::PublicKey(params);
        privateKey = CryptoPP::RSA::PrivateKey(params);
        keysize = n.BitCount();
    }

    Server(int keysize) : keysize(keysize)
    {
        CryptoPP::AutoSeededRandomPool prng;
        privateKey.GenerateRandomWithKeySize(prng, keysize);
        publicKey = CryptoPP::RSA::PublicKey(privateKey);
    }

    Server(const Server& srv)
    : privateKey(srv.privateKey), keysize(srv.keysize), publicKey(srv.publicKey)
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
    }

    std::ostream& debug(int t = 0)
    {
        for (int i = 0; i < t; ++i)
            os << "\t";
        return os << name << " debug: ";
    }
};

class Attacker
{
    std::string base_name;
    // static id counter for all attackers
    static int id;
    // static id counter mutex
    static std::mutex id_mutex;
    // limitat number of messages each attacker can send
    const int limitation = 200000;
    // counts the number of message this attacker sent
    int message_counter;
    const Server& srv;
    const Integer& c;

    protected:
    Logger clog;
    const Integer& n;
    const Integer B;

    inline bool is_good_pivot(const Integer& s)
    {
        ++message_counter;
        if (limitation > 0 && message_counter > limitation)
            throw std::runtime_error("message limitation was reached");
        return srv.is_pkcs_conforming(srv.publicKey.ApplyFunction(s).Times(c).Modulo(n));
    }

    public:
    Attacker(const Server& srv, const Integer& c, const std::string& base_name, int limitation = max_message_count)
    : base_name(base_name), limitation(limitation), srv(srv), c(c), clog(std::clog),
      n(srv.publicKey.GetModulus()), B(Integer::Power2(srv.publicKey.GetModulus().BitCount() - 16))
    {
    }

    int get_message_counter() const
    {
        return message_counter;
    }
    std::ostream& debug(int t = 0)
    {
        return clog.debug(t);
    }

    void reset()
    {
        std::lock_guard<std::mutex> lock(Attacker::id_mutex);
        clog.set_name(base_name + " (" + std::to_string(id++) + ")");
        message_counter = 0;
        debug() << "Beginning" << std::endl;
    }
};
int Attacker::id = 1;
std::mutex Attacker::id_mutex;

class BlindingAttacker : public Attacker
{
    public:
    BlindingAttacker(const Server& srv, const Integer& c)
    : Attacker(srv, c, "Blinding Attacker")
    {
    }
    Integer blind()
    {
        Integer s = 0;
        CryptoPP::AutoSeededRandomPool prng;
        do
        {
            s.Randomize(prng, 2, n / 2);
        } while (!is_good_pivot(s));
        return s;
    }
};

class RangeAttacker : public Attacker
{
    class Intervals
    {
        public:
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
    Integer s;

    public:
    RangeAttacker(const Server& srv, const Integer& c) : Attacker(srv, c, "Range Attacker")
    {
    }

    void attack()
    {
        M.insert(2 * B, 3 * B - 1);
        s = div_ceil(n, 3 * B);
        incremental_search(); // step 2.a
        debug() << "finished step 2.a" << std::endl;

        for (int i = 1; M.size() > 0; ++i)
        {
            if (i != 1 && M.count() > 1)
            {
                ++s;
                incremental_search();
                if (i % 100 == 0) debug() << "finished step 2.b for i=" << i << std::endl;
            }
            else if (i != 1 && M.count() == 1)
            {
                repivot();
                if (i % 100 == 0) debug() << "finished step 2.c for i=" << i << std::endl;
            }
            interval_divsion();
        }
    }

    II result()
    {
        return M.enclose();
    }

    // step 3
    void interval_divsion()
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
    void repivot()
    {
        const Integer& a = M.front().first;
        const Integer& b = M.front().second;
        for (Integer r = div_ceil(2 * b * s - 4 * B, n);; ++r)
            for (s = div_ceil(2 * B + r * n, b); s < div_ceil(3 * B + r * n, a); ++s)
                if (is_good_pivot(s)) return;
    }

    // step 2.a
    // step 2.b
    void incremental_search()
    {
        while (!is_good_pivot(s))
        {
            ++s;
        }
    }
};

class MultiThreadAttack
{

    private:
    std::ostream& os;
    std::mutex os_mutex;

    const Server& srv;
    const Integer& c;
    const int thread_num;
    int number_of_blindings;

    std::atomic_int32_t blindings_calced;
    std::mutex blindings_mutex;

    std::atomic_int32_t ranges_calced;
    std::mutex ranges_mutex;

    std::vector<Integer> blindings;

    public:
    MultiThreadAttack(const Server& srv,
                      const Integer& c,
                      int number_of_blindings,
                      std::ostream& os,
                      int thread_num = std::thread::hardware_concurrency())
    : os(os), srv(srv), c(c), thread_num(std::max(1,thread_num)), number_of_blindings(number_of_blindings)
        ,blindings(number_of_blindings)
    {
    }

    private:
    void blinding_thread()
    {
        BlindingAttacker attacker(srv, c);
        Integer blind_value;

        while (blindings_calced < number_of_blindings)
        {
            attacker.reset();
            try
            {
                blind_value = attacker.blind();
                {
                    std::lock_guard<std::mutex> lock(blindings_mutex);
                    if (blindings_calced >= number_of_blindings) break;
                    ++blindings_calced;
                }
                {
                    std::lock_guard<std::mutex> os_mutex(blindings_mutex);
                    attacker.debug() << "Found blinding value!" << std::endl;
                    os << blind_value << std::endl;
                    std::clog << "Number of blindings found " << blindings_calced << std::endl;
                }
            }
            catch (std::exception& e)
            {
                attacker.debug() << "Killed before blinding value found" << std::endl;
            }
        }
    }

    void range_thread()
    {
        int i;
        Integer c0;
        while (ranges_calced < number_of_blindings)
        {
            {
                std::lock_guard<std::mutex> lock(ranges_mutex);
                i = ranges_calced++;
                if (i >= number_of_blindings) break;
            }

            c0 = srv.publicKey.ApplyFunction(blindings[i]).Times(c).Modulo(srv.publicKey.GetModulus());
            RangeAttacker attacker(srv, c0);

            try
            {
                attacker.reset();
                attacker.attack();
                attacker.debug() << "Found final value!" << std::endl;
                os << attacker.result().first << std::endl;
                exit(1);
            }
            catch (std::exception& e)
            {
                attacker.debug() << "Killed before final value found" << std::endl;
            }

            {
                std::lock_guard<std::mutex> lock(os_mutex);
                os << i << std::endl;
                os << attacker.result().first << std::endl;
            }
        }
    }

    public:
    void calc_blindings(int begin)
    {
        if (blindings.size() != number_of_blindings)
            throw std::runtime_error("invalid number of blindings");
        blindings_calced = begin;
        std::vector<std::thread> threads;
        for (int i = 1; i < thread_num; ++i)
            threads.push_back(std::thread([this]() { this->blinding_thread(); }));
        blinding_thread();

        for (auto& t : threads)
            if (t.joinable()) t.join();
    }

    void calc_ranges(int begin)
    {
        ranges_calced = begin;
        std::vector<std::thread> threads;
        for (int i = 1; i < thread_num; ++i)
            threads.push_back(std::thread([this]() { this->range_thread(); }));
        range_thread();
        for (auto& t : threads)
            if (t.joinable()) t.join();
    }

    void set_blinding(int i, const Integer& x)
    {
        blindings[i] = x;
    }
};

std::string lap(const std::chrono::steady_clock::time_point& begin)
{
    using std::to_string;
    using std::chrono::steady_clock;

    int seconds =
    ((steady_clock::now() - begin).count() * steady_clock::period::num) / steady_clock::period::den;
    int hours = seconds / 3600;
    int minutes = (seconds % 3600) / 60;
    seconds %= 60;
    return to_string(hours) + "h" + to_string(minutes) + "m" + to_string(seconds) + "s";
}

class AttackHandler
{
    const int keysize;
    std::string params_file, blinding_file, ranges_file;


    int number_of_blindings()
    {
        return div_ceil(keysize, 8);
    }

    std::string pkcs_decode(const Integer& m) const
    {
        int sz = m.ByteCount();
        if (sz * 8 != keysize - 8) throw std::invalid_argument("invalid message length");
        if (m.GetByte(sz - 1) != 2) throw std::invalid_argument("invalid message padding");
        for (int i = sz - 2; i > sz - 10; --i)
            if (m.GetByte(i) == 0) throw std::invalid_argument("invalid message padding");

        std::vector<char> res;

        int i;
        for (i = m.ByteCount() - 2; i >= 0 && m.GetByte(i) != 0; --i)
            ;
        if (i < 0) throw std::invalid_argument("empty message");
        --i;

        for (; i >= 0; --i)
            res.push_back(m.GetByte(i));
        res.push_back(0);
        return res.data();
    }

    void generate_params(const std::string& message, int keysize)
    {
        std::ifstream is(params_file);
        if (is.good()) return;
        std::ofstream out(params_file);
        Server srv(keysize);
        Integer c = srv.pkcs_encrypt(message);
        srv.print(out) << c << std::endl;
    }

    std::string calc_result()
    {
        std::ifstream srv_is(params_file);
        std::ifstream blindings(blinding_file);
        std::ifstream ranges(ranges_file);

        //recovering the calculated data
        Server srv(srv_is);
        Integer N, c, x;
        srv_is >> c;
        CryptoPP::AutoSeededRandomPool prng;
        int k = number_of_blindings();
        N = srv.publicKey.GetModulus();
        std::vector<Integer> s(k),a(k);
        int t;
        for (int i = 0; i < k; ++i){
            blindings >> s[i];
            ranges >> t;
            ranges >> a[t];
        }

        //constructing the lattice matrix
        AlgebraTAU::matrix<Integer> M(k + 1, k + 1);
        for (int i = 0; i < k; ++i)
        {
            M(i + 1, i) = N;
            M(0, i) = s[i];
            M(k, i) = a[i];
        }
        M *= k;
        M(k, k) = N * (k - 1);
        M = M.transpose();
        
        //preforming the LLL reduction
        AlgebraTAU::integral_LLL(M);
        
        //finding the shortest vector
        std::vector<Integer> norms(k+1);
        for(int i = 0; i < k+1; ++i) norms[i] = M.get_column(i).norm();
        std::vector<int> sorted(k+1);
        for(int i = 0; i < k+1; ++i) sorted[i] = i;
        std::sort(sorted.begin(),sorted.end(),[&norms](int i , int j){ return norms[i] < norms[j]; });
        auto R = M.get_column(sorted[0]).transpose();

        //Recovering the message
        CryptoPP::ModularArithmetic ma(N);
        x = (R(0) / k) % N;
        Integer pred = ma.MultiplicativeInverse(s[0]);
        pred = ma.Multiply(pred,x);
        return pkcs_decode(pred);
    }

    void find_ranges()
    {
        std::ifstream srv_is(params_file);
        std::ifstream blindings(blinding_file);
        std::ofstream ranges(ranges_file, std::ios_base::app);
        Server srv(srv_is);
        Integer c;
        srv_is >> c;
        int calced = num_of_lines(ranges_file);
        if (calced >= number_of_blindings()) return;

        // logging attack beggining
        std::clog << "Main debug (ranging): ";
        std::clog << "keysize=" << keysize;
        std::clog << ", attacker will be killed after " << max_message_count << " messages" << std::endl;

        MultiThreadAttack MTA(srv, c, number_of_blindings(), ranges);
        Integer x;
        for (int i = 0; i < number_of_blindings(); ++i)
        {
            blindings >> x;
            MTA.set_blinding(i,x);
        }
        MTA.calc_ranges(calced);
    }

    void find_blindings()
    {
        // setting up server to be attacked
        std::ifstream params(params_file.c_str());
        std::ofstream blindings(blinding_file.c_str(), std::ios_base::app);
        Server srv(params);
        const int calced = num_of_lines(blinding_file);
        Integer c;
        params >> c;
        if (calced >= number_of_blindings()) return;

        // logging attack beggining
        std::clog << "Main debug (blinding): ";
        std::clog << "keysize=" << keysize;
        std::clog << ", attacker will be killed after " << max_message_count << " messages" << std::endl;

        // begining attack
        auto begin_time = std::chrono::steady_clock::now();
        MultiThreadAttack MTA(srv, c, number_of_blindings(), blindings);
        MTA.calc_blindings(calced);
        std::clog << "Main debug: running time " << lap(begin_time) << std::endl;
    }

    static bool file_exists(const std::string& path)
    {
        std::ifstream f(path.c_str());
        return f.good();
    }

    static int num_of_lines(const std::string& filename)
    {
        std::ifstream is(filename.c_str());
        int count = 0;
        std::string s;
        while (std::getline(is, s))
            ++count;
        return count;
    }

    public:
    AttackHandler(int keysize, const std::string& params_file, const std::string& blinding_file, const std::string& ranges_file)
    : keysize(keysize), params_file(params_file), blinding_file(blinding_file), ranges_file(ranges_file)
    {
        if (!file_exists(params_file)) generate_params("hello my name is ofer", keysize);
    }

    void run()
    {
        find_blindings();
        find_ranges();
        calc_result();
    }
};

int main(int argc, char const* argv[])
{
    if(argc == 3){
        int keysize = std::stoi(std::string(argv[1]));
        std::string dir = argv[2];
        dir += "/";
        //auto clogbuf = std::clog.rdbuf();
        std::ifstream log_file(dir+"log.txt",std::ios_base::app);
        std::clog.rdbuf(log_file.rdbuf());
        AttackHandler hndl(keysize,dir+"args.txt",dir+"blidings.txt",dir+"ranges.txt");
        hndl.run();
    }
    
    return 0;
}
