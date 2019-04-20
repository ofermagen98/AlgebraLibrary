#include <cryptopp/integer.h>
#include <cryptopp/modarith.h>
#include <cryptopp/osrng.h>
#include <cryptopp/rsa.h>
using CryptoPP::Integer;

#include <exception>
#include <iostream>
#include <fstream>
#include <mutex>
#include <thread>
#include <chrono>
#include <vector>

const int max_message_count = 5000;

typedef std::pair<Integer, Integer> II;

inline Integer div_ceil(const Integer& x, const Integer& y)
{
    return ((x + y - 1) / y);
}

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
    : limitation(limitation), clog(std::clog), srv(srv), n(srv.publicKey.GetModulus()),
      B(Integer::Power2(srv.publicKey.GetModulus().BitCount() - 16)), c(c), base_name(base_name)
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

    std::string pkcs_decode(const Integer& m)
    {
        if (m.BitCount() != n.BitCount() - 14) throw std::invalid_argument("invalid message length");
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
};
int Attacker::id = 1;
std::mutex Attacker::id_mutex;

class BlindingAttacker : public Attacker
{
    const std::atomic_bool* pkill;

    public:
    BlindingAttacker(const Server& srv, const Integer& c, const std::atomic_bool* pkill = nullptr)
    : Attacker(srv, c, "Blinding Attacker"), pkill(pkill)
    {
    }

    inline bool not_killed() const
    {
        return (pkill == nullptr || !*pkill);
    }

    Integer blind()
    {
        Integer s = 0;
        CryptoPP::AutoSeededRandomPool prng;
        do
        {
            s.Randomize(prng, 2, n / 2);
        } while (!is_good_pivot(s) && not_killed());
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

    void attack() {
        M.insert(2 * B, 3 * B - 1);
        s = div_ceil(n,3*B);
        incremental_search(); //step 2.a
        debug() << "finished step 2.a" << std::endl;

        for(int i = 1; M.size() > 0; ++i){
            if(i != 1 && M.count() > 1){
                ++s;
                incremental_search();
                if(i % 100 == 0) debug() << "finished step 2.b for i=" << i << std::endl;
            }
            else if (i != 1 && M.count() == 1){
                repivot();
                if(i % 100 == 0) debug() << "finished step 2.c for i=" << i << std::endl;
            }
            interval_divsion();
        }

    }
    
    II result(){
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

    public:
    static MultiThreadAttack& get_instance()
    {
        static MultiThreadAttack instance;
        return instance;
    }
    
    private:
    // singelton design pattern
    MultiThreadAttack()
    {
    }

    MultiThreadAttack(MultiThreadAttack const&) = delete;
    void operator=(MultiThreadAttack const&) = delete;

    private:
    const Server* srv;
    const Integer* c;

    const int thread_num = std::max(int(std::thread::hardware_concurrency()),1);
    
    int number_of_blindings;

    std::atomic_bool finish_blinding;
    std::mutex blindings_mutex;
    std::vector<Integer> blindings;
    
    int current_range;
    std::vector<II> ranges;
    std::mutex current_range_mutex;

    static void blinding_thread()
    {
        MultiThreadAttack& MTA = get_instance();
        BlindingAttacker attacker(*MTA.srv, *MTA.c, &MTA.finish_blinding);
        Integer blind_value;

        while (!MTA.finish_blinding)
        {
            attacker.reset();
            try
            {
                blind_value = attacker.blind();
                if (MTA.finish_blinding) break;
                attacker.debug() << "Found blinding value!" << std::endl;
                {
                    std::lock_guard<std::mutex> lock(MTA.blindings_mutex);
                    MTA.blindings.push_back(blind_value);
                    std::clog << "Number of blindings found " << MTA.blindings.size() << std::endl;
                    if (MTA.blindings.size() >= MTA.number_of_blindings) MTA.finish_blinding = true;
                }
            }
            catch (std::exception& e)
            {
                attacker.debug() << "Killed before blinding value found" << std::endl;
            }
        }
    }

    static void range_thread()
    {
        MultiThreadAttack& MTA = get_instance();
        int i;
        Integer c0;
        while (true)
        {
            {
                std::lock_guard<std::mutex> lock(MTA.current_range_mutex);
                i = MTA.current_range++;
            }
            if(i >= MTA.number_of_blindings) break;
            
            c0 = MTA.srv->publicKey.ApplyFunction(MTA.blindings[i]).Times(*MTA.c).Modulo(MTA.srv->publicKey.GetModulus());
            RangeAttacker attacker(*MTA.srv, c0);
            
            try
            {
                attacker.reset();
                attacker.attack();
                attacker.debug() << "Found final value!" << std::endl; 
            }
            catch (std::exception& e)
            {
                attacker.debug() << "Killed before final value found" << std::endl;
            }
            MTA.ranges[i] = attacker.result();
        }
    }

    public:

    void set_params(const Server& srv, const Integer& c,int number_of_blindings){
        this->srv = &srv;
        this->c = &c;
        this->number_of_blindings = number_of_blindings;
        blindings.clear();
        finish_blinding = false;
        current_range_idx = 0;
        ranges = std::vector<II>(number_of_blindings);
    }

    void get_blindings()
    {
        std::vector<std::thread> threads;
        for (int i = 1; i < thread_num; ++i)
            threads.push_back(std::move(std::thread(blinding_thread)));
        blinding_thread();
        
        for (auto& t : threads)
            if (t.joinable())
                t.join();
        finish_blinding = true;
    }

    void get_ranges(){
        std::vector<std::thread> threads;
        for (int i = 1; i < thread_num; ++i)
            threads.push_back(std::move(std::thread(range_thread)));
        range_thread();

        for (auto& t : threads)
            if (t.joinable())
                t.join();
        current_range_idx = ranges.size();
    }
};

std::string lap(const std::chrono::steady_clock::time_point& begin)
{
    using std::chrono::steady_clock;
    using std::to_string;

    int seconds = ((steady_clock::now()-begin).count() * steady_clock::period::num) / steady_clock::period::den;
    int hours = seconds / 3600;
    int minutes = (seconds % 3600) / 60;
    seconds %= 60;
    return to_string(hours) + "h" + to_string(minutes) + "m" + to_string(seconds) + "s";
}

int main(int argc, char* argv[])
{
    
    std::ofstream out("log1.txt");
    std::streambuf *coutbuf = std::clog.rdbuf(); //save old buf
    std::clog.rdbuf(out.rdbuf()); //redirect std::clog to log.txt

    Server srv(2048);
    Integer c = srv.pkcs_encrypt("He11o w0r1d! My n4me is 0fer! This is my secret");
    
    std::clog << "Main debug: ";
    std::clog << "keysize=" << srv.publicKey.GetModulus().BitCount();
    std::clog << ", attacker killed after " << max_message_count << " messages" << std::endl;



    auto begin_time = std::chrono::steady_clock::now();

    auto& MTA = MultiThreadAttack::get_instance();
    MTA.set_params(srv,c,50);
    MTA.get_blindings();
    MTA.get_ranges();

    std::clog << "Main debug: running time " << lap(begin_time) << std::endl;

    return 0;
}