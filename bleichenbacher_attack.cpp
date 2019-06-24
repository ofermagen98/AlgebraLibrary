#include <cryptopp/integer.h>
#include <cryptopp/modarith.h>
#include <cryptopp/osrng.h>
#include <cryptopp/rsa.h>

#include <chrono>
#include <exception>

#include <fstream>
#include <iostream>
#include <vector>

#include "Fraction.h"
#include "matrix.h"
#include "vector.h"

using AlgebraTAU::Fraction;
using CryptoPP::Integer;
const int max_message_count = 560;
typedef std::pair<Integer, Integer> II;

template <typename T>
inline T div_ceil(const T& x, const T& y)
{
    return ((x + y - 1) / y);
}

class Server
{
    //TODO change!
    public:
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

    bool MA(const Integer& c) const
    {
        CryptoPP::AutoSeededRandomPool prng;
        Integer m = privateKey.CalculateInverse(prng, c);
        return m.BitCount() <= keysize - 8;
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
    const std::string base_name;
    // static id counter for all attackers
    static int id;
    // limitat number of messages each attacker can send
    const int limitation = 200000;
    // counts the number of message this attacker sent
    int message_counter;
    const Server& srv;
    const Integer B;
    Integer c;
    Integer s0;

    Logger clog;
    II range;

    const Integer& N() const {
        return srv.publicKey.GetModulus();
    };


    void intersect(const Integer& a, const Integer& b){
        range.first = std::max(range.first, a);
        range.second = std::min(range.second, b);
    }

    void reset()
    {
        range = std::make_pair(0,B);
        clog.set_name(base_name + " (" + std::to_string(++id) + ")");
        message_counter = 0;
        debug() << "Beginning" << std::endl;
    }

    inline bool is_good_pivot(const Integer& s)
    {
        ++message_counter;
        if (limitation > 0 && message_counter > limitation)
            throw std::runtime_error("message limitation was reached");
        return srv.MA(srv.publicKey.ApplyFunction(s).Times(c).Modulo(N()));
    }

    void blind(){
        CryptoPP::AutoSeededRandomPool prng;
        do{
            s0.Randomize(prng,0,N());
        }while (!is_good_pivot(s0));
        c *= srv.publicKey.ApplyFunction(s0);
        c %= N();
    }

    public:
    Attacker(const Server& srv, const Integer& c, int limitation = max_message_count)
    : base_name("Manger Attacker"), limitation(limitation), srv(srv), 
    B(Integer::Power2(srv.publicKey.GetModulus().BitCount() - 8)), 
    c(c), clog(std::clog)
    {
        reset();
    }

    const II& get_range() const  {
        return range;
    }

    const Integer& get_blinding() const {
        return s0;
    }

    Integer size() const {
        return range.second - range.first;
    }
    
    void run(){
        blind();
        debug() << "finished blinding" << std::endl;

        Integer f1 = 2;
        while (is_good_pivot(f1)){
            intersect(0, B / f1);
            f1 <<= 1;
        }
        f1 >>= 1;

        intersect(B/(2*f1), B / f1);
        debug() << "finished step 1" << std::endl;

        Integer f2 = div_ceil(N()+B,B) * f1;
        intersect(N()/(2*f2),(N() + B) / f2);
        while (!is_good_pivot(f2))
        {
            f2 += f1;
            intersect(N()/(2*f2),(N() + B) / f2);
        }
        range = std::make_pair(div_ceil(N(),f2),(N() + B) / f2);
        debug() << "finished step 2" << std::endl;

        Integer i,f3;
        while(size() > 0){
            i = (2*B) / size();
            i = (i*range.first) / N();
            f3 = div_ceil(i*N() , range.first);

            if(is_good_pivot(f3))
                range.second = (i*N() + B) / f3;
            else
                range.first = div_ceil(i*N() + B, f3);
        }
    }

    int get_message_counter() const
    {
        return message_counter;
    }

    std::ostream& debug(int t = 0)
    {
        return clog.debug(t);
    }
};
int Attacker::id = 0;


std::string pkcs_decode(const Integer& m, int keysize)
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


int main(int argc, char const* argv[])
{
    const int keysize = 2048;
    Server srv(keysize);
    Integer c = srv.pkcs_encrypt("hello!");
    const Integer& N = srv.publicKey.GetModulus();

    CryptoPP::AutoSeededRandomPool prng;
    Integer m = srv.privateKey.CalculateInverse(prng, c);

    int n = 8;
    std::vector<Integer> s(n),a(n),b(n);
    int bits_learned = 0;
    for(int i = 0; i < n; ++i){
        Attacker attack(srv,c);
        try{
            attack.run();
        }catch(...){}

        bits_learned += keysize - attack.size().BitCount() - 1;
        a[i] = attack.get_range().first;
        b[i] = attack.get_range().second;
        s[i] = attack.get_blinding();
    }

    std::clog << "Learned: " << bits_learned << " bits of information" << std::endl;

    AlgebraTAU::matrix<Integer> M(n+2,n+2,0);
    for(int i = 0; i < n; ++i){
        M(0,i) = s[i];
        M(i+1,i) = N;
        M(n+1,i) = a[i];
        M(i,n+1) = 0;
    }
    M *= n;
    M(n+1,n) = N * (n-1);
    M = M.transpose();

    std::cout << M(n-1,n) << std::endl;
    AlgebraTAU::integral_LLL(M);
    
    return 0;
}
