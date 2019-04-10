#include <cryptopp/cryptlib.h>
#include <cryptopp/integer.h>
#include <cryptopp/modarith.h>
#include <cryptopp/osrng.h>
#include <cryptopp/rng.h>
#include <cryptopp/rsa.h>
using namespace CryptoPP;

#include <iomanip>
#include <iostream>
using namespace std;

class Server
{
    private:
    RSA::PrivateKey privateKey;

    public:
    int k = 384;
    RSA::PublicKey publicKey;

    Server(RandomNumberGenerator& rng)
    {
        privateKey.GenerateRandomWithKeySize(rng, k * 8);
        publicKey = RSA::PublicKey(privateKey);
    }
    ~Server()
    {
    }
};


int main(int argc, char* argv[])
{
    AutoSeededRandomPool prng;
    Server srv(prng);
    return 0;
}