#include <cryptopp/integer.h>
#include <cryptopp/modarith.h>
#include <cryptopp/rsa.h>
using namespace CryptoPP;

#include <iostream>
#include <iomanip>
using namespace std;

class Server
{
private:
	RSA::PrivateKey privateKey;
public:
	RSA::PublicKey publicKey;

	Server(RandomNumberGenerator &rng){
		privateKey.GenerateRandomWithKeySize(rng, 3072);
		publicKey = RSA::PublicKey(privateKey);
	}
	~Server(){

	}

	bool is
	
};




int main(int argc, char* argv[])
{
  Integer m("4294967295"), n("0x1000000000000000000000000000000"), j;
  j = 1999;

  ModularArithmetic ma(j);

  cout << "n+m mod j: " << ma.Add(n, m) << endl;
  cout << "n-m mod j: " << ma.Subtract(n, m) << endl;
  cout << "n*m mod j: " << ma.Multiply(n, m) << endl;
  cout << "n/m mod j: " << ma.Divide(n, m) << endl;
  cout << "n%m mod j: " << ma.Reduce(n, m) << endl;
  cout << "n^m mod j: " << ma.Exponentiate(n, m) << endl;

  return 0;
}