#include <cryptopp/integer.h>
#include <sstream>

#ifndef BASE_H
#define BASE_H

#define self (*this)

namespace AlgebraTAU
{
class Fraction;

std::string to_string(const CryptoPP::Integer& x)
{
    std::stringstream ss;
    ss << x;
    return ss.str();
}

CryptoPP::Integer abs(const CryptoPP::Integer& x)
{
    return x.AbsoluteValue();
}

AlgebraTAU::Fraction abs(const AlgebraTAU::Fraction& x);
std::string to_string(const AlgebraTAU::Fraction& x);

template <typename T>
inline T sqaure(const T& t)
{
    return t * t;
}

enum orientation
{
    row = 0,
    column
};
template <orientation O, typename T>
class vector;
template <typename T>
class matrix;

} // namespace AlgebraTAU

#endif