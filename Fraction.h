
#ifndef FRACTION_H
#define FRACTION_H

#include "base.h"
#include <cryptopp/integer.h>
#include <iostream>
#include <sstream>

namespace AlgebraTAU
{
class Fraction
{
    CryptoPP::Integer a, b;

    void fix()
    {
        if (b.IsNegative())
        {
            a.Negate();
            b.Negate();
        }
        CryptoPP::Integer d = CryptoPP::Integer::Gcd(a.AbsoluteValue(), b);
        a /= d;
        b /= d;
    }

    public:
    Fraction(const int64_t& a, const int64_t& b = 1) : a(a), b(b)
    {
        fix();
    }

    Fraction(CryptoPP::Integer a = 0, CryptoPP::Integer b = 1) : a(std::move(a)), b(std::move(b))
    {
        fix();
    }

    Fraction(const Fraction& o) : a(o.a), b(o.b)
    {
        fix();
    }

    Fraction& operator=(const Fraction& o)
    {
        a = o.a;
        b = o.b;
        fix();
        return *this;
    }

    Fraction& operator*=(const Fraction& o)
    {
        a *= o.a;
        b *= o.b;
        fix();
        return *this;
    }

    Fraction& operator/=(const Fraction& o)
    {
        a *= o.b;
        b *= o.a;
        fix();
        return *this;
    }

    Fraction& operator+=(const Fraction& o)
    {
        a *= o.b;
        a += o.a * b;
        b *= o.b;
        fix();
        return *this;
    }

    Fraction& operator-=(const Fraction& o)
    {
        a *= o.b;
        a -= o.a * b;
        b *= o.b;
        fix();
        return *this;
    }

    Fraction& Negate()
    {
        a.Negate();
        fix();
        return *this;
    }

    Fraction operator-() const
    {
        Fraction res = *this;
        res.Negate();
        return res;
    }

    bool IsNegative() const
    {
        return a.IsNegative();
    }

    bool IsZero() const
    {
        return a.IsZero();
    }

    bool IsPositive() const
    {
        return a.IsPositive();
    }

    Fraction AbsoluteValue() const
    {
        Fraction res = *this;
        if (res.IsNegative()) res.Negate();
        return res;
    }

    std::ostream& print(std::ostream& os) const
    {
        return os << a << "/" << b;
    }

    CryptoPP::Integer round() const;
};

Fraction operator*(const Fraction& f1, const Fraction& f2)
{
    Fraction res = f1;
    res *= f2;
    return res;
}

Fraction operator/(const Fraction& f1, const Fraction& f2)
{
    Fraction res = f1;
    res /= f2;
    return res;
}

Fraction operator+(const Fraction& f1, const Fraction& f2)
{
    Fraction res = f1;
    res += f2;
    return res;
}

Fraction operator-(const Fraction& f1, const Fraction& f2)
{
    Fraction res = f1;
    res -= f2;
    return res;
}

bool operator<(const Fraction& f1, const Fraction& f2)
{
    return (f1 - f2).IsNegative();
}

bool operator>(const Fraction& f1, const Fraction& f2)
{
    return (f2 - f1).IsNegative();
}

bool operator<=(const Fraction& f1, const Fraction& f2)
{
    return !(f2 > f1);
}

bool operator>=(const Fraction& f1, const Fraction& f2)
{
    return !(f1 < f2);
}

bool operator==(const Fraction& f1, const Fraction& f2)
{
    return (f1 - f2).IsZero();
}

bool operator!=(const Fraction& f1, const Fraction& f2)
{
    return !(f1 == f2);
}

std::string to_string(const Fraction& f)
{
    std::stringstream ss;
    f.print(ss);
    return ss.str();
}

Fraction abs(const Fraction& f)
{
    return f.AbsoluteValue();
}

CryptoPP::Integer round(const Fraction& f)
{
    return f.round();
}

CryptoPP::Integer Fraction::round() const
{
    CryptoPP::Integer res = a / b;
    Fraction x = (*this - res);

    if (x.AbsoluteValue() >= 1) throw std::runtime_error("algorithmic impossibility");
    if (x < Fraction(-1, 2)) return res - 1;
    if (x < Fraction(1, 2)) return res;
    return res + 1;
}

}; // namespace AlgebraTAU

std::ostream& operator<<(std::ostream& os, const AlgebraTAU::Fraction& f)
{
    return f.print(os);
}

#endif
