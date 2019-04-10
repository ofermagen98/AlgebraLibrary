#include "vector.h"
namespace AlgebraTAU
{
template <orientation O, typename T>
template <typename F>
void vector<O, T>::map(const F& f)
{
    for (int i = 0; i < size(); ++i)
        self(i) = f(self(i));
}

template <orientation O, typename T>
vector<orientation(!O), T> vector<O, T>::transpose() const
{
    return vector<orientation(!O), T>(arr);
}

template <orientation O, typename T>
T vector<O, T>::norm() const
{
    return dot(self, self);
}

template <orientation O, typename T>
vector<O, T> operator*(const T& b, const vector<O, T>& a)
{
    return a * b;
}

template <orientation O, typename T>
vector<O, T>& vector<O, T>::operator*=(const T& a)
{
    for (int i = 0; i < size(); ++i)
        self(i) *= a;
    return self;
}

template <orientation O, typename T>
vector<O, T> vector<O, T>::operator*(const T& a) const
{
    auto res = self;
    res *= a;
    return res;
}

template <orientation O, typename T>
vector<O, T>& vector<O, T>::operator+=(const vector<O, T>& other)
{
    if (size() != other.size()) throw std::invalid_argument("vectors must have same shapes");
    for (int i = 0; i < size(); ++i)
        self(i) += other(i);
    return self;
}

template <orientation O, typename T>
vector<O, T> vector<O, T>::operator+(const vector<O, T>& other) const
{
    auto res = self;
    res += other;
    return res;
}

template <orientation O, typename T>
vector<O, T>& vector<O, T>::operator-=(const vector<O, T>& other)
{
    if (size() != other.size()) throw std::invalid_argument("vectors must have same shapes");
    for (int i = 0; i < size(); ++i)
        self(i) -= other(i);
    return self;
}

template <orientation O, typename T>
vector<O, T> vector<O, T>::operator-(const vector<O, T>& other) const
{
    auto res = self;
    res -= other;
    return res;
}

template <orientation O, typename T>
vector<O, T> vector<O, T>::operator-() const
{
    auto res = self;
    for (int i = 0; i < size(); ++i)
        res(i) = -self(i);
    return res;
}

template <orientation O, typename T>
size_t vector<O, T>::size() const
{
    return arr.size();
}

template <orientation O, typename T>
const T& vector<O, T>::operator()(size_t i) const
{
    return arr[i];
}

template <orientation O, typename T>
T& vector<O, T>::operator()(size_t i)
{
    return arr[i];
}

template <typename T>
vector<row, T> operator*(const vector<row, T>& v, const matrix<T>& mat)
{
    if (v.size() != mat.rows())
        throw std::invalid_argument("matrix and vector dimensions doesn't agree");

    vector<row, T> res(mat.columns(), 0);
    for (int i = 0; i < mat.rows(); ++i)
        for (int j = 0; j < mat.columns(); ++j)
            res(j) += v(i) * mat(i, j);
    return res;
}

template <typename T>
vector<row, T>& operator*=(vector<row, T>& v, const matrix<T>& mat)
{
    if (v.size() != mat.rows())
        throw std::invalid_argument("matrix and vector dimensions doesn't agree");
    v = v * mat;
    return v;
}

template <orientation O, typename T>
vector<O, T>::vector(size_t size, const T& a) : arr(size, a)
{
    if (size == 0) throw std::invalid_argument("can't create empty vectors");
}

template <orientation O, typename T>
vector<O, T>::vector(const std::initializer_list<T>& _arr) : arr(_arr.begin(), _arr.end())
{
    if (size() == 0) throw std::invalid_argument("can't create empty vectors");
}

template <orientation O, typename T>
vector<O, T>::vector(const std::vector<T>& _arr) : arr(_arr.begin(), _arr.end())
{
    if (size() == 0) throw std::invalid_argument("can't create empty vectors");
}

template <orientation O, typename T>
T dot(const vector<O, T>& a, const vector<O, T>& b)
{
    if (a.size() != b.size()) throw std::invalid_argument("vectos must have same shapes");
    T res = 0;
    for (int i = 0; i < a.size(); ++i)
        res += a(i) * b(i);
    return res;
}

template <orientation O, typename T>
vector<O, T> project(const vector<O, T>& a, const vector<O, T>& b)
{
    return (dot(a, b) / dot(b, b)) * b;
}

template <orientation O, typename T>
bool vector<O, T>::operator==(const vector& other) const
{
    if (size() != other.size()) return false;
    for (int i = 0; i < size(); ++i)
        if (self(i) != other(i)) return false;
    return true;
}

template <orientation O, typename T>
bool vector<O, T>::operator!=(const vector<O, T>& other) const
{
    return !(self == other);
}

template <orientation O, typename T>
std::ostream& operator<<(std::ostream& out, const vector<O, T>& v)
{
    using std::to_string;
    std::string res = "";

    res += "(";

    for (int i = 0; i < v.size(); ++i)
        res += to_string(v(i)) + ", ";

    res.pop_back();
    res.pop_back();

    res += ")";
    if (O == column) res += "^T";

    return out << res;
}
} // namespace AlgebraTAU