#include "matrix.h"
namespace AlgebraTAU
{

template <typename T>
matrix<T> operator*(const T& b, const matrix<T>& a)
{
    return a * b;
}

template <typename T>
vector<row, T> matrix<T>::get_row(int i) const
{
    if (i > rows()) throw std::invalid_argument("index out of range");

    std::vector<T> res(columns());
    for (int j = 0; j < columns(); ++j)
        res[j] = self(i, j);
    return res;
}

template <typename T>
vector<column, T> matrix<T>::get_column(int j) const
{
    if (j > columns()) throw std::invalid_argument("index out of range");

    std::vector<T> res(rows());
    for (int i = 0; i < columns(); ++i)
        res[i] = self(i, j);
    return res;
}

template <typename T>
void matrix<T>::set_row(int i, const vector<row, T>& v)
{
    if (i > rows()) throw std::invalid_argument("index out of range");

    if (v.size() != columns())
        throw std::invalid_argument("vector and matrix dimensions doesn't agree");

    for (int j = 0; j < columns(); ++j)
        self(i, j) = v(j);
}

template <typename T>
void matrix<T>::set_column(int j, const vector<column, T>& v)
{
    if (j > columns()) throw std::invalid_argument("index out of range");

    if (v.size() != rows())
        throw std::invalid_argument("vector and matrix dimensions doesn't agree");

    for (int i = 0; i < rows(); ++i)
        self(i, j) = v(j);
}

template <typename T>
void gram_schmidt(matrix<T>& m)
{
    if (m.rows() != m.columns())
        throw std::domain_error("can't preform gram_schmidt on non-square matrix");

    for (int i = 1; i < m.rows(); ++i)
    {
        vector<row, T> v = m.get_row(i), s(m.columns(), 0);
        for (int j = 0; j < i; ++j)
        {
            s += project(v, m.get_row(j));
        }
        m.set_row(i, v - s);
    }
}

template <typename T>
bool is_upper_triangular(const matrix<T>& m)
{
    for (int i = 0; i < m.rows(); ++i)
        for (int j = 0; j < i && j < m.columns(); ++j)
            if (m(i, j) != 0) return false;
    return true;
};

template <typename T>
bool is_lower_triangular(const matrix<T>& m)
{
    for (int i = 0; i < m.rows(); ++i)
        for (int j = i + 1; j < m.columns(); ++j)
            if (m(i, j) != 0) return false;
    return true;
}

template <typename T>
vector<column, T> matrix<T>::operator*(const vector<column, T>& vec) const
{
    if (columns() != vec.size())
        throw std::invalid_argument("matrix and vector dimensions doesn't agree");
    vector<column, T> res(rows(), true, 0);
    for (int i = 0; i < rows(); ++i)
        for (int j = 0; j < columns(); ++j)
            res(i) += self(i, j) * vec(j);
    return res;
}

template <typename T>
matrix<T>& matrix<T>::operator+=(const matrix& other)
{
    if (columns() != other.columns() || rows() != other.rows())
        throw std::invalid_argument("matrixes must have same shapes");
    for (int i = 0; i < rows(); ++i)
        for (int j = 0; j < columns(); ++j)
            self(i, j) += other(i, j);
    return self;
}

template <typename T>
matrix<T> matrix<T>::operator+(const matrix& other) const
{
    if (columns() != other.columns() || rows() != other.rows())
        throw std::invalid_argument("matrixes must have same shapes");
    auto res = self;
    res += other;
    return res;
}

template <typename T>
matrix<T>& matrix<T>::operator-=(const matrix& other)
{
    if (columns() != other.columns() || rows() != other.rows())
        throw std::invalid_argument("matrixes must have same shapes");
    for (int i = 0; i < rows(); ++i)
        for (int j = 0; j < columns(); ++j)
            self(i, j) -= other(i, j);
    return self;
}

template <typename T>
matrix<T> matrix<T>::operator-() const
{
    auto res = self;
    for (int i = 0; i < rows(); ++i)
        for (int j = 0; j < columns(); ++j)
            res(i, j) = -res(i, j);
    return res;
}

template <typename T>
matrix<T> matrix<T>::operator-(const matrix& other) const
{
    if (columns() != other.columns() || rows() != other.rows())
        throw std::invalid_argument("matrixes must have same shapes");
    auto res = self;
    res -= other;
    return res;
}

template <typename T>
matrix<T>& matrix<T>::operator*=(const T& a)
{
    for (int i = 0; i < rows(); ++i)
        for (int j = 0; j < columns(); ++j)
            self(i, j) *= a;
    return self;
}

template <typename T>
matrix<T> matrix<T>::operator*(const matrix& other) const
{
    if (columns() != other.rows()) throw std::invalid_argument("matrixes dimensions don't agree");
    matrix<T> res(rows(), other.columns(), 0);
    for (int i = 0; i < rows(); ++i)
        for (int j = 0; j < other.columns(); ++j)
            for (int k = 0; k < columns(); ++k)
                res(i, j) += self(i, k) * other(k, j);
    return res;
}

template <typename T>
matrix<T>& matrix<T>::operator*=(const matrix& other)
{
    if (columns() != other.rows()) throw std::invalid_argument("matrixes dimensions don't agree");
    self = self * other;
    return self;
}

template <typename T>
matrix<T> matrix<T>::operator*(const T& a) const
{
    auto res = self;
    res *= a;
    return res;
}

// The algorithm as described in
// https://en.wikipedia.org/wiki/Lenstra%E2%80%93Lenstra%E2%80%93Lov%C3%A1sz_lattice_basis_reduction_algorithm
template <typename T>
void LLL(matrix<T>& m, const T& delta)
{

    using std::abs;
    int n = m.rows() - 1;
    int dim = m.columns();
    vector<row, T> vec(dim, 0);
    matrix<T> ortho = m;
    gram_schmidt(ortho);

    auto mu = [&m, &ortho](int i, int j) {
        return dot(m.get_row(i), ortho.get_row(j)) / dot(ortho.get_row(j), ortho.get_row(j));
    };

    int k = 1;
    while (k <= n)
    {
        for (int j = k - 1; j >= 0; --j)
        {
            if (2 * abs(mu(k, j)) > 1)
            {
                m.set_row(k, m.get_row(k) - round(mu(k, j)) * m.get_row(j));
                ortho = m;
                gram_schmidt(ortho);
            }
        }

        if (ortho.get_row(k).norm() >= (delta - pow(mu(k, k - 1), 2)) * ortho.get_row(k - 1).norm())
        {
            k = k + 1;
        }
        else
        {
            vec = m.get_row(k);
            m.set_row(k, m.get_row(k - 1));
            m.set_row(k - 1, vec);
            ortho = m;
            gram_schmidt(ortho);

            k = std::max(k - 1, 1);
        }
    }
}

template <typename T>
T dot(const matrix<T>& a, const matrix<T>& b)
{
    if (a.columns() != b.columns() || a.rows() != b.rows())
        throw std::invalid_argument("matrixes must have same shapes");
    T res = 0;
    for (int i = 0; i < a.rows(); ++i)
        for (int j = 0; j < b.columns(); ++j)
            res += a(i, j) * b(i, j);
    return res;
}

template <typename T>
matrix<T>::matrix(size_t rows, size_t columns, const T& a)
: m_rows(rows), m_columns(columns), arr(rows * columns, a)
{
    if (rows == 0 || columns == 0) throw std::invalid_argument("can't create empty matrices");
}

template <typename T>
matrix<T>::matrix(const std::initializer_list<std::initializer_list<T>>& _arr)
{
    if (_arr.size() == 0) throw std::invalid_argument("can't create empty matrices");

    m_rows = _arr.size();
    m_columns = _arr.begin()->size();

    for (const auto& v : _arr)
        if (v.size() != columns()) throw std::invalid_argument("all rows must be of same size");

    if (columns() == 0) throw std::invalid_argument("can't create empty matrices");

    arr = std::vector<T>(rows() * columns());

    int i = 0;
    for (const auto& v : _arr)
        for (const T& x : v)
            arr[i++] = x;
}


template <typename T>
matrix<T>::matrix(const std::vector<std::vector<T>>& _arr)
{
    if (_arr.size() == 0) throw std::invalid_argument("can't create empty matrices");

    m_rows = _arr.size();
    m_columns = _arr.begin()->size();

    for (const auto& v : _arr)
        if (v.size() != columns()) throw std::invalid_argument("all rows must be of same size");

    if (columns() == 0) throw std::invalid_argument("can't create empty matrices");

    arr = std::vector<T>(rows() * columns());

    int i = 0;
    for (const auto& v : _arr)
        for (const T& x : v)
            arr[i++] = x;
}


template <typename T>
size_t matrix<T>::rows() const
{
    return m_rows;
}

template <typename T>
size_t matrix<T>::columns() const
{
    return m_columns;
}

template <typename T>
inline const T& matrix<T>::operator()(size_t i, size_t j) const
{
    return arr[i * columns() + j];
}

template <typename T>
inline T& matrix<T>::operator()(size_t i, size_t j)
{
    return arr[i * columns() + j];
}

template <typename T>
bool matrix<T>::operator==(const matrix& other) const
{
    if (other.columns() != columns() || other.rows() != rows()) return false;

    for (int i = 0; i < rows(); ++i)
        for (int j = 0; j < columns(); ++j)
            if (self(i, j) != other(i, j)) return false;
    return true;
}

template <typename T>
bool matrix<T>::operator!=(const matrix& other) const
{
    return !(self == other);
}

template <typename T>
matrix<T> matrix<T>::transpose() const
{
    using namespace std;
    matrix<T> res(columns(), rows(), 0);

    for (int i = 0; i < rows(); ++i)
        for (int j = 0; j < columns(); ++j)
            res(j, i) = self(i, j);

    return res;
}

template <typename T>
template <typename F>
void matrix<T>::map(const F& f)
{
    for (int i = 0; i < rows(); ++i)
        for (int j = 0; j < rows(); ++j)
            self(i, j) = f(self(i, j));
}

template <typename T>
void gaussian_elimination(matrix<T>& m)
{
    using namespace std;
    int t = 0;
    T r;

    for (int i = 0; i < m.rows() && i < m.columns(); ++i)
    {
        if (m(i, i) == 0)
        {
            for (t = i + 1; t < m.rows() && m(t, i) == 0; ++t)
                ;
            if (t >= m.rows())
            {
                --i;
                continue;
            }
            if (t < m.rows())
            {
                for (int j = 0; j < m.columns(); ++j)
                {
                    swap(m(i, j), m(t, j));
                    m(i, j) *= -1;
                }
            }
            else
            {
                continue;
            }
        }

        for (t = i + 1; t < m.rows(); ++t)
        {
            r = m(t, i) / m(i, i);
            for (int j = i; j < m.columns(); ++j)
            {
                m(t, j) -= r * m(i, j);
            }
        }
    }
}

template <typename T>
T matrix<T>::det() const
{
    if (rows() != columns())
        throw std::domain_error("can't take determinanent of non-square matrix");

    matrix M = self;
    gaussian_elimination(M);
    T res = 1;
    for (int i = 0; i < rows(); ++i)
        res *= M(i, i);
    return res;
}

template <typename T>
T matrix<T>::trace() const
{
    if (rows() != columns()) throw std::domain_error("can't take trace of non-square matrix");

    T res = 0;
    for (int i = 0; i < rows(); ++i)
        res += self(i, i);
    return res;
}

template <typename T>
std::ostream& operator<<(std::ostream& out, const matrix<T>& m)
{
    using std::to_string;
    std::string res = "";

    for (int i = 0; i < m.rows(); ++i)
    {
        for (int j = 0; j < m.columns(); ++j)
            res += to_string(m(i, j)) + ", ";

        res.pop_back();
        res.back() = '\n';
    }
    res.pop_back();

    return out << res;
}
} // namespace AlgebraTAU