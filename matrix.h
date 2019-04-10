#ifndef MARIX_H
#define MARIX_H

#include <cmath>
#include <iostream>
#include <stdexcept>
#include <string>
#include <vector>

#include "base.h"

namespace AlgebraTAU
{

// generative class matrix represents a matrix of type T
template <typename T>
class matrix
{
    // stores the shape of the matrix
    size_t m_rows, m_columns;
    // stores the matrix's data - rowise
    std::vector<T> arr;

    public:
    // constructs matrix of shape rows x columns with default value = a
    // throws std::invalid_argument if rows == 0 or columns == 0
    matrix(size_t rows, size_t columns, const T& a = {});

    // constructs matrix given data _arr, _arr is a row-wise representation
    // throws std::invalid_argument if _arr is empty
    // throws std::invalid_argument if not all rows in _arr are of same size
    matrix(const std::initializer_list<std::initializer_list<T>>& _arr);

    // constructs matrix given data vector _arr, _arr is a row-wise representation
    // throws std::invalid_argument if _arr is empty
    // throws std::invalid_argument if not all rows in _arr are of same size
    matrix(const std::vector<std::vector<T>>& _arr);

    // returns the number of rows in the matrix
    inline size_t rows() const;
    // returns the number of columns in the matrix
    inline size_t columns() const;

    // const access operator
    // does not preform input checking (does not check if index is out of range)
    inline const T& operator()(size_t i, size_t j) const;
    // access operator
    // does not preform input checking (does not check if index is out of range)
    inline T& operator()(size_t i, size_t j);

    // returns the transposed matrix
    matrix transpose() const;
    // maps a function f into the elments of the matrix (elementwise)
    template <typename F>
    void map(const F& f);
    // calculates the determinant of a matrix
    T det() const;

    // matrix invert() const; // Not implemented

    // calculates the trace of the matrix
    T trace() const;

    // cheacks if the shapes of the matrices are equal and preforms elementwise comparison
    bool operator==(const matrix& other) const;
    // negates ==
    bool operator!=(const matrix& other) const;

    // adds two matrices and returns the result
    // throws std::invalid_argument if matrices do not have same shapes
    matrix operator+(const matrix& other) const;
    // adds matrix "other" to "self" and returns reference to "self"
    // throws std::invalid_argument if matrices do not have same shapes
    // addition is done in-place
    matrix& operator+=(const matrix& other);

    // negates each element of the matrix
    matrix operator-() const;
    // substracts two matrices and returns the result
    // throws std::invalid_argument if matrices do not have same shapes
    matrix operator-(const matrix& other) const;
    // substracts matrix "other" from "self" and returns reference to "self"
    // substraction is done in-place
    // throws std::invalid_argument if matrices do not have same shapes
    matrix& operator-=(const matrix& other);

    // preforms matrix multiplication and returns the result
    // throws std::invalid_argument if matrix shapes do not allow matrix multiplication
    matrix operator*(const matrix& other) const;
    // preforms matrix multiplication and stores result in "self", returns reference to "self"
    // throws std::invalid_argument if matrix shapes do not allow matrix multiplication
    matrix& operator*=(const matrix& other);

    // preforms multiplication of self * vec (right matrix-vector multiplication)
    // returns the result as a column vector
    // throws std::invalid_argument if matrix and vector do not allow matrix-vector multiplication
    vector<column, T> operator*(const vector<column, T>& vec) const;

    // preforms right scalar multiplication and returns the result
    matrix operator*(const T& a) const;
    // preforms in-place scalar multiplication, the result is stored in "self"
    // returns reference to self
    matrix& operator*=(const T& a);

    // returns the i'th row of the matrix as a row vector
    // throws std::invalid_argument if index is out of range
    vector<row, T> get_row(int i) const;

    // returns the j'th column of the matrix as a column vector
    // throws std::invalid_argument if index is out of range
    vector<column, T> get_column(int j) const;

    // set's the i'th row of the matrix to be some input vector v
    // throws std::invalid_argument if i is out of range
    // throws std::invalid_argument if v.size() is not v.columns()
    void set_row(int i, const vector<row, T>& v);

    // set's the j'th row of the matrix to be some input vector v
    // throws std::invalid_argument if j is out of range
    // throws std::invalid_argument if v.size() is not v.rows()
    void set_column(int j, const vector<column, T>& v);
};

// read_JSON(std::istream &IS);        // Not implemented
// write_JSON(std::ostream &OS) const; // Not implemented

// left scalar multiplication
template <typename T>
matrix<T> operator*(const T& b, const matrix<T>& a);

// preforms in place, row-wise, gaussian elimination of matrix m
template <typename T>
void gaussian_elimination(matrix<T>& m);

// preforms in place, row-wise, gram schmidt process of matrix m
template <typename T>
void gram_schmidt(matrix<T>& m);

// preforms LLL over matrix m with size paremeter delta
// assumes m is a row-wise base matrix
// result is stored in m but not all calculations is done in place
template <typename T>
void LLL(matrix<T>& m, const T& delta);

} // namespace AlgebraTAU

#include "matrix.inl"

#endif
