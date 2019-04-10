#ifndef VECTOR_H
#define VECTOR_H

#include <cmath>
#include <iostream>
#include <stdexcept>
#include <string>
#include <vector>

#include "base.h"

namespace AlgebraTAU
{
// generativeclass vector represents a vector of orientation O (row / column) and type T
template <orientation O, typename T>
class vector
{
    // stores the vector's data
    std::vector<T> arr;

    public:
    // constructs matrix of shape rows x columns with default value = a
    // throws std::invalid_argument if rows == 0 or columns == 0
    vector(size_t size, const T& x = {});
    vector(const std::initializer_list<T>& _arr);
    vector(const std::vector<T>& _arr);

    // returns the size of the vector
    inline size_t size() const;

    // const access operator
    // does not preform input checking (does not check if index is out of range)
    inline const T& operator()(size_t i) const;

    // access operator
    // does not preform input checking (does not check if index is out of range)
    inline T& operator()(size_t i);

    // maps a function f into the elments of the vector (elementwise)
    template <typename F>
    void map(const F& f);

    // cheacks if the sizes of the vectors are equal and preforms elementwise comparison
    bool operator==(const vector& other) const;
    // negates ==
    bool operator!=(const vector& other) const;

    // adds two vectores and returns the result
    // throws std::invalid_argument if vectores do not have same size
    vector operator+(const vector& other) const;
    // adds vector "other" to "self" and returns reference to "self"
    // throws std::invalid_argument if vectors do not have same size
    // addition is done in-place
    vector& operator+=(const vector& other);

    // negates each element of the vector
    vector operator-() const;
    // substracts two vectores and returns the result
    // throws std::invalid_argument if vectores do not have same size
    vector operator-(const vector& other) const;
    // subtracts vector "other" from "self" and returns reference to "self"
    // throws std::invalid_argument if vectors do not have same size
    // addition is done in-place
    vector& operator-=(const vector& other);

    // preforms right scalar multiplication and returns the result
    vector operator*(const T& a) const;
    // preforms in-place scalar multiplication, the result is stored in "self"
    // returns reference to self
    vector& operator*=(const T& a);

    // turns vector into vector of transposed shape
    vector<orientation(!O), T> transpose() const;

    // calculates the norm of the matrix - i.e dot(self,self)
    T norm() const;
};

// read_JSON(std::istream &IS);        // Not implemented
// write_JSON(std::ostream &OS) const; // Not implemented

// preforms multiplication of  vec*mat (left matrix-vector multiplication)
// returns the result as a row vector
// throws std::invalid_argument if matrix and vector do not allow matrix-vector multiplication
template <typename T>
vector<row, T> operator*(const vector<row, T>& vec, const matrix<T>& mat);

// preforms multiplication of  vec*mat (left matrix-vector multiplication)
// stores result in self and returns reference to self
template <typename T>
vector<row, T> operator*=(vector<row, T>&, const matrix<T>& mat);

// calculates the dot product of vectors a,b
template <orientation O, typename T>
T dot(const vector<O, T>& a, const vector<O, T>& b);

// calculates the projection of vector a on vector b
template <orientation O, typename T>
vector<O, T> project(const vector<O, T>& a, const vector<O, T>& b);

// left scalar multiplication
template <orientation O, typename T>
vector<O, T> operator*(const T& b, const vector<O, T>& a);

} // namespace AlgebraTAU

#include "vector.inl"

#endif
