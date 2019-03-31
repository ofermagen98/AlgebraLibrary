#ifndef VECTOR_H
#define VECTOR_H

#include "base.h"
#include <iostream>
#include <stdexcept>
#include <string>
#include <vector>

#define self (*this)

namespace AlgebraTAU {

template <orientation O, typename T> class vector {
  std::vector<T> arr;

public:
  vector(size_t size, const T &x);
  //change to explicit constructor with initializer list
  vector(const std::vector<T> &_arr);

  inline size_t size() const;

  inline const T &operator()(size_t i) const;
  inline T &operator()(size_t i);

  template <typename F> 
  void map(const F &f);

  bool operator==(const vector &other) const;
  bool operator!=(const vector &other) const;

  vector operator+(const vector &other) const;
  vector &operator+=(const vector &other);

  vector operator-() const;
  vector operator-(const vector &other) const;
  vector &operator-=(const vector &other);

  vector operator*(const T &a) const;
  vector &operator*=(const T &a);


  vector<orientation_negate(O),T> transpose() const {
    return vector<orientation_negate(O),T>(arr);
  }
  // void read_JSON(std::istream &IS);        // Not implemented
  // void write_JSON(std::ostream &OS) const; // Not implemented
};

template <typename T>
vector<row, T> operator*(const vector<row, T> &, const matrix<T> &mat);

template <typename T>
vector<row, T> operator*=(vector<row, T> &, const matrix<T> &mat);


} // namespace AlgebraTAU


#include "vector.inl"

#endif
