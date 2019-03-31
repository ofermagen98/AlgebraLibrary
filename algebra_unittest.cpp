#include "matrix.h"
#include "vector.h"
#include <gtest/gtest.h>
#include <iostream>
#include <math.h>

TEST(MatrixOperators, MatrixNEQ) {
  AlgebraTAU::matrix<double> M1(
      {{8, 5, 5, 9, 7}, {9, 1, 2, 2, 5}, {8, 0, 7, 4, 7}, {6, 9, 1, 9, 2}});

  AlgebraTAU::matrix<double> M2(
      {{9, 3, 7, 3, 5}, {1, 3, 3, 4, 4}, {7, 9, 4, 9, 9}, {9, 8, 6, 6, 5}});

  EXPECT_TRUE(M1 != M2);
}

TEST(MatrixOperators, MatrixEQ) {
  AlgebraTAU::matrix<double> M1(
      {{8, 5, 5, 9, 7}, {9, 1, 2, 2, 5}, {8, 0, 7, 4, 7}, {6, 9, 1, 9, 2}});

  AlgebraTAU::matrix<double> M2(
      {{8, 5, 5, 9, 7}, {9, 1, 2, 2, 5}, {8, 0, 7, 4, 7}, {6, 9, 1, 9, 2}});

  EXPECT_TRUE(M1 == M2);
}

TEST(MatrixOperators, MatrixMultiplication) {
  AlgebraTAU::matrix<double> M1({{0, 1, 2}, {3, 4, 5}});
  AlgebraTAU::matrix<double> M2({{0, 1}, {2, 3}, {4, 5}});
  AlgebraTAU::matrix<double> res({{10, 13}, {28, 40}});

  EXPECT_EQ(M1 * M2, res);
}

TEST(AdvanceAlgebraicOperations, GaussianElimination) {
  AlgebraTAU::matrix<double> M({{1, 2, 2, 0, 5, 1, 7, 4},
                                {9, 7, 5, 2, 1, 9, 3, 1},
                                {7, 2, 4, 4, 4, 5, 9, 3},
                                {5, 8, 6, 5, 9, 8, 8, 8}});

  gaussian_elimination(M);
  EXPECT_TRUE(is_upper_triangular(M));
}

TEST(MatrixMethods, TransposeTranpose) {
  AlgebraTAU::matrix<double> M({{1, 2, 2, 0, 5, 1, 7, 4},
                                {9, 7, 5, 2, 1, 9, 3, 1},
                                {7, 2, 4, 4, 4, 5, 9, 3},
                                {5, 8, 6, 5, 9, 8, 8, 8}});

  EXPECT_EQ(M, M.transpose().transpose());
}

TEST(VectorOperators, Transpose) {
  AlgebraTAU::vector<AlgebraTAU::row, double> v1({1, 2, 2, 0, 5, 1, 7, 4});
  AlgebraTAU::vector<AlgebraTAU::column, double> v2({1, 2, 2, 0, 5, 1, 7, 4});

  EXPECT_EQ(v1.transpose(), v2);
  EXPECT_EQ(v2.transpose(), v1);
}

TEST(VectorOperators, ScalarMultiplication) {
  AlgebraTAU::vector<AlgebraTAU::row, double> v({1, 2, 3, 4});
  AlgebraTAU::vector<AlgebraTAU::row, double> res({2.5, 5, 7.5, 10});
  v *= 2.5;

  EXPECT_EQ(v, res);
}

TEST(VectorMatrixOperations, VectorMatrixMultiplication) {
  AlgebraTAU::vector<AlgebraTAU::row, double> v(std::vector<double>({1, 2, 3}));
  AlgebraTAU::matrix<double> m({{1, 2}, {3, 4}, {5, 6}});
  AlgebraTAU::vector<AlgebraTAU::row, double> res(
      std::vector<double>({22, 28}));

  EXPECT_EQ(v * m, res);
}

TEST(AdvanceAlgebraicOperations, GramSchmidt) {
  AlgebraTAU::matrix<double> M(
      {{4.0, 0.0, 4.0}, {9.8, 2.0, 7.8}, {55.18, 7.2, 44.98}});

  AlgebraTAU::matrix<double> N(
      {{4.0, 0.0, 4.0}, {1.0, 2.0, -1.0}, {1.0, -1.0, -1.0}});

  gram_schmidt(M);
  M -= N;
  M.map([](const double &x) { return fabs(x) < 1e-7 ? 0 : x; });

  EXPECT_EQ(M, AlgebraTAU::matrix<double>(3, 3, 0));
}

TEST(AdvanceAlgebraicOperations, LLL) {
  AlgebraTAU::matrix<double> B(
      {{1.0, 1.0, 1.0}, {-1.0, 0.0, 2.0}, {3.0, 5.0, 6.0}});

  AlgebraTAU::matrix<double> res(
      {{0.0, 1.0, 0.0}, {1.0, 0.0, 1.0}, {-1.0, 0.0, 2.0}});

  AlgebraTAU::LLL(B, 0.75);
  B -= res;
  B.map([](const double &x) { return fabs(x) < 1e-7 ? 0 : x; });

  EXPECT_EQ(B, AlgebraTAU::matrix<double>(3, 3, 0));
}

int main(int argc, char const *argv[]) {
  testing::InitGoogleTest(&argc, (char **)(argv));
  return RUN_ALL_TESTS();
}