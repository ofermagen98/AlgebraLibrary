#ifndef BASE_H
#define BASE_H

#define self (*this)

namespace AlgebraTAU
{

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