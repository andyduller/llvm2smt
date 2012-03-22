#include "smt.h"

int fonction(int x, int y) {
  int z;
  assume(x >= 0 && y >= 0 && x < 4 && y < 5);
  z = x * y + 2;
  check(z < 100);
  return z;
}
