#include "smt.h"

int fonction(int x, int y) {

	int z;
	
	assume(x < 4 && y < 5);
	z = x + y;
	check(!(z > 6));

}
