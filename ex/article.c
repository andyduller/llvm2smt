#include "smt.h"

int fonction(int x, int y) {

	int z;
	
	assume(x < 10 && y < 50 && x > 0 && y > 0);
	z = x + y;
	
	check(z < 60);

	if (z > 30) {
		z -= 30;
	} else {
		z += 5;
	}
	check(z <= 30);

}
