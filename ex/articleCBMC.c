#include <assert.h>

int fonction(int x, int y) {

	int z;
	
	if (!(x < 10 && y < 50 && x > 0 && y > 0)) return 1;
	z = x + y;
	
	assert(z < 60);

	if (z > 30) {
		z -= 30;
	} else {
		z += 5;
	}
	assert(z <= 30);

}
