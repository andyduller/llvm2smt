#include "smt.h"

int function(int x, int y, int z, int val, int ret) {

	assume(x == 2 && y ==5);

	z = x+y;
	val = z*2+x-y;
	
	switch (val) {
	case 5:
		z = 10;
		ret = 12;
		break;
	case 6:
		z = 9;
		ret = 126;
		break;
	case 7:
		z = 8;
		ret = 162;
		break;
	case 8:
		z = 7;
		ret = 2;
		break;
	case 9:
		z = 6;
		ret = 1;
		break;
	case 10:
		z = 5;
		ret = 11;
		break;
	case 11:
		z = 4;
		ret = 13;
		break;
	default:
		z = 42;
		ret = 42;
	}
	
	if (y == 5) {
		x = 8;
	} else if (z+5 == x) {
		x = 12;
	} else {
		x = 42;
	}
	z = x + 1;

	check(z > 9);
	
	return z;
}
