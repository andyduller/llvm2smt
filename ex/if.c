

int main(int argc, char ** argv) {
	int x,y,z;

	x = 2;
	y = 5;
	z = x+y;

	if (y == 5) {
		x = 8;
	/* } else if (z+5 == x) { */
	/* 	x = 12; */
	} else {
		x = 42;
	}
	z = x + 1;
	return z;
}
