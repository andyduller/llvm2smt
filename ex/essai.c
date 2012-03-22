
int main(int argc, char ** argv) {
	int x,y,z;

	x = 2;
	y = 5;
	z = x+y;

	x = 6;
	if (z > 0) {
		x = 8;
	} else {
		x = 12;
	}
	z = x + 1;
	return z;
}
