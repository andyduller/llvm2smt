#include<stdio.h>
#include<assert.h>

int main(int argc, char ** argv) {
	int x,y,z;

	x = 2;
	y = 5;
	z = x+y;

	if (y == 5) {
		x = 8;
	} else if (z+5 == x) {
		printf("%d\n",x);
		x = 12;
	} else {
		printf("The answer\n");
		x = 42;
	}
	z = x + 1;
	assert(z>0);
	return z;
}


/*
( and 

(= x 2)
(= y 5)
(= z (+ x y))
(or
   ((= y 5)  and (= x 8) )
   ((!= y 5) and (= x 12))
)
(= z (+ x 1))   
)
*/
	
