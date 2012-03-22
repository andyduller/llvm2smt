/********************************************************************
 * Copyright (C) 2008 by Verimag                                    *
 * Initial author: Matthieu Moy                                     *
 * This file must not be distributed outside Verimag                *
 ********************************************************************/

// We check for process termination, so assertion failure can be
// modeled with an infinite loop.
#define ASSERT(c) if(c) {int x; while(1) {x = x;};}


void compute() {
	int tmp = 0;
	int b1 = 0;
	int b2 = 0;
	int b3 = 0;
	int b4 = 0;
	int b5 = 0;
	int b6 = 0;
	int b7 = 0;
	int b8 = 0;

	int i1 = 0, i2 = 0, i3 = 0; // intermediate results

	int nd1, nd2, nd3, nd4, nd5, nd6, nd7, nd8, nd9; // non-deterministic values.

#define SHL             b1 = b2; b2 = b3; b3 = b4; b4 = b5; b5 = b6; b6 = b7; b7 = b8; b8 = 0
#define SHR             b8 = b7; b7 = b6; b6 = b5; b5 = b4; b4 = b3; b3 = b2; b2 = b1; b1 = 0;

#define ROL   tmp = b1; b1 = b2; b2 = b3; b3 = b4; b4 = b5; b5 = b6; b6 = b7; b7 = b8; b8 = tmp;
#define ROR   tmp = b8; b8 = b7; b7 = b6; b6 = b5; b5 = b4; b4 = b3; b3 = b2; b2 = b1; b1 = tmp;
                
#ifndef SCP_IN_PARSER
	// SCP_IN_PARSER is defined only within Pinapa. This
	// portion is just for debugging and won't be used for
	// the proof.
	nd1 = 1;
	nd2 = 1;
	nd3 = 1;
	nd4 = 1;
	nd5 = 1;
	nd6 = 1;
	nd7 = 1;
#endif


	if      ( nd7 &&  nd8 &&  nd9)
	{ /*    nothing. That's the only case where
		nd1..nd6 are all 1. Uncomment the
		line below to make the property true. */
		//nd1 = 0;
	}
	else if (!nd7 &&  nd8 &&  nd9)
		nd1 = 0;
	else if ( nd7 && !nd8 &&  nd9)
		nd2 = 0;
	else if (!nd7 && !nd8 &&  nd9)
		nd3 = 0;
	else if ( nd7 &&  nd8 && !nd9)
		nd4 = 0;
	else if (!nd7 &&  nd8 && !nd9)
		nd5 = 0;
	else 
		nd6 = 0;

	/* If nd1 = 0 is uncommented above, then at this
	 * point, one of nd1, nd2, nd3, nd4, nd5 or nd6 is
	 * 0. IOW, an invariant at this point is
	 * !nd1 || !nd2 || !nd3 || !nd4 || !nd5 || !nd6
	 * if nd1 = 0 is commented out, then this
	 * invariant doesn't hold.
	 */
	b1 = 0;
	b2 = 0;
	b3 = 0;
	b4 = 0;
	b5 = 0;
	b6 = 0;
	b7 = 0;
	b8 = nd1;


	SHL; SHL; SHL; SHL; SHL; SHL; SHL;
	// nd1 has moved to b1.

	SHR;
	// nd1 is back on b2.

	if (nd2) {
		SHR; SHR; SHR;
	}

	i1 = !b2;


	// nd1 might have moved back to b5.
                
	if (nd3) {
		ROR; ROR; ROR; ROR;
	}
	// nd1 might have rotated back to b1

	i2 = !b5;


	if (nd4) {
		b2 = b1 || b2; // it's possible that b1 == b2
		// == 1
	}
                
	if (nd5) {
		b3 = b1 && b2; // b3 can be 1
	}

	SHR; SHR; // b5 can be 1.
                

	if (b5) {
		b6 = 1;
	}
                
	if (b5 && b6) {
		b7 = nd6;
	}

	ROR;
                
	i3 = b8;

                
	ASSERT((!i1) || (!i2) || (!i3));
}
        
