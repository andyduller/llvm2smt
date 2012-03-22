/********************************************************************
 * Copyright (C) 2008 by Verimag                                    *
 * Initial author: Matthieu Moy                                     *
 * This file must not be distributed outside Verimag                *
 ********************************************************************/

#include <iostream>

//#include "8-bits-counter.h"
// This version will be easier to debug.
#include "8-bits-counter.h"

using namespace std;


void compute1() {
	DECLARE_COUNTER(count1_);
	INIT_COUNTER(count1_);
	
	BEGINNING_OF_PROCESS;
	step(count1_);
	step(count1_);
	
}
