/********************************************************************
 * Copyright (C) 2009 by Verimag                                    *
 * Initial author: Matthieu Moy                                     *
 * This file must not be distributed outside Verimag                *
 ********************************************************************/

/*!
  \file bit-counter.h
  \brief Utility file to create counters based on bits (bool variables)

  
*/
#ifndef EIGHT_BITS_COUNTER_H
#define EIGHT_BITS_COUNTER_H

#ifdef SOME_BITS_COUNTER_H
#error Including several counter files won t work, sorry.
#endif
#define SOME_BITS_COUNTER_H

#define INCREMENT_BIT(counter,prev,cur)         \
        c       ## cur = counter ## cur && c ## prev; \
        counter ## cur =                               \
                   (counter ## cur || c ## prev) &&    \
                !  (counter ## cur && c ## prev)

#define DECLARE_COUNTER(counter) \
        bool counter ## 1;       \
        bool counter ## 2;       \
        bool counter ## 3;       \
        bool counter ## 4;       \
        bool counter ## 5;       \
        bool counter ## 6;       \
        bool counter ## 7;       \
        bool counter ## 8;       \
        bool counter ## finished; \
        bool counter ## started

#define INIT_COUNTER(counter) \
        counter ## 1 = false;     \
        counter ## 2 = false;     \
        counter ## 3 = false;     \
        counter ## 4 = false;     \
        counter ## 5 = false;     \
        counter ## 6 = false;     \
        counter ## 7 = false;     \
        counter ## 8 = false;     \
        counter ## finished = false; \
        counter ## started  = false

/* define this to disable debugging (it's defined by Pinapa in LusSy) */
//#define SCP_IN_PARSER

#define DEBUG_COUNTER(counter) /* nothing */


/* A macro for LusSy (we get the inlining for free), but a "function"
   version will probably be needed for ssa->signal */
#define step(counter)                           \
	INCREMENT_BIT(counter, 0, 1);           \
	INCREMENT_BIT(counter, 1, 2);           \
	INCREMENT_BIT(counter, 2, 3);           \
	INCREMENT_BIT(counter, 3, 4);           \
	INCREMENT_BIT(counter, 4, 5);           \
	INCREMENT_BIT(counter, 5, 6);           \
	INCREMENT_BIT(counter, 6, 7);           \
	INCREMENT_BIT(counter, 7, 8);           \
	if (counter ## 1 == true &&             \
	    counter ## 2 == true &&             \
	    counter ## 3 == true &&             \
	    counter ## 4 == true &&             \
	    counter ## 5 == true &&             \
	    counter ## 6 == true &&             \
	    counter ## 7 == true &&             \
	    counter ## 8 == true) {             \
		counter ## finished = true;     \
	}                                       \
	counter ## started = true;              \
	DEBUG_COUNTER(counter)

/* LusSy doesn't deal with quantitative time. So, several processes
   doing wait(time) will be elected non-deterministically. This is
   really what we mean by "yield()".
   
   A special case is the origin of time: if the processes start at
   time 0, then the first one doing a yield() is no longer eligible,
   and the second has to run (while we'd have expected non-determinism
   for a real asynchronous "yield"). We work around this by inserting
   a yield() statement at the beginning of each process.
*/

/* Declare temporary variables used for carries */
#define BEGINNING_OF_PROCESS \
	bool c0 = true, c1, c2, c3, c4, c5, c6, c7, c8; \


#endif // EIGHT_BITS_COUNTER_H
