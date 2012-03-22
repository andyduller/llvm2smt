/********************************************************************
 * Copyright (C) 2009 by Verimag                                    *
 * Initial author: Matthieu Moy                                     *
 * This file must not be distributed outside Verimag                *
 ********************************************************************/

/*!
  \file 2-bits-counter.h
  \brief 2 bits variant of 8-bits-counter.h.

  Should be 100% compatible, but greatly helps debugging ...
*/
#ifndef TWO_BITS_COUNTER_H
#define TWO_BITS_COUNTER_H

#ifdef SOME_BITS_COUNTER_H
#error Including several counter files won't work, sorry.
#endif
#define SOME_BITS_COUNTER_H

#define INCREMENT_BIT(counter,prev,cur)         \
	c ## cur        = counter ## cur && c ## prev; \
	counter ## cur =                               \
		   (counter ## cur || c ## prev) &&    \
		!  (counter ## cur && c ## prev)

#define DECLARE_COUNTER(counter) \
	bool counter ## 1;       \
	bool counter ## 2;       \
	bool counter ## finished; \
	bool counter ## started

#define INIT_COUNTER(counter) \
	counter ## 1 = false;     \
	counter ## 2 = false;     \
	counter ## finished = false; \
	counter ## started  = false

/* define this to disable debugging (it's defined by Pinapa in LusSy) */
//#define SCP_IN_PARSER

#ifdef SCP_IN_PARSER
#define DEBUG_COUNTER(counter) /* nothing */
#else
#define DEBUG_COUNTER(counter) \
	printf(#counter ": %d %d (started=%d, finished=%d)\n",\
	       counter ## 2,                          \
	       counter ## 1,                          \
	       counter ## started,                    \
	       counter ## finished)
#endif

/* A macro for LusSy (we get the inlining for free), but a "function"
   version will probably be needed for ssa->signal */
#define step(counter)                           \
	INCREMENT_BIT(counter, 0, 1);           \
	INCREMENT_BIT(counter, 1, 2);           \
	if (counter ## 1 == true &&             \
	    counter ## 2 == true) {             \
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
#define yield() wait(42, SC_NS)

/* Declare temporary variables used for carries */
#define BEGINNING_OF_PROCESS \
	bool c0 = true, c1, c2; \
	yield()


#endif // TWO_BITS_COUNTER_H
