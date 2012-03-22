/********************************************************************
 * Copyright (C) 2008 by Verimag                                    *
 * Initial author: Matthieu Moy                                     *
 * This file must not be distributed outside Verimag                *
 ********************************************************************/

#include "systemc.h"
#include <iostream>
#include "scp-verification.h"

//#include "8-bits-counter.h"
// This version will be easier to debug.
#include "2-bits-counter.h"

using namespace std;

SC_MODULE(module) {
        DECLARE_COUNTER(count1_);
        DECLARE_COUNTER(count2_);

        void compute1() {
                BEGINNING_OF_PROCESS;
                /* start after counter 1 has started (polling). */
                while(!(count2_started)) {
                        yield();
                }
                while(!(count1_finished)) {
                        step(count1_);
                        yield();
                }
                ASSERT(count2_finished);
        }

        void compute2() {
                BEGINNING_OF_PROCESS;
                while(!(count2_finished)) {
                        step(count2_);
                        /* no yield here => if the counter has stared,
                           it has also finished. => true property.

                           with the yield, it's possible to start
                           count2 without finishing it, and then
                           compute1 can run till the end => false
                           property. */
                        //yield();
                }
        }

        SC_HAS_PROCESS(module);
        module(sc_module_name name) {
                INIT_COUNTER(count1_);
                INIT_COUNTER(count2_);

                SC_THREAD(compute1);
                SC_THREAD(compute2);
        }
};


int sc_main (int argc, char ** argv) {
        new module("module");
        sc_start();
        return 0;
}
