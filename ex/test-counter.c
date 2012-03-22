// #define DISABLE_DEBUG 0                                                      

#include "8-bits-counter.h"
#include <stdio.h>
#include "smt.h"

#define bool int
#define true 1
#define false 0


int main() {
        DECLARE_COUNTER(counter);
        BEGINNING_OF_PROCESS;

        INIT_COUNTER(counter);

        while (!counterfinished) {
                step(counter);
                DEBUG_COUNTER(counter);
        }
        check(false);
        return 0;
}





