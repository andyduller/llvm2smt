#ifndef __SMT_H
#define __SMT_H

extern void verif_stop();
extern void verif_fail();
extern void verif_warn();

#define assume(x) do { if (!(x)) verif_stop(); } while(0)
#define check(x) do { if (!(x)) verif_warn(); } while(0)
#define assert(x) do { if (!(x)) { verif_warn(); verif_fail(); }} while(0)

#endif
