/* IPASIR: Incremental Satisfiability Interface Standard.
 * Reference header for consumers of liballoy_ipasir. */

#ifndef IPASIR_H
#define IPASIR_H

#ifdef __cplusplus
extern "C" {
#endif

const char *ipasir_signature(void);

void *ipasir_init(void);

void ipasir_release(void *solver);

void ipasir_add(void *solver, int lit_or_zero);

void ipasir_assume(void *solver, int lit);

int ipasir_solve(void *solver);

int ipasir_val(void *solver, int lit);

void ipasir_set_terminate(void *solver, void *state,
                          int (*terminate)(void *state));

void ipasir_set_learn(void *solver, void *state, int max_length,
                      void (*learn)(void *state, const int *clause));

#ifdef __cplusplus
}
#endif

#endif /* IPASIR_H */
