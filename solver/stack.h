/*-------------------------------------------------------------------------
This is an AWS-ARG-ATS-Science intern project developed by the intern
Joseph Reeves (jsreeves@) and mentor Benjamin Kiesl-Reiter (benkiesl@).

This code extends the solver yal-lin (Md Solimul Chowdhury, Cayden Codel, Marijn Heule), found at the [Github repository](https://github.com/solimul/yal-lin), which itself extended the solver [yalsat](https://github.com/arminbiere/yalsat) (Armin Biere).
-------------------------------------------------------------------------*/

/*

  Macros for a vector (stack) in C.

  Follows the same structure as Armin Biere's other C solvers.
  This allows us to use the heap from Kissat without modification.

  Memory allocation is tracked by the solver, ensuring there is 
  not a leak at the end of execution.

*/


#ifndef _stack_h_INCLUDED
#define _stack_h_INCLUDED

/*------------------------------------------------------------------------*/

#define NEWN(P,N) \
  do { (P) = yals_malloc (yals, (N)*sizeof *(P)); } while (0)

#define DELN(P,N) \
  do { yals_free (yals, (P), (N)*sizeof *(P)); } while (0)

#define RSZ(P,O,N) \
do { \
  (P) = yals_realloc (yals, (P), (O)*sizeof *(P), (N)*sizeof *(P)); \
} while (0)

/*------------------------------------------------------------------------*/

#define STACK(T) \
  struct { T * start; T * top; T * end; }

#define INIT(S) \
  do { (S).start = (S).top = (S).end = 0; } while (0)

#define SIZE(S) \
  ((S).end - (S).start)

#define COUNT(S) \
  ((S).top - (S).start)

#define EMPTY(S) \
  ((S).top == (S).start)

#define FULL(S) \
  ((S).top == (S).end)

#define CLEAR(S) \
  do { (S).top = (S).start; } while (0)

#define ENLARGE(S) \
do { \
  size_t OS = SIZE (S); \
  size_t OC = COUNT (S); \
  size_t NS = OS ? 2*OS : 1; \
  assert (OC <= OS); \
  RSZ ((S).start, OS, NS); \
  (S).top = (S).start + OC; \
  (S).end = (S).start + NS; \
} while (0)

#define FIT(S) \
do { \
  size_t OS = SIZE (S); \
  size_t NS = COUNT (S); \
  RSZ ((S).start, OS, NS); \
  (S).top = (S).start + NS; \
  (S).end = (S).start + NS; \
} while (0)

#define RESET(S,N) \
do { \
  assert ((N) <= SIZE (S) ); \
  (S).top = (S).start + (N); \
} while (0)

#define PUSH(S,E) \
do { \
  if (FULL(S)) ENLARGE (S); \
  *(S).top++ = (E); \
} while (0)

#define POP(S) \
  (assert (!EMPTY (S)), *--(S).top)

#define TOP(S) \
  (assert (!EMPTY (S)), (S).top[-1])

#define PEEK(S,P) \
  (assert ((P) < COUNT(S)), (S).start[(P)])

#define POKE(S,P,E) \
  do { assert ((P) < COUNT(S)); (S).start[(P)] = (E); } while (0)

#define RELEASE(S) \
do { \
  size_t N = SIZE (S); \
  DELN ((S).start, N); \
  INIT (S); \
} while (0)

#define BEGIN(S) (S).start

#endif