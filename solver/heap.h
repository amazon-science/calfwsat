/*-------------------------------------------------------------------------
This is an AWS-ARG-ATS-Science intern project developed by the intern
Joseph Reeves (jsreeves@) and  mentor Benjamin Kiesl-Reiter (benkiesl@).

This code extends the heap from the solver [kissat](https://github.com/arminbiere/kissat) (Armin Biere).
-------------------------------------------------------------------------*/

#ifndef _heap_h_INCLUDED
#define _heap_h_INCLUDED

#include "stack.h"

#include <assert.h>
#include <limits.h>
#include <stdbool.h>
#include <stdlib.h>

#define DISCONTAIN UINT_MAX
#define DISCONTAINED(IDX) ((int) (IDX) < 0)

#define MAX(A,B) (((A) > (B)) ? (A) : (B))

typedef struct heap heap;

typedef STACK (unsigned) unsigneds;

struct Yals;

struct heap {
  bool tainted;
  unsigned vars;
  unsigned size;
  unsigneds stack;
  double *score;
  unsigned *pos;
  double (*score_fun)(struct Yals *,int);
};

struct Yals;

void yals_resize_heap (struct Yals *yals, heap *, unsigned size);
void yals_release_heap (struct Yals *yals, heap *);

static inline bool yals_heap_contains (heap *heap, unsigned idx) {
  return idx < heap->vars && !DISCONTAINED (heap->pos[idx]);
}

static inline unsigned yals_get_heap_pos (const heap *heap,
                                            unsigned idx) {
  return idx < heap->vars ? heap->pos[idx] : DISCONTAIN;
}

static inline double yals_get_heap_score (const heap *heap,
                                            unsigned idx) {
  return idx < heap->vars ? heap->score[idx] : 0.0;
}

static inline bool yals_empty_heap (heap *heap) {
  return EMPTY (heap->stack);
}

static inline size_t yals_size_heap (heap *heap) {
  return SIZE (heap->stack);
}

static inline unsigned yals_max_heap (heap *heap) {
  assert (!yals_empty_heap (heap));
  return PEEK (heap->stack, 0);
}

void yals_rescale_heap (struct Yals *yals,heap *heap, double factor);

void yals_enlarge_heap (struct Yals *yals,heap *, unsigned new_vars);

static inline double yals_max_score_on_heap (heap *heap) {
  if (!heap->tainted)
    return 0;
  assert (heap->vars);
  const double *const score = heap->score;
  const double *const end = score + heap->vars;
  double res = score[0];
  for (const double *p = score + 1; p != end; p++)
    res = MAX (res, *p);
  return res;
}

void yals_clear_heap (struct Yals *yals,heap *heap);

#ifndef NDEBUG
void yals_dump_heap (heap *);
#endif

#ifndef NDEBUG
void yals_check_heap (heap *);
#else
#define yals_check_heap(...) \
  do { \
  } while (0)
#endif

#endif
