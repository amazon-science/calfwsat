/*-------------------------------------------------------------------------
This is an AWS-ARG-ATS-Science intern project developed by the intern
Joseph Reeves (jsreeves@) and manager Benjamin Kiesl (benkiesl@).

This code extends the heap from the solver [kissat](https://github.com/arminbiere/kissat) (Armin Biere).
-------------------------------------------------------------------------*/

#include "yals.h"
#include "heap.h"


#include <string.h>

void yals_release_heap (Yals *yals,heap *heap) {
  RELEASE (heap->stack);
  DELN (heap->pos, heap->size);
  DELN (heap->score, heap->size);
  memset (heap, 0, sizeof *heap);
}

#ifndef NDEBUG

void yals_check_heap (heap *heap) {
  const unsigned *const stack = BEGIN (heap->stack);
  const unsigned end = SIZE (heap->stack);
  const unsigned *const pos = heap->pos;
  const double *const score = heap->score;
  for (unsigned i = 0; i < end; i++) {
    const unsigned idx = stack[i];
    const unsigned idx_pos = pos[idx];
    assert (idx_pos == i);
    unsigned child_pos = HEAP_CHILD (idx_pos);
    unsigned parent_pos = HEAP_PARENT (child_pos);
    assert (parent_pos == idx_pos);
    if (child_pos < end) {
      unsigned child = stack[child_pos];
      assert (score[idx] >= score[child]);
      if (++child_pos < end) {
        parent_pos = HEAP_PARENT (child_pos);
        assert (parent_pos == idx_pos);
        child = stack[child_pos];
        assert (score[idx] >= score[child]);
      }
    }
  }
}

#endif

void yals_resize_heap (Yals *yals,heap *heap, unsigned new_size) {
  const unsigned old_size = heap->size;
  if (old_size >= new_size)
    return;
  LOG ("resizing %s heap from %u to %u",
       (heap->tainted ? "tainted" : "untainted"), old_size, new_size);

  heap->pos = yals_nrealloc (heap->pos, old_size, new_size,
                               sizeof (unsigned));
  if (heap->tainted) {
    heap->score = yals_nrealloc (yals, heap->score, old_size, new_size,
                                   sizeof (double));
  } else {
    if (old_size)
      DELN (heap->score, old_size);
    heap->score = yals_calloc (yals, new_size, sizeof (double));
  }
  heap->size = new_size;
#ifdef CHECK_HEAP
  yals_check_heap (heap);
#endif
}

void yals_rescale_heap (Yals *yals,heap *heap, double factor) {
  LOG ("rescaling scores on heap with factor %g", factor);
  double *score = heap->score;
  for (unsigned i = 0; i < heap->vars; i++)
    score[i] *= factor;
#ifndef NDEBUG
  yals_check_heap (heap);
#endif
}

void yals_enlarge_heap (Yals *yals,heap *heap, unsigned new_vars) {
  const unsigned old_vars = heap->vars;
  assert (old_vars < new_vars);
  assert (new_vars <= heap->size);
  const size_t delta = new_vars - heap->vars;
  memset (heap->pos + old_vars, 0xff, delta * sizeof (unsigned));
  heap->vars = new_vars;
  if (heap->tainted)
    memset (heap->score + old_vars, 0, delta * sizeof (double));
  LOG ("enlarged heap from %u to %u", old_vars, new_vars);
}

#ifndef NDEBUG

static void dump_heap (heap *heap) {
  for (unsigned i = 0; i < SIZE (heap->stack); i++)
    printf ("heap.stack[%u] = %u\n", i, PEEK (heap->stack, i));
  for (unsigned i = 0; i < heap->vars; i++)
    printf ("heap.pos[%u] = %u\n", i, heap->pos[i]);
  for (unsigned i = 0; i < heap->vars; i++)
    printf ("heap.score[%u] = %g\n", i, heap->score[i]);
}

void yals_dump_heap (heap *heap) { dump_heap (heap); }

#endif
