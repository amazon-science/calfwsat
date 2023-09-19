#include "main.h"

#ifdef NDEBUG
#undef NDEBUG
#endif

#include <assert.h>
#include <stdio.h>

/*
  Unit test to ensure unit propagation [yals_preprocess ()] is working
  correctly for both clauses and cardinality constraints.

  Units found in the call to yals_preprocess are stored in the stack
  yals->trail. We loop through the stack to check which literals
  have been propagated. 

  INPUT KNF:
  p knf 6 5
  1 2 0
  k 2 1 2 -3 0
  -2 0
  k 2 2 3 4 5 0
  -5 6 0

  v 1 -2 -3 4 5 6 0
*/
int main () {
  Yals * yals;

  int temp_iter;
  yals = yals_new_with_mem_mgr (0, mymalloc, myrealloc, myfree);

  yals_srand (yals, 0);

  yals_setprefix (yals, "c ");
  setsighandlers ();

  // ****** adding constraints

  yals_add (yals, 1); // literal
  yals_add (yals, 2); // literal
  yals_add (yals, 0); // end normal clause

  yals_card_add (yals, 2, 1); // bound
  yals_card_add (yals, 1, 0); // literal
  yals_card_add (yals, 2, 0); // literal
  yals_card_add (yals, -3, 0); // literal
  yals_card_add (yals, 0, 0); // end cardinality constraint

  yals_add (yals, -2); // unit
  yals_add (yals, 0); // end normal clause

  yals_card_add (yals, 2, 1); // bound
  yals_card_add (yals, 2, 0); // literal
  yals_card_add (yals, 3, 0); // literal
  yals_card_add (yals, 4, 0); // literal
  yals_card_add (yals, 5, 0); // literal
  yals_card_add (yals, 0, 0); // end cardinality constraint
  
  yals_add (yals, -5); // literal
  yals_add (yals, 6); // literal
  yals_add (yals, 0); // end normal clause

  // ****** run unit propagation algorithm

  yals_preprocess (yals); 


  // ****** print results

  printf ("\nUNIT TEST: UNIT PROPAGATION\n");

  printf ("\nExpected units: 1 -2 -3 4 5 6\n");
  printf ("Note, unit propagation allows duplicates\nif duplicate units are propagated from same watch lists.\n\n");

  printf("Output after running unit propagation:\n");
  // check the trail, see what has been assigned
  for (temp_iter = 0; temp_iter < COUNT (yals->trail); temp_iter++) {
    printf("unit %d\n", PEEK (yals->trail, temp_iter));
  }

  return 0;
}