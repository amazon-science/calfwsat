#ifndef MAIN_H_INCLUDED
#define MAIN_H_INCLUDED

#include "../../yals.c"
#include "../../yils.h"
#include "../../yils_card.h"

#include <assert.h>
#include <stdio.h>
#include <signal.h>

struct { size_t allocated, max; } mem;


void die (const char * fmt, ...) {
  va_list ap;
  fflush (stdout);
  printf ("*** error: ");
  va_start (ap, fmt);
  vprintf (fmt, ap);
  va_end (ap);
  fputc ('\n', stdout);
  fflush (stdout);
  exit (1);
}

#define INCMAIN(BYTES) \
do { \
  mem.allocated += (BYTES); \
  if (mem.allocated > mem.max) mem.max = mem.allocated; \
} while (0)

#define DECMAIN(BYTES) \
do { \
  assert (mem.allocated >= (BYTES)); \
  mem.allocated -= (BYTES); \
} while (0)

void * mymalloc (void * dummy, size_t bytes) {
  void * res = malloc (bytes);
  if (!res) die ("out of memory during 'malloc'");
  (void) dummy;
  INCMAIN (bytes);
  return res;
}

void myfree (void * dummy, void * ptr, size_t bytes) {
  DECMAIN (bytes);
  free (ptr);
}

void * myrealloc (void * dummy, void * ptr, size_t o, size_t n) {
  void * res;
  DECMAIN (o);
  res = realloc (ptr, n);
  if (!res) die ("out of memory during 'realloc'");
  INCMAIN (n);
  return res;
}

void (*sig_int_handler)(int);
void (*sig_segv_handler)(int);
void (*sig_abrt_handler)(int);
void (*sig_term_handler)(int);

void resetsighandlers (void) {
  (void) signal (SIGINT, sig_int_handler);
  (void) signal (SIGSEGV, sig_segv_handler);
  (void) signal (SIGABRT, sig_abrt_handler);
  (void) signal (SIGTERM, sig_term_handler);
}

void caughtsigmsg (int sig) {
  printf ("c\nc [yalsat] CAUGHT SIGNAL %d\nc\n", sig);
  fflush (stdout);
}

int catchedsig;

void catchsig (int sig) {
  if (!catchedsig) {
    fputs ("c s UNKNOWN\n", stdout);
    fflush (stdout);
    catchedsig = 1;
    caughtsigmsg (sig);
  }
  resetsighandlers ();
  raise (sig);
}

void setsighandlers (void) {
  sig_int_handler = signal (SIGINT, catchsig);
  sig_segv_handler = signal (SIGSEGV, catchsig);
  sig_abrt_handler = signal (SIGABRT, catchsig);
  sig_term_handler = signal (SIGTERM, catchsig);
}

#endif