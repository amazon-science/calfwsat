/*-------------------------------------------------------------------------
This is an AWS-ARG-ATS-Science intern project developed by the intern
Joseph Reeves (jsreeves@) and manager Benjamin Kiesl (benkiesl@).

This code extends the solver yal-lin (Md Solimul Chowdhury, Cayden Codel, Marijn Heule), found at the [Github repository](https://github.com/solimul/yal-lin), which itself extended the solver [yalsat](https://github.com/arminbiere/yalsat) (Armin Biere).
-------------------------------------------------------------------------*/

#include "config.h"
#include "cflags.h"

#define YALSINTERNAL
#include "yils_card.h"

#include <stdio.h>

#define MSG(STR) printf ("%s%s\n", prefix, (STR))

void yals_banner (const char * prefix) {
  MSG ("Version " YALS_VERSION " " YALS_ID);
  MSG ("Copyright (C) 2013-2016 by Armin Biere, JKU, Linz, Austria.");
  MSG ("Released " YALS_RELEASED);
  MSG ("Compiled " YALS_COMPILED);
  MSG (YALS_OS);
  MSG ("CC " YALS_CC);
  MSG ("CFLAGS " YALS_CFLAGS);
}

const char * yals_version () { return YALS_VERSION " " YALS_ID; }
