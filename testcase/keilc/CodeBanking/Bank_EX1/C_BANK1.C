/*------------------------------------------------------------------------------
C_BANK1.C

Copyright 1995-2005 Keil Software, Inc.
------------------------------------------------------------------------------*/

#include <stdio.h>

extern void func2(void);

void func1(void) {
  printf("FUNCTION IN BANK 1 CALLS A FUNCTION IN BANK 2 \n");
  func2();
}
