#include <stdio.h>

int ghx_npd_23_f23 ()
{
  char *buffer =NULL;
  int n, a=5, b=3;
  n=sprintf (buffer, "%d plus %d is %d", a, b, a+b);//DEFECT

  return 0;
}