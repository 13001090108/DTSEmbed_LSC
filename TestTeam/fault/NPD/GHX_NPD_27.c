#include <string.h>

int ghx_npd_27_f27 ()
{
  char *s1 = NULL;
  char *s2=NULL;
  int ptr;
  ptr=strcmp (s1,s2) ;//DEFECT

  return 0;
}

