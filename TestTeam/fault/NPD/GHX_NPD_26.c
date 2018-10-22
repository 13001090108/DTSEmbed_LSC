#include <string.h>

int ghx_npd_26_f26 ()
{
  char *str = NULL;
  char * pch;
  int i=1;
  pch=strchr(str,'s');//DEFECT
  pch[i]=0;//DEFECT
  return 0;
}

