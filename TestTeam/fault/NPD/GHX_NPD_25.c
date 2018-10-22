#include <stdio.h>

int ghx_npd_25_f25 ()
{
  char *s =NULL;
  char str [20];
  int i;

  sscanf (s,"%s %*s %d",str,&i);//DEFECT
  printf ("%s -> %d\n",str,i);
  
  return 0;
}

