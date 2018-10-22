#include <stdio.h>
#include <stdlib.h>

int ghx_npd_10_f10 ()
{
  int i;
  char * buffer;
  scanf ("%d", &i);

  buffer = (char*) malloc (i+1);

  buffer[i]='\0';//DEFECT
  printf ("%s\n",buffer);
  free (buffer);

  return 0;
}


int ghx_npd_10_f9 ()
{
  int i;
  char * buffer;
  scanf ("%d", &i);

  buffer = (char*) malloc (i+1);
  if (buffer==NULL) exit (1);

else
{
  buffer[i]='\0';//FP

  printf ("%s\n",buffer);
  free (buffer);
}
  return 0;
}

