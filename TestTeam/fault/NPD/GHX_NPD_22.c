#include <stdio.h>
#include <string.h>

int ghx_npd_22_f22 ()
{
  char *str=NULL;
  strcat (str,"strings ");//DEFECT

  return 0;
}


int ghx_npd_22_f21 ()
{
  char str[80];
  strcpy (str,"these ");//FP
  strcat (str,"strings ");//FP
  strcat (str,"are ");//FP
  strcat (str,"concatenated.");//FP
  puts (str);
  return 0;
}

