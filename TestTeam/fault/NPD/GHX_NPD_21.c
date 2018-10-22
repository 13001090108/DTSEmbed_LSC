#include <stdio.h>

int ghx_npd_21_f21 ()
{
  char *string = NULL;
  puts (string);//DEFECT
  return 0;
}

int ghx_npd_21_f20()
{
char *string="welcome to beijing";
puts (string);//FP
return 0;
}
