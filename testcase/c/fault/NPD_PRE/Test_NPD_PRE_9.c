#include <stdio.h>
#include <string.h>

int ghx_npd_22_f22 ()
{
  char *str=NULL;
  strcat (str,"strings ");//DEFECT

  return 0;
}

}
