#include <stdio.h>
int ghx_npd_24_f24(void)
{
   char *file=NULL; 
  remove(file); //DEFECT
   return 0;
}




