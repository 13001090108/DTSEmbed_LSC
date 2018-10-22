#include <stdio.h>
int ghx_npd_19_f19(void)
{
   FILE *fp;
   fp = fopen("perror.dat", "r");

      perror(fp);//DEFECT
   return 0;
}

