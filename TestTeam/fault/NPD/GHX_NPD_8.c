#include <time.h>
int ghx_npd_8_f8 ()
{
  time_t * rawtime=NULL;
  struct tm * timeinfo;
  timeinfo =localtime (rawtime );//DEFECT
  
  return 0;
}


int ghx_npd_8_f9 ()
{
  time_t rawtime;
  struct tm * timeinfo;

  time ( &rawtime );
  timeinfo = localtime ( &rawtime ); //FP
  return 0;
}
