#include <time.h>
#include <stdio.h>
int ghx_npd_16_f16()
{
struct tm * timeinfo=NULL;
mktime(timeinfo);//DEFECT
return 0;

}
int ghx_npd_16_f15 ()
{
  time_t rawtime;
  struct tm * timeinfo;
  int year, month ,day;
  char * weekday[] = { "Sunday", "Monday","Tuesday", "Wednesday","Thursday", "Friday", "Saturday"};

  printf ("Enter year: "); scanf ("%d",&year);
  printf ("Enter month: "); scanf ("%d",&month);
  printf ("Enter day: "); scanf ("%d",&day);

  time ( &rawtime );
  timeinfo = localtime ( &rawtime );
  timeinfo->tm_year = year - 1900;
  timeinfo->tm_mon = month - 1;
  timeinfo->tm_mday = day;
  mktime ( timeinfo );//FP

  printf ("That day is a %s.\n", weekday[timeinfo->tm_wday]);
  
  return 0;
}

