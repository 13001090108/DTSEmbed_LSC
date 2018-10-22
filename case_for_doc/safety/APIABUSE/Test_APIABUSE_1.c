#include <stdlib.h>
#include <stdio.h>
#include <time.h>

void ghx_api_9_f9( void )
{
   int i;
srand( (unsigned)time( NULL ) );//DEFECT
i=rand()%100;//DEFECT
printf("%d\n",i);
}