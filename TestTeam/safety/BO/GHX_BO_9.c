#include <stdio.h>
int ghx_BO_9_f9()
{
char fixed_buf[10];
sprintf(fixed_buf,"Very long format string\n");//DEFECT
return 0;
}