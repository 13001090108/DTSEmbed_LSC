#include <stdio.h>
int ghx_oob_8_f8()
{
char buffer[68];
int b=4;
int a=1;
buffer[b]=1;
b+=34;
if(a)
{
 if(b)
   b+=34;
}

buffer[b]=2;//DEFECT
return 0;
}
