#include "stdio.h"
void ghx_dc_2_f2()
{
  int i=5;
  while(i)//DEFECT
  {
   printf("abc");
  }
return;
}
void ghx_dc_2_f3()
{
 while(111)//DEFECT
 {
 printf("cba");
 }
return;
}
