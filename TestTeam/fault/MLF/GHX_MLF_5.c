#include <malloc.h>
#include <stdio.h>
void ghx_mlf_5_f5()
{
char *p = (char*)malloc(100);

delete(p); //DEFECT
  
}
void ghx_mlf_5_f1(int i)
{
char *p=(char*)malloc(100);
free(p);
if(i>0)
free(p);//DEFECT
}
void ghx_mlf_5_f2()
{
char *p = (char*)malloc(100);

free(p); //FP
  
}
