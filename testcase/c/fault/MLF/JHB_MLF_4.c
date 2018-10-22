#include <malloc.h>
#include <stdio.h>
void jhb_mlf_4_f1(unsigned int i)
{
char *p = (char*)malloc(12);
if(i>0) {
free(p); 
}
return;   //FT
}
