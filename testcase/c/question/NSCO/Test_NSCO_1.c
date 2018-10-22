#include <stdio.h>
#include <string.h>

void f_NSCO_2(char name[])
{
     if(name==NULL){
         return;
     }
     
     if(strcmp(name,"seed") | !strcmp(name,"kira")){// NSCO,defect
         printf("OK");
     }
     return;
}
