#include <stdio.h>
#include <stdlib.h>
#include <string.h>

int ghx_uckret_2_f2(int argc, char *argv[])
{
int i=0,j=0;
printf("Enter two numbers:\n");
scanf("%d %d", &i, &j);//DEFECT
printf ("Result = %d\n", i / j);
return 0;
}


int ghx_uckret_2_f1(int argc, char *argv[])
{
unsigned int i=0,j=0;
unsigned int result = 0;
printf("Enter two numbers:\n");
result = scanf("%d %d", &i, &j);
if (result != 2)//FP
 {
printf ("Error, you should enter two numbers!\n");      
return 1;
}              
printf ("Result = %d\n", i / j);
return 0;
}