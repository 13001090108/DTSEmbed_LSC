#include <stdio.h>
#include <math.h>
int ghx_npd_17_f17() 
{ 
double fraction;
double *integer=NULL; 
double number = 100000.567; 
fraction = modf(number, integer); //DEFECT
return 0; 
} 

int ghx_npd_17_f16() 
{ 
double fraction, integer; 
double number = 100000.567; 
fraction = modf(number, &integer); //FP
printf("The whole and fractional parts of %lf are %lf and %lf\n", 
number, integer, fraction); 

return 0; 
} 


 

