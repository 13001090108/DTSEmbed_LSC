#include <stdlib.h>   
int* p;                 
void f(){               
	*p=1;                 
}                       
void f1(){              
    f();               
}                       
void f2(){              
   p=(int*)malloc(1);   
   free(p);             
   f1(); //defect       
}