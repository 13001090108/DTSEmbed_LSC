#include <stdlib.h>
int* p;
void f(){
	 free(p);
}
void f1(){
     f();
}
void f2(){
   p=(int*)malloc(1);
   f1(); 
   *p=1; //defect
}
