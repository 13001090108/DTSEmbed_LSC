#include <stdlib.h>        
void f1(int *p)            
{                          
	int i = *p;           
}                          
int* f2()                  
{                          
	return NULL;          
}                          
void f()                   
{                          
	f1(f2());//DEFECT     
}