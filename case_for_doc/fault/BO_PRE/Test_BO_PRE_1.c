#include <stdio.h>       
void f1(int a)                    
{                                 
	char buffer1[a];                 
	scanf("%12s",buffer1);//DEFECT   
}                                 
void f2()                         
{                                 
	int a=10;                        
	f1(a);//DEFECT                   
}