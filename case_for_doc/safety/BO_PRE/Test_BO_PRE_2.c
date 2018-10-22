#include <string.h>
void f1(int a) 
{
char buffer2[15]="1234567890",buffer1[10];
strncat (buffer1,buffer2,a);//DEFECT"
}                                                                  
void f2()                                                            
{                                                                    
int a=11;                                                          
f1(a);                                                              
}
