#include <string.h>                                               
                                                                   
void f1(char *p) 
{
char buffer1[10];
strcpy (buffer1,p);
}                                                                  
void f2()                                                            
{                                                                    
char buffer[15],*p=buffer;                                          
strcpy (p,"1234567890");                                           
f1(p);//DEFECT"                                                      
} 
