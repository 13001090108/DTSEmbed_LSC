#include <string.h>          
char g_array[10];            
void func2(char*);           
void func1()                 
{                            
	char *str = "This is a too long string";                        
	func2(str); //DEFECT        
}                                                         
void func2(char *ptr)        
{                            
	strcpy(g_array, ptr);       
}