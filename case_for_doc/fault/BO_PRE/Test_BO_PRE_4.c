typedef struct{
	char array[10];
} aa; 
aa g;
void func2(char*);                                     
void func1()                 
{                        
	char *str = "This is a too long string";                       
	func2(str); //DEFECT        
}                                                     
void func2(char *ptr)        
{                            
	strcpy(g.array, ptr);
}