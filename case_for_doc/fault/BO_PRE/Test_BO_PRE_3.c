void f1(char* p)                    
{                                 
	scanf("%12s",p); 
}                                 
void f2()                         
{                                 
	typedef struct{
		char x[10];
	} aa;
	aa a;
	char* p=a.x;
	f1(p);//DEFECT
}