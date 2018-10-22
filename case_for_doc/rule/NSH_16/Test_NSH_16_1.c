#include"stdio.h"
int get(int a)
{	
	return a;
}
void fun(int a)
{
	if(a != 0) a++; 
	if(a >10) a++;
	if(a && a+1 > 10)
		return;
	if(get(a))
		 a = get(a);
	 while(a){
		a--;
	}
	while(!a && a+1>0)
	{
		a++;
	}
	for(int i = 10,j=10;i&&j;i--);
	}
	
int* get2(int a)
{
	return &a;
}
void fun2(int* a)
{
	if(a != NULL) a++; 	
	if(a && *a+1 > 10)
		return;
		if(get(a))
			 a = get(a);
	while(a){
		a--;
	}
	while(!a && *a+1>0)
	{
		 a++;
	}
	for(int *i = a;i;i--);
}
