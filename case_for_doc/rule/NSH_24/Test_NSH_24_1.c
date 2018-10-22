#include"stdio.h"
fun(int a, int b, int c,int d,int e)
{
	int* t;
	int* p; 
	p = (int*)malloc(sizeof(int)*100); 
	t = (int*)malloc(sizeof(int)*100); 
	free(p);
	free(t); 
	p = NULL;
	int r = t[0];
	if(t!=NULL){
		t = NULL;
	}	
	if(p==NULL) return;
	for(;;){
		break;
	}
	return;
}