#include "stdlib.h"
void ghx_mlf_4_f4(int i)
{
	int a[5]={4,4,4,4,4,};
	int* m4=NULL;
	if(i>0){
		m4=a;
	}else{
		m4=(int*)malloc(100);
	}
	if(i>0)//DEFECT
	{
		free(m4);
	}
}
void ghx_mlf_4_f5(int i)
{
	int a[5]={4,4,4,4,4,};
	int* m4=NULL;
	if(i>0){
		m4=a;
	}else{
		m4=(int*)malloc(100);
	}
	if(i<0)//FP
	{
		free(m4);
	}
}

