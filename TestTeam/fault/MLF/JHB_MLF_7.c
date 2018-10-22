#include <malloc.h>
#include <stdio.h>
class jhb_mlf_7_c1{
	void f();
};
void jhb_mlf_7_c1::f(){
	int *ptr = malloc(sizeof(int));
	*ptr = 25;
	ptr = malloc(sizeof(int));       //DEFECT
	*ptr = 35;
}
