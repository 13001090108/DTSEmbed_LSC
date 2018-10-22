#include<stdlib.h>
#include<stdio.h>
#define NELEMS(arr) (sizeof(arr) / sizeof(arr[0]))
int numarray[] = {123, 145, 512, 627, 800, 933};
int numeric (const int *p1, const int *p2){
	return(*p1 - *p2);
}
int jhb_npd_13_f1(int key){
int *itemptr;
itemptr = (int *)bsearch (&key, numarray, NELEMS(numarray),
						  sizeof(int), (int(*)(const void *,const void *))numeric);
return (*itemptr) ;     //DEFECT
}

