#include <string.h>
#include <malloc.h>
void jhb_npd_7_f1(){
	char* p;
	p=(char*)malloc(100);
	memset(p,0,100);      //DEFECT
}
