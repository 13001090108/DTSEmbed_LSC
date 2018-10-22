#include <stdlib.h>
void jhb_npd_10_f1(char* str){
	float f;
    f=atof(str);      //DEFECT
}
int jhb_npd_10_f2()
{
	float t;
	char *str="12345.67";
	t=atof(str);       //FT
	return 0;
}
