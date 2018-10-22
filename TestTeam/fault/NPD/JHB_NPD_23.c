#include <stdio.h>
int jhb_npd_23_f1()
{
	FILE *fp; 
	fp = fopen("myfile.ly","w"); 
	fclose(fp);   //DEFECT
	return 0;
}
