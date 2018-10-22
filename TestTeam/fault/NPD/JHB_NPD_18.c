#include <stdio.h>
int jhb_npd_18_f1(void){
	FILE *stream;
	stream = fopen("DUMMY.FIL", "w");
	if (ferror(stream))       //DEFECT
	{
		printf("Error reading from DUMMY.FIL\n");
//		clearerr(stream);
	}
//	fclose(stream);
	return 0;
}
