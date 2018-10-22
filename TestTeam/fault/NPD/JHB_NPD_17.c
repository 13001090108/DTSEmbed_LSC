#include <stdio.h>
int jhb_npd_14_f1(void)
{
	FILE *stream;
	stream = fopen("DUMMY.FIL", "r");
	fgetc(stream);
	if (feof(stream))     //DEFECT
		printf("We have reached end-of-file\n");
	fclose(stream);
	return 0;
}