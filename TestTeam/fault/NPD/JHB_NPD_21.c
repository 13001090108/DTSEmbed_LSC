#include <string.h>
#include <stdio.h>
int jhb_npd_21_f1(void)
{
	FILE *stream;
	char string[] = "This is a test";
	fpos_t filepos;
	stream = fopen("DUMMY.FIL", "w+");
	fwrite(string, strlen(string), 1, stream);
	fgetpos(stream, &filepos);             //DEFECT
	printf("The file pointer is at byte %ld\n", filepos);
	fclose(stream);
	return 0;
}
