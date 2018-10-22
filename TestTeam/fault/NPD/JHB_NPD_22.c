#include <string.h>
#include <stdio.h>
int jhb_npd_22_f1(void)
{
	FILE *stream;
	char string[] = "This is a test";
	char msg[20];
	stream = fopen("DUMMY.FIL", "w+");
	fwrite(string, strlen(string), 1, stream);
	fseek(stream, 0, SEEK_SET);
	fgets(msg, strlen(string)+1, stream);  //DEFECT
	printf("%s", msg);
	fclose(stream);
	return 0;
} 
