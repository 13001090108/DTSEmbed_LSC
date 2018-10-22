#include <string.h>
#include <stdio.h>
int jhb_npd_28_f1(void)
{
	FILE *stream;
	char msg[] = "this is a test";
	char buf[20];
	stream = fopen("DUMMY.FIL", "w+");
	fread(buf, strlen(msg)+1, 1,stream);  //DEFECT
	printf("%s\n", buf);
	return 0;
}
