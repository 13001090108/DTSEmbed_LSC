#include <string.h>
#include <stdio.h>
#include <conio.h>
int jhb_npd_20_f1(void)
{
	FILE *stream;
	char string[] = "This is a test";
	char ch;
	stream = fopen("DUMMY.FIL", "w+");
	ch = fgetc(stream);  //DEFECT
	return 0;
}
