#include <stdio.h>

void func()
{
	FILE *fp;

	fp = fopen("myfile.txt", "w");
	setvbuf(fp, NULL, _IOFBF, 1024);//DEFECT
}