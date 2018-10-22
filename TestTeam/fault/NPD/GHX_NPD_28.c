#include <stdio.h>

void func()
{
	FILE *fp;

	fp = fopen("myfile.txt", "w");
	rewind(fp); //DEFECT
}