#include <string.h>
#include <stdio.h>
#include <stdlib.h>
#include <time.h>

#define MAXSIZE 1024

void main(void)
{
	char *str1 = NULL;
	char *str2 = new char[11];

	strcoll(NULL, str2); //DEFECT
	strcpy(NULL, str2); //DEFECT
	strcspn(NULL, str2); //DEFECT
	strftime(NULL, MAXSIZE, NULL, NULL); //DEFECT
	strlen(NULL); //DEFECT
	strncat(NULL, str2, 5); //DEFECT
	strncmp(NULL, str2, 5); //DEFECT
	strncpy(NULL, str2, 4); //DEFECT
	strpbrk(NULL, str2); //DEFECT
	strrchr(NULL, 's'); //DEFECT
	strspn(NULL, str2); //DEFECT
	strstr(NULL, str2); //DEFECT
	strtod(NULL, &str2); //DEFECT
	strtok(NULL, str2); //DEFECT
	strtol(NULL, &str2, 2); //DEFECT
	strtoul(NULL, &str2, 2); //DEFECT
	strxfrm(NULL, str2, 5); //DEFECT


	FILE *fp = tmpfile();
	fputc((int)'a', NULL); //DEFECT
	ungetc('c', NULL); //DEFECT
	vfprintf(fp, NULL, NULL); //DEFECT
	vprintf(NULL, NULL); //DEFECT
	vsprintf(NULL, NULL, NULL); //DEFECT
	wcstombs(NULL, NULL, 0); //DEFECT
	wctomb(NULL, 0); //DEFECT

	return;
}