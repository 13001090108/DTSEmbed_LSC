#include <time.h>

#define MAXSIZE 1024

void zk_npd_4_f1()
{
	char *ptr = NULL;
	char *format = NULL;
	struct tm *timeptr = NULL;

	strftime(ptr, MAXSIZE, format, timeptr); //DEFECT
	return;
}

void zk_npd_4_f2()
{
	char ptr[MAXSIZE];
	time_t rawtime;
	struct tm *timeptr;

	time(&rawtime);
	timeptr = localtime(&rawtime);

	strftime(ptr, MAXSIZE, "Time is %c", timeptr); //FP
	return;
}