#include <stdio.h>
#include <stdarg.h>

void zk_npd_22_f1(FILE *fp, char *format, ...)
{
	va_list args;
	va_start(args, format);
	vfprintf(fp, format, args); //DEFECT
	va_end(args);
	return;
}

void zk_npd_22_f2()
{
	FILE *stream = NULL;

	zk_npd_22_f1(stream, NULL, NULL);
	return;
}

void zk_npd_22_f3(FILE *fp, char *format, ...)
{
	char *ptr;

	if (fp == NULL || format == NULL)
		return;

	va_list args;
	va_start(args, format);
	ptr = va_arg(args, char *);
	if (ptr == NULL) {
		va_end(args);
		return;
	}
	vfprintf(fp, format, args); //FP
	va_end(args);
	return;
}