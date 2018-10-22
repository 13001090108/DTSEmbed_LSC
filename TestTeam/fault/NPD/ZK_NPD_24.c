#include <stdio.h>
#include <stdarg.h>

void zk_npd_24_f1(char *format, ...)
{
	char *buf = NULL;
	va_list args;

	va_start(args, format);
	vsprintf(buf, format, args); //DEFECT
	va_end(args);
	return;
}

void zk_npd_24_f2(char *buf, char *format, ...)
{
	char *ptr;
	va_list args;

	if (buf == NULL || format == NULL)
		return;
	va_start(args, format);
	ptr = va_arg(args, char *);
	if (ptr == NULL) {
		va_end(args);
		return;
	}
	vsprintf(buf, format, args); //FP
	va_end(args);
	return;
}