#include <stdio.h>
#include <stdarg.h>

void zk_npd_23_f1(char *format, ...)
{
	va_list args;
	va_start(args, format);
	vprintf(format, args); //DEFECT
	va_end(args);
	return;
}

void zk_npd_23_f2(char *format, ...)
{
	char *ptr;

	if (format == NULL)
		return;

	va_list args;
	va_start(args, format);
	ptr = va_arg(args, char *);
	if (ptr = NULL) {
		va_end(args);
		return;
	}
	vprintf(format, args); //FP
	va_end(args);
	return;
}