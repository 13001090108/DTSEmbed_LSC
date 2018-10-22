#include <stdlib.h>
#include <string.h>

#define SIZE 10

char *g_ptr;

void func2(bool, int&);

void func1(bool flag)
{
	int len;
	char *buf;

	buf = (char*)malloc(SIZE * sizeof(char));
	func2(flag, len);
	strncpy(buf, g_ptr, len); //DEFECT
	free(buf);
}

void func2(bool flag, int &var)
{
	if (flag) {
		var = 2 * SIZE;
		g_ptr = new char[var];
	} else {
		var = 0;
	}
}