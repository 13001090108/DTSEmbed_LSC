#include <string.h>
#include <stdlib.h>

#define SIZE 10

char *g_ptr;

void func2(bool);

void func1(bool flag)
{
	char buf[] = "This is a long string";

	func2(flag);
	strncpy(g_ptr, buf, strlen(buf)); //DEFECT
}

void func2(bool flag)
{
	if (flag) {
		g_ptr = new char[SIZE];
	} else {
		g_ptr = (char*)malloc(SIZE * sizeof(char));
	}
}