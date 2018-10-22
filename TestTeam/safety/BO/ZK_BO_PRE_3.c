#include <string.h>

char g_array[10];

void func2(int, char*, bool);
void func3(int, int, char*);

void func1(bool flag)
{
	char *str = "This is a too long string";

	func2(0, str, flag); //DEFECT
}

void func2(int n, char *ptr, bool flag)
{
	if (flag) {
		return;
	} else {
		func3(0, 0, ptr);
	}
}

void func3(int n, int m, char *ptr)
{
	strcat(g_array, ptr);
}