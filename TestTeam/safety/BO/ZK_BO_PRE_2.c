#include <string.h>

char g_array[10];

void func2(int, char*, bool);
void func3(int, char*);

void func1(bool flag)
{
	char *str = "This is a too long string";
	int len = strlen(str);

	func2(len, str, flag); //DEFECT
}

void func2(int len, char *ptr, bool flag)
{
	if (flag) {
		strcpy(g_array, ptr);
	} else {
		func3(len, ptr);
	}
}

void func3(int len, char *ptr)
{
	strncpy(g_array, ptr, len);
}