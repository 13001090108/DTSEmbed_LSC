#include <string.h>
#include <stdlib.h>

#define SIZE 10

char g_array[SIZE];

char* func2(bool);
void func3(bool, char*);

void func1(bool flag)
{
	char *ptr;

	ptr = func2(flag);
	strcpy(g_array, ptr); //DEFECT
	func3(flag, ptr);
}

char* func2(bool flag)
{
	char *ptr;

	if (flag) {
		ptr = (char*)malloc(2 * SIZE * sizeof(char));
	} else {
		ptr = new char[SIZE+1];
	}
	return ptr;
}

void func3(bool flag, char *ptr)
{
	if (flag) {
		free(ptr);
	} else {
		delete[] ptr;
	}
}