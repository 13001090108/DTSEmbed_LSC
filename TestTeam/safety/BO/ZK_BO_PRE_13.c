#include <wchar.h>

#define SIZE 10

wchar_t g_buf[SIZE];

void func2(wchar_t*);

void func1()
{
	wchar_t ptr[SIZE+1];

	func2(ptr); //DEFECT
}

void func2(wchar_t *ptr)
{
	wmemcpy(g_buf, ptr, sizeof(ptr));
}