#include <stdio.h>

int g();
int h();

int f()
{
	printf("Function f() in Callee.c!\n");
	g();
	h();
}

int g()
{
	h();
}

int h()
{

}