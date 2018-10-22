#include <stdio.h>

int (*funP)();
int b();
int c();
int d();
int h();
extern int f();
extern int g();

void a()
{
	b();b();
	c();
	d();
	funP=&f;
	funP();
}

int b()
{
	c();
	d();
}

int c()
{
	d();
}

int d()
{
	h();
}

int h(){
	int i;
	i++;
	return i;
}

int main()
{
	a();
	f();
	
	funP=&g;
	funP();
	(*funP)();
	
	funP=&d;
	funP();
	(*funP)();
	printf("OK!\n");
	return 0;
}