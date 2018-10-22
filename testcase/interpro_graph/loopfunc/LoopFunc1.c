#include <stdio.h>
int i=0;

void c(){
	void a();
	printf("c!\n");
	while(i++<5)
		a();
}

void b(){
	printf("b!\n");
	c();
}

void a(){
	printf("a!\n");
	if(i<5)
		b();
}

int main(){
	a();
	printf("hello world!\n");
	return 0;
}
