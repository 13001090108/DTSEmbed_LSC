#include <stdlib.h>
#include <time.h>
void foo_8_6(int a) {
}
void bar_8_6() {
	srand(time(0));
	foo_8_6(10 % rand());
}
