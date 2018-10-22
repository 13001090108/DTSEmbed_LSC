#include <stdlib.h>
struct A_2_1 {
	char *f;
};
int foo_2_1() {
	struct A_2_1 a;
	a.f = (char*)malloc(sizeof(char));
	free(a.f);
	*(a.f) = 1;
	return 0;
}
