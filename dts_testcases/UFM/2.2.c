#include <stdlib.h>
struct A_2_2 {
	char *f;
};
int foo_2_2(int s) {
	struct A_2_2 a;
	a.f = (char*)malloc(sizeof(char));
	free(a.f);
	if (s == 1)
		*(a.f) = 'a';
	return 0;
}
