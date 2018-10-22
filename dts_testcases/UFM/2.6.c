#include <stdlib.h>
struct A_2_6 {
	char *f;
};
int foo_2_6(int i, int j) {
	struct A_2_6 a;
	a.f = (char*)malloc(sizeof(char));
	free(a.f);
	if (i || a.f);
	*(a.f) = 'a';
	return 0;
}
