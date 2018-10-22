#include <stdlib.h>
struct A_2_4 {
	char *f;
};
int foo_2_4(int i, int j) {
	struct A_2_4 a;
	a.f = (char*)malloc(sizeof(char));
	if (i)
		free(a.f);
	if (j)
		*(a.f) = 'a';
	return 0;
}
