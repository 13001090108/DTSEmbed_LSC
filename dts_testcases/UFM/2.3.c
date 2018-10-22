#include <stdlib.h>
struct A_2_3 {
	char *f;
};
int foo_2_3(int i) {
	struct A_2_3 a;
	a.f = (char*)malloc(sizeof(char));
	free(a.f);
	if (a.f || i)
		*(a.f) = 'a';
	return 0;
}
