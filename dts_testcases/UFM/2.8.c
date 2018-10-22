#include <stdlib.h>
struct A_2_8 {
	char *f;
};
int foo_2_8(int i, int j) {
	struct A_2_8 a;
	a.f = (char*)malloc(sizeof(char));
	free(a.f);
	*(a.f) = 'a';
	if (i || a.f) ;
	return 0;
}
