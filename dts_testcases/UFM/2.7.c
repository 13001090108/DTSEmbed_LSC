#include <stdlib.h>
struct A_2_7 {
	char *f;
};
int foo_2_7(int i, int j) {
	struct A_2_7 a;
	a.f = (char*)malloc(sizeof(char));
	free(a.f);
	*(a.f) = 'a';
	if (a.f) ;
	return 0;
}
