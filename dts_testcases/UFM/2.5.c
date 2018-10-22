#include <stdlib.h>
struct A_2_5 {
	char *f;
};
int foo_2_5(int i, int j) {
	struct A_2_5 a;
	a.f = (char*)malloc(sizeof(char));
	free(a.f);
	if (a.f) ;
	*(a.f) = 'a';
	return 0;
}
