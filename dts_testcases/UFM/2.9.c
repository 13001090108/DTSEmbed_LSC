#include <stdlib.h>
void myfree_2_9(char *f) {
	free(f);
}
struct A_2_9 {
	char *f;
};
int foo_2_9() {
	struct A_2_9 a;
	a.f = (char*)malloc(sizeof(char));
	myfree_2_9(a.f);
	*a.f = 'a';
	return 0;
}
