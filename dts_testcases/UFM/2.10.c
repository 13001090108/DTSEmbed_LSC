#include <stdlib.h>
void myfree_2_10(char *f) {
	free(f);
}
void foo_2_10(char *p) {
	myfree_2_10(p);
}
struct A_2_10 {
	char *f;
};
int main() {
	struct A_2_10 a;
	a.f = (char*)malloc(sizeof(char));
	//myfree_2_10(f);
	foo_2_10(a.f);
	*a.f = 'a';
	return 0;
}
