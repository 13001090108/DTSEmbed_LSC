#include <stdlib.h>
void myfree_4_10(char *p) {
	free(p);
}
void foo_4_10(char * p) {
	myfree_4_10(p);
}
int bar_4_10() {
    char *f[10];
	f[0] = (char*)malloc(sizeof(char));
	//myfree_4_10(f);
	foo_4_10(f[0]);
	* f[0] = 1;
	return 0;
}
