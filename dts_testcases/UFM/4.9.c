#include <stdlib.h>
void myfree_4_9(char * p) {
	free(p);
}
int foo_4_9() {
    char *f[10];
	f[0] = (char*)malloc(sizeof(char));
	myfree_4_9(f[0]);
	*(f[0]) = 1;
	return 0;
}
