#include <stdlib.h>
char *f;
void myfree_1_9() {
	free(f);
}
int foo_1_9() {
	f = (char*)malloc(sizeof(char));
	myfree_1_9();
	*f = 'a';
	return 0;
}
