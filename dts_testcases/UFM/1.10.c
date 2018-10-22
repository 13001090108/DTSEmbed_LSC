#include <stdlib.h>
void myfree_1_10(char *f) {
	free(f);
}
void bar_1_10(char * f) {
	myfree_1_10(f);
}
int main() {
    char *f;
	f = (char*)malloc(sizeof(char));
	bar_1_10(f);
	*f = 'a';
	return 0;
}
