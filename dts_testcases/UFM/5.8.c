#include <stdlib.h>
char *foo_5_8() {
	char *p = (char *)malloc(sizeof(char));
	free(p);
	return p;
}
int bar_5_8(int i) {

	*foo_5_8() = 'a';
	if (i == 1 || foo_5_8());
	return 0;
}
