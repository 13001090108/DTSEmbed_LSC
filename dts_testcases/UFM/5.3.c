#include <stdlib.h>
char *foo_5_3() {
	char *p = (char *)malloc(sizeof(char));
	free(p);
	return p;
}
int bar_5_3(int i) {
	if (i == 1 || foo_5_3())
		*foo_5_3() = 'a';
	return 0;
}
