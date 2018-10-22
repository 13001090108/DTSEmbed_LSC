#include <stdlib.h>
char *foo_5_4() {
	char *p = (char *)malloc(sizeof(char));
	free(p);
	return p;
}
int bar_5_4(int i) {
	if (i == 1)
		foo_5_4();
	if (i == 2)
		*foo_5_4() = 'a';
	return 0;
}
