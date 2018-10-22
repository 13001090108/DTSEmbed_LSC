#include <stdlib.h>
char *foo_5_6() {
	char *p = (char *)malloc(sizeof(char));
	free(p);
	return p;
}
int bar_5_6(int i) {

	if (i == 1 || foo_5_6());
	*foo_5_6() = 'a';
	return 0;
}
