#include <stdlib.h>
char *foo_5_5(char *p) {
	free(p);
	return p;
}
int bar_5_5(int i) {
	char *p = (char *)malloc(sizeof(char));
	if (i == 1);
	*foo_5_5(p) = 'a';
	return 0;
}
