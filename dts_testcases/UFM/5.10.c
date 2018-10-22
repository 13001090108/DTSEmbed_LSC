#include <stdlib.h>
char *foo_5_10(char *p) {
	free(p);
	return p;
}
int bar_5_10(int i) {
	char *p = (char *)malloc(sizeof(char));
	if (i || *foo_5_10(p) == 'a') ;
	return 0;
}
