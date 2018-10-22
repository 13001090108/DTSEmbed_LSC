#include <stdlib.h>
char *foo_5_9(char *p) {
	free(p);
	return p;
}
int bar_5_9(int i) {
	char *p = (char *)malloc(sizeof(char));
	if (*foo_5_9(p) == 'a') ;
	return 0;
}
