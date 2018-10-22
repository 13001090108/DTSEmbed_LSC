#include <stdlib.h>
struct A_2_12 {
	char *p;
};
int foo_2_12(int i) {
	struct A_2_12 a;
	a.p = (char*)malloc(sizeof(char));
	free(a.p);
	if (i || *a.p =='a') {
		// do something
	}
	return 0;
}
