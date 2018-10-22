#include <stdlib.h>
struct A_2_11 {
	char *p;
};
int foo_2_11() {
	struct A_2_11 a;
	a.p = (char*)malloc(sizeof(char));
	free(a.p);
	if (*a.p =='a') {
		// do something
	}
	return 0;
}
