#include <stdlib.h>

int* func1(int *var1, char *var2)
{
	if (var1 == NULL || var2 == NULL) {
		*var1 = 0; //DEFECT
		return NULL;
	}
	return var1;
}