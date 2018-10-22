#include <stdio.h>

void f_NBCL(_Bool debug) {
	// ...
	if (debug);{ // NBCL,defect
		printf("Enter");
	}
}
