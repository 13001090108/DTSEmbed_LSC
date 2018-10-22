#include <stdlib.h>
 int *func_RET(unsigned n)
{
      			int aux;
      			int *p;
      			if (n == 1) {
          				p = &aux;   //defect
	      			} else {
          				p = (int *)malloc(n * sizeof(int));
	      			}
      			return p;
 	}
