#include <stdlib.h>
  	void func_ARG(int **pp, unsigned n)
{
      			int aux;
      			if (n == 1) {
          				*pp = &aux;   //defect
      			} else {
          				*pp = (int *)malloc(n * sizeof(int));
      			}
 }
