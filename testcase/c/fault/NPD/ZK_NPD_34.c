#include <stdlib.h>

#define get_new(type, num)  (type *)malloc(sizeof(type)*num)

int zk_npd_34_f1()
{
	int *ptr;

	ptr = get_new(int, 1);

	return *ptr; //DEFECT
}
