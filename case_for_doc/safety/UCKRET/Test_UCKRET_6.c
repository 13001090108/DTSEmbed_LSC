#include <stdlib.h>
	 
int ghx_uckret_4_f4 ()
{
malloc(sizeof(int)*4);//DEFECT
/* If a functions return value is not checked, it could have failed without any warning. */
return 0;
}