#define true 1
#define false 0
#include <stdio.h>

void f_CAE(_Bool b)
{
    //...
    if (b=false){// CAE,defect
	    printf("false");
    }
}
