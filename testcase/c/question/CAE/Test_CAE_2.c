#include <stdio.h>

int qq()
{
    return 0;
}

void f_CAE_3(int i)
{
    if(i = qq()){// CAE,defect
        printf("OK");
    }
}
