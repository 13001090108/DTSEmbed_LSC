#include <string.h>
#include <stdio.h>

void f_IIEO(char *str)
{
    int i=0;
    for(i=0; i<strlen(str); i++){//IIEO,defect
        printf("%c",str[i]);
    }
    return;
}
