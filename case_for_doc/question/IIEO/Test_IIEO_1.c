#include <string.h>

int f_IIEO_2(int i,char *str)
{
    int num=0;
    while(i>func(str))
    {
        num++;
        i--;
    }
    return num;
}

int func(char *str){
    return strlen(str);
}
