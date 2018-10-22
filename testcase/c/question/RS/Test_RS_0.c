#include <stdio.h>

void f_RS(int i)
{
    switch (i){
        case 1:
        	printf("hello");
        	break;
        	printf("never");//RS,defect
       	default:
            printf("world");
            break;
    }
}
