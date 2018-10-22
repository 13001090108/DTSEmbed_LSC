#include <stdio.h>
#define OK 1
int a;
int* f_RLVAP_1 ()
{
     int i=a;
     return &i;//RLVAP
}
void f_RLVAP_main ()
{
     int *p = f_RLVAP_1 ();
     *p = 0xbb;
}
