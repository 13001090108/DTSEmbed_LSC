#include <stdlib.h>
typedef struct _ST {
    char a;
}ST;
int func1(ST* st)
{
    ST *sa = (void*)0;
    sa->a = 'a';  //DEFECT,NPD,sa
    return 0;
}
