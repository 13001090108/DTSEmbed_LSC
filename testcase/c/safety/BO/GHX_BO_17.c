#include <string.h>
int ghx_bo_17_f17(char *POINTERbuf)
{
char FIXEDbuf[12];

strcpy(FIXEDbuf, "Something rather large");//DEFECT
strcpy(POINTERbuf, "Something very large as well");
return 0;
}
