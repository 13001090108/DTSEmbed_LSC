#include <stdlib.h>
#include <string.h>
char *ghx_npd_4_f4(char *b)
{
    int i, m, n;
    char *s;

    m = strlen(b);
    n = m;
    s = (char *) malloc(n + 1);
    for (i = 0; i < m; i++)
	{
        *(s + i) = *(b + i);//DEFECT
	}
    *(s + m) = NULL;
    return (s);
}
