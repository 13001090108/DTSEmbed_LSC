
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

int main()
{
    char *buf;
    int req_size = 10;
    char xfer[10];

    buf = (char*) malloc(req_size);
    strncpy(buf, xfer, req_size); //DEFECT, UCKRET

    return 0;
}
