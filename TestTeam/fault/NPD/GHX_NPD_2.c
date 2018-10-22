#include <stdlib.h>
#include <string.h>

void ghx_npd_2_f2(int flag,char* to)
{
	char* from;
    char* buffer =(char*) calloc(1, 10);
	if(buffer){
	}
    if (flag== 0) {
		from = to;
    }
    else {
        from = buffer;
    }
    memcpy(from, to, 10);
	*from;//DEFECT
	*buffer;//DEFECT
}
