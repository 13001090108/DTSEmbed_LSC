#include "string.h"
void ghx_bo_4_f4(char * buffer)
{
	 char buf[20];
	 if(buffer && strlen( buffer) < 20)
	 {
		strcpy(buf,buffer);
	 }
	 if(buffer )
	 {
		strcpy(buf,buffer);
	 }
}
void ghx_bo_4_F5()
{
char buffer[25];
ghx_bo_4_f4(buffer);//DEFECT
}