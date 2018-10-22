#include <string.h>
#include <stdlib.h>
f(){
	char* s[4];
	s[1]=(char*)malloc(12);//OK
	if(!s[1])
		return;
}