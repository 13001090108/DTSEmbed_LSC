#include <stdlib.h>
void fun(){
	int i;
	for(i=1;i<10;i++){
		char* ch=(char*)malloc(1);
		*ch='1';     //DEFECT
	}
	for(i=1;i<10;i++){
		char* ch=(char*)malloc(1);
		*ch='1';     //DEFECT
	}

}
