#include <stdio.h>
FILE* file;       
void f(){         
		file=fopen("wdw",0);                          
		   }                 
void f1(){        
          	f();             
           }                 
void f2(){        
	FILE * pFile;pFile=fopen("dwd",0);	file=pFile;                            
		f(); //defect
}
