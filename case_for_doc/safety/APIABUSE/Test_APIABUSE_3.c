#include <stdlib.h>
#include <stdio.h>
int ghx_api_3_f3(){
const char *filename = "hello.txt";
FILE *f;
f = fopen(filename,"w");
if(f == NULL) {
//Handle error
}
fprintf(f,"Hello, World\n");
abort();/* oops! data might not be written! */ //DEFECT
return 0;
}