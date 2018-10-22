#include <stdio.h>
void ghx_bo_13_f13(FILE* f, char* x)
{
char tmp[100];
//char* tmp=new char[100];
fscanf(f, "%10s", tmp);
fscanf(f, "%20s", tmp);
fscanf(f, "%10s", x);
fscanf(f, "%s", x);//DEFECT
fscanf(f, "%%%s", x);//DEFECT
fscanf(f, "%%%10s", x);
fscanf(f, "%*s%s", x);//DEFECT
fscanf(f, "%*s%10s", x);
}