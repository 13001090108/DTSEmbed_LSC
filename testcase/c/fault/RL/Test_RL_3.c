#include <stdio.h>
int func3 ()
{
  FILE * pFile;
  pFile = fopen ("myfile.txt","w");
  fputs("fopen example",pFile);
  return 0;//DEFECT, RL, pFile
}
