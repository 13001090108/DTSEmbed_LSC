#include <stdio.h>
int func6()
{
  FILE * pFile;
  pFile = fopen ("myfile.txt","w");
  if (pFile==NULL) {
  	return 0;
  }
  fputs ("fopen example",pFile);
  return 0;//DEFECT, RL, pFile
}
