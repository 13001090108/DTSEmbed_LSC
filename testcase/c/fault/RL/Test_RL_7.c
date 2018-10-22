#include <stdio.h>
int func7 ()
{
  FILE * pFile;
  pFile = fopen ("myfile.txt","w");
  if (pFile!=NULL)
  {
    fputs ("fopen example",pFile);
  }
  return 0;//DEFECT, RL, pFile
}
