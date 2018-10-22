#include <stdio.h>
FILE * gFile;
int ff (){
	 gFile = fopen ("myfile_1.txt","w");
	}
int func9 ()
{
  FILE * pFile;
  pFile = fopen ("myfile.txt","w");
  if (pFile==NULL) {
  	return 0;
  }
  fputs ("fopen example",pFile);
  gFile = pFile;
  ff ();
  return 0;//FP, RL
}
