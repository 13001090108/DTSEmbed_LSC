#include <stdio.h>

int ghx_npd_20_f20 ()
{
  FILE * pFile;
  char c;

  pFile=fopen("alphabet.txt","wt");
    for (c = 'A' ; c <= 'Z' ; c++)
    {
    putc (c , pFile);//DEFECT
    }
  fclose (pFile); //DEFECT
  return 0;
}

int ghx_npd_20_f19()
{
FILE * pFile;
  char c;

  pFile=fopen("alphabet.txt","wt");
    for (c = 'A' ; c <= 'Z' ; c++)
	{
		if(pFile!=NULL)
		{
		putc(c,pFile);//FP
		fclose(pFile);
		}
	}
		return 0;
}
