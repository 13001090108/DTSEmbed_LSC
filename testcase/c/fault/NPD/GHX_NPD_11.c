#include <string.h>
#include <stdio.h>

char ghx_npd_11_f11()
{
	char *ptr=NULL;
	char *ph;
	int i=1;
    ph=(char *)memchr(ptr,'p',10);//DEFECT
    ph[i]=0;//DEFECT
	return 0;
}


int ghx_npd_11_f10 ()
{
  char * pch;
  char str[] = "Example string";
  int i=1;
  pch = (char*) memchr (str, 'p', strlen(str));//FP
  if (pch!=NULL)
    printf ("'p' found at position %d.\n", pch-str+1);
  else
    pch[i]=0;//FP
  return 0;
}
