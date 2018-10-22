#include <stdio.h>
#include <string.h>

int ghx_npd_12_f12 (size_t len1,size_t len2)
{
  char *str1=NULL;
  char *str2=NULL;
  int n;

  n=memcmp ( str1, str2, len1>len2?len1:len2 );//DEFECT
  if (n>0) printf ("'%s' is greater than '%s'.\n",str1,str2);
  else if (n<0) printf ("'%s' is less than '%s'.\n",str1,str2);
  else printf ("'%s' is the same as '%s'.\n",str1,str2);
  return 0;
}


int ghx_npd_12_f11 ()
{
  char str1[]="abcdefg";
  char str2[]="abc";
  int n;
  size_t len1, len2;
  len1=strlen(str1);
  len2=strlen(str2);
  n=memcmp ( str1, str2, len1>len2?len1:len2 );//FP
  if (n>0) printf ("'%s' is greater than '%s'.\n",str1,str2);
  else if (n<0) printf ("'%s' is less than '%s'.\n",str1,str2);
  else printf ("'%s' is the same as '%s'.\n",str1,str2);
  return 0;
}
