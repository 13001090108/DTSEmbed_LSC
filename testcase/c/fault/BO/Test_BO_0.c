#include <stdio.h> 
void fopen_compchk()
{ 
 char tmpfile[16384];
 fopen_comp(tmpfile, 1);
}

void fopen_comp(const char *file, int flag)
{
   
   char command[16384];
   if (flag) 
   {
       sprintf(command, "gzip.exe -d -c %s", file);
   }
}
