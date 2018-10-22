#include <stdio.h>
int ghx_bo_5_f5()
{
   FILE * File;
   char string [100];

   File = fopen ("myfile.txt" , "r");
 
     fgets (string , 200 , File);//DEFECT
     puts (string);
     fclose (File);

   return 0;
}
