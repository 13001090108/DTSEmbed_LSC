#include <stdio.h>
#include <stdlib.h>
#include<string.h>
char *retrieve_input_string() 
{
  char fname[50]; 
  printf("please input file name: ");
  scanf("%s",fname);
  return strdup(fname); 
}

int main(int argc, char *argv[])
{
  char *line;
  if ((!(line = retrieve_input_string()) )) 
  return 0;	
     printf ("the input string is: %s" , line) ;
  system("PAUSE");	
  return 0;
}
