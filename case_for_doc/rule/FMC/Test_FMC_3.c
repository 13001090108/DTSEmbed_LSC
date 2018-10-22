#include <stdio.h>
int main(  )
{
	FILE *stream;
   stream=fopen("hello.c","r");
   if(!stream)
   {
         printf( "The file 'hello.c' wasn't opened\n" );
   }
  		  fclose(stream); 
}