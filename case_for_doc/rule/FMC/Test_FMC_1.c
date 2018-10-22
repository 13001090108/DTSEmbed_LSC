#include <stdio.h>
int main(  )
{
	FILE *stream, *stream2, *stream3;
   int numclosed;
   stream3=fopen("hello.c","r"); //DEFECT
   if( (stream  = fopen( "crt_fopen.c", "r" )) == NULL )
      printf( "The file 'crt_fopen.c' was not opened\n" );
   else
      printf( "The file 'crt_fopen.c' was opened\n" );
   if( (stream2 = fopen( "data2", "w+" )) != NULL )
      printf( "The file 'data2' was opened\n" );
   if( stream)
   {
      if ( fclose( stream ) )
      {
         printf( "The file 'crt_fopen.c' was not closed\n" );
      }
   }
   numclosed = _fcloseall( );
   printf( "Number of files closed by _fcloseall: %u\n", numclosed );
}