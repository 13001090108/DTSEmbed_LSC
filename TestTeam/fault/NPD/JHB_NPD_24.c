#include <stdio.h> 
#include <process.h> 
FILE *stream; 
void jhb_npd_24_f1( void ) 
{ 
	char s[] = "this is a string"; 
	char c = '\n'; 
	stream = fopen( "fprintf.out", "w" ); 
	fprintf( stream, "%s%c", s, c ); //DEFECT 
	system( "type fprintf.out" ); 
} 
