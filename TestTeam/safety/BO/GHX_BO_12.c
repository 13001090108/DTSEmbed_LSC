#include <stdio.h>
void ghx_bo_12_f12()
{
char s[4]; // small destination buffer
// create a file with a string of length 50
FILE* m_file = fopen("test.txt", "w");
fprintf( m_file ,
"AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAA");

// buffer overrun because width is set to incorrect length
fscanf(m_file, "%50s", s);//DEFECT
fclose(m_file);
}