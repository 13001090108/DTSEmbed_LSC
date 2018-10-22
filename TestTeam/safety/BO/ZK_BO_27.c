#include <stdio.h>

void zk_bo_27_f1()
{
	char s[4];

	FILE* m_file = fopen("test.txt", "w");
	fprintf( m_file ,
		"AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAA");
	fclose(m_file);

	fscanf(m_file, "%50s", s); //DEFECT
}