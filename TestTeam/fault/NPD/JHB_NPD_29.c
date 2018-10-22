#include <stdio.h>
#include <stdlib.h>
#include "time.h"
#include <math.h>
int jhb_npd_29_f1(void){
	FILE* f;
	f=freopen("OUTPUT.FIL", "w", stdout);
	*f;                               //DEFECT
	fclose(stdout);
	return 0;
}
int jhb_npd_29_f2(void){
	double mantissa, number;
	number = 8.0;
	int i;
	mantissa = frexp(number, NULL);   //DEFECT
	fscanf(NULL,"%d",&i);             //DEFECT
	return 0;
}
int jhb_npd_29_f3(void){
	FILE *stream;
	fpos_t filepos;
	stream = fopen("MYFILE.TXT", "w+");
	fseek(stream, 0L, SEEK_END);      //DEFECT
	fgetpos(stream, &filepos);        //DEFECT
	ftell(stream);                    //DEFECT
	return 0;
}
struct jhb_npd_29_s1
{
	int i;
	char ch;
};
int jhb_npd_29_f4(void)
{
	FILE *stream;
	struct jhb_npd_29_s1 s;
	s.i = 0;
	s.ch = 'A';
	char ch;
	char* p;
	stream = fopen("TEST.$$$", "wb");
	fwrite(&s, sizeof(s), 1, stream); //DEFECT
	ch=getc(stream);                  //DEFECT
	p=getenv(NULL);                   //DEFECT
	p=gets(NULL);                     //DEFECT
	gmtime(NULL);                     //DEFECT
	return 0;
}
