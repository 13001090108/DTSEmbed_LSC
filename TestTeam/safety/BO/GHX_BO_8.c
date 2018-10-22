#include <stdio.h>
#include <io.h>
#include <conio.h>
//#include <libgen.h> 
void ghx_bo_8_f8(char *argv[],char a[3],char b[33],char ch)
{
FILE *fp;
int hand;
int i=0;
 char *password;
char string [2];
 fp = fopen ("myfile.txt" , "r");
fgets(string,5,fp);//DEFECT
fread(string,10,10,fp);//DEFECT
read(hand,string,20);//DEFECT

//wmemcpy(string, password, 10);//DEFECT
//wmemmove(string, password, 10);//DEFECT
//wmemset(string, ch, 10);//DEFECT
//gettext(10,10,10,10,string);//DEFECT
//getpass((char *)password);//DEFECT
//streadd(string, "abcd", "efg"); //DEFECT
//strecpy(string,"abcd","efg");//DEFECT
//strtrns(argv[1],a,b,string);//DEFECT
while((ch = getchar()) != '\n') 
  { 
  if(ch == -1) break; 
  string[i++] = ch; 
  } 
//strccpy(string,a);//DEFECT
//strcadd(string,b);//DEFECT
}