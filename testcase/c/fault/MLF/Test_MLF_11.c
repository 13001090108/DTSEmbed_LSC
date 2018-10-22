#include <stdio.h>
#include <stdlib.h>
#include<string.h>

struct Student
{
 		union
   		{
     		 char ab[4];
     		 int bdummy;
  		}u;
};
int main(int argc, char *argv[])
{ 
  struct Student *p = (struct Student *)malloc(sizeof(struct Student));
//p->u.bdummy = 2;
system("PAUSE");	
return p->u.bdummy;
}
