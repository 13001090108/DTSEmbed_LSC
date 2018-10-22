#include <stdio.h>
#include<stdlib.h>
struct Student
{
  int age;
};

struct Student *func2()
{
  struct Student *r;
   if((r=(struct Student *)malloc(sizeof(struct Student)))==NULL)
     return NULL;
   else 
     return r;
}

int main()
{
  struct Student *r;
  r=func2();
 r->age=1;
  return 0;
}
