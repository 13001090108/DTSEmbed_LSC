#include <stdio.h>
#include <stdlib.h>
void func(int *s)
{
    int i;
    for(i=0;i<10;i++)
    s[i]=i+1;
	
}
int main(int argc, char *argv[])
{
  int *p;
  int a[10];
  int i;
  p=(int *)malloc(10);
  func(p);
  for(i=0;i<10;i++)
  {
    a[i]=p[i];
  } 
  printf("%d",a[0]);
  free(p);
  return 0;
}
