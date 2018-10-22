#include  <stdio.h>
int all=8;
void f()
{
all=6;
}
void f1(){
f();
char buffer[all];
scanf("%7s",buffer);
}
