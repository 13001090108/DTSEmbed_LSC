#include<stdlib.h>

int read_cep(char **cep)
{
  int a = 0;
  *cep = (char *)malloc(12);
  return a;
}
int main(int argc, char *argv[])
{
  char  *cep;
  if (read_cep(&cep) == 0)
     return 0;
}
