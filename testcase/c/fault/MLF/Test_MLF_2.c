#include<stdlib.h>

int read_cep(float **cep)
{
  char *mfcbuf;
  mfcbuf = malloc(10);
  *cep = mfcbuf;
  return 0;
}
int main(int argc, char *argv[])
{
  char  *cep;
  if (read_cep(&cep) == 0)
     return 0;
}
