#include<stdlib.h>
void *__ckd_malloc__(int32 size)
{
    void *mem;
    mem = malloc(size);
    return mem;
}

void ** __ckd_calloc_2d__( )
{
     float32 **ref;
     ref = (char **) __ckd_malloc__(16);
     return ((void **) ref);
}

int read_cep(float32 ***cep)
{
  float32 **mfcbuf;
  mfcbuf = (float32 **)__ckd_calloc_2d__( );
  *cep = mfcbuf;
  return 0;
}
int main(int argc, char *argv[])
{
  float32  **cep;
  if (read_cep(&cep) == 0)
     return 0;
}
