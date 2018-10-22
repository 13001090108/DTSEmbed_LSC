#include <stdio.h>
#include <setjmp.h>

int ghx_npd_9_f9()
{
  int *env=NULL;
  int val=0;
  
  if (!val) 
   longjmp(env, 1);//DEFECT
  return 0;
}

int ghx_npd_9_f8()
{
  jmp_buf env;
  int val=0;

  val=setjmp(env);

  printf ("val is %d\n",val);

  if (!val) longjmp(env, 1);//FP

  return 0;
}

