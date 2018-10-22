typedef struct S{
    int a,b,c;
  }tS, *pS;

  void foo(int n) {
    pS tmp1 = (pS) malloc(n * sizeof(pS));
    free(tmp1);
  }
