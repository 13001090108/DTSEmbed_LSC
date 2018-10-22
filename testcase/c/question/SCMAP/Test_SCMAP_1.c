typedef struct S_2{
     int a,b;
     char c;
}tS, *pS;

void f_SCMAP_2(int n) {
     pS tmp1 = (pS) malloc(4);
     //...
     tmp1 = (pS) realloc(tmp1,n * sizeof(pS));//SCMAP
     free(tmp1);
}
