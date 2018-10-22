typedef struct S_1{
     int a,b,c;
}tS, *pS;

void f_SCMAP_1(int n) {
     pS tmp1 = (pS) malloc(n * sizeof(pS));
     free(tmp1);
}
