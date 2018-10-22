typedef struct S_3{
     int a,b,c;
}tS, *pS;

void f_SCMAP_3(int n) {
     pS tmp1 = (pS) calloc(n, sizeof(pS));//SCMAP
     free(tmp1);
}
