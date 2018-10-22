#define N 10
int ghx_oob_5_f4(int x)
{
   int a[11];
   a[x]=1;
return 1;
}
int ghx_oob_5_f5()
{
int a[N];
for (int i = 0; i<=N; ++i)
{
    int x =i;
    a[i] = ghx_oob_5_f4(x); //DEFECT
    x = ghx_oob_5_f4(11);   //DEFECT
}
return 0;
}
