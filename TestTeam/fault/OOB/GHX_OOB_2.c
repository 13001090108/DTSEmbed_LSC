#define  m 100
struct ghx_oob_2_sl
{
	char*s;
	char a[m];
};

ghx_oob_2_f2(int i)
{
      int a[12];
      a[13]=1;
  	  ghx_oob_2_sl s;
	  if(i<=m){
		  s.a[i]=1;//DEFECT
	  }
	  return 0;
}

