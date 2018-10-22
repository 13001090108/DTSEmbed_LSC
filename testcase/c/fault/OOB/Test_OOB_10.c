struct str{
	char*s;
	char a[100];
};

void test5(int i){
      int a[120];
	  struct str s;
      a[110]=1;//FP,OOB
	  if(i<=100){
		  s.a[i]=1;//DEFECT,OOB,a
	  }

}
