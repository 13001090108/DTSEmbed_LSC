int test1 () {
  int a[4] ;
  int i = 4;
  a[i] = 1;	//DEFECT,OOB,a
  return 0;
}
