int test3 () {
  int i ;
  int a[4];
  if(i > 0 || i < 3)
  {
     a[i] = 1; //DEFECT,OOB,a
  }
  return 0;
}
