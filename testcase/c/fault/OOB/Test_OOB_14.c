int test1 () {
  int i ;
  int a[4] ;
  if(i > 2)
  { 
     a[i] = 1; //DEFECT,OOB,a
  }	
  return 0;
}
