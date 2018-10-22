void ghx_oob_3_f3 (int i) 
{

  int a[4] = {1,2,3,4};
  if(i > 2)
  {
     a[i] = 1;//DEFECT
  }
  else if(i> 0 && i < 3)
  {
     a[i] = 1;//FP
  }
  else
  {
     a[i] = 2;//DEFECT
  }
  return ;
}
