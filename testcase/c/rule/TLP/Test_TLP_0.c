void f_TLP_1() {
  int a[10] = {0};
  int *p1_ptr,**p2_ptr;
  int ***p3_ptr;      
  int w;
  p1_ptr = a;
  p2_ptr = &p1_ptr;
  p3_ptr = &p2_ptr;    
  w = ***p3_ptr;
}
