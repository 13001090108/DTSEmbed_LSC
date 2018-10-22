int* f_PTF_1(int *pl_ptr) {
  int *a;
  pl_ptr = &a;//PTF
  return &a;    
}
