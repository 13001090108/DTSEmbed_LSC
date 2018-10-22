  #include <stdlib.h>
 
  int *foo(int t) {
      int *x = (int *)malloc(1);
      if (t) {
          free(x);
      }
      *x = t; //DEFECT
      return x;
}
