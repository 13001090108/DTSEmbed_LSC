void foo(int a, int b) {
  int x = (sizeof(int) == 4) ? a : b; // defect - the condition is constant 
 }
