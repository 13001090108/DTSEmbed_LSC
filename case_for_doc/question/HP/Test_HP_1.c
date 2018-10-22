void foo(int a) {
 int a = 0;   	// defect - local variable hides the function parameter
 a++;
 }
