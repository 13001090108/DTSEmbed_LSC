struct ugly {
  	 int x[20];
  	 char y[100];
  	 int z[20];
}
 void foo(struct ugly arg) {} // defect - argument 'arg' is too large
