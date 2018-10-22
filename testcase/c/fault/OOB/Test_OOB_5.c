int c[5];
void f () {
  int b[5];
  b[6]; //DEFECT,OOB,b
}
