int c[3][3];
void f(){
  int b[3][3];
  b[1][1]=0;
  b[1][2]=0;
  b[2][3]=0;  //DEFECT,OOB,b
}
