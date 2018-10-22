void f(){
  int b[3][3];
  b[1][1]=0;
  b[1][2]=0;
  b[1][3]=0; //DEFECT,OOB,b
}
