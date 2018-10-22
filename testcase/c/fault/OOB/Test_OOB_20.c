int c[3][3];
void f(){
  c[1][3]=0;  //DEFECT,OOB,c
}
