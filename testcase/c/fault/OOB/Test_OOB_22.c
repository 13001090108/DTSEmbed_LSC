int c[3][3];
void f(){
  c[3][1]=0;  //DEFECT,OOB,c
}
