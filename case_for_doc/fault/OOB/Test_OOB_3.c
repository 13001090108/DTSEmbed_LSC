int i;
void f(){
	int b[][3]={{1,2,4},{1,2,3},{1,2,3}};
	b[1][1]=0;
	b[1][2]=0;
	b[3][1]=0; //DEFECT,OOB,b
	b[2][3]=0; //DEFECT,OOB,b
	b[2][2]=0;  //FP,OOB
}