int c[3][3];
void f(){
	int b[3][3];
	b[1][1]=0;
	b[1][2]=0;
	b[3][1]=0;  //DEFECT,OOB,b
	b[2][3]=0;  //DEFECT,OOB,b
	b[2][2]=0;  //FP,OOB
	c[1][3]=0;  //DEFECT,OOB,c
	c[3][1]=0;  //DEFECT,OOB,c
	char g[3]={"ac"};
	g[3] = 'c';  //DEFECT,OOB,g
}