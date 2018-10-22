void test10(){
	int *p1,*p2,*p3;
	p2=(int *)malloc(4);
	p3=(int *)malloc(4);
	p1=p2;
	p1=p3;
	free(p1);
}//DEFECT, MLF, p2