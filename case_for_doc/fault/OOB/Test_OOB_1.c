int c[5];
int test1 () {
	int a[] = {1,2,3,4,2};
	a[6] = 1;  //DEFECT,OOB,a
	a[5] = 1;	 //DEFECT,OOB,a
	int b[5];
	b[6]; //DEFECT,OOB,b
	c[6];  //DEFECT,OOB,c
	return 0;
}