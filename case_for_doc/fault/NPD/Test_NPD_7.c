int test2(int b){
	int* x = NULL;
	if (b)
		x =(int *)malloc(8);
	if (!b)
		return *x;   //DEFECT,NPD,x
	return 0;
}