void doSomething{
	int* p=(int*)malloc(4*sizeof(int));
	int c=p[0];//DEFECT
}
