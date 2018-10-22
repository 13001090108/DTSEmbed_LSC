void test1(){
	int* p=(int *)malloc(44);
	int* q=p;
	for(int i=0;i<10;i++){
		(p++)[0]=i;// DEFECT, MLF, p
	}		
	free(p); 
}