void test4(){
	int *q=(int *)malloc(4);
	if(var>10){
		free(q);
	}else{
	}
}// DEFECT, MLF, q