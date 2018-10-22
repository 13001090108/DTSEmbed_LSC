void test8(int i){
	int *p;
	if(i>0){
		p=NULL;
	}else{
		p=(int *)malloc(8);
	}
	if(i>0){
		return;
	}
}  //DEFECT, MLF, p