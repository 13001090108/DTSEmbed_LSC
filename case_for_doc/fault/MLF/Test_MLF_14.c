void *malloc(int nmemb);
void free(void* p);
void f7(int i){
	int a[5]={4,4,4,4,4,};
	int* melleak_error8=NULL;
	if(i>0){
		melleak_error8=a;
	}else{
		melleak_error8=(int*)malloc(100);
	}
	if(i>0){
		free(melleak_error8);
	}
}//DEFECT, MLF, melleak_error8