void *malloc(int nmemb);
void free(void* p);
void f8(){
	int* melleak_error9=NULL;
	melleak_error9=(int*)malloc(100);
	melleak_error9++;//DEFECT, MLF, melleak_error9
	free(melleak_error9);
}