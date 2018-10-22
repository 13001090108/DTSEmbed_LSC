void *malloc(int nmemb);
void free(void* p);
int * f5(){
	int *memleak_error6=NULL;
	memleak_error6=(int*)malloc(100);
	if(memleak_error6 != NULL){
		return NULL;//DEFECT, MLF, memleak_error6
	}
}