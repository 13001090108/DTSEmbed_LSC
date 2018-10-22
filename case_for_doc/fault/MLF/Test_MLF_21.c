void *malloc(int nmemb);
void free(void* p);
int *p;
void f4(){
	int *memleak_error5=NULL,*not_memleak_error5=NULL;
	memleak_error5=(int*)malloc(100);
	not_memleak_error5=(int*)malloc(10);
	p=not_memleak_error5; //assignment it to var that is global
}//DEFECT, MLF, memleak_error5