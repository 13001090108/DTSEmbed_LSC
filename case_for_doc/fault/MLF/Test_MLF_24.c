void* malloc(int size);
void free(void* p);
int* test1(){
	int* a=(int*)malloc(100);	
	return a; // FP, MLF
}	
int* test2(){
	int* q=test1();
	return q;	
}
void test3(){
	int* qq;
	qq=test2();
}// DEFECT, MLF, qq