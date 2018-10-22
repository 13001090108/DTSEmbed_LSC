int* test4(){
	int* a=(int*)malloc(100);	
	return a; // FP, MLF
}
int* test5(){
	return test4();	
}
void test6(){
	int* qq;
	qq=test5(); 
}// DEFECT, MLF, qq