void test1(int** a){
	*a=(int*)malloc(100);	
}
void test2(){
	int* aa;
	test1(&aa);
}//DEFECT, MLF, aa