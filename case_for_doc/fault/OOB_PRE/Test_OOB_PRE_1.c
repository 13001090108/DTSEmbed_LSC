int func1(int i){
	int a[3]={1,2,3};
	return a[i]*2; 
}
void func2(){
	int x=func1(5);// DEFECT, OOB_PRE
}