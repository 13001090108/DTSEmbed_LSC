char* new2() {
	return (char *)malloc(1);
}
void test2(){
	char *p=new2();
	free(p);// DEFECT, MLF, p
}