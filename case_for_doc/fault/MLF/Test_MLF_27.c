char *new1(){
	return (char *)malloc(12);
}
void test1(){
	char *p=new1();
	free(p);// DEFECT, MLF, p
}