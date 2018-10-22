typedef struct {
	int i;
	int j;
}Test;
void test1(){
	Test a,b;
	b.i=a.j;//DEFECT, UVF, a
	a.i=b.j; 
}