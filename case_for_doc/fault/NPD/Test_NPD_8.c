typedef struct _st{
	int a;
}ST;
void test1(ST* st, int c){
	int b;
	if (st == 0 || c ==1) {
		b = (*st).a;  //DEFECT,NPD,st
	}
}