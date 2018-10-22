#define MAX 10
void test3(){
	int a[MAX];
	int *p=a;
	p[MAX]=1;//DEFECT,OOB,p
	a[MAX]=1;//DEFECT,OOB,a
}