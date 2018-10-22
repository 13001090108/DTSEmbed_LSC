typedef struct _Test {
	int a[2];
} Test;

int test1()
{
	Test *p;
	p->a[2] = 1;  //DEFECT,OOB,a
	return 0;
}
