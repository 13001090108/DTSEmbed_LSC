typedef struct _Test {
	int a[2];
} Test;
int test1()
{
	Test st[2] = {0};
	st[0].a[0] = 1;
	st[0].a[1] = 1;
	st[2].a[0] = 1;  //DEFECT,OOB,st
	st[2].a[2] = 1;  //DEFECT,OOB,st
	return 0;
}