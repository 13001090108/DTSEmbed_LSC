typedef struct _Test {
	int a[3][3];
} Test;

int test1()
{
	Test st[2];
	st[1].a[0][3] = 1;  //DEFECT,OOB,a
	return 0;
}
