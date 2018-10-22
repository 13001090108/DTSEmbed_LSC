void yxh_oob_f1()
{
	char buf[13];
	int arr[4];

	((int *)buf)[4] = 1; //DEFECT

	((char *)arr)[15] = 'c';
	((char *)arr)[16] = 'c'; //DEFECT
}
