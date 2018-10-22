void yxh_oob_f1()
{
	char buf[4];
	int i = 1, j = 2;

	//char c = (buf+j)[j]; //DEFECT

	(buf+1)[2+i] = 'c'; //DEFECT
	(buf+j)[i] = 'c';
}
