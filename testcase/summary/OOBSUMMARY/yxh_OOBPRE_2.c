
int i;

void yxh_oob_6_f1()
{
	char buf[10];
	buf[i] = 'c';
}

void yxh_oob_6_f2()
{
    i = 12;
	yxh_oob_6_f1(); //DEFECT
}

void yxh_oob_6_f3(int j)
{	
	char buf[6];
	buf[j] = 'c';
} 

void yxh_oob_6_f4()
{
	int k = 8;
	yxh_oob_6_f3(7); //DEFECT
	yxh_oob_6_f3(k); //DEFECT
}