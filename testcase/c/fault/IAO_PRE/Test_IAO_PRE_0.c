void f1(int i) //记录IAO前置信息
{
	int b;
	b = 2/i;
}

void f2(int j) //记录IAO前置信息
{
	f1(j);
}

void f3()
{
	int b = 2;
	f1(b);
	f1(0);	//DEFECT, 利用前置信息
	f2(2);
	f2(0); //DEFECT, 利用前置信息
}
