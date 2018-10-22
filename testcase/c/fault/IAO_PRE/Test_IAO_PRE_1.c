int g1 ;

void f1() //记录前置信息
{
	int b = 1/g1; 
}

void f2()
{
	g1 = 0;
	f1();	//DEFECT, 利用前置信息
}

void f3(int i, int j) //记录前置信息i != 0
{
	int b = 1/i; 
}

void f4(int j) //记录前置信息j != 0
{
	f3(j, 5);
}

void f5()
{
	int i=0;
	f3(i, 4); //DEFECT, IAO
	f4(i); //DEFECT, IAO
}
