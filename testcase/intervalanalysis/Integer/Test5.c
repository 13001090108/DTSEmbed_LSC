enum Test1{ENUM1, ENUM2};
typedef enum {ENUM3, ENUM4}Test2;
enum Test3{ENUM5 = 6, ENUM6};
int main()
{
	Test1 t1, t2;
	t1 = ENUM1;
	t2 = ENUM2;
	int aa[ENUM4];
	int a = ENUM2;
	int b = ENUM6;
	Test2 t3;
	t3 = ENUM4;
	return 0;
}

int func(Test2 t2)
{
	int a = 0;
	switch(t2) 
	{
		case ENUM3:
			a = 1;
			break;
		case ENUM4:
			a = 2;
			break;
	}	
	return 0;
}