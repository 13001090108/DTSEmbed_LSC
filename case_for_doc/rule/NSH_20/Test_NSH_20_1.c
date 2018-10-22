void fun(int a, int b)
{
	switch(a)
	{
		case 1:a++;break;
	}
	switch(b)
	{
		case 1:{a++;break;}
		case 2:a++;break;
		default : a = b;
	}
}