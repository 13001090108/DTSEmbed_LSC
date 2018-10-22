int f1(int i){
	char buf[10];
	buf[i]=5;
	return 1;
}

int f2(int j){
	j=5;
	f1(j);
	return 2;
}

int f3(){
	int k=20;
	f2(k);
	return 3;
}
/*int k = 10;

void f1(int i)
{
//	int a[9][10];
	char buf[10];
	buf[i] = 10;
//	a[i][k]=4;
//	k=10;
}

void f2(int i)
{
	char cc[10];
	cc[k]=5;
//	i=10;
	f1(i);
}

int f3(int j)
{
	k=10;
	j = 100;
	f2(j);
//	f1(i);
	return 3;
}
*/