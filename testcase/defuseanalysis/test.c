int i=1;
int j=2;
void f()
{
	i=3;
	int k=4;
	k=4;
	if(k>3 && i<10)
		{
			k++;
			++i;
		}
	j--;
}

int main()
{
	i=100;
	if(i>50)
		j=i+1;
	printf(j);
	return 0;
}