int fun (int i)
{
	return i;
}
int test () {
	int i ;
	int j = fun ( i);  //DEFECT,UVF,i
	i = fun(2);
	j = i;
	return 0;
}