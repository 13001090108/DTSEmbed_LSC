struct A_2_4 {
	int a;
};
int foo_2_4(struct A_2_4 a, int i, int j) {
	if (i)
		a.a=0;
	if(j)
		10 % a.a;
	return 0;
}
