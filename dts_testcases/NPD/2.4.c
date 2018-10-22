struct A_2_4 {
	char *p;
};
int foo_2_4(struct A_2_4 a, int i, int j) {
	if (i)
		a.p=0;
	if(j)
		*a.p = 1;
	return 0;
}
