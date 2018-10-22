struct A_2_3 {
	char * a;
};
int foo_2_3(struct A_2_3 a, int i) {
	if (i || !a.a)
		*a.a;
	return 0;
}
