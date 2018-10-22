struct A_2_3 {
	int p;
};
int foo_2_3(struct A_2_3 a, int i) {
	if (i || a.p == 0)
		10 % a.p;
	return 0;
}
