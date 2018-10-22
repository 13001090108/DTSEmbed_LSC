struct A_2_12 {
	char *p;
};
int foo_2_12(int i) {
	struct A_2_12 a;
	a.p = 0;
	if (i == 1 && *a.p != 'a') {
		// do something
	}
	return 0;
}
