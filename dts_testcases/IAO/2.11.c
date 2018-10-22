struct A_2_11 {
	int a;
};
int foo_2_11() {
	struct A_2_11 a;
	a.a = 0;
	if (10 % a.a == 0) {
		// do something
	}
	return 0;
}
