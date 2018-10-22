struct A_2_12 {
	int a;
};
int foo_2_12(int i) {
	struct A_2_12 a;
	a.a = 0;
	if (i == 1 && 10 % a.a == 0) {
		// do something
	}
	return 0;
}
