struct A_2_1 {
	int a;
};
int foo_2_1() {
	struct A_2_1 a;
	a.a = 0;
	10 % a.a;
	return 0;
}
