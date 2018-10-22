struct A_2_1 {
	char *a;
};
int foo_2_1() {
	struct A_2_1 a;
	a.a = 0;
	*a.a;
	return 0;
}
