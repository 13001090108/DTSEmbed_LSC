struct A_2_2 {
	char * a;
};
int foo_2_2(struct A_2_2 a) {
	if (a.a == 0)
		*a.a;
	return 0;
}
