struct A_2_7 {
	char *p;
};
int foo_2_7(struct A_2_7 a) {
	*a.p;
	if (!a.p) ;
	return 0;
}
