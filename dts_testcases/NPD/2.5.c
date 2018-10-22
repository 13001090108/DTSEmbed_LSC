struct A_2_5 {
	char *p;
};
int foo_2_5(struct A_2_5 a) {
	if (!a.p) ;
	*a.p;
	return 0;
}
