struct A_6_3 {
	char *p;
};
struct A_6_3 a;
void foo_6_3() {
	*(a.p) = 'a';
}
int bar_6_3() {
	a.p = 0;
	foo_6_3();
	return 0;
}
