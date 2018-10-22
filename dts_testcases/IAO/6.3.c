struct A_6_3 {
	int a;
};
struct A_6_3 a;
void foo_6_3() {
	10 % a.a;
}
int ff_6_3() {
	a.a = 0;
	foo_6_3();
	return 0;
}
