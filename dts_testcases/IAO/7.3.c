struct A_7_3 {
	int p;
};
struct A_7_3 a;
void foo_7_3() {
	10 % a.p;
}
void bar_7_3() {
	foo_7_3();
}
int ff_7_3() {
	a.p = 0;
	bar_7_3();
	//foo_7_3();
	return 0;
}
