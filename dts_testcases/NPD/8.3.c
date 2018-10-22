struct A_8_3 {
	char *p;
};
struct A_8_3 a;
void foo_8_3(char p) {
}
void bar_8_3() {
	a.p = 0;
	foo_8_3(*a.p);
}
