struct A_8_3 {
	int a;
};
struct A_8_3 a;
void foo_8_3(int a) {
}
void bar_8_3() {
	a.a = 0;
	foo_8_3(10 % a.a);
}
