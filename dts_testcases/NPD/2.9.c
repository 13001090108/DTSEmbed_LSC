struct A_2_9 {
	char *p;
};
struct A_2_9 a;
void setNull_2_9() {
	a.p = 0;
}
int foo_2_9() {
	setNull_2_9();
	*a.p = 'a';
	return 0;
}
