struct A_2_10 {
	char *p;
};
struct A_2_10 a;
void setNull_2_10() {
	a.p = 0;
}
void callSetNull_2_10() {
	setNull_2_10();
}
int foo_2_10() {
	callSetNull_2_10 ();
	*a.p = 'a';
	return 0;
}
