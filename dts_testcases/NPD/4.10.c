int *p[10];
void setNull_4_10() {
	p[0] = 0;
}
void callSetNull_4_10() {
	setNull_4_10();
}
int foo_4_10() {
	callSetNull_4_10();
	*p[0] = 'a';
	return 0;
}
