void foo_8_7(char p) {
	char c = p;
}
char baz_8_7() {
	char p;
	return p;
}
void bar_8_7() {
	fooa_8_7(baz_8_7());
}

// Memory
void fooa_8_7(char p) {
	*p;
}
char *baza_8_7() {
	char *p;
	return p;
}
void bara_8_7(char *p) {
	fooa_8_7(baza_8_7());
}

