char *foo_5_3() {
	return 0;
}
int bar_5_3(int i) {
	if (i ==1 || foo_5_3())
		*foo_5_3() = 'a';
	return 0;
}
