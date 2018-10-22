char *foo_5_7() {
	return 0;
}
int bar_5_7(int i) {
	*foo_5_7() = 'a';
	if (i) {
		// do something
	}
	return 0;
}
