char *foo_5_5() {
	return 0;
}
int bar_5_5() {
	if (foo_5_5()) {
		// do something
	}
	*foo_5_5() = 'a';
	return 0;
}
