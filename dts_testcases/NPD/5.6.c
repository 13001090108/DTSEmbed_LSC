char *foo_5_6() {
	return 0;
}
int bar_5_6(int i) {
	if (i && foo_5_6()) {
		// do something
	}
	*foo_5_6() = 'a';
	return 0;
}
