char *foo_5_8() {
	return 0;
}
int bar_5_8(int i) {
	*foo_5_8() = 'a';
	if (i && foo_5_8()) {
		// do something
	}
	return 0;
}
