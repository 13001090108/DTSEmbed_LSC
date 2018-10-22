int foo_4_3(int *p[10], int i) {
	if (i || !p[0])
		*p[0] = 1;
	return 0;
}
