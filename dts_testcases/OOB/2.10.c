struct A_2_10 {
	char *p;
};
struct A_2_10 a;
void alloc_2_10() {
	a.p = (int *)malloc(sizeof(int) * 5);
}
void callAlloc_2_10() {
	alloc_2_10();
}
int foo_2_10() {
	callAlloc_2_10();
	a.p[5] = 'a';
	free(a.p);
	return 0;
}
