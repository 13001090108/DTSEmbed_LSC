void deref(int *p){
	*p = *p + 10;
}
void rnpd_2(int *t){
	deref(t); // NPD_Check
	if (!t) return;
	*t ++;
}