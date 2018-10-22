void xstrcpy(char *dst, char *src){
	if (!src) return;
	dst[0] = src[0]; // NPD
}
void npd_gen_must(int flag, char *arg){
	char *p = arg;
	if (flag) p = 0;
	if (arg) {;}
	xstrcpy(p,"Hello"); // NPD
}