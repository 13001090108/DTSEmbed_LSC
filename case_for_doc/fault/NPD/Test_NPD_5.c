void npd_check_must(){
	char *p = getSomeValue();
	if (p != (void*)0) { }
	p[0] = 0;// NPD
}