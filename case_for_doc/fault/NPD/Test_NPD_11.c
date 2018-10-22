int *getNull(){
	return 0;
}
void npd_gen_must(int flag, char *arg){
	int *p = getNull();
	*p = 1; // NPD
}