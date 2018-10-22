void fuc(int a){
	char * x ;
	if (a) x= (char*)malloc(sizeof(char*));
	free(x);
}