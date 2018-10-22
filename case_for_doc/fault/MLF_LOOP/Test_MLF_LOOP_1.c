void  f1(){
	int cc;
	char *ff;
	for (cc=0; cc<500; cc++){
		ff=(char*)malloc(10);
	}
	free (ff);
	return 0;
}