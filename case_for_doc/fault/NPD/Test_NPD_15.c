void test18_1(int flag,char* to)
{
	char *s;
	s=(char *)malloc(sizeof(8));
	read(1,s,sizeof(s));  //DEFECT,NPD,s 
	free(s);
}