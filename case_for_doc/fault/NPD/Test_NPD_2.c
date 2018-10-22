typedef struct _ST {
	char a;
}ST;
int func1(ST* st)
{
	ST *sa = NULL;
	sa->a = 'a';  //DEFECT,NPD,sa
	return 0;
}