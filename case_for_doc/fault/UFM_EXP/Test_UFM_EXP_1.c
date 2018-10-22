typedef struct
{
	char* x;
	int y;
} aa;
char* func(int m)
{
	aa a;
	a.x = (char*)malloc(8);
	a.y = m/7;
	if(a.y>3)
		free(a.x);
	return a.x; //DEFECT, UFM_EXP, a.x
}