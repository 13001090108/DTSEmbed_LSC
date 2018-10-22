struct x
{
	int y;
	char a;
};
void fun()
{
	struct x xx;
	int k;
	xx.y=1;
	k=xx.y;
	char b=xx.a; //DEFECT, UVF_EXP, xx.a
}