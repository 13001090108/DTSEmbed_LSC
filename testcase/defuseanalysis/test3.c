//目前有问题：局部作用域退出后定义使用链没有区分
void f1(int i){}

void f2()
{
	 int i;
	 i = 3;
	 f1(i);
	 if(1)
	 {
	 	 int i;
	 	 i = 3;
	 	 f1(i);
	 }
	 int j=i+5;
}
int main()
{
	return 0;
}