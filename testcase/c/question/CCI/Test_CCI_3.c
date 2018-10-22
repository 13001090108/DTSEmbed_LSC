int  fun()
{
   return 1;
}
void fun1()
{
	int k=0;
    if(k=fun())//defect
      k++;
}
