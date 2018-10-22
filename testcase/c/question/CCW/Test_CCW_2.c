int fun1()
{
 int i=-1;
  while(i<=0)//ok
 {
	i++;
	}
 return i;
}
void main()
{
 int k=5;
 while(k= fun1())//defect
  k--;
}
