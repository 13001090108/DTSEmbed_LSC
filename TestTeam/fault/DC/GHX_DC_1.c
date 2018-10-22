 void ghx_dc_1_f1()
{
  int i;
  for(i=1;;i++)//DEFECT
{
  i++;
}
return;
}
void ghx_dc_1_f2()
{
	int m=1;
    for(;;)//DEFECT
	{
     m++;
	}
return;
}
