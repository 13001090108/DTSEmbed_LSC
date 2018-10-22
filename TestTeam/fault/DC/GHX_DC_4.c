int ghx_dc_4_f4()
{
int m=1;
return m;
}
void ghx_dc_4_f1()
{
int i;
 for(i=ghx_dc_4_f4();;i++)//DEFECT
 {
 i++;
 }
}