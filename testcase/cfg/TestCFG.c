int main()
{
__label__ label;
void *ptr=&&label;
int i=1;
if(i==1){
	i=2;
	goto *ptr;
}
i=0;
label:
	i++;
printf(\"%d\\n\",i);
return 0;
}