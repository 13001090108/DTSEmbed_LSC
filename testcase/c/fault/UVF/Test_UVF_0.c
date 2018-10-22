void call(int);

void f1()
{
	int i;
	int j = 2;
	call(i);  //DEFECT, UVF, i
	call(j); //FP 
}
