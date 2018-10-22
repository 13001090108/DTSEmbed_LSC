void test1(int i) 
{
	int *c;
	switch(i){
		case 1:
		default:
			c=&i;
			break;
		case 2:
			c=&i;
			break;
		case 3:
			break;
	}
	c++;   //DEFECT,UVF,c
}