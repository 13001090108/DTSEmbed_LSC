	int *buf;
	void func_GLOB(unsigned n)
{
	      		int aux;
	      		if (n == 1) {
	          			buf = &aux; 
	      		} else {
	          			buf = (int *)malloc(n * sizeof(int));
	      		}
	      		buf =  &aux;
}
