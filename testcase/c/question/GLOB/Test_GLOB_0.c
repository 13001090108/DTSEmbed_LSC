	int *buf;
	void func_GLOB(unsigned n)
{
	      		int aux;
	      		if (n == 1) {
	          			buf = &aux;   //defect
	      		} else {
	          			buf = (int *)malloc(n * sizeof(int));
	      		}
}
