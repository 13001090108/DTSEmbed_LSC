	int *buf;
	void func_GLOB(unsigned n)
{
	      		int aux;
                 buf = &aux; 
                if(n > 2)
                 buf = &aux; 
	      		if (n == 1) {
	          			buf = &aux;   //defect
	      		} else if(n == 2){
	          			buf = (int *)malloc(n * sizeof(int));
	      		}
                else 
               {
                    buf = &aux; 
               }

               
}
