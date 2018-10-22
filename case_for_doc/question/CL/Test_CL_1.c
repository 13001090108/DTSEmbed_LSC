int foo(int k){
   		int j = 1;
   		k = 0;
   		if(j){
      				j > k;     //defect
       				return j;
   		}else{
       			k++;
      			return k;
   		}
}