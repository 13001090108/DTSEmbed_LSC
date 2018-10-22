void f(int i){     
	int a[10];      
	a[i]=1; //defect
	if(i>10)
	i++;  
}