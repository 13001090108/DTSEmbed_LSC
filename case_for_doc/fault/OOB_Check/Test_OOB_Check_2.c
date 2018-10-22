int k;
void f(){     
	int a[10];      
	a[k]=1; //defect
	if(k>10)
	k++;  
}