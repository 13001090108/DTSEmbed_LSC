int* func(int *pl_ptr) {
	int a = 1;
	pl_ptr = &a;
	return &a;    
}
