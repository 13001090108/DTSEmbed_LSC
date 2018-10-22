void func4() {
	void *ptr = (void*)0;
	char* net = (char*)ptr;
	*net = '1';  //DEFECT,NPD,net
}
