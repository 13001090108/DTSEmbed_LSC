int *getPointer(bool flag);  //flag == false, return NULL

int zk_npd_33_f1()
{
	int num;
	int *ptr;

	ptr = getPointer(false);

	if (ptr) {
		num = *ptr;
	}

	num = *ptr + 1; //DEFECT
}