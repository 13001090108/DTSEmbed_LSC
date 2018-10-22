int test3()
{
	int arr[20];
	int n;
	n = arr[sizeof(arr)-1];   //DEFECT,OOB,arr
	n = arr[sizeof(arr)/sizeof(int)-1];
}