long foo(long arr[]) {
	long time1 = 0;
	long time2 = 0;
	long len = 0;
	int i = 0;
	for (i = 0; i < sizeof(arr); i += 2) {
		time1 = arr[i];
		time1 = arr[i + 1];//NUAV,time1,defect
		if (time1 < time2) {
			long d = time1 - time2;
			if (d > len) len = d;
		}
	}
	return len;
}
