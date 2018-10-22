 long foo(long arr[]) {
      		long time1 = 0;
      		long time2 = 0;
      		long len = 0;
      		for (int i = 0; i < arr.length; i += 2) {
      			time1 = arr[i];
      			time1 = arr[i + 1];
      			if (time1 < time2) {
      				long d = time1 - time2;
      				if (d > len) len = d;
      			}
      		}
      		return len;
      }
