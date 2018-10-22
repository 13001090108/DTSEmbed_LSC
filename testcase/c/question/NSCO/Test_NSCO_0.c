#include <stdio.h>

static void check(int arr[]) {
	if (arr!=NULL & sizeof(arr)!=0) {//NSCO,defect
        printf("OK\\n"); 
	}
	return;
}
