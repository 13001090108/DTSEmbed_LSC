//#include <stdlib.h>
//
//// Memory
//int bar_1_4(int i) {
//	int *p;
//	p = (int *)malloc(sizeof(int) * 10);
//	if (i == 1) {
//		free(p);
//		p = (int *)malloc(sizeof(int) * 5);
//	}
//	if (i == 2)
//		p[5] = 'a';
//	free(p);
//	return 0;
//}
//
