//#include <stdlib.h>
//
//// Memory
//int bar_4_4(int i) {
//	int *p[5];
//	p[0] = (int *)malloc(sizeof(int) * 10);
//	if (i == 1) {
//		free(p[0]);
//		p[0] = (int *)malloc(sizeof(int) * 5);
//	}
//	if (i == 2)
//		p[0][5] = 'a';
//	free(p[0]);
//	return 0;
//}
//
