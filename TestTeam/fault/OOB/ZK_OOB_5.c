#include <stdio.h>

#define BUFSIZE 10

bool zk_oob_5_f1()
{
	int buf[BUFSIZE];
	int count;

	for(;;) {
		if (count >= BUFSIZE) {
			return false;
		}

		count = count + 1;
		buf[count] = 1; //DEFECT
	}
}