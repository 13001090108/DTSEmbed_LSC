#include<stdbool.h>
 int get0() { return 0; }
    void test(bool b) {
    	if (get0())                                // defect
		return;
	}
