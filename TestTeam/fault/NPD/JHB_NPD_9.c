#include <time.h>
void jhb_npd_9_f1(){
	struct tm * ptr;
	ptr=(struct tm*)0;
	asctime(ptr); //DEFECT
}
