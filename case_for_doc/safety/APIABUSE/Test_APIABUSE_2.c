#include <unistd.h>

void zk_api_1_f1() {
	execlp("li", "li", "-al", 0); //DEFECT
}