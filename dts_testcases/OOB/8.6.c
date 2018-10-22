#include <stdlib.h>

// Memory
void fooa_8_6(char p) {
}
void bara_8_6() {
	fooa_8_6(((char *)malloc(sizeof(char) * 5))[5]);
}
