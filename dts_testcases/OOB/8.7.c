#include <stdlib.h>

// Memory
void fooa_8_7(char p) {
}
char *baza_8_7() {
	return (char *)malloc(sizeof(char) * 5);
}
void bara_8_7(char *p) {
	fooa_8_7(baza_8_7()[5]);
}

