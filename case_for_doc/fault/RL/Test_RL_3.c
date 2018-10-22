#include <winsock2.h>
int func7 (int portnum)
{
	SOCKET s; 
	s = socket(AF_INET, SOCK_STREAM, 0);
	if (s != INVALID_SOCKET) {
		if (bind(s, (struct sockaddr *)&sa, sizeof(struct sockaddr_in)) == SOCKET_ERROR) { 
		closesocket(s); 
		return(INVALID_SOCKET); 
		} else {
		int a = 1;
		a = 1;
		} 
	}
	return 1;//DEFECT, RL, s
}