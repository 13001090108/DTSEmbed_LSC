#include <winsock2.h>
int func4 (int portnum)
{
	SOCKET s; 
	s = socket(AF_INET, SOCK_STREAM, IPPROTO_TCP);
	if (s == INVALID_SOCKET) 
	return INVALID_SOCKET;
	if (bind(s, (struct sockaddr *)&s, sizeof(struct sockaddr_in)) == SOCKET_ERROR) { 
		closesocket(s); 
		return(INVALID_SOCKET); 
	} 
	return 1;//DEFECT, RL, s
}