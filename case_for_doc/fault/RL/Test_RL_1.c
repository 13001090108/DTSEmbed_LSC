#include <winsock2.h>
int func2(SOCKET s)
{
	SOCKET new_sock = socket(AF_INET, SOCK_STREAM, IPPROTO_TCP); 
	//do_something(new_sock); 
	//closesocket(new_sock);  RL
	return 0;//DEFECT, RL, new_sock
}