#include<windows.h>
void test()
{ 
LPNETRESOURCE lpnr;
DWORD	cbBuffer = 16384;
DWORD	status;
	DWORD	cEntries = 0xffffffff;
		HANDLE	hEnum;
     lpnr = (LPNETRESOURCE) GlobalAlloc (GPTR, cbBuffer);
     	status = WNetEnumResource (hEnum, &cEntries, lpnr, &cbBuffer);
     		if (lpnr[0].lpRemoteName != NULL) ;//defect
}
