#define true 1
#define false 0

void f_BBU(_Bool flags)
{
    if(flags & 4 == 0){// BBU,defect
        flags = true;
    }
}
