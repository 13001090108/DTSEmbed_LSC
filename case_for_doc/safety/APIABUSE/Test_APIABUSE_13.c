#include <unistd.h>
main()
{
    execl("/bin/ls", "ls", "-al", "/etc/passwd", (char *)0);
}