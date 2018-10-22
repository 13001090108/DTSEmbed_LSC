#include <unistd.h>
main()
{
    char * argv[] = {"ls", "-al", "/etc/passwd", 0};
    execvp("ls", argv);
}