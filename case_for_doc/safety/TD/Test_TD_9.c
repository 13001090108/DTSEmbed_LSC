void func1() {
    char name[100];
    scanf("%s", name);
	gethostbyaddr(name);
}

void func2() {
    char name[100];
    scanf("%s", name);
	gethostbyname(name);
}

void func3() {
    char name[100];
    scanf("%s", name);
	sethostname(name);
}
