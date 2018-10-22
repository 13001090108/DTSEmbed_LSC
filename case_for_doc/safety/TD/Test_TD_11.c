void func1() {
    int id;
    scanf("%d", id);
	setpid(id);
}

void func2() {
    int id;
    scanf("%d", id);
	setpgid(1, id);
}

void func3() {
    int pri;
    scanf("%d", pri);
	setpriority(1, 1, pri);
}
