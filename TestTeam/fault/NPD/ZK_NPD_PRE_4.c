#include <stdlib.h>

struct s_val {
	int i;
	int j;
};

void func2(int, struct s_val *);
void func3(struct s_val *, int);
void func4(int, struct s_val *, int);

void func1()
{
	func2(1, NULL); //DEFECT
}

void func2(int val, struct s_val *var)
{
	func3(var, val);
}

void func3(struct s_val *var, int val)
{
	func4(val, var, 1);
}

void func4(int val, struct s_val *var, int flag)
{
	if (flag > 0) {
		var->i = val;
	} else {
		return;
	}
}