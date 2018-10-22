int fun0(int flag){
	char c[5];//Start:c[5]{NULL}
	int i=4;//Start:c[5]{i:[4,4]}
	switch(flag){
		case 0:i++;break;
		default: c[i]=5;break;
	}
	
	if(flag){//真分支：Start:c[5]{i:[4,5],flag[!=0]}
		c[i]=5;//error:{i:[5,5]}
	}//假分支：Start:c[5]{i:[4,5],flag[0,0]}
	
	return 0;
}/*
int fun1(int flag){//OOB
	char c[5];//Start:c[5]{NULL}
	int i=4;//Start:c[5]{i:[4,4]}
	if(flag){//真分支
		c[i]=5;//Start:c[5]{i:[4,4],flag[!=0]}
	}else{//假分支
		i++;//Start:c[5]{i:[5,5],flag[0,0]}
	}
	
	//状态合并：Start:c[5]{i:[4,5],flag[INF]}
	
	if(flag){//真分支：Start:c[5]{i:[4,5],flag[!=0]}
		c[i]=5;//error:{i:[5,5]}
	}//假分支：Start:c[5]{i:[4,5],flag[0,0]}
	
	return 0;
}*/
/*
int fun2(int flag){
	char c[5];//Start:c[5]{NULL}
	int i=4;//Start:c[5]{i:[4,4]}
	if(flag){//真分支
		c[i]=5;//Start:c[5]{i:[4,4],flag[!=0]}
	}else{//假分支
		i++;//Start:c[5]{i:[5,5],flag[0,0]}
	}
	
	//不进行状态合并：Start:c[5]{i:[4,4],flag[!=0]}  Start:c[5]{i:[5,5],flag[0,0]}
	
	if(flag){//真分支：Start:c[5]{i:[4,4],flag[!=0]}
		c[i]=5;//Start:c[5]{i:[4,4],flag[!=0]}
	}//假分支：Start:c[5]{i:[5,5],flag[0,0]}
	
	return 0;
}*/