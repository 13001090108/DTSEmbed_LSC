package softtest.DefUseAnalysis.c;

import java.util.Arrays;

public class DUStatistics {
	public static int usepoints=0,defpoints=0;
	public static int func=0,entrance=0,global=0;//函数内，参数，全局
	public static int simple=0,complex=0;//简单变量，复杂变量
	public static int assign=0,condition=0,loop=0,function=0,param=0,other=0;
	public static int[] def = new int[4];

	public static void print() {
		System.out.println("DUStatistics [usepoints=" + usepoints + ", defpoints=" + defpoints + ", func=" + func + ", entrance="
				+ entrance + ", global=" + global + ", simple=" + simple + ", complex=" + complex + ", assign=" + assign
				+ ", condition=" + condition + ", loop=" + loop + ", function=" + function + ", param=" + param
				+ ", other=" + other + ", def=" + Arrays.toString(def) + "]");
	}

	
}
