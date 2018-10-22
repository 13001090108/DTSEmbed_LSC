package softtest.fsm.c;

import java.io.IOException;

public class TestFSM {
	public static void main(String args[]) {
		FSMMachine fsm = FSMLoader
				.loadXML("softtest\\rules\\c\\fault\\RL-0.1.xml");
		String name = "temp/" + fsm.getName();
		fsm.accept(new DumpFSMVisitor(), name + ".dot");
		System.out.println("状态机输出到了文件" + name + ".dot");
		try {
			java.lang.Runtime.getRuntime().exec(
					"dot -Tjpg -o " + name + ".jpg " + name + ".dot").waitFor();
		} catch (IOException e1) {
			System.out.println(e1);
		} catch (InterruptedException e2) {
			System.out.println(e2);
		}
		System.out.println("状态机打印到了文件" + name + ".jpg");
	}
}
