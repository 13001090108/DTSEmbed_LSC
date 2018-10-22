package softtest.callgraph.c;

import java.io.*;

import softtest.DefUseAnalysis.c.DUAnalysisVisitor;
import softtest.ast.c.*;
import softtest.cfg.c.ControlFlowVisitor;
import softtest.symboltable.c.*;

import java.util.*;

public class TestCallGraph {
	public static void main(String args[]) throws Exception{
		String parsefilename="testcase/callgraph/testCallGraph.c";
		//产生抽象语法树
		System.out.println("生成抽象语法树...");
		CParser parser = CParser.getParser(new CCharStream(new FileInputStream(parsefilename)));
		ASTTranslationUnit root=parser.TranslationUnit();
		
		//产生符号表
		System.out.println("生成符号表...");
		ScopeAndDeclarationFinder sc=new ScopeAndDeclarationFinder();
		root.jjtAccept(sc, null);
		OccurrenceAndExpressionTypeFinder o=new OccurrenceAndExpressionTypeFinder();
		root.jjtAccept(o, null);
		
		CGraph g = new CGraph();
		((AbstractScope)root.getScope()).resolveCallRelation(g);
		
		List<CVexNode> list=g.getTopologicalOrderList();
		Collections.reverse(list);
		System.out.println("调用关系拓扑逆序：");
		for(CVexNode n:list){
			System.out.print(n.getName()+"  ");
		}
		System.out.println();
		
		String name ="temp/testCallGraph";
		g.accept(new DumpCGraphVisitor(), name + ".dot");
		System.out.println("调用图图输出到了文件" + name + ".dot");
		try {
			java.lang.Runtime.getRuntime().exec("dot -Tjpg -o " + name + ".jpg " + name + ".dot").waitFor();
		} catch (IOException e1) {
			System.out.println(e1);
		} catch (InterruptedException e2) {
			System.out.println(e2);
		}
		System.out.println("调用图打印到了文件" + name + ".jpg");
	}
}
