package softtest.DefUseAnalysis.c;

import java.io.*;

import softtest.ast.c.*;
import softtest.symboltable.c.*;
import softtest.cfg.c.*;
import softtest.config.c.Config;

public class TestDefUseAnalysis {
	public static void main(String args[])throws Exception{
		String parsefilename="testcase/defuseanalysis/test3.c";
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
		
		//产生控制流图
		System.out.println("生成控制流图...");
		root.jjtAccept(new ControlFlowVisitor(), null);
		
		//处理定义使用
		System.out.println("生成定义使用链...");
		Config.TRACE=true;
		root.jjtAccept(new DUAnalysisVisitor() , null);
		
		System.out.println("分析完毕.");
	}
}
