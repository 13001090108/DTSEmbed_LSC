package softtest.domain.c.analysis;

import java.io.FileInputStream;

import softtest.domain.c.analysis.ControlFlowDomainVisitor;
import softtest.ast.c.ASTTranslationUnit;
import softtest.ast.c.CCharStream;
import softtest.ast.c.CParser;
import softtest.cfg.c.ControlFlowVisitor;
import softtest.config.c.Config;
import softtest.symboltable.c.AbstractScope;
import softtest.symboltable.c.OccurrenceAndExpressionTypeFinder;
import softtest.symboltable.c.ScopeAndDeclarationFinder;

public class TestIntervalAnalysis {
	public static void main(String[] args) throws Exception{
		String parsefilename="testcase/intervalanalysis/TestIntervalAnalysis.c";
		Config.TRACE=true;
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
		
		//区间分析
		root.jjtAccept(new ControlFlowDomainVisitor(), null);
		
		System.out.println("分析完毕.");
	}

}
