package softtest.symboltable.c;

import java.io.File;
import java.io.FileInputStream;

import softtest.ast.c.ASTTranslationUnit;
import softtest.ast.c.CCharStream;
import softtest.ast.c.CParser;

public class TestSymbolTable
{
	private static final String filePath="testcase/symboltable/a.c";
	public static void main(String[] args) throws Exception
	{
		File file=new File(filePath);
		CParser parser=CParser.getParser(new CCharStream(new FileInputStream(file)));
		ASTTranslationUnit root=parser.TranslationUnit();
		ScopeAndDeclarationFinder sc=new ScopeAndDeclarationFinder();
		
		root.jjtAccept(sc, null);
		
		OccurrenceAndExpressionTypeFinder oat=new OccurrenceAndExpressionTypeFinder();
		root.jjtAccept(oat, null);
		System.out.println(root.getScope().print());
	}

}
