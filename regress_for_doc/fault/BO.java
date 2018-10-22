package fault;

import java.util.Arrays;
import java.util.Collection;
import java.util.Set;

import org.junit.BeforeClass;
import org.junit.runner.RunWith;
import org.junit.runners.Parameterized;
import org.junit.runners.Parameterized.Parameters;

import softtest.fsm.c.FSMLoader;
import softtest.fsm.c.FSMMachine;
import softtest.fsmanalysis.c.FSMAnalysisVisitor;
import softtest.interpro.c.InterContext;
import softtest.symboltable.c.MethodNameDeclaration;
import softtest.test.c.rules.ModelTestBase;

@RunWith(Parameterized.class)
public class BO extends ModelTestBase{
	public BO(String source,String compiletype, String result)
	{
		super(source, compiletype, result);
	}

	@BeforeClass
	public static void setUpBaseChild()
	{
		fsmPath="softtest/rules/gcc/fault/BO-0.1.xml";
		FSMMachine fsm = FSMLoader.loadXML(fsmPath);
		fsm.setType("fault");
		//每次加入自动机前都清空一下原来的fsms
		FSMAnalysisVisitor.clearFSMS();
		FSMAnalysisVisitor.addFSMS(fsm);
		
		//加载库函数摘要
		LIB_SUMMARYS_PATH="gcc_lib/bo_summary.xml";
		libManager.loadSingleLibFile(LIB_SUMMARYS_PATH);
		Set<MethodNameDeclaration> libDecls = libManager.compileLib(pre.getLibIncludes());
		interContext = InterContext.getInstance();
		interContext.addLibMethodDecl(libDecls);
	}
	
	 @Parameters
	 public static Collection<Object[]> testcaseAndResults()
	 {
		 return Arrays.asList(new Object[][] {
	/////////////////  1   ///////////////////	
		            {
		            "#include <string.h>"                                                  +"\n"+
		            "int main(int argc, char *argv[])"                                     +"\n"+
		            "{"                                                                    +"\n"+
		            "	char buf[10];"                                                       +"\n"+
		            "	/*  BAD  */"                                                         +"\n"+
		            "	strcpy(buf, \"AAAAAAAAAAAAAAAAA\");"                                   +"\n"+
		            "	return 0;"                                                           +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "BO"
		            ,
		            },
		            
	/////////////////  2   ///////////////////	
		            {
		            "int main()"                                                           +"\n"+
		            "{"                                                                    +"\n"+
		            "	char a[10];"                                                         +"\n"+
		            "	char b[100];"                                                        +"\n"+
		            "	strcpy(a, b);"                                                       +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "BO"
		            ,
		            },
		            
	/////////////////  3   ///////////////////	
		            {
		            "#include <stdio.h>"                                                   +"\n"+
		            "#include <string.h>"                                                  +"\n"+
		            "int main() {"                                                         +"\n"+
		            "	char longString[] = \"Cellular bananular phone\";"                     +"\n"+
		            "	char shortString[16];"                                               +"\n"+
		            "	strncpy(shortString, longString, 16);"                               +"\n"+
		            "	printf(\"The last character in shortString is: %c %1$x\\n\","           +"\n"+
		            "	shortString[15]);"                                                   +"\n"+
		            "	return (0);"                                                         +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "BO"
		            ,
		            },
		            
		            
	/////////////////  4  ///////////////////	
		            {
		            "#include <stdio.h>"                                                   +"\n"+
		            "#include <string.h>"                                                  +"\n"+
		            "#define MAXSIZE 40 "                                                  +"\n"+
		            "void test(char *str){"                                                +"\n"+
		            "	char buf[MAXSIZE];"                                                  +"\n"+
		            "	bcopy(str,buf, MAXSIZE);"                                            +"\n"+
		            "	printf(\"results: %s\\n\", buf);"                                       +"\n"+
		            "} "                                                                   +"\n"+
		            "int main(int argc, char **argv){"                                     +"\n"+
		            "	char *userstr;"                                                      +"\n"+
		            "	if(argc > 1){"                                                       +"\n"+
		            "		userstr = argv[1];"                                                 +"\n"+
		            "		test(userstr);"                                                     +"\n"+
		            "	}"                                                                   +"\n"+
		            "	return 0;"                                                           +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "BO"
		            ,
		            },

	/////////////////  5   ///////////////////	
		            {
		            "#include <string.h>"                                                  +"\n"+
		            "#include <stdio.h>"                                                   +"\n"+
		            "int main(int argc, char *argv[])"                                     +"\n"+
		            "{"                                                                    +"\n"+
		            "	char source[10];"                                                    +"\n"+
		            "	int i;"                                                              +"\n"+
		            "	strcpy(source, \"0123456789\");"                                       +"\n"+
		            "	char *dest = (char *)malloc(strlen(source));"                        +"\n"+
		            "	for (i=1;i<=11;i++)"                                                 +"\n"+
		            "		dest[i] = source[i];"                                               +"\n"+
		            "	dest[i] = '\\0';"                                                     +"\n"+
		            "	printf(\"dest = %s\\n\", dest);"                                        +"\n"+
		            "	return 0;"                                                           +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "BO"
		            ,
		            },

		 
		 });
	 }
}

