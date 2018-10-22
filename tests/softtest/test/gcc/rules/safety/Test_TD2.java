package softtest.test.gcc.rules.safety;

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
import softtest.summary.lib.c.LibManager;
import softtest.symboltable.c.MethodNameDeclaration;
import softtest.test.c.rules.ModelTestBase;

@RunWith(Parameterized.class)
public class Test_TD2 extends ModelTestBase
{

	public Test_TD2(String source,String compiletype, String result)
	{
		super(source, compiletype, result);
	}

	@BeforeClass
	public static void setUpBaseChild()
	{
		fsmPath = "softtest/rules/gcc/safety/TD-0.1.xml";
		FSMMachine fsm = FSMLoader.loadXML(fsmPath);
		fsm.setType("safety");
		//每次加入自动机前都清空一下原来的fsms
		FSMAnalysisVisitor.clearFSMS();
		FSMAnalysisVisitor.addFSMS(fsm);
		
		/*
		LIB_SUMMARYS_PATH="gcc_lib";
		libManager.loadLib(LIB_SUMMARYS_PATH);
		Set<MethodNameDeclaration> libDecls = libManager.compileLib(pre.getLibIncludes());
		interContext = InterContext.getInstance();
		interContext.addLibMethodDecl(libDecls);
		*/

	}

	@Parameters
	 public static Collection<Object[]> testcaseAndResults()
	 {
		 return Arrays.asList(new Object[][]
				 {
				 
				 {
			            "#include<stdio.h>"                                                    +"\n"+
			            "#include<stdlib.h>"                                                   +"\n"+
			            "int func(int a, double b)"                                            +"\n"+
			            "{"                                                                    +"\n"+
			            "	char *s = getenv(\"ConFig_File\");"                                    +"\n"+
			            "	fopen(s, \"r\");"                                                      +"\n"+
			            "	return 0;"                                                           +"\n"+
			            "}"                                                                    
			            ,
			            "gcc"
			            ,
			            "TD"
			            ,
			            },					 	
//////////////////////////////0////////////////////////////////////////////////
				 
			        {
			            "#include <string.h>"                                                  +"\n"+
			            "#define BUFSIZE 256"                                                  +"\n"+
			            "int main(int argc, char **argv) {"                                    +"\n"+
			            "char *buf;"                                                           +"\n"+
			            "buf = (char *)malloc(BUFSIZE);"                                       +"\n"+
			            "strcpy(buf, argv[1]);"                                                +"\n"+
			            "}"                                                                    
			            ,
			            "gcc"
			            ,
			            "TD"
			            ,
			            },

//////////////////////////////1////////////////////////////////////////////////
			        {
			            "#include <stdio.h>"                                                   +"\n"+
			            "int main(int argc, char **argv) {"                                    +"\n"+
			            "  char buf[5012];"                                                +"\n"+
			            "  memcpy(buf, argv[1], 5012);"                                    +"\n"+
			            "  printf(argv[1]);  /*  Bad */"                                   +"\n"+
			            "  return (0);"                                                    +"\n"+
			            "}"                                                                    
			            ,
			            "gcc"
			            ,
			            "TD"
			            ,
			            },
			            
//////////////////////////////2////////////////////////////////////////////////			                
			        {
			            "#include <stdio.h>"                                                   +"\n"+
			            "#include <process.h>"                                                 +"\n"+
			            "int main()"                                                           +"\n"+
			            "{"                                                                    +"\n"+
			            "char buf[5];"                                                         +"\n"+
			            "scanf(\"%s\", buf);"                                                    +"\n"+
			            "execl(buf, buf, \"hello\", NULL);"                                      +"\n"+
			            "	return 0;"                                                           +"\n"+
			            "}"                                                                    
			            ,
			            "gcc"
			            ,
			            "TD"
			            ,
			            },
			            
///////////////////////////////3////////////////////////////////////////////////			                    
			        {
			            "#include <stdio.h>"                                                   +"\n"+
			            "#include <stdlib.h>"                                                  +"\n"+
			            "#include <string.h>"                                                  +"\n"+
			            "#define bufsize 256"                                                  +"\n"+
			            "int main () {"                                                        +"\n"+
			            "char input[bufsize];"                                                 +"\n"+
			            "char s[bufsize];"                                                     +"\n"+
			            "printf(\"Enter file name:\\n\");"                                        +"\n"+
			            "scanf(\"%s\",input);"                                                   +"\n"+
			            "FILE *fp;"                                                            +"\n"+
			            "fp=fopen(input,\"r\");"                                                 +"\n"+
			            "fgets(s,bufsize,fp);"                                                 +"\n"+
			            "printf(\"%s\",s);"                                                      +"\n"+
			            "return 0;} "                                                          
			            ,
			            "gcc"
			            ,
			            "TD"
			            ,
			            },
			            
///////////////////////////////4////////////////////////////////////////////////			                        
			        {
			            "#include <stdio.h>"                                                   +"\n"+
			            "#include <stdlib.h>"                                                  +"\n"+
			            "int main(int argc, char **argv) {"                                    +"\n"+
			            "system(argv[0]);"                                                     +"\n"+
			            "return (0);"                                                          +"\n"+
			            "}"                                                                    +"\n"+
			            " "                                                                    
			            ,
			            "gcc"
			            ,
			            "TD"
			            ,
			            }			            			                
				 
				 }
	 );
	 }
				 }