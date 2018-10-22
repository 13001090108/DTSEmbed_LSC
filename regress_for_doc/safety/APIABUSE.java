package safety;

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

/**
 * 
 * @author liuyan
 *
 */
@RunWith(Parameterized.class)
public class APIABUSE extends ModelTestBase
{
	public APIABUSE(String source,String compiletype, String result)
	{
		super(source, compiletype, result);
	}
//	@Override
//	public void initFSM()
//	{
//		fsmPath = "softtest/rules/gcc/safety/APIABUSE-0.1.xml";
//		
//	}
	@BeforeClass
	public static void setUpBaseChild()
	{
		fsmPath="softtest/rules/gcc/safety/APIABUSE-0.1.xml";
		FSMMachine fsm = FSMLoader.loadXML(fsmPath);
		fsm.setType("safety");
		//每次加入自动机前都清空一下原来的fsms
		FSMAnalysisVisitor.clearFSMS();
		FSMAnalysisVisitor.addFSMS(fsm);
		
		// 加载库函数摘要
		LIB_SUMMARYS_PATH="gcc_lib/apiabuse_summary.xml";
		libManager.loadSingleLibFile(LIB_SUMMARYS_PATH);
		Set<MethodNameDeclaration> libDecls = libManager.compileLib(pre.getLibIncludes());
		interContext = InterContext.getInstance();
		interContext.addLibMethodDecl(libDecls);
	}

	@Parameters
	 public static Collection<Object[]> testcaseAndResults()
	 {
		 return Arrays.asList(
				 new Object[][]
				 {
			/////////////////  1   ///////////////////	
				            {
				            "#include <stdlib.h>"                                                  +"\n"+
				            "#include <stdio.h>"                                                   +"\n"+
				            "#include <time.h>"                                                    +"\n"+
				            ""                                                                     +"\n"+
				            "void ghx_api_9_f9( void )"                                            +"\n"+
				            "{"                                                                    +"\n"+
				            "   int i;"                                                            +"\n"+
				            "srand( (unsigned)time( NULL ) );//DEFECT"                             +"\n"+
				            "i=rand()%100;//DEFECT"                                                +"\n"+
				            "printf(\"%d\\n\",i);"                                                    +"\n"+
				            "}"                                                                    
				            ,
				            "gcc"
				            ,
				            "APIABUSE"
				            ,
				            },
			/////////////////  2   ///////////////////	
				            {
				            "#include <unistd.h>"                                                  +"\n"+
				            ""                                                                     +"\n"+
				            "void zk_api_1_f1() {"                                                 +"\n"+
				            "	execlp(\"li\", \"li\", \"-al\", 0); //DEFECT"                              +"\n"+
				            "}"                                                                    
				            ,
				            "gcc"
				            ,
				            "APIABUSE"
				            ,
				            },
			/////////////////  3   ///////////////////	
				            {
				            "#include <stdlib.h>"                                                  +"\n"+
				            "#include <stdio.h>"                                                   +"\n"+
				            "int ghx_api_3_f3(){"                                                  +"\n"+
				            "const char *filename = \"hello.txt\";"                                  +"\n"+
				            "FILE *f;"                                                             +"\n"+
				            "f = fopen(filename,\"w\");"                                             +"\n"+
				            "if(f == NULL) {"                                                      +"\n"+
				            "//Handle error"                                                       +"\n"+
				            "}"                                                                    +"\n"+
				            "fprintf(f,\"Hello, World\\n\");"                                         +"\n"+
				            "abort();/* oops! data might not be written! */ //DEFECT"              +"\n"+
				            "return 0;"                                                            +"\n"+
				            "}"                                                                    
				            ,
				            "gcc"
				            ,
				            "APIABUSE"
				            ,
				            },
			/////////////////  4   ///////////////////	
				            {
				            "#include <stdio.h>"                                                   +"\n"+
				            "int ghx_api_5_f5()"                                                   +"\n"+
				            "{"                                                                    +"\n"+
				            "remove(\"D:\\1.txt\");"                                                  +"\n"+
				            "return 0;"                                                            +"\n"+
				            "}"                                                                    
				            ,
				            "gcc"
				            ,
				            "APIABUSE"
				            ,
				            },
			/////////////////  5   ///////////////////	
				            {
				            "#include <stdio.h>"                                                   +"\n"+
				            "#include <stdlib.h>"                                                  +"\n"+
				            "int ghx_api_6_f6()"                                                   +"\n"+
				            "{"                                                                    +"\n"+
				            "char *path;"                                                          +"\n"+
				            "char *ptr = getenv(\"PATH\");"                                          +"\n"+
				            "putenv(path);//DEFECT\"                                              " +"\n"+
				            "return 0;"                                                            +"\n"+
				            "}"                                                                    
				            ,
				            "gcc"
				            ,
				            "APIABUSE"
				            ,
				            },
			/////////////////  6   ///////////////////	
				            {
				            "#include <stdio.h>"                                                   +"\n"+
				            "int g()"                                                              +"\n"+
				            "{"                                                                    +"\n"+
				            "  printf(\"a\");//OK"                                                   +"\n"+
				            "}"                                                                    
				            ,
				            "gcc"
				            ,
				            "APIABUSE"
				            ,
				            },
			/////////////////  7   ///////////////////	
				            {
				            "/* remove example: remove myfile.txt */"                              +"\n"+
				            "#include <stdio.h>"                                                   +"\n"+
				            ""                                                                     +"\n"+
				            "int main ()"                                                          +"\n"+
				            "{"                                                                    +"\n"+
				            "  if( remove( \"myfile.txt\" ) != 0 ) //DEFECT,APIABUSE"                +"\n"+
				            "    perror( \"Error deleting file\" );"                                 +"\n"+
				            "  else"                                                               +"\n"+
				            "    puts( \"File successfully deleted\" );"                             +"\n"+
				            "  return 0;"                                                          +"\n"+
				            "}"                                                                    
				            ,
				            "gcc"
				            ,
				            "APIABUSE"
				            ,
				            },
			/////////////////  8   ///////////////////	
				            {
				            "#include <stdio.h>"                                                   +"\n"+
				            "#include <stdlib.h>"                                                  +"\n"+
				            "#include <time.h>"                                                    +"\n"+
				            ""                                                                     +"\n"+
				            "int main ()"                                                          +"\n"+
				            "{"                                                                    +"\n"+
				            "  int iSecret, iGuess;"                                               +"\n"+
				            ""                                                                     +"\n"+
				            "  srand ( time(NULL) );//DEFECT,APIABUSE"                             +"\n"+
				            ""                                                                     +"\n"+
				            "  iSecret = rand() % 10 + 1;//DEFECT,APIABUSE"                        +"\n"+
				            ""                                                                     +"\n"+
				            "  do {"                                                               +"\n"+
				            "    printf (\"Guess the number (1 to 10): \");"                         +"\n"+
				            "    scanf (\"%d\",&iGuess);"                                            +"\n"+
				            "    if (iSecret<iGuess) puts (\"The secret number is lower\");"         +"\n"+
				            "    else if (iSecret>iGuess) puts (\"The secret number is higher\");"   +"\n"+
				            "  } while (iSecret!=iGuess);"                                         +"\n"+
				            ""                                                                     +"\n"+
				            "  puts (\"Congratulations!\");"                                         +"\n"+
				            "  return 0;"                                                          +"\n"+
				            "}"                                                                    
				            ,
				            "gcc"
				            ,
				            "APIABUSE"
				            ,
				            },
			/////////////////  9   ///////////////////	
				            {
				            "/* abort example */"                                                  +"\n"+
				            "#include <stdio.h>"                                                   +"\n"+
				            "#include <stdlib.h>"                                                  +"\n"+
				            ""                                                                     +"\n"+
				            "int main ()"                                                          +"\n"+
				            "{"                                                                    +"\n"+
				            "  FILE * pFile;"                                                      +"\n"+
				            "  pFile= fopen (\"myfile.txt\",\"r\");"                                   +"\n"+
				            "  if (pFile == NULL) "                                                +"\n"+
				            "  {"                                                                  +"\n"+
				            "    fputs (\"error opening file\\n\",stderr);"                           +"\n"+
				            "    abort();  //DEFECT,APIABUSE"                                      +"\n"+
				            "  }"                                                                  +"\n"+
				            ""                                                                     +"\n"+
				            "  /* regular process here */"                                         +"\n"+
				            ""                                                                     +"\n"+
				            "  fclose (pFile);"                                                    +"\n"+
				            "  return 0;"                                                          +"\n"+
				            "}"                                                                    
				            ,
				            "gcc"
				            ,
				            "APIABUSE"
				            ,
				            },
			/////////////////  10   ///////////////////	
				            {
				            "#include<stdlib.h>"                                                   +"\n"+
				            "int gen_rand()"                                                       +"\n"+
				            "{"                                                                    +"\n"+
				            "	int n;"                                                              +"\n"+
				            "	n=random(100);"                                                      +"\n"+
				            "	return(n);"                                                          +"\n"+
				            "}"                                                                    
				            ,
				            "gcc"
				            ,
				            "APIABUSE"
				            ,
				            },
			/////////////////  11   ///////////////////	
				            {
				            "#include<stdlib.h>"                                                   +"\n"+
				            "void f()"                                                             +"\n"+
				            "{"                                                                    +"\n"+
				            "	char c='c';"                                                         +"\n"+
				            "	char *state;"                                                        +"\n"+
				            "	char *setstate=*setstate(state);"                                    +"\n"+
				            "}"                                                                    
				            ,
				            "gcc"
				            ,
				            "APIABUSE"
				            ,
				            },
			/////////////////  12   ///////////////////	
				            {
				            "#include <stdlib.h>"                                                  +"\n"+
				            "#include <stdio.h>"                                                   +"\n"+
				            "int main(void)"                                                       +"\n"+
				            "{"                                                                    +"\n"+
				            "printf(\"About to spawn command.com and run a DOS command\\n\");"        +"\n"+
				            "system(\"dir\");"                                                       +"\n"+
				            "return 0;"                                                            +"\n"+
				            "}"                                                                    
				            ,
				            "gcc"
				            ,
				            "APIABUSE"
				            ,
				            },
			/////////////////  13   ///////////////////	
				            {
				            "#include <unistd.h>"                                                  +"\n"+
				            "main()"                                                               +"\n"+
				            "{"                                                                    +"\n"+
				            "    execl(\"/bin/ls\", \"ls\", \"-al\", \"/etc/passwd\", (char *)0);"         +"\n"+
				            "}"                                                                    
				            ,
				            "gcc"
				            ,
				            "APIABUSE"
				            ,
				            },
			/////////////////  14   ///////////////////	
				            {
				            "#include <unistd.h>"                                                  +"\n"+
				            "main()"                                                               +"\n"+
				            "{"                                                                    +"\n"+
				            "    char * argv[] = {\"ls\", \"-al\", \"/etc/passwd\", 0};"                 +"\n"+
				            "    execvp(\"ls\", argv);"                                              +"\n"+
				            "}"                                                                    
				            ,
				            "gcc"
				            ,
				            "APIABUSE"
				            ,
				            },
			/////////////////  15   ///////////////////	
				            {
				            "#include <unistd.h>"                                                  +"\n"+
				            "main()"                                                               +"\n"+
				            "{"                                                                    +"\n"+
				            "    char * argv[] = {\"ls\", \"-al\", \"/etc/passwd\", (char *)0};"         +"\n"+
				            "    char * envp[] = {\"PATH=/bin\", 0};"                                +"\n"+
				            "    execve(\"/bin/ls\", argv, envp);"                                   +"\n"+
				            "}"                                                                    
				            ,
				            "gcc"
				            ,
				            "APIABUSE"
				            ,
				            },
				 });
	 }

}
