package softtest.test.c.gcc.expression;

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
public class RL_EXP extends ModelTestBase {
	public RL_EXP(String source,String compiletype, String result)
	{
		super(source, compiletype, result);
	}

	@BeforeClass
	public static void setUpBaseChild()
	{
		fsmPath="softtest/rules/gcc/fault/RL-0.1.xml";
		FSMMachine fsm = FSMLoader.loadXML(fsmPath);
		fsm.setType("fault");
		//每次加入自动机前都清空一下原来的fsms
		FSMAnalysisVisitor.clearFSMS();
		FSMAnalysisVisitor.addFSMS(fsm);
		
		//加载库函数摘要
		LIB_SUMMARYS_PATH="gcc_lib/rm_summary.xml";
		libManager.loadSingleLibFile(LIB_SUMMARYS_PATH);
		Set<MethodNameDeclaration> libDecls = libManager.compileLib(pre.getLibIncludes());
		interContext = InterContext.getInstance();
		interContext.addLibMethodDecl(libDecls);
	}
	
	@Parameters
	 public static Collection<Object[]> testcaseAndResults()
	 {
		 return Arrays.asList(new Object[][] {
	/////////////////  0   ///////////////////	
		            {
		            "#include <stdio.h>"                                                   +"\n"+
		            "int func1 ()"                                                         +"\n"+
		            "{"                                                                    +"\n"+
		            "  FILE * pFile;"                                                      +"\n"+
		            "  pFile = fopen (\"myfile.txt\",\"w\");"                              +"\n"+
		            "  if (pFile!=NULL)"                                                   +"\n"+
		            "  {"                                                                  +"\n"+
		            "    fputs (\"fopen example\",pFile);"                                 +"\n"+
		            "    fclose (pFile);"                                                  +"\n"+
		            "  }"                                                                  +"\n"+
		            "  return 0;"                                                  +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "OK"
		            ,
		            },	 
	/////////////////  1   ///////////////////	
		            {
		            "#include <stdio.h>"                                                   +"\n"+
		            "FILE * gFile;"                                                        +"\n"+
		            "int func4 ()"                                                         +"\n"+
		            "{"                                                                    +"\n"+
		            "  FILE * pFile;"                                                      +"\n"+
		            "  pFile = fopen (\"myfile.txt\",\"w\");"                                  +"\n"+
		            "  if (pFile==NULL) {"                                                 +"\n"+
		            "  	return 0;"                                                         +"\n"+
		            "  }"                                                                  +"\n"+
		            "  fputs (\"fopen example\",pFile);"                                     +"\n"+
		            "  gFile = pFile;"                                                     +"\n"+
		            "  return 0;//FP, RL"                                                  +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "OK"
		            ,
		            },
	/////////////////  2   ///////////////////	
		            {
		            "#include <stdio.h>"                                                   +"\n"+
		            "int func7 ()"                                                         +"\n"+
		            "{"                                                                    +"\n"+
		            "  FILE * pFile;"                                                      +"\n"+
		            "  pFile = fopen (\"myfile.txt\",\"w\");"                                  +"\n"+
		            "  if (pFile!=NULL)"                                                   +"\n"+
		            "  {"                                                                  +"\n"+
		            "    fputs (\"fopen example\",pFile);"                                   +"\n"+
		            "  }"                                                                  +"\n"+
		            "  return 0;//DEFECT, RL, pFile"                                       +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "RL"
		            ,
		            },
	/////////////////  3   ///////////////////	
		            {
		            "#include <stdio.h>"                                                   +"\n"+
		            "int func1 ()"                                                         +"\n"+
		            "{"                                                                    +"\n"+
		            "    struct e{"                                                        +"\n"+
		            "      FILE * pFile;  "                                                +"\n"+
		            "   }g;"                                                               +"\n"+
		            "  "                                                                   +"\n"+
		            "  g.pFile = fopen (\"myfile.txt\",\"w\");"                                +"\n"+
		            "  if (g.pFile!=NULL)"                                                 +"\n"+
		            "  {"                                                                  +"\n"+
		            "    fputs (\"fopen example\",g.pFile);"                                 +"\n"+
		            "  }"                                                                  +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "RL"
		            ,
		            },
//////////////////////////4//////////////////////////////////////////////	
		            {
		            "#include<stdio.h>"                                                    +"\n"+
		            "main()"                                                               +"\n"+
		            "{"                                                                    +"\n"+
		            "    struct a{"                                                        +"\n"+
		            "        FILE *f;"                                                     +"\n"+
		            "    } *s;"                                                            +"\n"+
		            ""                                                                     +"\n"+
		            "    s->f = fopen(\"abc.txt\", \"r\");"                                +"\n"+
		            "    if(s->f == NULL)"                                                 +"\n"+
		            "        return 0;"                                                    +"\n"+
		            ""                                                                     +"\n"+
		            "    fclose(s->f);"                                                    +"\n"+
		            "    return 0;"                                                        +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "OK"
		            ,
		            },
		            

	     });
	 }
}