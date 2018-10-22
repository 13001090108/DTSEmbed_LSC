package softtest.test.gcc.rules.rule;

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
public class FMC extends ModelTestBase {
	public FMC(String source,String compiletype, String result)
	{
		super(source, compiletype, result);
	}

	@BeforeClass
	public static void setUpBaseChild()
	{
		fsmPath="softtest/rules/gcc/rule/FMC-0.1.xml";
		FSMMachine fsm = FSMLoader.loadXML(fsmPath);
		fsm.setType("rule");
		//每次加入自动机前都清空一下原来的fsms
		FSMAnalysisVisitor.clearFSMS();
		FSMAnalysisVisitor.addFSMS(fsm);
	}
	
	 @Parameters
	 public static Collection<Object[]> testcaseAndResults()
	 {
		 return Arrays.asList(new Object[][] {
	/////////////////  1   ///////////////////	
		            {
		            "#include <stdio.h>"                                                   +"\n"+
		            "int main(  )"                                                         +"\n"+
		            "{"                                                                    +"\n"+
		            "	FILE *stream, *stream2, *stream3;"                                             +"\n"+
		            "   int numclosed;"                                                    +"\n"+
		            "   stream3=fopen(\"hello.c\",\"r\"); //DEFECT"                                     +"\n"+
		            "   if( (stream  = fopen( \"crt_fopen.c\", \"r\" )) == NULL )"             +"\n"+
		            "      printf( \"The file 'crt_fopen.c' was not opened\\n\" );"           +"\n"+
		            "   else"                                                              +"\n"+
		            "      printf( \"The file 'crt_fopen.c' was opened\\n\" );"               +"\n"+
		            "   if( (stream2 = fopen( \"data2\", \"w+\" )) != NULL )"                  +"\n"+
		             "      printf( \"The file 'data2' was opened\\n\" );"                     +"\n"+
		            "   if( stream)"                                                       +"\n"+
		            "   {"                                                                 +"\n"+
		            "      if ( fclose( stream ) )"                                        +"\n"+
		            "      {"                                                              +"\n"+
		            "         printf( \"The file 'crt_fopen.c' was not closed\\n\" );"        +"\n"+
		            "      }"                                                              +"\n"+
		            "   }"                                                                 +"\n"+
		            "   numclosed = _fcloseall( );"                                        +"\n"+
		            "   printf( \"Number of files closed by _fcloseall: %u\\n\", numclosed );"+"\n"+
		            "}"                                                                  
		            ,
		            "gcc"
		            ,
		            "FMC"
		            ,
		            },
	///////////////// 2   ///////////////////	
		            {
		            "#include <stdio.h>"                                                   +"\n"+
		            "int main(  )"                                                         +"\n"+
		            "{"                                                                    +"\n"+
		            "	FILE *stream;"                                    +"\n"+
		            "   stream=fopen(\"hello.c\",\"r\");"                                     +"\n"+
		            "   if(stream)"                                                        +"\n"+
		            "   {"                                                                 +"\n"+
		            "         printf( \"The file 'hello.c' was opened\\n\" );"                +"\n"+
		            "  		  fclose(stream); "                                                                 +"\n"+
		            "   }"                                                                 +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "OK"
		            ,
		            },
    /////////////////  3   ///////////////////	

		            {
			            "#include <stdio.h>"                                                   +"\n"+
			            "int main(  )"                                                         +"\n"+
			            "{"                                                                    +"\n"+
			            "	FILE *stream;"                                    +"\n"+
			            "   stream=fopen(\"hello.c\",\"r\");"                                     +"\n"+
			            "   if(!stream)"                                                        +"\n"+
			            "   {"                                                                 +"\n"+
			            "         printf( \"The file 'hello.c' wasn't opened\\n\" );"                +"\n"+
			            "   }"                                                                 +"\n"+
			            "  		  fclose(stream); "                                                                 +"\n"+
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
