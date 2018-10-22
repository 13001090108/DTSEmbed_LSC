package softtest.test.gcc.rules.rule;

import java.util.Arrays;
import java.util.Collection;

import org.junit.BeforeClass;

import org.junit.runner.RunWith;
import org.junit.runners.Parameterized;
import org.junit.runners.Parameterized.Parameters;


import softtest.fsm.c.FSMLoader;
import softtest.fsm.c.FSMMachine;

import softtest.fsmanalysis.c.FSMAnalysisVisitor;

import softtest.test.c.rules.ModelTestBase;

@RunWith(Parameterized.class)
public class NNM extends ModelTestBase{
	public NNM(String source,String compiletype, String result)
	{
		super(source, compiletype, result);
	}
	
	@BeforeClass
	public static void setUpBaseChild()
	{
		fsmPath="softtest/rules/gcc/question/NNM-0.1.xml";
		FSMMachine fsm = FSMLoader.loadXML(fsmPath);
		fsm.setType("question");
		//每次加入自动机前都清空一下原来的fsms
		FSMAnalysisVisitor.clearFSMS();
		FSMAnalysisVisitor.addFSMS(fsm);
	}
	 @Parameters
	 public static Collection<Object[]> testcaseAndResults()
	 {
		 return Arrays.asList(new Object[][] {
		/////////////////  0   ///////////////////	
			            {
			            "#include <stdlib.h>"                                                  +"\n"+
			            "#include <stdio.h>"                                                   +"\n"+
			            "#include <malloc.h>"                                                  +"\n"+
			            ""                                                                     +"\n"+
			            "int main( void )"                                                     +"\n"+
			            "{"                                                                    +"\n"+
			            "   char *string;"                                                     +"\n"+
			            "   string =(char *) malloc(20);"                                              +"\n"+
			            ""                                                                     +"\n"+
			            "   if( string == NULL )"                                              +"\n"+
			            "      printf( \"Insufficient memory available\\n\" );"                   +"\n"+
			            "   else"                                                              +"\n"+
			            "   {"                                                                 +"\n"+
			            "      printf( \"Memory space allocated for path name\\n\" );"            +"\n"+
			            "      free( string );"                                                +"\n"+
			            "      printf( \"Memory freed\\n\" );"                                    +"\n"+
			            "   }"                                                                 +"\n"+
			            "}"                                                                    
			            ,
			            "gcc"
			            ,
			            "NNM"
			            ,
			            },
		/////////////////  1   ///////////////////	
			            {
			            "#include <stdio.h>"                                                   +"\n"+
			            "#include <malloc.h>"                                                  +"\n"+
			            ""                                                                     +"\n"+
			            "int main( void )"                                                     +"\n"+
			            "{"                                                                    +"\n"+
			            "   long *buffer;"                                                     +"\n"+
			            ""                                                                     +"\n"+
			            "   buffer = (long *)calloc( 40, sizeof( long ) );"                    +"\n"+
			            "   if( buffer != NULL )"                                              +"\n"+
			            "      printf( \"Allocated 40 long integers\\n\" );"                      +"\n"+
			            "   else"                                                              +"\n"+
			            "      printf( \"Can't allocate memory\\n\" );"                           +"\n"+
			            "   free( buffer );"                                                   +"\n"+
			            "}"                                                                    
			            ,
			            "gcc"
			            ,
			            "NNM"
			            ,
			            },
		/////////////////  2   ///////////////////	
					            {
					            "#include <stdlib.h>"                                                  +"\n"+
					            "#include <stdio.h>"                                                   +"\n"+
					            "#include <malloc.h>"                                                  +"\n"+
					            ""                                                                     +"\n"+
					            "int main( void )"                                                     +"\n"+
					            "{"                                                                    +"\n"+
					            "   char *string;"                                                     +"\n"+
					            "   char test[10]=\"abdrfjal\";"                                              +"\n"+
					            "	string=test;"                                                                     +"\n"+
					            "   printf( \"%s\",*string);"                                    +"\n"+
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
			            "#include <malloc.h>"                                                  +"\n"+
			            "#include <stdlib.h>"                                                  +"\n"+
			            ""                                                                     +"\n"+
			            "int main( void )"                                                     +"\n"+
			            "{"                                                                    +"\n"+
			            "   long *buffer, *oldbuffer;"                                         +"\n"+
			            "   size_t size;"                                                      +"\n"+
			            ""                                                                     +"\n"+
			            "   if( (buffer = (long *)malloc( 1000 * sizeof( long ) )) == NULL )"  +"\n"+
			            "      exit( 1 );"                                                     +"\n"+
			            ""                                                                     +"\n"+
			            "   size = _msize( buffer );"                                          +"\n"+
			            "   printf_s( \"Size of block after malloc of 1000 longs: %u\\n\", size );"+"\n"+
			            ""                                                                     +"\n"+
			            "   // Reallocate and show new size:"                                  +"\n"+
			            "   oldbuffer = buffer;     // save pointer in case realloc fails"     +"\n"+
			            "   if( (buffer = realloc( buffer, size + (1000 * sizeof( long )) )) " +"\n"+
			            "        ==  NULL )"                                                   +"\n"+
			            "   {"                                                                 +"\n"+
			            "      free( oldbuffer );  // free original block"                     +"\n"+
			            "      exit( 1 );"                                                     +"\n"+
			            "   }"                                                                 +"\n"+
			            "   size = _msize( buffer );"                                          +"\n"+
			            "   printf_s( \"Size of block after realloc of 1000 more longs: %u\\n\", "+"\n"+
			            "            size );"                                                  +"\n"+
			            ""                                                                     +"\n"+
			            "   free( buffer );"                                                   +"\n"+
			            "   exit( 0 );"                                                        +"\n"+
			            "}"                                                                    
			            ,
			            "gcc"
			            ,
			            "NNM"
			            ,
			            },


	 
		 });
	 }
}

