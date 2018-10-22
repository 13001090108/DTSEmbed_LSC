package softtest.test.c.gcc.regression;

import static org.junit.Assert.fail;
import static org.junit.Assert.assertEquals;

import java.io.ByteArrayInputStream;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
import java.util.Collections;
import java.util.List;

import org.apache.log4j.BasicConfigurator;
import org.apache.log4j.PropertyConfigurator;
import org.junit.After;
import org.junit.Before;
import org.junit.BeforeClass;
import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.runners.Parameterized;
import org.junit.runners.Parameterized.Parameters;

import softtest.DefUseAnalysis.c.DUAnalysisVisitor;
import softtest.ast.c.ASTFunctionDefinition;
import softtest.ast.c.ASTTranslationUnit;
import softtest.ast.c.CCharStream;
import softtest.ast.c.CParser;
import softtest.ast.c.ParseException;
import softtest.ast.c.SimpleNode;
import softtest.callgraph.c.CGraph;
import softtest.callgraph.c.CVexNode;
import softtest.cfg.c.ControlFlowData;
import softtest.cfg.c.ControlFlowVisitor;
import softtest.domain.c.analysis.ControlFlowDomainVisitor;
import softtest.config.c.Config;
import softtest.fsm.c.FSMLoader;
import softtest.fsm.c.FSMMachine;
import softtest.fsmanalysis.c.FSMAnalysisVisitor;
import softtest.fsmanalysis.c.FSMControlFlowData;
import softtest.fsmanalysis.c.Report;
import softtest.interpro.c.InterCallGraph;
import softtest.interpro.c.InterMethodVisitor;
import softtest.symboltable.c.AbstractScope;
import softtest.symboltable.c.OccurrenceAndExpressionTypeFinder;
import softtest.symboltable.c.ScopeAndDeclarationFinder;

@RunWith(Parameterized.class)
public class UVF {
	private String source = null;
	private String compiletype=null;
	private String result = null;
	private static final String fsmPath="softtest/rules/gcc/fault/UVF-0.1.xml";
	FSMAnalysisVisitor fsmAnalysis; 
	private FSMControlFlowData cfData;
	
	public UVF(String source,String compiletype, String result)
	{
		this.source=source;	
		this.compiletype=compiletype;
		this.result = result;
	}

	@BeforeClass
	public static void setUpBase()
	{
		BasicConfigurator.configure();
        PropertyConfigurator.configure("log4j.properties") ;
		//根据待测试模式XML文件路径初始化自动机列表
		FSMMachine fsm = FSMLoader.loadXML(fsmPath);
		
		//ZYS:最好根据状态机描述文件XML中的相关字段读取出该模式所属于的故障类别
		fsm.setType("fault");
		//每次加入自动机前都清空一下原来的fsms
		FSMAnalysisVisitor.clearFSMS();
		FSMAnalysisVisitor.addFSMS(fsm);
		
		Config.REGRESS_RULE_TEST=true;
	}
	
	//	根据不同的模式需求，自行分配当前AST分析到的步骤
	private void analysis(ASTTranslationUnit astroot){
		astroot.jjtAccept(new ScopeAndDeclarationFinder(), null);
		astroot.jjtAccept(new OccurrenceAndExpressionTypeFinder(), null);
		
		//清空原有全局分析中产生的函数摘要信息
		InterCallGraph.getInstance().clear();
		astroot.jjtAccept(new InterMethodVisitor(), null);
		
		CGraph g = new CGraph();
		((AbstractScope)(astroot.getScope())).resolveCallRelation(g);
		List<CVexNode> list = g.getTopologicalOrderList();
		Collections.reverse(list);
		
		ControlFlowData flow = new ControlFlowData();
		ControlFlowVisitor cfv = new ControlFlowVisitor();
		ControlFlowDomainVisitor cfd = new ControlFlowDomainVisitor();
		
		for (CVexNode cvnode : list) {
			SimpleNode node = cvnode.getMethodNameDeclaration().getNode();
			if (node instanceof ASTFunctionDefinition) {
				cfv.visit((ASTFunctionDefinition)node, flow);
				cfd.visit((ASTFunctionDefinition)node, null);
			} 
		}
		
		astroot.jjtAccept(fsmAnalysis, cfData);
		
		assertEquals(result,getFSMAnalysisResult());
	}
	
	private String getFSMAnalysisResult()
	{
		List<Report> reports=cfData.getReports();
		String analysisResult=null;
		if(reports.size()==0)
		{
			analysisResult="OK";
			return analysisResult;
		}
		for(Report r:reports)
		{
			analysisResult=r.getFsmName();
			System.out.println(r.getFsmName()+" : "+r.getDesp());
		}
		return analysisResult;
	}

	@Before
	public void init() {
		cfData = new FSMControlFlowData();
		List<Report> reports = new ArrayList<Report>();
		cfData.setReports(reports);
		fsmAnalysis=new FSMAnalysisVisitor(cfData); 
	}

	@After
	public void shutdown() {
		//清除临时文件夹
	}
	
	@Test
	public void test() {
		CParser.setType("gcc");
		CParser parser_gcc = CParser.getParser(new CCharStream(new ByteArrayInputStream(source.getBytes())));
		CParser.setType("keil");
		CParser parser_keil = CParser.getParser(new CCharStream(new ByteArrayInputStream(source.getBytes())));
		ASTTranslationUnit gcc_astroot=null,keil_astroot=null;
		if(compiletype.equals("gcc")){
			CParser.setType("gcc");
			try {
				gcc_astroot = parser_gcc.TranslationUnit();
			} catch (ParseException e) {
				e.printStackTrace();
				fail("parse error");
			}
			analysis(gcc_astroot); 
		}else if(compiletype.equals("keil")){
			CParser.setType("keil");
			try {
				keil_astroot= parser_keil.TranslationUnit();
			} catch (ParseException e) {
				e.printStackTrace();
				fail("parse error");
			}
			analysis(keil_astroot);
		}else{
			CParser.setType("gcc");
			try {
				gcc_astroot = parser_gcc.TranslationUnit();
			} catch (ParseException e) {
				e.printStackTrace();
				fail("parse error");
			}
			analysis(gcc_astroot);
			
			CParser.setType("keil");
			try {
				keil_astroot= parser_keil.TranslationUnit();
			} catch (ParseException e) {
				e.printStackTrace();
				fail("parse error");
			}
			analysis(keil_astroot);
		}
	}
	
	 @Parameters
	 public static Collection<Object[]> testcaseAndResults()
	 {
		 return Arrays.asList(new Object[][] {
				//总用例：31
					//未通过用例：0
					//未通过用例序号:0
////////////////	/  0   ///////////////////	
					{
			            "void call(int);"                                                      +"\n"+
			            ""                                                                     +"\n"+
			            "void f1()"                                                            +"\n"+
			            "{"                                                                    +"\n"+
			            "	int i;"                                                              +"\n"+
			           // "	int j = 2;"                                                          +"\n"+
			            "	call(i);  //DEFECT, UVF, i"                                          +"\n"+
			           // "	call(j); //FP "                                                      +"\n"+
			            "}"                                                                    
			            ,
			            "gcc"
			            ,
			            "UVF"
			            ,
			            },
		
////////////////		/  1   chh///////////////////	
			             {
			            "void f3()"                                                            +"\n"+
			            "{"                                                                    +"\n"+
			            "	int j;"                                                              +"\n"+
			            "	int m;"                                                              +"\n"+
			            "	m += 1; //DEFECT, UVF, m"                                            +"\n"+
			            "	j++; //DEFECT, UVF, j"                                               +"\n"+
			            "}"                                                                    
			            ,
			            "gcc"
			            ,
			            "UVF"
			            ,
			            },
////////////////		/  2   chh///////////////////	
			            {
			            "void f4() {"                                                          +"\n"+
			            "  int k;"                                                             +"\n"+
			            "  int a = 2;"                                                         +"\n"+
			            "  a = k;   //DEFECT, UVF, k"                                          +"\n"+
			            "}"                                                                    
			            ,
			            "gcc"
			            ,
			            "UVF"
			            ,
			            },
////////////////		/  3  chh ///////////////////	
			            {
			            "void f5()"                                                            +"\n"+
			            "{"                                                                    +"\n"+
			            "	int a;"                                                              +"\n"+
			            "	int b;"                                                              +"\n"+
			            "	b = a; //DEFECT, UVF, a"                                             +"\n"+
			            "}"                                                                    
			            ,
			            "gcc"
			            ,
			            "UVF"
			            ,
			            },
////////////////		/  4  chh   普通函数初始化///////////////////	
			             {
			            "int getValue(int);"                                                   +"\n"+
			            ""                                                                     +"\n"+
			            "int f7()"                                                             +"\n"+
			            "{"                                                                    +"\n"+
			            "    int	c;"                                                           +"\n"+
			            "    return (c = getValue(0)) == 1 ? 1 : getValue(c); //FP"            +"\n"+
			            "}"                                                                    
			            ,
			            "gcc"
			            ,
			            "OK"
			            ,
			            },
////////////////		/  5   chh  input(int*)函数初始化///////////////////	
			            {
			            "void input(int*);"                                                    +"\n"+
			            ""                                                                     +"\n"+
			            "int f10()"                                                            +"\n"+
			            "{"                                                                    +"\n"+
			            "	int ii;"                                                             +"\n"+
			            "	input(&ii); //FP"                                                    +"\n"+
			            "	return ii;"                                                           +"\n"+
			            "}"                                                                    
			            ,
			            "gcc"
			            ,
			            "OK"
			            ,
			            },
		/////////////////  6   chh  sscanf函数初始化///////////////////---------------		
			            {
			            "void fun()"                                                           +"\n"+
			            "{"                                                                    +"\n"+
			            "	char c[],d[];"                                                         +"\n"+
			                                                               
			            "	sscanf(\"123456\",\"%s\",c);//FP"                                            +"\n"+
			            "	d=c;;"                                                        +"\n"+
			            "}"                                                                    
			            ,
			            "gcc"
			            ,
			            
			            "OK"
			            ,
			            },
		/////////////////  7  chh strcpy初始化 ///////////////////---------------	
			             {
			            "void fun()"                                                           +"\n"+
			            "{"                                                                    +"\n"+
			            "char st1[],st2[]=\"aaaaa\";"                                                  +"\n"+
			            "strcpy(st1,st2);"                                                    +"\n"+
			            "}" 
			            ,
			            "gcc"
			            ,
			            
			            "OK"
			            ,
			            },
	/////////////////  8  chh strcpy初始化不合法 ///////////////////---------------	
			             {
			            "void fun()"                                                           +"\n"+
			            "{"                                                                    +"\n"+
			            "char st1[];"                                                  +"\n"+
			            "strcpy(st1,st1);"                                                    +"\n"+
			            "}" 
			            ,
			            "gcc"
			            ,
			            
			            "UVF"
			            ,
			            },
		/////////////////  9  chh strcpy初始化不合法 ///////////////////--------------	
					  {
			            "void fun()"                                                           +"\n"+
			            "{"                                                                    +"\n"+
			            "char str2[],str1[];"                                                  +"\n"+
			            "strcpy(str1,str2);"                                                    +"\n"+
			            "}" 
			            ,
			            "gcc"
			            ,
			            
			            "UVF"
			            ,
			            },
	/////////////////  10   chh  f(int *i)函数初始化///////////////////	
			             {
			            "void f(int *i);"                                                 +"\n"+
			            "void fun()"                                                           +"\n"+
			            "{"                                                                    +"\n"+
			            "	int a[],c[];"                                                    +"\n"+
			            "	f(a);"                                                    +"\n"+
			            "	c=a;"                                                             +"\n"+
			            "}" 
			            ,
			            "gcc"
			            ,
			            "OK"
			            ,
			            },

		/////////////////  11  chh  i=i+1///////////////////	
			            {
			            "fun()"                                                                +"\n"+
			            "{"                                                                    +"\n"+
			            "	int i;"                                                         +"\n"+
			            "	i=i+1;//DEFECT, UVF, i"                                                              +"\n"+
			            "}"
			            ,
			            "gcc"
			            ,
			            "UVF"
			            ,
			            },
	/////////////////  12 chh for 内先使用后初始化   ///////////////////	
			            {
			            "f()"                                                                  +"\n"+
			            "{"                                                                    +"\n"+
			            "char a;"                                                              +"\n"+
			            "for(;;){a++;a=0;}"                                                      +"\n"+
			            "}"                                                                    
			            ,
			            "gcc"
			            ,
			            "UVF"
			            ,
			            },
		/////////////////  13 chh if 内先使用后初始化   ///////////////////	
			            {
			            "f()"                                                                  +"\n"+
			            "{"                                                                    +"\n"+
			            "char a;"                                                              +"\n"+
			            "if(1){a++;a=0;}"                                                      +"\n"+
			            "}"                                                                    
			            ,
			            "gcc"
			            ,
			            "UVF"
			            ,
			            },		            
	/////////////////  14   chh 数组初始化不合法///////////////////----------------	
			    		
			            {
			            "fun()"                                                                +"\n"+
			            "{"                                                                    +"\n"+
			            "	int a[];"                                                        +"\n"+
			            "	a[0]=a[1];"                                                                +"\n"+
			            "}"                                                                    
			            ,
			            "gcc"
			            ,
			            "UVF"
			            ,
			            },
	/////////////////  15   chh  数组初始化///////////////////----------------	
			    		
			            {
			            "fun()"                                                                +"\n"+
			            "{"                                                                    +"\n"+
			            "	int a[];"                                                        +"\n"+
			            "	a[0]=a[1]=0;"                                                                +"\n"+
			            "}"                                                                    
			            ,
			            "gcc"
			            ,
			            "OK"
			            ,
			            },
		/////////////////  16   chh sizeof(i)不算对i的非法使用///////////////////	
			              {
			            "int fun()"                                                            +"\n"+
			            "{"                                                                    +"\n"+
			            "	int i;"                                                              +"\n"+
			            "	"                                                                    +"\n"+
			            "	return sizeof(i);"                                                   +"\n"+
			            "}"  
			            ,
			            "gcc"		           
			            ,
			            "OK"
			            ,
			            },

	/////////////////  17  chh strcpy初始化 ///////////////////-----------	
			            {
			            "void fun()"                                                           +"\n"+
			            "{"                                                                    +"\n"+
			            "char st1[],st2[];"                                                  +"\n"+
			            "strcmp(st1,st2);"                                                    +"\n"+
			            "}" 
			            ,
			            "gcc"
			            ,
			            
			            "UVF"
			            ,
			            },
		/////////////////  18 ///////////////////	
			             {
			            "void fun()"                                                           +"\n"+
			            "{"                                                                    +"\n"+
			            "int i;"                                                  +"\n"+
			            "i&=0x03;"                                                    +"\n"+
			            "}" 
			            ,
			            "gcc"
			            ,
			            
			            "OK"
			            ,
			            },         
	/////////////////  19  chh  for_out///////////////////	//
					     {
				            " fun()"                                                            +"\n"+
				            "{"                                                                    +"\n"+
				            "	int i,k;"                                                              +"\n"+
				            "	for(i=0;i>5;i++)"                                                    +"\n"+
				            "	{"                                                                   +"\n"+
				            "		//k=i;"                                                             +"\n"+
				            "	}"                                                                   +"\n"+
				            "	k=5;"                                                           +"\n"+
				            "}"                                                                    
				            ,
				            "gcc"		           
				            ,
				            "OK"
				            ,
				            }, 
	/////////////////  20  chh while_head///////////////////	
				             {
				            "void  f()"                                                            +"\n"+
				            "{"                                                                    +"\n"+
				            "int a,b=0;"                                                             +"\n"+
				            "while(b<5)"                                                           +"\n"+
				            "{"                                                                    +"\n"+
				            "b++;"                                                                 +"\n"+
				            "}"                                                                    +"\n"+
				            "a=b;}"                                                                    
				            ,
				            "gcc"
				            ,
				            "OK"
				            ,
				            },
	/////////////////  21  chh   do_while_head///////////////////	
							  {
						            ""                                                                     +"\n"+
						            "void fun()"                                                            +"\n"+
						            "{"                                                                    +"\n"+
						            "	int i,k;"                                                          +"\n"+
						            "	k=0;"                                                          +"\n"+
						            "	do{"                                                                 +"\n"+
						            "	    i=k;"                                                                 +"\n"+
						            "		"                                                               +"\n"+
						            "		k++;"                                                               +"\n"+
						            "		}while(i<10);"                                                       +"\n"+
						            "		i++;"                                                               +"\n"+
						            "}"
						            ,
						            "gcc"
						            ,
						            "OK"
						            ,
						            },
			

	/////////////////  22   chh   for不可达初始化///////////////////	////
				            {
					            
					            "int fun()"                                                            +"\n"+
					            "{"                                                                    +"\n"+
					            "	int i,k,j;"                                                            +"\n"+
					            "	for(i=12;i<10;i++)//条件不符合，不会进入for循环，k没有初始化，但是结果OK"                                                    +"\n"+
					            "	{"                                                                   +"\n"+
					            "		//break;"                                                                   +"\n"+
					            "		k=i;"                                                                   +"\n"+
					            "	}"                                                               +"\n"+
					            "	j=k;"                                                                   +"\n"+
					            "}"
					            ,
					            "gcc"
					            ,
					            "UVF"
					            ,
					            },

	/////////////////  23  chh if 不可达初始化///////////////////	
					             {
					            "void fun()"                                                           +"\n"+
					            "{"                                                                    +"\n"+
					            "	int i=1,x,n;"                                                        +"\n"+
					            "	if(i==0) scanf(\"%d\",&x);//判断条件不成立，即x未赋值，依旧OK"                                            +"\n"+
					            "	n=x;"                                                                +"\n"+
					            "}" 
					            ,
					            "gcc"
					            ,
					            
					            "UVF"
					            ,
					            },
	/////////////////  24 chh switch初始化不可达   ///////////////////	
					            {
					            "void fun()"                                                           +"\n"+
					            "{"                                                                    +"\n"+
					            "int i,a,b;"                                                         +"\n"+
					            "i=0;"                                                                   +"\n"+
					            "switch(i)"                                                            +"\n"+
					            "{"                                                                    +"\n"+
					            "case 1:a=2;break;"                                                    +"\n"+
					            "default:break;"                                                       +"\n"+
					            "}"                                                                    +"\n"+
					            "b=a;"                                                                 +"\n"+
					            "}"                                                                    
					            ,
					            "gcc"
					            ,
					            "UVF"
					            ,
					            },
	/////////////////  25 chh  if初始化不可达  ///////////////////	
		
							             {
							            "void  f()"                                                            +"\n"+
							            "{"                                                                    +"\n"+
							            "int j,y,x;"                                                             +"\n"+
							            "x=1;"                                                                 +"\n"+
							            "y=x+1;"                                                               +"\n"+
							            "if(x>y)"                                                              +"\n"+
							            "{"                                                                    +"\n"+
							            "j=5;"                                                                 +"\n"+
							            "}"                                                                    +"\n"+
							            "x=j;"                                                                 +"\n"+
							            "}"                                                                    
							            ,
							            "gcc"
							            ,
							            "UVF"
							            ,
							            },
		
	/////////////////  26 chh do_while 内先使用后初始化   ///////////////////	
			            {
			            "f()"                                                                  +"\n"+
			            "{"                                                                    +"\n"+
			            "char a;"                                                              +"\n"+
			            "do{a++;a=0;}while(1);"                                                      +"\n"+
			            "}"                                                                    
			            ,
			            "gcc"
			            ,
			            "UVF"
			            ,
			            },
		/////////////////  27 chh while 内先使用后初始化   ///////////////////	
			            {
			            "f()"                                                                  +"\n"+
			            "{"                                                                    +"\n"+
			            "char a;"                                                              +"\n"+
			            "while(1){a++;a=0;}"                                                      +"\n"+
			            "}"                                                                    
			            ,
			            "gcc"
			            ,
			            "UVF"
			            ,
			            },
	/////////////////  28   ///////////////////	
		            {
		            ""                                                                     +"\n"+
		            "void f2(int f){"                                                      +"\n"+
		            "	int p=f;"                                                            +"\n"+
		            "}"                                                                    +"\n"+
		            "void f1(int f){"                                                      +"\n"+
		            "	f2(f);"                                                              +"\n"+
		            ""                                                                     +"\n"+
		            "}"                                                                    +"\n"+
		            "main(){"                                                              +"\n"+
		            "    int flag;"                                                        +"\n"+
		            "	f1(flag); //DEFECT"                                                  +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "UVF"
		            ,
		            },
	/////////////////  29   ///////////////////	
		            {
		            "#include <stdio.h>"                                                   +"\n"+
		            "#include <string.h>"                                                  +"\n"+
		            "void jhb_uvf_1_f1(int *nLines,char sName[]){"                         +"\n"+
		            "	int nNameNo=32;"                                                     +"\n"+
		            "	char sOldName[128];"                                                 +"\n"+
		            "	if ((*nLines)>=10)"                                                  +"\n"+
		            "	{"                                                                   +"\n"+
		            "		while (nNameNo)"                                                    +"\n"+
		            "		{"                                                                  +"\n"+
		            "			strcpy(sOldName,sName);   //DEFECT"                                +"\n"+
		            "		}"                                                                  +"\n"+
		            "	//	unlink(sOldName);"                                                +"\n"+
		            "	}"                                                                   +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "OK"
		            ,
		            },
//////////////////////////30/////////////////////////////////////////////
		            {
		            "#include <stdio.h>"                                                   +"\n"+
		            "int ghx_uvf_1_f1(int a)"                                              +"\n"+
		            "{"                                                                    +"\n"+
		            "	int b;"                                                              +"\n"+
		            "switch(a)"                                                            +"\n"+
		            "{"                                                                    +"\n"+
		            "case 1:"                                                              +"\n"+
		            "	b=1;"                                                                +"\n"+
		            "case 2:"                                                              +"\n"+
		            "	b=2;"                                                                +"\n"+
		            "case 3:"                                                              +"\n"+
		            "	b=3;"                                                                +"\n"+
		            "}"                                                                    +"\n"+
		            "b++;//DEFECT"                                                         +"\n"+
		            "return 0;"                                                            +"\n"+
		            "}"    
		            ,
		            "gcc"
		            ,
		            "UVF"
		            ,
		            },
	
		 });
	 }
}


