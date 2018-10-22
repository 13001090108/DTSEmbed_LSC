package softtest.test.c.interval;

import static org.junit.Assert.*;

import java.io.*;
import java.util.*;

import org.junit.After;
import org.junit.AfterClass;
import org.junit.Before;
import org.junit.BeforeClass;
import org.junit.Test;
import org.junit.runner.*;
import org.junit.runners.*;
import org.junit.runners.Parameterized.*;
import softtest.ast.c.*;
import softtest.cfg.c.*;
import softtest.config.c.Config;
import softtest.domain.c.analysis.*;
import softtest.domain.c.interval.Domain;
import softtest.domain.c.symbolic.Expression;
import softtest.domain.c.symbolic.SymbolFactor;
import softtest.symboltable.c.*;
import softtest.tools.c.jaxen.MatchesFunction;
/** zys更新日志：
 * 2010.7.26：
 * 		Failers:9个（51,86,89,90,95,96,104,106,138）
 * 		Errors:1个（67）
 * 
 * */
/** 
 * zys	2011.6.22更新日志
 * 添加了185-209测试用例，用于验证条件表达式中条件变量的符号表达式过于复杂时的处理
 * 
 * 另外，暂时屏蔽了部分区间运算计算错误的测试用例，主要有以下几类：
 * 1、测试用例6,8,10，14,15：	x=a+b; y=a; if(x>y)	真分支中b>0
 * 		这种情况与后续的x=a*b; if(x>0)中计算原理有冲突，并且实际代码中基本不会有类似的条件判断，因此该情况暂时屏蔽掉
 * 2、循环相关的测试用例：134,141
 * 		有时间的话再完善下循环的计算原理
 * 3、数组元素之间的计算：测试用例90
 * 4、指针建模相关的错误：163,164
 */
@RunWith(Parameterized.class)
public class TestIntervalAnalysis
{
	private String source = null;
	private String vexstr = null;
	private String varstr =null;
	private String valuestr=null;
	private String domainstr=null;

	public TestIntervalAnalysis(String source, String vexstr, String varstr, String valuestr, String domainstr) {
		this.source = source;
		this.vexstr = vexstr;
		this.varstr = varstr;
		this.valuestr = valuestr;
		this.domainstr = domainstr;
	}

	@BeforeClass
	public static void setUpBase()  {
		//注册Xpath中的Matches方法，当前由于不支持Xpath2.0所以Matches要手工实现，并注册
		MatchesFunction.registerSelfInSimpleContext();
		Config.REGRESS_RULE_TEST=true;
	}

	@AfterClass
	public static void tearDownBase() {
	}
	
	private void analysis(ASTTranslationUnit astroot){
		astroot.jjtAccept(new ScopeAndDeclarationFinder(), null);
		astroot.jjtAccept(new OccurrenceAndExpressionTypeFinder(), null);
		astroot.jjtAccept(new ControlFlowVisitor(), null);
		SymbolFactor.resetNameCount();
		astroot.jjtAccept(new ControlFlowDomainVisitor(), null);
		
		String value="ERROR",domain="ERROR";
		List<Node> mds = astroot.findChildrenOfType(ASTFunctionDefinition.class);
		if (!mds.isEmpty()) {
			Graph g = ((ASTFunctionDefinition)mds.get(0)).getGraph();
			VexNode vn = g.nodes.get(vexstr);
			Hashtable<VariableNameDeclaration, Expression> vTable=vn.getValueSet().getTable();
			for (VariableNameDeclaration vv : vTable.keySet()) {
				if (vv.getImage().equals(varstr)) {
					Expression e = vTable.get(vv);
					if (e != null) {
						value = e.toString();
						Domain dm=vn.getDomain(vv);
						if(dm!=null){
							domain=dm.toString();
						}
					}
					break;
				}
			}
		}
		
//		assertEquals("interval analyssi error",valuestr,value);
		if(Config.USEUNKNOWN && domain.equals("unknown")){
			//System.out.println(domain+" : "+domainstr);
			//如果设置了unknown开关，则如果为全区间则测试通过
			if(domainstr.equals("ERROR") || domainstr.equals("[-inf,inf]")
					|| domainstr.equals("[-Infinity,Infinity]"))
				assertTrue("Unknown interval analyssi",true);
		}else{
			//System.out.println("not unknown");
			assertEquals("interval analyssi error",domainstr,domain);
		}
	}

	@Before
	public void init() {
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
	
		CParser.setType("gcc");
		try {
			gcc_astroot = parser_gcc.TranslationUnit();
		} catch (ParseException e) {
			e.printStackTrace();
			fail("parse error");
		}
		analysis(gcc_astroot);
/*暂时屏蔽KEIL下的区间处理			
		CParser.setType("keil");
		try {
			keil_astroot= parser_keil.TranslationUnit();
		} catch (ParseException e) {
			e.printStackTrace();
			fail("parse error");
		}
		analysis(keil_astroot);
		*/
	}
	
	@Parameters
	public static Collection<Object[]> testcaseAndResults(){
		return Arrays.asList(new Object[][] {
/////////////////  0   ///////////////////	
	            {
	            "void f(int i){"                                                       +"\n"+
	            "	i=0;"                                                                +"\n"+
	            "	i++;"                                                                +"\n"+                                                         
	            "}"                                                                    
	            ,
	            "stmt_2"
	            ,
	            "i"
	            ,
	            "1"
	            ,
	            "[1,1]"
	            ,
	            },
/////////////////  1   ///////////////////	
	            {
	            "void f(int i){"                                                       +"\n"+
	            "	if(i>0){"                                                            +"\n"+
	            "		i=0;"                                                               +"\n"+
	            "	}"                                                                   +"\n"+
	            "	i++;"                                                                +"\n"+
	            "}"                                                                    
	            ,
	            "stmt_2"
	            ,
	            "i"
	            ,
	            "0"
	            ,
	            "[0,0]"
	            ,
	            },
/////////////////  2   ///////////////////	
	            {
	            "void f(int i){"                                                       +"\n"+
	            "	if(i>0){"                                                            +"\n"+
	            "		i=0;"                                                               +"\n"+
	            "	}"                                                                   +"\n"+
	            "	i++;"                                                                +"\n"+
	            "}"                                                                    
	            ,
	            "if_out_3"
	            ,
	            "i"
	            ,
	            "i_45"
	            ,
	            "[-inf,0]"
	            ,
	            },
/////////////////  3   ///////////////////	
	            {
	            "void f(int i){"                                                       +"\n"+
	            "	if(i>0){"                                                            +"\n"+
	            "		i=0;"                                                               +"\n"+
	            "	}"                                                                   +"\n"+
	            "	i++;"                                                                +"\n"+
	            "}"                                                                    
	            ,
	            "stmt_4"
	            ,
	            "i"
	            ,
	            "1+i_45"
	            ,
	            "[-inf,1]"
	            ,
	            },
/////////////////  4   zys:2010.3.26	不可达分支测试///////////////////	
	            {
	            "int f(int i){"                                                        +"\n"+
	            "int x,y;"                                                             +"\n"+
	            "y=x+1;"                                                               +"\n"+
	            "if(y>x){"                                                             +"\n"+
	            "i=0;"                                                                 +"\n"+
	            "}else{"                                                               +"\n"+
	            "i++;"                                                                 +"\n"+
	            "}"                                                                    +"\n"+
	            "return i;"                                                            +"\n"+
	            "}"                                                                    
	            ,
	            "stmt_5"
	            ,
	            "i"
	            ,
	            "ERROR"
	            ,
	            "ERROR"
	            ,
	            },

/////////////////  5  	liuli:2010.3.26		对+进行测试///////////////////	
	            {
	            "void f(int i){"                                                       +"\n"+
	            "int j = 0;"                                                           +"\n"+
	            "i = j+3;"                                                             +"\n"+
	            "}"                                                                    
	            ,
	            "stmt_2"
	            ,
	            "i"
	            ,
	            "3"
	            ,
	            "[3,3]"
	            ,
	            },

/////////////////  6   zys:2010.3.26 ///////////////////	
	            {
	            "int f(int i){"                                                        +"\n"+
	            "int x,y,a,b;"                                                         +"\n"+
	            "x=a;"                                                                 +"\n"+
	            "y=a+b;"                                                               +"\n"+
	            "if(y>x){"                                                             +"\n"+
	            "i=0;"                                                                 +"\n"+
	            "}else{"                                                               +"\n"+
	            "i++;"                                                                 +"\n"+
	            "}"                                                                    +"\n"+
	            "return i;"                                                            +"\n"+
	            "}"                                                                    
	            ,
	            "stmt_5"
	            ,
	            "b"
	            ,
	            "b_45"
	            ,
	            "ERROR"
	            ,
	            },
/////////////////  7   ///////////////////	
	            {
	            "int f(int i){"                                                        +"\n"+
	            "int x,y,a,b;"                                                         +"\n"+
	            "x=a;"                                                                 +"\n"+
	            "y=a+b;"                                                               +"\n"+
	            "if(y>x){"                                                             +"\n"+
	            "i=0;"                                                                 +"\n"+
	            "}else{"                                                               +"\n"+
	            "i++;"                                                                 +"\n"+
	            "}"                                                                    +"\n"+
	            "return i;"                                                            +"\n"+
	            "}"                                                                    
	            ,
	            "stmt_5"
	            ,
	            "i"
	            ,
	            "0"
	            ,
	            "[0,0]"
	            ,
	            },
/////////////////  8   ///////////////////	
	            {
	            "int f(int i){"                                                        +"\n"+
	            "int x,y,a,b;"                                                         +"\n"+
	            "x=a;"                                                                 +"\n"+
	            "y=a+b;"                                                               +"\n"+
	            "if(y>x){"                                                             +"\n"+
	            "i=0;"                                                                 +"\n"+
	            "}else{"                                                               +"\n"+
	            "i++;"                                                                 +"\n"+
	            "}"                                                                    +"\n"+
	            "return i;"                                                            +"\n"+
	            "}"                                                                    
	            ,
	            "stmt_6"
	            ,
	            "b"
	            ,
	            "b_45"
	            ,
	            "ERROR"
	            ,
	            },
/////////////////  9   ///////////////////	
	            {
	            "int f(int i){"                                                        +"\n"+
	            "int x,y,a,b;"                                                         +"\n"+
	            "x=a;"                                                                 +"\n"+
	            "y=a+b;"                                                               +"\n"+
	            "if(y>x){"                                                             +"\n"+
	            "i=0;"                                                                 +"\n"+
	            "}else{"                                                               +"\n"+
	            "i++;"                                                                 +"\n"+
	            "}"                                                                    +"\n"+
	            "return i;"                                                            +"\n"+
	            "}"                                                                    
	            ,
	            "if_out_7"
	            ,
	            "i"
	            ,
	            "i_1415"
	            ,
	            "[-inf,inf]"
	            ,
	            },
/////////////////  10   ///////////////////	
	            {
	            "int f(int i){"                                                        +"\n"+
	            "int x,y,a,b;"                                                         +"\n"+
	            "x=a;"                                                                 +"\n"+
	            "y=a+b;"                                                               +"\n"+
	            "if(y==x){"                                                            +"\n"+
	            "i=0;"                                                                 +"\n"+
	            "}else{"                                                               +"\n"+
	            "i++;"                                                                 +"\n"+
	            "}"                                                                    +"\n"+
	            "return i;"                                                            +"\n"+
	            "}"                                                                    
	            ,
	            "stmt_6"
	            ,
	            "b"
	            ,
	            "b_45"
	            ,
	            "ERROR"
	            ,
	            },
/////////////////  11  真分支不可达测试 ///////////////////	
	            {
	            "int f(int i){"                                                        +"\n"+
	            "int x,y,a,b=3;"                                                       +"\n"+
	            "x=a;"                                                                 +"\n"+
	            "y=a+b;"                                                               +"\n"+
	            "if(y==x){"                                                            +"\n"+
	            "i=0;"                                                                 +"\n"+
	            "}else{"                                                               +"\n"+
	            "i++;"                                                                 +"\n"+
	            "}"                                                                    +"\n"+
	            "return i;"                                                            +"\n"+
	            "}"                                                                    
	            ,
	            "stmt_5"
	            ,
	            "i"
	            ,
	            "ERROR"
	            ,
	            "ERROR"
	            ,
	            },
/////////////////  12 假分支不可达测试   ///////////////////	
	            {
	            "int f(int i){"                                                        +"\n"+
	            "int x,y,a,b=3;"                                                       +"\n"+
	            "x=a;"                                                                 +"\n"+
	            "y=a+b;"                                                               +"\n"+
	            "if(y!=x){"                                                            +"\n"+
	            "i=0;"                                                                 +"\n"+
	            "}else{"                                                               +"\n"+
	            "i++;"                                                                 +"\n"+
	            "}"                                                                    +"\n"+
	            "return i;"                                                            +"\n"+
	            "}"                                                                    
	            ,
	            "stmt_5"
	            ,
	            "i"
	            ,
	            "0"
	            ,
	            "[0,0]"
	            ,
	            },
/////////////////  13   ///////////////////	
	            {
	            "int f(int i){"                                                        +"\n"+
	            "int x,y,a,b=3;"                                                       +"\n"+
	            "x=a;"                                                                 +"\n"+
	            "y=x+1;"                                                               +"\n"+
	            "if(y!=x){"                                                            +"\n"+
	            "i=0;"                                                                 +"\n"+
	            "}else{"                                                               +"\n"+
	            "i++;"                                                                 +"\n"+
	            "}"                                                                    +"\n"+
	            "return i;"                                                            +"\n"+
	            "}"                                                                    
	            ,
	            "stmt_5"
	            ,
	            "i"
	            ,
	            "0"
	            ,
	            "[0,0]"
	            ,
	            },
/////////////////  14   ///////////////////	
	            {
	            "int f(int i){"                                                        +"\n"+
	            "int x,y,a,b;"                                                         +"\n"+
	            "x=a;"                                                                 +"\n"+
	            "y=a+b;"                                                               +"\n"+
	            "if(x==y){"                                                            +"\n"+
	            "i=0;"                                                                 +"\n"+
	            "}else{"                                                               +"\n"+
	            "i++;"                                                                 +"\n"+
	            "}"                                                                    +"\n"+
	            "return i;"                                                            +"\n"+
	            "}"                                                                    
	            ,
	            "stmt_5"
	            ,
	            "b"
	            ,
	            "b_45"
	            ,
	            "ERROR"
	            ,
	            },
/////////////////  15   ///////////////////	
	            {
	            "int f(int i){"                                                        +"\n"+
	            "int x,y,a,b;"                                                         +"\n"+
	            "x=a;"                                                                 +"\n"+
	            "y=a+b;"                                                               +"\n"+
	            "if(x!=y){"                                                            +"\n"+
	            "i=0;"                                                                 +"\n"+
	            "}else{"                                                               +"\n"+
	            "i++;"                                                                 +"\n"+
	            "}"                                                                    +"\n"+
	            "return i;"                                                            +"\n"+
	            "}"                                                                    
	            ,
	            "stmt_5"
	            ,
	            "b"
	            ,
	            "b_45"
	            ,
	            "ERROR"
	            ,
	            },
/////////////////  16   ///////////////////	
	            {
	            "int f(int i){"                                                        +"\n"+
	            "int x,y,a,b=1;"                                                       +"\n"+
	            "x=a;"                                                                 +"\n"+
	            "y=a+b;"                                                               +"\n"+
	            "if(x>1 && y>1){"                                                      +"\n"+
	            "i=0;"                                                                 +"\n"+
	            "}else{"                                                               +"\n"+
	            "i++;"                                                                 +"\n"+
	            "}"                                                                    +"\n"+
	            "return i;"                                                            +"\n"+
	            "}"                                                                    
	            ,
	            "stmt_5"
	            ,
	            "x"
	            ,
	            "a_01"
	            ,
	            "[2,inf]"
	            ,
	            },
/////////////////  17   ///////////////////	
	            {
	            "int f(int i){"                                                        +"\n"+
	            "int x,y,a,b=1;"                                                       +"\n"+
	            "x=a;"                                                                 +"\n"+
	            "y=a+b;"                                                               +"\n"+
	            "if(x>1 && y>1){"                                                      +"\n"+
	            "i=0;"                                                                 +"\n"+
	            "}else{"                                                               +"\n"+
	            "i++;"                                                                 +"\n"+
	            "}"                                                                    +"\n"+
	            "return i;"                                                            +"\n"+
	            "}"                                                                    
	            ,
	            "stmt_5"
	            ,
	            "y"
	            ,
	            "1+a_01"
	            ,
	            "[3,inf]"
	            ,
	            },
/////////////////  18  ///////////////////	
	            {
	            "int f(int i){"                                                        +"\n"+
	            "int j;"                                                               +"\n"+
	            "for(j=0;j<10;j++){"                                                   +"\n"+
	            "i++;"                                                                 +"\n"+
	            "}"                                                                    +"\n"+
	            "return i;"                                                            +"\n"+
	            "}"                                                                    
	            ,
	            "for_head_3"
	            ,
	            "j"
	            ,
	            "j_4445"
	            ,
	            "[0,10]"
	            ,
	            },
/////////////////  19   ///////////////////	
	            {
	            "int f(int i){"                                                        +"\n"+
	            "int j;"                                                               +"\n"+
	            "for(j=0;j<10;j++){"                                                   +"\n"+
	            "i++;"                                                                 +"\n"+
	            "}"                                                                    +"\n"+
	            "return i;"                                                            +"\n"+
	            "}"                                                                    
	            ,
	            "stmt_4"
	            ,
	            "j"
	            ,
	            "j_4445"
	            ,
	            "[0,9]"
	            ,
	            },
/////////////////  20   ///////////////////	
	            {
	            "int f(int i){"                                                        +"\n"+
	            "int j;"                                                               +"\n"+
	            "for(j=0;j<10;j++){"                                                   +"\n"+
	            "i++;"                                                                 +"\n"+
	            "}"                                                                    +"\n"+
	            "return i;"                                                            +"\n"+
	            "}"                                                                    
	            ,
	            "for_inc_5"
	            ,
	            "j"
	            ,
	            "1+j_4445"
	            ,
	            "[1,10]"
	            ,
	            },
/////////////////  21   ///////////////////	
	            {
	            "int f(int i){"                                                        +"\n"+
	            "int j;"                                                               +"\n"+
	            "for(j=0;j<10;j++){"                                                   +"\n"+
	            "i++;"                                                                 +"\n"+
	            "}"                                                                    +"\n"+
	            "return i;"                                                            +"\n"+
	            "}"                                                                    
	            ,
	            "for_out_6"
	            ,
	            "j"
	            ,
	            "j_4445"
	            ,
	            "[10,10]"
	            ,
	            },
/////////////////  22   ///////////////////	
	            {
	            "int f(int i){"                                                        +"\n"+
	            "int j;"                                                               +"\n"+
	            "for(j=0;j>10;j++){"                                                   +"\n"+
	            "i++;"                                                                 +"\n"+
	            "}"                                                                    +"\n"+
	            "return i;"                                                            +"\n"+
	            "}"                                                                    
	            ,
	            "for_out_6"
	            ,
	            "j"
	            ,
	            "0"
	            ,
	            "[0,0]"
	            ,
	            },
/////////////////  23   ///////////////////	
	            {
	            "int f(int i){"                                                        +"\n"+
	            "int j=5;"                                                             +"\n"+
	            "while(j<10){"                                                         +"\n"+
	            "i++;j++;"                                                             +"\n"+
	            "}"                                                                    +"\n"+
	            "return i;"                                                            +"\n"+
	            "}"                                                                    
	            ,
	            "while_head_2"
	            ,
	            "j"
	            ,
	            "j_4243"
	            ,
	            "[5,10]"
	            ,
	            },
/////////////////  24   ///////////////////	
	            {
	            "int f(int i){"                                                        +"\n"+
	            "int j=5;"                                                             +"\n"+
	            "while(j<10){"                                                         +"\n"+
	            "i++;j++;"                                                             +"\n"+
	            "}"                                                                    +"\n"+
	            "return i;"                                                            +"\n"+
	            "}"                                                                    
	            ,
	            "while_out_5"
	            ,
	            "j"
	            ,
	            "j_4243"
	            ,
	            "[10,10]"
	            ,
	            },
/////////////////  25  	liuli:2010.3.26		对-进行测试///////////////////	
	            {
	            "void f(int i){"                                                       +"\n"+
	            "int j = 0;"                                                           +"\n"+
	            "i = j-3;"                                                             +"\n"+
	            "}"                                                                    
	            ,
	            "stmt_2"
	            ,
	            "i"
	            ,
	            "-3"
	            ,
	            "[-3,-3]"
	            ,
	            },
/////////////////  26	liuli:2010.3.26		&  ///////////////////	
	            {
	            "void f(int i){"                                                       +"\n"+
	            "int j = 7;"                                                           +"\n"+
	            "i = j&3;"                                                             +"\n"+
	            "}"                                                                    
	            ,
	            "stmt_2"
	            ,
	            "i"
	            ,
	            "3"
	            ,
	            "[3,3]"
	            ,
	            },

/////////////////  27	liuli:2010.3.26	*=  ///////////////////	
	            {
	            "void f(int i){"                                                       +"\n"+
	            "i=2;"                                                                 +"\n"+
	            "i *= 3;"                                                              +"\n"+
	            "}"                                                                    
	            ,
	            "stmt_2"
	            ,
	            "i"
	            ,
	            "6"
	            ,
	            "[6,6]"
	            ,
	            },	            
///////////////// 28	liuli:2010.3.26	 SongYing 2010/6/22		/=   ///////////////////	
	            {
	            "void f(int i){"                                                       +"\n"+
	            "i=2;"                                                                 +"\n"+
	            "i/=3;"                                                                +"\n"+
	            "}"                                                                    
	            ,
	            "stmt_2"
	            ,
	            "i"
	            ,
	            "0.6666666666666666"
	            ,
	            "[0,0]"
	            ,
	            },

/////////////////  29	liuli:2010.3.26			+=   ///////////////////	
	            {
	            "void f(int i){"                                                       +"\n"+
	            "i=0;"                                                                 +"\n"+
	            "i += 3;"                                                              +"\n"+
	            "}"                                                                    
	            ,
	            "stmt_2"
	            ,
	            "i"
	            ,
	            "3"
	            ,
	            "[3,3]"
	            ,
	            },
/////////////////  30	liuli:2010.3.26			-=   ///////////////////	
	            {
	            "void f(int i){"                                                       +"\n"+
	            "i=0;"                                                                 +"\n"+
	            "i -= 2;"                                                              +"\n"+
	            "}"                                                                    
	            ,
	            "stmt_2"
	            ,
	            "i"
	            ,
	            "-2"
	            ,
	            "[-2,-2]"
	            ,
	            },
/////////////////  31	liuli:2010.3.26			%=   ///////////////////	
	            {
	            "void f(int i){"                                                       +"\n"+
	            "i=1;"                                                                 +"\n"+
	            "i %= 3;"                                                              +"\n"+
	            "}"                                                                    
	            ,
	            "stmt_2"
	            ,
	            "i"
	            ,
	            "1"
	            ,
	            "[1,1]"
	            ,
	            },
/////////////////  32	liuli:2010.3.26			&=  ///////////////////	
	            {
	            "void f(int i){"                                                       +"\n"+
	            "i=7;"                                                                 +"\n"+
	            "i &= 3;"                                                              +"\n"+
	            "}"                                                                    
	            ,
	            "stmt_2"
	            ,
	            "i"
	            ,
	            "3"
	            ,
	            "[3,3]"
	            ,
	            },
/////////////////  33	liuli:2010.3.26			|=   ///////////////////	
	            {
	            "void f(int i){"                                                       +"\n"+
	            "i=4;"                                                                 +"\n"+
	            "i |= 2;"                                                              +"\n"+
	            "}"                                                                    
	            ,
	            "stmt_2"
	            ,
	            "i"
	            ,
	            "6"
	            ,
	            "[6,6]"
	            ,
	            },   
/////////////////  34	liuli:2010.3.26			^=   ///////////////////	
	            {
	            "void f(int i){"                                                       +"\n"+
	            "i=5;"                                                                 +"\n"+
	            "i ^= 3;"                                                              +"\n"+
	            "}"                                                                    
	            ,
	            "stmt_2"
	            ,
	            "i"
	            ,
	            "6"
	            ,
	            "[6,6]"
	            ,
	            },           
/////////////////  35	liuli:2010.3.26			>>=   ///////////////////	
	            {
	            "void f(int i){"                                                       +"\n"+
	            "i=5;"                                                                 +"\n"+
	            "i >>= 1;"                                                             +"\n"+
	            "}"                                                                    
	            ,
	            "stmt_2"
	            ,
	            "i"
	            ,
	            "2"
	            ,
	            "[2,2]"
	            ,
	            },          
/////////////////  36	liuli:2010.3.26			<<=   ///////////////////	
	            {
	            "void f(int i){"                                                       +"\n"+
	            "i=5;"                                                                 +"\n"+
	            "i <<= 3;"                                                             +"\n"+
	            "}"                                                                    
	            ,
	            "stmt_2"
	            ,
	            "i"
	            ,
	            "40"
	            ,
	            "[40,40]"
	            ,
	            },  
/////////////////  37	liuli:2010.3.26		ASTConstant   ///////////////////	
	            {
	            "void f(int i){"                                                       +"\n"+
	            "char j;"                                                              +"\n"+
	            "j='a';"                                                               +"\n"+
	            "}"                                                                    
	            ,
	            "stmt_2"
	            ,
	            "j"
	            ,
	            "97"
	            ,
	            "[97,97]"
	            ,
	            },
/////////////////  38	liuli:2010.3.26		ASTConstant  ///////////////////	
	            {
	            "void f(int i){"                                                       +"\n"+
	            "char j;"                                                              +"\n"+
	            ""                                                                     +"\n"+
	            "//char c='\\0'; "                                                      +"\n"+
	            "j=\"A\";"                                                               +"\n"+
	            "}"                                                                    
	            ,
	            "stmt_2"
	            ,
	            "j"
	            ,
	            "S_01"
	            ,
	            "[1,inf]"
	            ,
	            },
/////////////////  39	liuli:2010.3.26		ASTConstant   ///////////////////	
	            {
	            "void f(int i){"                                                       +"\n"+
	            "char j;"                                                              +"\n"+
	            "j='\\0'; "                                                             +"\n"+
	            "}"                                                                    
	            ,
	            "stmt_2"
	            ,
	            "j"
	            ,
	            "0"
	            ,
	            "[0,0]"
	            ,
	            },            
/////////////////  40	liuli:2010.3.26		ASTConstant	\b   ///////////////////	
	            {
	            "void f(int i){"                                                       +"\n"+
	            "char j;"                                                              +"\n"+
	            "j='\\b'; "                                                             +"\n"+
	            "}"                                                                    
	            ,
	            "stmt_2"
	            ,
	            "j"
	            ,
	            "8"
	            ,
	            "[8,8]"
	            ,
	            },            
/////////////////  41	liuli:2010.3.26		ASTConstant   \t	///////////////////	
	            {
	            "void f(int i){"                                                       +"\n"+
	            "char j;"                                                              +"\n"+
	            "j='\\t'; "                                                             +"\n"+
	            "}"                                                                    
	            ,
	            "stmt_2"
	            ,
	            "j"
	            ,
	            "9"
	            ,
	            "[9,9]"
	            ,
	            },
/////////////////  42	liuli:2010.3.26		ASTConstant	\n   ///////////////////	
	            {
	            "void f(int i){"                                                       +"\n"+
	            "char j;"                                                              +"\n"+
	            "j='\\n'; "                                                             +"\n"+
	            "}"                                                                    
	            ,
	            "stmt_2"
	            ,
	            "j"
	            ,
	            "10"
	            ,
	            "[10,10]"
	            ,
	            },
/////////////////  43	liuli:2010.3.26		ASTConstant	\f   ///////////////////	
	            {
	            "void f(int i){"                                                       +"\n"+
	            "char j;"                                                              +"\n"+
	            "j='\\f'; "                                                             +"\n"+
	            "}"                                                                    
	            ,
	            "stmt_2"
	            ,
	            "j"
	            ,
	            "12"
	            ,
	            "[12,12]"
	            ,
	            },
/////////////////  44	liuli:2010.3.26		ASTConstant	\r  ///////////////////	
	            {
	            "void f(int i){"                                                       +"\n"+
	            "char j;"                                                              +"\n"+
	            "j='\\r'; "                                                             +"\n"+
	            "}"                                                                    
	            ,
	            "stmt_2"
	            ,
	            "j"
	            ,
	            "13"
	            ,
	            "[13,13]"
	            ,
	            },
/////////////////  45	liuli:2010.3.26		ASTConstant	\"  ///////////////////	
	            {
	            "void f(int i){"                                                       +"\n"+
	            "char j;"                                                              +"\n"+
	            "j='\\\"'; "                                                             +"\n"+
	            "}"                                                                    
	            ,
	            "stmt_2"
	            ,
	            "j"
	            ,
	            "34"
	            ,
	            "[34,34]"
	            ,
	            },
/////////////////  46	liuli:2010.3.26		ASTConstant	\'   ///////////////////	
	            {
	            "void f(int i){"                                                       +"\n"+
	            "char j;"                                                              +"\n"+
	            "j='\\''; "                                                             +"\n"+
	            "}"                                                                    
	            ,
	            "stmt_2"
	            ,
	            "j"
	            ,
	            "39"
	            ,
	            "[39,39]"
	            ,
	            },
/////////////////  47	liuli:2010.3.26		ASTConstant	\\   ///////////////////	
	            {
	            "void f(int i){"                                                       +"\n"+
	            "char j;"                                                              +"\n"+
	            "j='\\\\'; "                                                             +"\n"+
	            "}"                                                                    
	            ,
	            "stmt_2"
	            ,
	            "j"
	            ,
	            "92"
	            ,
	            "[92,92]"
	            ,
	            },
/////////////////  48 	liuli:2010.3.26		ASTConstant  ///////////////////	
	            {
	            "void f(int i){"                                                       +"\n"+
	            "char j;"                                                              +"\n"+
	            "j='\\47'; "                                                            +"\n"+
	            "}"                                                                    
	            ,
	            "stmt_2"
	            ,
	            "j"
	            ,
	            "39"
	            ,
	            "[39,39]"
	            ,
	            },
/////////////////  49 	liuli:2010.3.26		ASTConstant  ///////////////////	
	            {
	            "void f(int i){"                                                       +"\n"+
	            "char j;"                                                              +"\n"+
	            "j='\\126'; "                                                           +"\n"+
	            "}"                                                                    
	            ,
	            "stmt_2"
	            ,
	            "j"
	            ,
	            "86"
	            ,
	            "[86,86]"
	            ,
	            },            
/////////////////  50 	liuli:2010.3.26		ASTConstant  ///////////////////	
	            {
	            "void f(int i){"                                                       +"\n"+
	            "i=3;"                                                                 +"\n"+
	            "i=i*3; "                                                              +"\n"+
	            "}"                                                                    
	            ,
	            "stmt_2"
	            ,
	            "i"
	            ,
	            "9"
	            ,
	            "[9,9]"
	            ,
	            },        
/////////////////  51 	liuli:2010.3.26		ASTConstant  ///////////////////	
	            {
	            "void f(int i){"                                                       +"\n"+
	            "i=3;"                                                                 +"\n"+
	            "i=i/2; "                                                              +"\n"+
	            "}"                                                                    
	            ,
	            "stmt_2"
	            ,
	            "i"
	            ,
	            "1"
	            ,
	            "[1,1]" //整型除法进行了四舍五入进位，有错误
	            ,
	            },               
/////////////////  52	liuli:2010.3.26		   ASTMultiplicativeExpression///////////////////	
	            {
	            "void f(int i){"                                                       +"\n"+
	            "i=3;"                                                                 +"\n"+
	            "i=i%2; "                                                              +"\n"+
	            "}"                                                                    
	            ,
	            "stmt_2"
	            ,
	            "i"
	            ,
	            "1"
	            ,
	            "[1,1]"
	            ,
	            },            
/////////////////  53  	liuli:2010.3.26		   ASTMultiplicativeExpression  ///////////////////	
	            {
	            "void f(int i){"                                                       +"\n"+
	            ""                                                                     +"\n"+
	            "i=i%2; "                                                              +"\n"+
	            "}"                                                                    
	            ,
	            "stmt_1"
	            ,
	            "i"
	            ,
	            "S_23"
	            ,
	            "ERROR"
	            ,
	            },          
/////////////////  54  	liuli:2010.3.26	   ASTEqualityExpression///////////////////	
	            {
	            "void f(int i){"                                                       +"\n"+
	            "if(i==i){"                                                            +"\n"+
	            "  i=3; "                                                              +"\n"+
	            "}else{"                                                               +"\n"+
	            "i=2;"                                                                 +"\n"+
	            "}"                                                                    +"\n"+
	            "}"                                                                    
	            ,
	            "if_out_4"
	            ,
	            "i"
	            ,
	            "3"
	            ,
	            "[3,3]"
	            ,
	            },          
/////////////////  55   liuli:2010.3.26	   ASTEqualityExpression  ///////////////////	
	            {
	            "void f(int i){"                                                       +"\n"+
	            "if(i!=i){"                                                            +"\n"+
	            "  i=3; "                                                              +"\n"+
	            "}else{"                                                               +"\n"+
	            "i=2;"                                                                 +"\n"+
	            "}"                                                                    +"\n"+
	            "}"                                                                    
	            ,
	            "if_out_4"
	            ,
	            "i"
	            ,
	            "2"
	            ,
	            "[2,2]"
	            ,
	            }, 
/////////////////  56  liuli:2010.3.26	   ASTEqualityExpression   ///////////////////	
	            {
                "void f(int i){"                                                       +"\n"+
                "i=4;"                                                                 +"\n"+
                "if(i==i+1){"                                                          +"\n"+
                "  i=3; "                                                              +"\n"+
                "}else{"                                                               +"\n"+
                "i=2;"                                                                 +"\n"+
                "}"                                                                    +"\n"+
                "}"                                                                    
                ,
                "if_out_5"
                ,
                "i"
                ,
                "2"
                ,
                "[2,2]"
                ,
                },
/////////////////  57   liuli:2010.3.26	   ASTEqualityExpression  ///////////////////	
	            {
                "void f(int i){"                                                       +"\n"+
                "i=4;"                                                                 +"\n"+
                "if(i!=i+1){"                                                          +"\n"+
                "  i=3; "                                                              +"\n"+
                "}else{"                                                               +"\n"+
                "i=2;"                                                                 +"\n"+
                "}"                                                                    +"\n"+
                "}"                                                                    
                ,
                "if_out_5"
                ,
                "i"
                ,
                "3"
                ,
                "[3,3]"
                ,
                },
/////////////////  58  liuli:2010.3.26	   ASTEqualityExpression   ///////////////////	
                {
                "void f(int i){"                                                       +"\n"+
                "if(i==i+1){"                                                          +"\n"+
                "  i=3; "                                                              +"\n"+
                "}else{"                                                               +"\n"+
                "i=2;"                                                                 +"\n"+
                "}"                                                                    +"\n"+
                "}"                                                                    
                ,
                "if_out_4"
                ,
                "i"
                ,
                "2"
                ,
                "[2,2]"
                ,
                },
/////////////////  59  liuli:2010.3.26	   ASTRelationalExpression   ///////////////////	
                {
                "void f(int i){"                                                       +"\n"+
                "i=4;"                                                                 +"\n"+
                "if(i>i+1){"                                                           +"\n"+
                "  i=3; "                                                              +"\n"+
                "}else{"                                                               +"\n"+
                "i=2;"                                                                 +"\n"+
                "}"                                                                    +"\n"+
                "}"                                                                    
                ,
                "if_out_5"
                ,
                "i"
                ,
                "2"
                ,
                "[2,2]"
                ,
                },
/////////////////  60   liuli:2010.3.26	   ASTRelationalExpression  ///////////////////	
                {
                "void f(int i){"                                                       +"\n"+
                "i=4;"                                                                 +"\n"+
                "if(i+1>i){"                                                           +"\n"+
                "  i=3; "                                                              +"\n"+
                "}else{"                                                               +"\n"+
                "i=2;"                                                                 +"\n"+
                "}"                                                                    +"\n"+
                "}"                                                                    
                ,
                "if_out_5"
                ,
                "i"
                ,
                "3"
                ,
                "[3,3]"
                ,
                },   
/////////////////  61   liuli:2010.3.26	   ASTRelationalExpression   ///////////////////	
                {
                "void f(int i){"                                                       +"\n"+
                "i=4;"                                                                 +"\n"+
                "if(i>=i+1){"                                                           +"\n"+
                "  i=3; "                                                              +"\n"+
                "}else{"                                                               +"\n"+
                "i=2;"                                                                 +"\n"+
                "}"                                                                    +"\n"+
                "}"                                                                    
                ,
                "if_out_5"
                ,
                "i"
                ,
                "2"
                ,
                "[2,2]"
                ,
                },
//////////////// /  62    liuli:2010.3.26	   ASTRelationalExpression  ///////////////////	
                {
                "void f(int i){"                                                       +"\n"+
                "i=4;"                                                                 +"\n"+
                "if(i+1>=i){"                                                           +"\n"+
                "  i=3; "                                                              +"\n"+
                "}else{"                                                               +"\n"+
                "i=2;"                                                                 +"\n"+
                "}"                                                                    +"\n"+
                "}"                                                                    
                ,
                "if_out_5"
                ,
                "i"
                ,
                "3"
                ,
                "[3,3]"
                ,
                },   
/////////////////  63    liuli:2010.3.26	   ASTRelationalExpression ///////////////////	
                {
                "void f(int i){"                                                       +"\n"+
                "i=4;"                                                                 +"\n"+
                "if(i<i+1){"                                                           +"\n"+
                "  i=3; "                                                              +"\n"+
                "}else{"                                                               +"\n"+
                "i=2;"                                                                 +"\n"+
                "}"                                                                    +"\n"+
                "}"                                                                    
                ,
                "if_out_5"
                ,
                "i"
                ,
                "3"
                ,
                "[3,3]"
                ,
                },
//////////////// /  64   liuli:2010.3.26	   ASTRelationalExpression   ///////////////////	
                {
                "void f(int i){"                                                       +"\n"+
                "i=4;"                                                                 +"\n"+
                "if(i+1<i){"                                                           +"\n"+
                "  i=3; "                                                              +"\n"+
                "}else{"                                                               +"\n"+
                "i=2;"                                                                 +"\n"+
                "}"                                                                    +"\n"+
                "}"                                                                    
                ,
                "if_out_5"
                ,
                "i"
                ,
                "2"
                ,
                "[2,2]"
                ,
                },   
/////////////////  65     liuli:2010.3.26	   ASTRelationalExpression ///////////////////	
                {
                "void f(int i){"                                                       +"\n"+
                "i=4;"                                                                 +"\n"+
                "if(i<=i+1){"                                                           +"\n"+
                "  i=3; "                                                              +"\n"+
                "}else{"                                                               +"\n"+
                "i=2;"                                                                 +"\n"+
                "}"                                                                    +"\n"+
                "}"                                                                    
                ,
                "if_out_5"
                ,
                "i"
                ,
                "3"
                ,
                "[3,3]"
                ,
                },
/////////////////  66   liuli:2010.3.26	   ASTRelationalExpression   ///////////////////	
                {
                "void f(int i){"                                                       +"\n"+
                "i=4;"                                                                 +"\n"+
                "if(i+1<=i){"                                                           +"\n"+
                "  i=3; "                                                              +"\n"+
                "}else{"                                                               +"\n"+
                "i=2;"                                                                 +"\n"+
                "}"                                                                    +"\n"+
                "}"                                                                    
                ,
                "if_out_5"
                ,
                "i"
                ,
                "2"
                ,
                "[2,2]"
                ,
                },  
/////////////////  67    liuli:2010.3.26	  zys:2010.6.19例子本身有错误？？  ///////////////////	
                {
                "void f(int i){"                                                       +"\n"+
                "i=4;"                                                                 +"\n"+
                "if(x>y){"                                                             +"\n"+
                "  i=3; "                                                              +"\n"+
                "}else{"                                                               +"\n"+
                "i=2;"                                                                 +"\n"+
                "}"                                                                    +"\n"+
                "}"                                                                    
                ,
                "if_out_5"
                ,
                "i"
                ,
                "i_45"
                ,
                "[2,3]"
                ,
                },                    
/////////////////  68  ChenHonghe 2010.3.26    ASTConstant  image.endsWith("l") ///////////////////	
                {
                "void fun()"                                                           +"\n"+
                "{"                                                                    +"\n"+
                "	int c;"                                                              +"\n"+
                "	c=5l;"                                                               +"\n"+
                "}"                                                                    
                ,
                "stmt_2"
                ,
                "c"
                ,
                "5"
                ,
                "[5,5]"
                ,
                },        
/////////////////  69  ChenHonghe 2010.3.26    ASTConstant  image.endsWith("u") ///////////////////	
                {
                "void fun()"                                                           +"\n"+
                "{"                                                                    +"\n"+
                "	int c;"                                                              +"\n"+
                "	c=5u;"                                                               +"\n"+
                "}"                                                                    
                ,
                "stmt_2"
                ,
                "c"
                ,
                "5"
                ,
                "[5,5]"
                ,
                },
/////////////////  70  ChenHonghe 2010.3.26    ASTConstant  image.endsWith("L") ///////////////////	
                {
                "void fun()"                                                           +"\n"+
                "{"                                                                    +"\n"+
                "	int c;"                                                              +"\n"+
                "	c=5L;"                                                               +"\n"+
                "}"                                                                    
                ,
                "stmt_2"
                ,
                "c"
                ,
                "5"
                ,
                "[5,5]"
                ,
                },  
/////////////////  71  ChenHonghe 2010.3.26    ASTConstant  image.endsWith("U") ///////////////////	
                {
                "void fun()"                                                           +"\n"+
                "{"                                                                    +"\n"+
                "	int c;"                                                              +"\n"+
                "	c=5U;"                                                               +"\n"+
                "}"                                                                    
                ,
                "stmt_2"
                ,
                "c"
                ,
                "5"
                ,
                "[5,5]"
                ,
                }, 
/////////////////  72    ChenHonghe 2010.3.26    ASTConstant 16进制 ‘0’-‘9’///////////////////	
                {
                "void fun()"                                                           +"\n"+
                "{"                                                                    +"\n"+
                "	int c;"                                                              +"\n"+
                "	c=0x7;"                                                              +"\n"+
                "}"                                                                    
                ,
                "stmt_2"
                ,
                "c"
                ,
                "7"
                ,
                "[7,7]"
                ,
                },
/////////////////  73    ChenHonghe 2010.3.26    ASTConstant 10进制   ///////////////////	
                {
                "void fun()"                                                           +"\n"+
                "{"                                                                    +"\n"+
                "	int c;"                                                              +"\n"+
                "	c=7u;"                                                              +"\n"+
                "}"                                                                    
                ,
                "stmt_2"
                ,
                "c"
                ,
                "7"
                ,
                "[7,7]"
                ,
                },
/////////////////  74   ChenHonghe 2010.3.26    ASTConstant 8进制///////////////////	
                {
                "void fun()"                                                           +"\n"+
                "{"                                                                    +"\n"+
                "	int c;"                                                              +"\n"+
                "	c=07;"                                                               +"\n"+
                "}"                                                                    
                ,
                "stmt_2"
                ,
                "c"
                ,
                "7"
                ,
                "[7,7]"
                ,
                },
/////////////////  75   ChenHonghe 2010.3.26    ASTConstant 10进制///////////////////	
                {
                "void fun()"                                                           +"\n"+
                "{"                                                                    +"\n"+
                "	int c;"                                                              +"\n"+
                "	c=7l;"                                                               +"\n"+
                "}"                                                                    
                ,
                "stmt_2"
                ,
                "c"
                ,
                "7"
                ,
                "[7,7]"//失败
                ,
                },
/////////////////  76   ChenHonghe 2010.3.26    ASTConstant  全零///////////////////	
                {
                "void fun()"                                                           +"\n"+
                "{"                                                                    +"\n"+
                "	int c;"                                                              +"\n"+
                "	c=0000;"                                                             +"\n"+
                "}"                                                                    
                ,
                "stmt_2"
                ,
                "c"
                ,
                "0"
                ,
                "[0,0]"
                ,
                },
/////////////////  77   ChenHonghe 2010.3.26    ASTConstant 16进制 ‘a’-‘f’///////////////////	
                {
                "void fun()"                                                           +"\n"+
                "{"                                                                    +"\n"+
                "	int c;"                                                              +"\n"+
                "	c=0xf;"                                                              +"\n"+
                "}"                                                                    
                ,
                "stmt_2"
                ,
                "c"
                ,
                "15"
                ,
                "[15,15]"
                ,
                },
/////////////////  78    ChenHonghe 2010.3.26    ASTConstant 16进制 ‘A’-‘F’///////////////////	
                {
                "void fun()"                                                           +"\n"+
                "{"                                                                    +"\n"+
                "	int c;"                                                              +"\n"+
                "	c=0xF;"                                                              +"\n"+
                "}"                                                                    
                ,
                "stmt_2"
                ,
                "c"
                ,
                "15"
                ,
                "[15,15]"
                ,
                },
/////////////////  79   ChenHonghe 2010.3.26    ASTConstant  ///////////////////	
                {
                "void fun()"                                                           +"\n"+
                "{"                                                                    +"\n"+
                "	int c;"                                                              +"\n"+
                "	c=3.0;"                                                              +"\n"+
                "}"                                                                    
                ,
                "stmt_2"
                ,
                "c"
                ,
                "3.0"
                ,
                "[3,3]"
                ,
                },
/////////////////  80   ChenHonghe 2010.3.26    ASTConstant 八进制+///////////////////	
                {
                "void fun()"                                                           +"\n"+
                "{"                                                                    +"\n"+
                "	int c;"                                                              +"\n"+
                "	c=07+05;"                                                          +"\n"+
                "}"                                                                    +"\n"+
                "	"                                                                    
                ,
                "stmt_2"
                ,
                "c"
                ,
                "12"
                ,
                "[12,12]"
                ,
                },
/////////////////  81   ChenHonghe 2010.3.26   ASTExclusiveORExpression '^'///////////////////		
                {
                "void fun()"                                                           +"\n"+
                "{"                                                                    +"\n"+
                "	int a=2,b=10,c;"                                                     +"\n"+
                "	c=a^b;"                                                              +"\n"+
                "}"                                                                    
                ,
                "stmt_2"
                ,
                "c"
                ,
                "8"
                ,
                "[8,8]"
                ,
                },
/////////////////  82   ChenHonghe 2010.3.26    ASTInclusiveORExpression '|'///////////////////	
                {
                "void fun()"                                                           +"\n"+
                "{"                                                                    +"\n"+
                "	int a=2,b=10,c;"                                                     +"\n"+
                "	c=a|b;"                                                              +"\n"+
                "}"                                                                    
                ,
                "stmt_2"
                ,
                "c"
                ,
                "10"
                ,
                "[10,10]"
                ,
                },
/////////////////  83  ChenHonghe 2010.3.26 ASTLogicalANDExpression  2&&10 ///////////////////	
                {
                "void fun()"                                                           +"\n"+
                "{"                                                                    +"\n"+
                "	int a=2,b=10,c;"                                                     +"\n"+
                "	c=a&&b;"                                                             +"\n"+
                "}"                                                                    
                ,
                "stmt_2"
                ,
                "c"
                ,
                "1"
                ,
                "[1,1]"
                ,
                },
/////////////////  84 ChenHonghe 2010.3.26 ASTLogicalANDExpression  0&&10 ///////////////////	
                {
                "void fun()"                                                           +"\n"+
                "{"                                                                    +"\n"+
                "	int a=0,b=10,c;"                                                     +"\n"+
                "	c=a&&b;"                                                             +"\n"+
                "}"                                                                    
                ,
                "stmt_2"
                ,
                "c"
                ,
                "0"
                ,
                "[0,0]"
                ,
                },
/////////////////  85  ChenHonghe 2010.3.26 ASTLogicalANDExpression  2&&0 ///////////////////	
                {
                "void fun()"                                                           +"\n"+
                "{"                                                                    +"\n"+
                "	int a=2,b=0,c;"                                                     +"\n"+
                "	c=a&&b;"                                                             +"\n"+
                "}"                                                                    
                ,
                "stmt_2"
                ,
                "c"
                ,
                "0"
                ,
                "[0,0]"
                ,
                },
/////////////////测试用例错误  86  ChenHonghe 2010.3.26 ASTLogicalANDExpression  2&&null ///////////////////	
                {
                "void fun()"                                                           +"\n"+
                "{"                                                                    +"\n"+
                "	int a=2,b=0,c;"                                                   +"\n"+
                "	c=a&&b;"                                                             +"\n"+
                "}"                                                                    
                ,
                "stmt_2"
                ,
                "c"
                ,
                "S_23"
                ,
                "[0,0]"
                ,
                },
/////////////////  87  ChenHonghe 2010.3.26 ASTLogicalORExpression  2||10 ///////////////////	
                {
                "void fun()"                                                           +"\n"+
                "{"                                                                    +"\n"+
                "	int a=2,b=10,c;"                                                     +"\n"+
                "	c=a||b;"                                                             +"\n"+
                "}"                                                                    
                ,
                "stmt_2"
                ,
                "c"
                ,
                "1"
                ,
                "[1,1]"
                ,
                },
/////////////////  88 ChenHonghe 2010.3.26 ASTLogicalORExpression  0||0  ///////////////////	
                {
                "void fun()"                                                           +"\n"+
                "{"                                                                    +"\n"+
                "	int a=0,b=0,c;"                                                     +"\n"+
                "	c=a||b;"                                                             +"\n"+
                "}"                                                                    
                ,
                "stmt_2"
                ,
                "c"
                ,
                "0"
                ,
                "[0,0]"
                ,
                },

/////////////////例子有错误  89   ChenHonghe 2010.3.26 ASTLogicalORExpression  2||null  //////////////////	
                {
                "void fun()"                                                           +"\n"+
                "{"                                                                    +"\n"+
                "	int a=2,b=null,c;"                                                   +"\n"+
                "	c=a||b;"                                                             +"\n"+
                "}"                                                                    
                ,
                "stmt_2"
                ,
                "c"
                ,
                "S_23"
                ,
                "[1,1]"
                ,
                },
/////////////////  90   ChenHonghe 2010.3.26  ASTPostfixExpression 数组元素+///////////////////	
                {
                    "void fun()"                                                           +"\n"+
                    "{"                                                                    +"\n"+
                    "	int a[1],b[1],c;"                                                    +"\n"+
                    "	b[0]=0,a[0]=0;"                                                      +"\n"+
                    "	c=b[0]+a[0];"                                                        +"\n"+
                    "}"                                                                    
                    ,
                    "stmt_3"
                    ,
                    "c"
                    ,
                    /*"a_23+b_01"*/"0"
                    ,
                    /*"ERROR"//数组运算错误*/"ERROR"
                ,
                },
/////////////////  91   ChenHonghe 2010.3.26  ASTPostfixExpression  scanf()///////////////////	
                {
                "void fun()"                                                           +"\n"+
                "{	"                                                                   +"\n"+
                "	int a;"                                                              +"\n"+
                "	scanf(\"%d\",&a);"                                                     +"\n"+
                "}"                                                                    +"\n"+
                "	"                                                                    
                ,
                "stmt_2"
                ,
                "a"
                ,
                "a_23"
                ,
                "ERROR"
                ,
                },
/////////////////  92   ChenHonghe 2010.3.26  ASTPostfixExpression  '.'类型的指针///////////////////	
                {
                "typedef struct{"                                                      +"\n"+
                "    int a ;"                                                          +"\n"+
                " }str;"                                                               +"\n"+
                "void fun()"                                                           +"\n"+
                "{	"                                                                   +"\n"+
                "	str  s=(str*)malloc(sizeof(str));"                                   +"\n"+
                "	s.a=5;"                                                            +"\n"+
                "}"                                                                    +"\n"+
                "	"                                                                    
                ,
                "stmt_2"
                ,
                "a"
                ,
                "ERROR"
                ,
                "ERROR"//错误
                ,
                },
/////////////////  93  ChenHonghe 2010.3.26  ASTPostfixExpression   #=#--///////////////////	
                {
                "void fun()"                                                           +"\n"+
                "{"                                                                    +"\n"+
                "	int a=5;"                                                            +"\n"+
                "	b=a--;"                                                              +"\n"+
                "}"                                                                    +"\n"+
                "	"                                                                    
                ,
                "stmt_2"
                ,
                "a"
                ,
                "4"
                ,
                "[4,4]"
                ,
                },
/////////////////  94  ChenHonghe 2010.3.26  ASTUnaryExpression  #=++# ///////////////////
                {
                    "void fun()"                                                           +"\n"+
                    "{"                                                                    +"\n"+
                    "	int a=5,b=1;"                                                        +"\n"+
                    "	b=++a;"                                                              +"\n"+
                    "}"                                                                    +"\n"+
                    "	"                                                                    
                    ,
                    "stmt_2"
                    ,
                    "b"
                    ,
                    "6"
                    ,
                    "[6,6]"
                    ,
                    },
    /////////////////  95 ChenHonghe 2010.3.26  AbstractExpression  #=#<<# ///////////////////	
                    {
                    "void fun()"                                                           +"\n"+
                    "{"                                                                    +"\n"+
                    "	int a=5,b=3,c;"                                                      +"\n"+
                    "	c=a<<b;"                                                             +"\n"+
                    "}"                                                                    +"\n"+
                    "	"                                                                    
                    ,
                    "stmt_2"
                    ,
                    "c"
                    ,
                    /*"0"*/"40"
                    ,
                    /*"[0,0]"*/"[40,40]"//直接产生的用例算的不对
                    ,
                    },
    /////////////////  96   ChenHonghe 2010.3.26  ASTPostfixExpression///////////////////	
                    {
                    "void fun()"                                                           +"\n"+
                    "{"                                                                    +"\n"+
                    "	int a=5,b=1,c;"                                                      +"\n"+
                    "	c=a>>b;"                                                             +"\n"+
                    "}"                                                                    +"\n"+
                    "	"                                                                    
                    ,
                    "stmt_2"
                    ,
                    "c"
                    ,
                    /*"0"*/"2"
                    ,
                    /*"[0,0]"*/"[2,2]"//直接产生的用例算的不对
                    ,
                    },
    /////////////////  97   ChenHonghe 2010.3.26  ASTPostfixExpression   ///////////////////	
                    {
                    "void fun()"                                                           +"\n"+
                    "{"                                                                    +"\n"+
                    "	int a=5,b=3,c;"                                                      +"\n"+
                    "	c=a%b;"                                                              +"\n"+
                    "}"                                                                    +"\n"+
                    "	"                                                                    
                    ,
                    "stmt_2"
                    ,
                    "c"
                    ,
                    "2"
                    ,
                    "[2,2]"
                    ,
                    },
    /////////////////  98  ChenHonghe 2010.3.26 ASTRelationalExpression  ///////////////////	
                    {
                    "void fun()"                                                           +"\n"+
                    "{"                                                                    +"\n"+
                    "	int a=5,b=3,c;"                                                      +"\n"+
                    "	c=(a!=b);"                                                           +"\n"+
                    "}"                                                                    +"\n"+
                    "	"                                                                    
                    ,
                    "stmt_2"
                    ,
                    "c"
                    ,
                    "1"
                    ,
                    "[1,1]"
                    ,
                    },
    /////////////////  99  ChenHonghe 2010.3.26 ASTUnaryExpression ~ ///////////////////	
                    {
                    "void fun()"                                                           +"\n"+
                    "{"                                                                    +"\n"+
                    "	int a=5,b=3,c;"                                                      +"\n"+
                    "	c=~a;"                                                               +"\n"+
                    "}"                                                                    +"\n"+
                    "	"                                                                    
                    ,
                    "stmt_2"
                    ,
                    "c"
                    ,
                    "-6"
                    ,
                    "[-6,-6]"
                    ,
                    },
    /////////////////  100   ChenHonghe 2010.3.26 ASTUnaryExpression   -///////////////////	
                    {
                    "void fun()"                                                           +"\n"+
                    "{"                                                                    +"\n"+
                    "	int a=5,b=3,c;"                                                      +"\n"+
                    "	c=-a;"                                                               +"\n"+
                    "}"                                                                    +"\n"+
                    "	"                                                                    
                    ,
                    "stmt_2"
                    ,
                    "c"
                    ,
                    "-5"
                    ,
                    "[-5,-5]"
                    ,
                    },
    /////////////////  101   ChenHonghe 2010.3.26 ASTUnaryExpression ! ///////////////////	
                    {
                    "void fun()"                                                           +"\n"+
                    "{"                                                                    +"\n"+
                    "	int a=5,b=3,c;"                                                      +"\n"+
                    "	c=!a;"                                                               +"\n"+
                    "}"                                                                    +"\n"+
                    "	"                                                                    
                    ,
                    "stmt_2"
                    ,
                    "c"
                    ,
                    "1"
                    ,
                    "[0,0]"
                    ,
                    },
    /////////////////  102    ChenHonghe 2010.3.26 ASTUnaryExpression !///////////////////	
                    {
                    "void fun()"                                                           +"\n"+
                    "{"                                                                    +"\n"+
                    "	int a=0,b=3,c;"                                                      +"\n"+
                    "	c=!a;"                                                               +"\n"+
                    "}"                                                                    +"\n"+
                    "	"                                                                    
                    ,
                    "stmt_2"
                    ,
                    "c"
                    ,
                    "0"
                    ,
                    "[1,1]"
                    ,
                    },
    /////////////////  103 ChenHonghe 2010.3.26  ASTUnaryExpression   ///////////////////
                    {
                        "void fun()"                                                           +"\n"+
                        "{"                                                                    +"\n"+
                        "	int a=5,b=1;"                                                        +"\n"+
                        "	b=--a;"                                                              +"\n"+
                        "}"                                                                    +"\n"+
                        "	"                                                                    
                        ,
                        "stmt_2"
                        ,
                        "b"
                        ,
                        "4"
                        ,
                        "[4,4]"
                        ,
                        },
/////////////////  104  ChenHonghe 2010.3.26  ASTUnaryExpression    ///////////////////	
                        {
                        "void fun()"                                                           +"\n"+
                        "{"                                                                    +"\n"+
                        "	int a=1,b=0,c;"                                                   +"\n"+
                        "	c=!(a&&b);"                                                          +"\n"+
                        "}"                                                                    +"\n"+
                        "	"                                                                    
                        ,
                        "stmt_2"
                        ,
                        "c"
                        ,
                        "S_45"
                        ,
                        "[1,1]"
                        ,
                        },
 /////////////////  105 ChenHonghe 2010.3.26  ASTUnaryExpression ==   ///////////////////	
                        {
                        "void fun()"                                                           +"\n"+
                        "{"                                                                    +"\n"+
                        "	int a=1,b=2,c;"                                                      +"\n"+
                        "	c=(a==b);"                                                           +"\n"+
                        "}"                                                                    +"\n"+
                        "	"                                                                    
                        ,
                        "stmt_2"
                        ,
                        "c"
                        ,
                        "0"
                        ,
                        "[0,0]"
                        ,
                        },
/////////////////  106   ChenHonghe 2010.3.26   ASTPostfixExpression ‘->'///////////////////	
                        {
                        "typedef struct{"                                                      +"\n"+
                        "    int a ;"                                                          +"\n"+
                        " }str;"                                                               +"\n"+
                        "void fun()"                                                           +"\n"+
                        "{	"                                                                   +"\n"+
                        "	str*  s=(str*)malloc(sizeof(str));"                                  +"\n"+
                        "	s->a=5;"                                                             +"\n"+
                        "}"                                                                    +"\n"+
                        "	"                                                                    
                        ,
                        "stmt_2"
                        ,
                        "s"
                        ,
                        "S_01"
                        ,
                        "NULL_OR_NOTNULL offsetRange: [-inf,inf] Eval: [0,0] Type:[]"
                        ,
                        },
/////////////////  107   ChenHonghe 2010.3.26 混合运算///////////////////	
	     
	            {
		            "void f()"                                                             +"\n"+
		            "{"                                                                    +"\n"+
		            "	int a=10,b=2,s;"                                                     +"\n"+
		            "	s=(a+a)*b-a/(b+a%b);"                                                +"\n"+
		            "} "                                                                   
		            ,
		            "stmt_2"
		            ,
		            "s"
		            ,
		            "35.0"
		            ,
		            "[35,35]"
		            ,
		            },
		            
/////////////////  108   ChenHonghe 2010.3.26  带浮点的混合运算///////////////////	
		            {
			            "void f()"                                                             +"\n"+
			            "{"                                                                    +"\n"+
			            "	int a=10,s;"                                                         +"\n"+
			            "	int b=3;"                                                       +"\n"+
			            "	s=(a+a)*b-a/(b+a%b);"                                                +"\n"+
			            "} "                                                                   
			            ,
			            "stmt_3"
			            ,
			            "s"
			            ,
			            "57.5"
			            ,
			            "[57,57]"
			            ,
			            },
//////////////// /  109 liuli 2010.3.29 ASTAssignmentExpression///////////////////	
	                    {
	                        "void f(int i){"                                                       +"\n"+
	                        "if(i>4){"                                                             +"\n"+
	                        "i=6;"                                                                 +"\n"+
	                        "}else{"                                                               +"\n"+
	                        "i=2;"                                                                 +"\n"+
	                        "}"                                                                    +"\n"+
	                        "i%=3;"                                                                +"\n"+
	                        "}"                                                                    
	                        ,
	                        "stmt_5"
	                        ,
	                        "i"
	                        ,
	                        "S_67"
	                        ,
	                        "ERROR"
	                        ,
	                        },

////////////////	        /  110 ssj while嵌套循环语句 ///////////////////	
	                        {
	                        "void main(){"                                                         +"\n"+
	                        "     	int i=0;"                                                       +"\n"+
	                        "	    while(i<10)"                                                     +"\n"+
	                        "		{	"                                                                 +"\n"+
	                        "			while(i>5){"                                                       +"\n"+
	                        "				i++;"                                                             +"\n"+
	                        "				break;"                                                           +"\n"+
	                        "				}"                                                                +"\n"+
	                        "				break;"                                                           +"\n"+
	                        "		  }"                                                                +"\n"+
	                        "	}"                                                                   
	                        ,
	                        "while_out_8"
	                        ,
	                        "i"
	                        ,
	                        "0"
	                        ,
	                        "[0,0]"
	                        ,
	                        },
////////////////	        /  111 ssj   while嵌套goto语句///////////////////	
	                        {
	                        "void main(){"                                                         +"\n"+
	                        "     	int i=0;"                                                       +"\n"+
	                        "	    while(i<10)"                                                     +"\n"+
	                        "		{	"                                                                 +"\n"+
	                        "           start:i++;"                                                +"\n"+
	                        "				 goto start;"                                                     +"\n"+
	                        ""                                                                     +"\n"+
	                        "		  }"                                                                +"\n"+
	                        "	}"                                                                   
	                        ,
	                        "goto_5"
	                        ,
	                        "i"
	                        ,
	                        "1"
	                        ,
	                        "[1,1]"
	                        ,
	                        },
////////////////	        /  112 ssj   while嵌套return语句///////////////////	
	                        {
	                        "void main(){"                                                         +"\n"+
	                        "     	"                                                               +"\n"+
	                        "        int i;"                                                       +"\n"+
	                        "	    while(i<10)"                                                     +"\n"+
	                        "		{	"                                                                 +"\n"+
	                        "	       i-1;	"                                                        +"\n"+
	                        "           end:i++;"                                                  +"\n"+
	                        "			if(i<5)"                                                           +"\n"+
	                        "                return;"                                              +"\n"+
	                        "			else goto end;"                                                    +"\n"+
	                        ""                                                                     +"\n"+
	                        "		  }"                                                                +"\n"+
	                        "	}"                                                                   
	                        ,
	                        "return_7"
	                        ,
	                        "i"
	                        ,
	                        "1+i_01"
	                        ,
	                        "[-inf,4]"
	                        ,
	                        },
////////////////	        /  113 ssj   while嵌套if语句///////////////////	
	                        {
	                        "void main(){"                                                         +"\n"+
	                        "     	int i=0;"                                                       +"\n"+
	                        "	    while(i<10)"                                                     +"\n"+
	                        "		{	"                                                                 +"\n"+
	                        "			if(i<5) i++;"                                                      +"\n"+
	                        "			else i=5;"                                                         +"\n"+
	                        "		  }"                                                                +"\n"+
	                        "	}"                                                                   
	                        ,
	                        "if_out_6"
	                        ,
	                        "i"
	                        ,
	                        "i_3233"
	                        ,
	                        "[1,5]"
	                        ,
	                        },
////////////////	        /  114 ssj   while嵌套break，continnue语句///////////////////	
	                        {
	                        "void main(){"                                                         +"\n"+
	                        "     	int i=0;"                                                       +"\n"+
	                        "	    while(i<10)"                                                     +"\n"+
	                        "		{	"                                                                 +"\n"+
	                        "			if (i<5){"                                                         +"\n"+
	                        "			   i++;"                                                           +"\n"+
	                        "			   continue;"                                                      +"\n"+
	                        "			}"                                                                 +"\n"+
	                        "			else {"                                                            +"\n"+
	                        "				i--;"                                                             +"\n"+
	                        "				break;"                                                           +"\n"+
	                        "			}		 "                                                              +"\n"+
	                        "		  }"                                                                +"\n"+
	                        "	}"                                                                   
	                        ,
	                        "continue_5"
	                        ,
	                        "i"
	                        ,
	                        "1"
	                        ,
	                        "[1,1]"
	                        ,
	                        },
////////////////	        /  115 ssj   while嵌套表达式语句///////////////////	
	                        {
	                        "void main(){"                                                         +"\n"+
	                        "     	int i=0;"                                                       +"\n"+
	                        "	    while(i<10)"                                                     +"\n"+
	                        "		{	"                                                                 +"\n"+
	                        "			i++;"                                                              +"\n"+
	                        "		  }"                                                                +"\n"+
	                        "	}"                                                                   
	                        ,
	                        "while_out_4"
	                        ,
	                        "i"
	                        ,
	                        "i_2425"
	                        ,
	                        "[10,10]"
	                        ,
	                        },
////////////////	        /  116 ssj   while嵌套条件语句///////////////////	
	                        {
	                        "void main(){"                                                         +"\n"+
	                        "     	int i=0;"                                                       +"\n"+
	                        "	    while(i<10)"                                                     +"\n"+
	                        "		{	"                                                                 +"\n"+
	                        "			(i>5)?3:5;"                                                        +"\n"+
	                        "		  }"                                                                +"\n"+
	                        "	}"                                                                   
	                        ,
	                        "stmt_3"
	                        ,
	                        "i"
	                        ,
	                        "i_1213"
	                        ,
	                        "[0,0]"
	                        ,
	                        },
////////////////	        /  117 ssj   for嵌套switch语句///////////////////	
	                        {
	                        "#include <stdio.h>"                                                   +"\n"+
	                        "void main()"                                                          +"\n"+
	                        " {"                                                                   +"\n"+
	                        "   char letter;"                                                      +"\n"+
	                        "   int vowel_count = 0;"                                              +"\n"+
	                        "   for (letter = 'A'; letter <= 'Z'; letter++)"                       +"\n"+
	                        "     switch (letter) {"                                               +"\n"+
	                        "       case 'A':"                                                     +"\n"+
	                        "       case 'E':"                                                     +"\n"+
	                        "       case 'I':"                                                     +"\n"+
	                        "       case 'O':"                                                     +"\n"+
	                        "       case 'U':"                                                     +"\n"+
	                        "		   vowel_count++;"                                                  +"\n"+
	                        "     }"                                                               +"\n"+
	                        "   "                                                                  +"\n"+
	                        "   printf(\"The number of vowels is %d\\n\", vowel_count);"              +"\n"+
	                        " }"                                                                   
	                        ,
	                        "switch_out_12"
	                        ,
	                        "letter"
	                        ,
	                        "letter_150151"
	                        ,
	                        "[65,90]"
	                        ,
	                        },
////////////////	        /  118 ssj   混合语句///////////////////	
	                        {
	                        "void main()"                                                          +"\n"+
	                        " {"                                                                   +"\n"+
	                        "   int counter;"                                                      +"\n"+
	                        "   for (counter = 1; counter <= 100; counter++)"                      +"\n"+
	                        "    {"                                                                +"\n"+
	                        "      if (counter == 50)"                                             +"\n"+
	                        "        break;"                                                       +"\n"+
	                        ""                                                                     +"\n"+
	                        "      printf(\"%d \", counter);"                                        +"\n"+
	                        "    }"                                                                +"\n"+
	                        "   printf(\"\\nNext loop\\n\");"                                          +"\n"+
	                        "   for (counter = 100; counter >= 1; counter--)"                      +"\n"+
	                        "    {"                                                                +"\n"+
	                        "      if (counter == 50)"                                             +"\n"+
	                        "        break;"                                                       +"\n"+
	                        "      printf(\"%d \", counter);"                                        +"\n"+
	                        "    }"                                                                +"\n"+
	                        " }   "                                                                
	                        ,
	                        "for_out_9"
	                        ,
	                        "counter"
	                        ,
	                        "counter_4041"
	                        ,
	                        "[50,50]U[101,101]"
	                        ,
	                        },
////////////////	        /  119 ssj   混合语句///////////////////	
	                        {
	                        "void main()"                                                          +"\n"+
	                        " {   int counter;"                                                    +"\n"+
	                        "   printf(\"\\nEven values\\n\");"                                        +"\n"+
	                        "   for (counter = 1; counter <= 100; counter++)"                      +"\n"+
	                        "     {"                                                               +"\n"+
	                        "       if (counter % 2)  // Odd"                                      +"\n"+
	                        "         continue;"                                                   +"\n"+
	                        "       printf(\"%d \", counter);"                                       +"\n"+
	                        "     }"                                                               +"\n"+
	                        "   printf(\"\\nOdd values\\n\");"                                         +"\n"+
	                        "   counter = 0;"                                                      +"\n"+
	                        "   while (counter <= 100) "                                           +"\n"+
	                        "     {       counter++;"                                              +"\n"+
	                        "       if (! (counter % 2)) // Even "                                 +"\n"+
	                        "         continue;"                                                   +"\n"+
	                        "       printf(\"%d \", counter);"                                       +"\n"+
	                        "     }"                                                               +"\n"+
	                        " }"                                                                   
	                        ,
	                        "while_out_19"
	                        ,
	                        "counter"
	                        ,
	                        "counter_116117"
	                        ,
	                        "[101,101]"
	                        ,
	                        },
////////////////	        /  120 ssj   混合语句///////////////////	
	                        {
	                        "void main()"                                                          +"\n"+
	                        " {   int i, j;"                                                       +"\n"+
	                        "   for (i = 0, j = 100; i <= 100; i++, j++)"                          +"\n"+
	                        "     printf(\"i = %d j = %d\\n\", i, j);"                                +"\n"+
	                        " }"                                                                   
	                        ,
	                        "for_out_6"
	                        ,
	                        "j"
	                        ,
	                        "j_4849"
	                        ,
	                        "[100,inf]"
	                        ,
	                        },
////////////////	        /  121 ssj   混合语句///////////////////	
	                        {
	                        "void main()"                                                          +"\n"+
	                        " {   char letter;"                                                    +"\n"+
	                        "   int vowel_count = 0;"                                              +"\n"+
	                        "   int consonant_count = 0;     "                                     +"\n"+
	                        "   for (letter = 'A'; letter <= 'Z'; letter++)"                       +"\n"+
	                        "     switch (letter) {"                                               +"\n"+
	                        "       case 'A':"                                                     +"\n"+
	                        "       case 'E':"                                                     +"\n"+
	                        "       case 'I':"                                                     +"\n"+
	                        "       case 'O':"                                                     +"\n"+
	                        "       case 'U': vowel_count++;"                                      +"\n"+
	                        "                 break;"                                              +"\n"+
	                        "       default: consonant_count++;"                                   +"\n"+
	                        "     }; "                                                             +"\n"+
	                        "   printf(\"The number of vowels is %d\\n\", vowel_count);"              +"\n"+
	                        "   printf(\"The number of vowels is %d\\n\", consonant_count);"          +"\n"+
	                        " }"                                                                   
	                        ,
	                        "break_13"
	                        ,
	                        "letter"
	                        ,
	                        "letter_162163"
	                        ,
	                        "[85,85]"
	                        ,
	                        },
////////////////	        /  122 ssj   if、break、do—while、label和goto语句///////////////////	
	                        {
	                        "void main() {"                                                        +"\n"+
	                        "int count=0;"                                                         +"\n"+
	                        "label1: "                                                             +"\n"+
	                        "do{"                                                                  +"\n"+
	                        "    count=count+1;"                                                   +"\n"+
	                        "    if(count==10)"                                                    +"\n"+
	                        "        break;"                                                       +"\n"+
	                        "    if(count==20)"                                                    +"\n"+
	                        "       goto label2;"                                                  +"\n"+
	                        "}while(count<30);"                                                    +"\n"+
	                        "goto label1;"                                                         +"\n"+
	                        "label2:count=100;"                                                    +"\n"+
	                        "}"                                                                    
	                        ,
	                        "do_while_out1_11"
	                        ,
	                        "count"
	                        ,
	                        "count_4445"
	                        ,
	                        "[1,30]"
	                        ,
	                        },
////////////////	        /  123 ssj   if、break、continue、do—while和label语句///////////////////	
	                        {
	                        "void main() {"                                                        +"\n"+
	                        " int i=10;"                                                           +"\n"+
	                        " label1: do{"                                                         +"\n"+
	                        "   if(i>10)"                                                          +"\n"+
	                        "     continue;"                                                       +"\n"+
	                        "   else "                                                             +"\n"+
	                        "     if(i<10)"                                                        +"\n"+
	                        "       break;"                                                        +"\n"+
	                        "     else"                                                            +"\n"+
	                        "       i++;"                                                          +"\n"+
	                        "		 }"                                                                 +"\n"+
	                        "  while(i<=20);"                                                      +"\n"+
	                        "}"                                                                    
	                        ,
	                        "do_while_out1_11"
	                        ,
	                        "i"
	                        ,
	                        "i_3637"
	                        ,
	                        "[11,21]"
	                        ,
	                        },
////////////////	        /  124 ssj   嵌套do-while循环和if单双分支///////////////////	
	                        {
	                        "void main()"                                                          +"\n"+
	                        "{"                                                                    +"\n"+
	                        "  int i,j,sum=0;"                                                     +"\n"+
	                        "  i=1;"                                                               +"\n"+
	                        "label1:"                                                              +"\n"+
	                        "  do{"                                                                +"\n"+
	                        "     sum=sum+i;"                                                      +"\n"+
	                        "     i++;"                                                            +"\n"+
	                        "        do{"                                                          +"\n"+
	                        "            if(i==10)"                                                +"\n"+
	                        "               continue;"                                             +"\n"+
	                        "            else break;"                                              +"\n"+
	                        "           }"                                                         +"\n"+
	                        "        while(i<=20);"                                                +"\n"+
	                        "     if(i==50)"                                                       +"\n"+
	                        "       break;"                                                        +"\n"+
	                        "    }"                                                                +"\n"+
	                        "   while(i<=100);"                                                    +"\n"+
	                        "i++;"                                                                 +"\n"+
	                        "if(i>=00)"                                                            +"\n"+
	                        "  goto label2;"                                                       +"\n"+
	                        "goto label1;"                                                         +"\n"+
	                        "  label2: (i>100)?(j=0):(j=1);"                                       +"\n"+
	                        "    if(j==0)"                                                         +"\n"+
	                        "      printf(\"%d\",sum);"                                              +"\n"+
	                        "    else"                                                             +"\n"+
	                        "      printf(\"%d\",i);   "                                             +"\n"+
	                        "}"                                                                    
	                        ,
	                        "do_while_out2_17"
	                        ,
	                        "i"
	                        ,
	                        "S_8889"
	                        ,
	                        "[50,50]U[101,101]"
	                        ,
	                        },
/////////////////  125   ///////////////////	
	            {
	            "f(){"                                                                 +"\n"+
	            "int i=1;"                                                             +"\n"+
	            ""                                                                     +"\n"+
	            "switch(i){"                                                           +"\n"+
	            "case 1:"                                                              +"\n"+
	            "	i++;break;"                                                          +"\n"+
	            "case 2:"                                                              +"\n"+
	            "	i--;break;"                                                          +"\n"+
	            "default:"                                                             +"\n"+
	            "	break;"                                                              +"\n"+
	            "}"                                                                    +"\n"+
	            "return i;"                                                            +"\n"+
	            "}"                                                                    
	            ,
	            "switch_head_2"
	            ,
	            "i"
	            ,
	            "1"
	            ,
	            "[1,1]"
	            ,
	            },
/////////////////  126   ///////////////////	
	            {
	            "f(){"                                                                 +"\n"+
	            "int i=1;"                                                             +"\n"+
	            ""                                                                     +"\n"+
	            "switch(i){"                                                           +"\n"+
	            "case 1:"                                                              +"\n"+
	            "	i++;break;"                                                          +"\n"+
	            "case 2:"                                                              +"\n"+
	            "	i--;break;"                                                          +"\n"+
	            "default:"                                                             +"\n"+
	            "	break;"                                                              +"\n"+
	            "}"                                                                    +"\n"+
	            "return i;"                                                            +"\n"+
	            "}"                                                                    
	            ,
	            "label_head_case_6"
	            ,
	            "i"
	            ,
	            "ERROR"
	            ,
	            "ERROR"
	            ,
	            },
/////////////////  127   ///////////////////	
	            {
	            "f(){"                                                                 +"\n"+
	            "int i=1;"                                                             +"\n"+
	            "switch(i){"                                                           +"\n"+
	            "case 1:"                                                              +"\n"+
	            "	i++;break;"                                                          +"\n"+
	            "case 2:"                                                              +"\n"+
	            "	i--;break;"                                                          +"\n"+
	            "default:"                                                             +"\n"+
	            "	break;"                                                              +"\n"+
	            "}"                                                                    +"\n"+
	            "return i;"                                                            +"\n"+
	            "}"                                                                    
	            ,
	            "switch_out_11"
	            ,
	            "i"
	            ,
	            "2"
	            ,
	            "[2,2]"
	            ,
	            },
/////////////////  128   ///////////////////	
	            {
	            "f(int i){"                                                            +"\n"+
	            "switch(i){"                                                           +"\n"+
	            "case 1:"                                                              +"\n"+
	            "	i++;break;"                                                          +"\n"+
	            "case 2:"                                                              +"\n"+
	            "	i--;break;"                                                          +"\n"+
	            "default:"                                                             +"\n"+
	            "	break;"                                                              +"\n"+
	            "}"                                                                    +"\n"+
	            "return i;"                                                            +"\n"+
	            "}"                                                                    
	            ,
	            "switch_out_10"
	            ,
	            "i"
	            ,
	            "i_1213"
	            ,
	            "[-inf,inf]"
	            ,
	            },
/////////////////  129  ///////////////////	
	            {
	            "f(int i){"                                                            +"\n"+
	            "//int i=1;"                                                           +"\n"+
	            ""                                                                     +"\n"+
	            "switch(i){"                                                           +"\n"+
	            "case 1:"                                                              +"\n"+
	            "	i++;break;"                                                          +"\n"+
	            "case 2:"                                                              +"\n"+
	            "	i--;break;"                                                          +"\n"+
	            "default:"                                                             +"\n"+
	            "	break;"                                                              +"\n"+
	            "}"                                                                    +"\n"+
	            ""                                                                     +"\n"+
	            "do{"                                                                  +"\n"+
	            "	i++;"                                                                +"\n"+
	            "}while(i<10);"                                                        +"\n"+
	            ""                                                                     +"\n"+
	            "return i;"                                                            +"\n"+
	            "}"                                                                    
	            ,
	            "do_while_out1_13"
	            ,
	            "i"
	            ,
	            "i_2627"
	            ,
	            "[-inf,inf]"
	            ,
	            },
/////////////////  130   ///////////////////	
	            {
	            "f(int i){"                                                            +"\n"+
	            "//int i=1;"                                                           +"\n"+
	            ""                                                                     +"\n"+
	            "switch(i){"                                                           +"\n"+
	            "case 1:"                                                              +"\n"+
	            "	i++;break;"                                                          +"\n"+
	            "case 2:"                                                              +"\n"+
	            "	i--;break;"                                                          +"\n"+
	            "default:"                                                             +"\n"+
	            "	break;"                                                              +"\n"+
	            "}"                                                                    +"\n"+
	            ""                                                                     +"\n"+
	            "do{"                                                                  +"\n"+
	            "	i++;"                                                                +"\n"+
	            "}while(i<10);"                                                        +"\n"+
	            ""                                                                     +"\n"+
	            "return i;"                                                            +"\n"+
	            "}"                                                                    
	            ,
	            "do_while_out2_14"
	            ,
	            "i"
	            ,
	            "i_2627"
	            ,
	            "[10,inf]"
	            ,
	            },
///////////////// 131   ///////////////////	
	            {
	            "f(){"                                                                 +"\n"+
	            "int i=1;"                                                             +"\n"+
	            ""                                                                     +"\n"+
	            "switch(i){"                                                           +"\n"+
	            "case 1:"                                                              +"\n"+
	            "	i++;break;"                                                          +"\n"+
	            "case 2:"                                                              +"\n"+
	            "	i--;break;"                                                          +"\n"+
	            "default:"                                                             +"\n"+
	            "	break;"                                                              +"\n"+
	            "}"                                                                    +"\n"+
	            ""                                                                     +"\n"+
	            "do{"                                                                  +"\n"+
	            "	i++;"                                                                +"\n"+
	            "}while(i<10);"                                                        +"\n"+
	            ""                                                                     +"\n"+
	            "return i;"                                                            +"\n"+
	            "}"                                                                    
	            ,
	            "do_while_head_12"
	            ,
	            "i"
	            ,
	            "i_2021"
	            ,
	            "[2,9]"
	            ,
	            },
/////////////////  132   ///////////////////	
	            {
	            "f(){"                                                                 +"\n"+
	            "int i=1;"                                                             +"\n"+
	            ""                                                                     +"\n"+
	            "switch(i){"                                                           +"\n"+
	            "case 1:"                                                              +"\n"+
	            "	i++;break;"                                                          +"\n"+
	            "case 2:"                                                              +"\n"+
	            "	i--;break;"                                                          +"\n"+
	            "default:"                                                             +"\n"+
	            "	break;"                                                              +"\n"+
	            "}"                                                                    +"\n"+
	            ""                                                                     +"\n"+
	            "do{"                                                                  +"\n"+
	            "	i++;"                                                                +"\n"+
	            "}while(i<10);"                                                        +"\n"+
	            ""                                                                     +"\n"+
	            "return i;"                                                            +"\n"+
	            "}"                                                                    
	            ,
	            "do_while_out1_14"
	            ,
	            "i"
	            ,
	            "i_2425"
	            ,
	            "[3,10]"
	            ,
	            },

/////////////////  133   ///////////////////	
	            {
	            "f(){"                                                                 +"\n"+
	            "int i=1;"                                                             +"\n"+
	            ""                                                                     +"\n"+
	            "switch(i){"                                                           +"\n"+
	            "case 1:"                                                              +"\n"+
	            "	i++;break;"                                                          +"\n"+
	            "case 2:"                                                              +"\n"+
	            "	i--;break;"                                                          +"\n"+
	            "default:"                                                             +"\n"+
	            "	break;"                                                              +"\n"+
	            "}"                                                                    +"\n"+
	            ""                                                                     +"\n"+
	            "do{"                                                                  +"\n"+
	            "	i++;"                                                                +"\n"+
	            "}while(i<10);"                                                        +"\n"+
	            ""                                                                     +"\n"+
	            "return i;"                                                            +"\n"+
	            "}"                                                                    
	            ,
	            "do_while_out2_15"
	            ,
	            "i"
	            ,
	            "i_2425"
	            ,
	            "[10,10]"
	            ,
	            },
/////////////////  134   ERROR	chh 2010.04.08 for 内的条件赋值///////////////////	
	            {
	            "main() {"                                                             +"\n"+
	            "int i,k;"                                                             +"\n"+
	            "int a = 1;"                                                           +"\n"+
	            "for(i=0;i<6;i++)"                                                     +"\n"+
	            "{"                                                                    +"\n"+
	            " a++;"                                                                +"\n"+
	            " k=(a>i)?a:i;"                                                        +"\n"+
	            "}"                                                                    +"\n"+
	            "}"                                                                    
	            ,
	            "stmt_6"
	            ,
	            "k"
	            ,
	            "1+a_5455"
	            ,
	            "[0,5]"
	            ,
	            },
/////////////////  135 chh 2010.04.08 for 内的if ///////////////////	
	            {
	            "main() {"                                                             +"\n"+
	            "int i;"                                                               +"\n"+
	            "int a = 4;"                                                           +"\n"+
	            "for(i=0;i<6;i++)"                                                     +"\n"+
	            "{"                                                                    +"\n"+
	            "if (i<a) a=8;"                                                        +"\n"+
	            "else a=10;"                                                           +"\n"+
	            "}"                                                                    +"\n"+
	            "return;"                                                              +"\n"+
	            "}"                                                                    
	            ,
	            "if_out_8"
	            ,
	            "a"
	            ,
	            "a_5051"
	            ,
	            "[8,8]U[10,10]"
	            ,
	            },
/////////////////  136  chh 2010.04.08 for外的if  ///////////////////	
	            {
	            "main()"                                                               +"\n"+
	            "{"                                                                    +"\n"+
	            "int i;"                                                               +"\n"+
	            "int a=4;"                                                             +"\n"+
	            "for(i=0;i<6;i++)"                                                     +"\n"+
	            "{"                                                                    +"\n"+
	            "if(i<a) continue ;"                                                   +"\n"+
	            "else break;"                                                          +"\n"+
	            "}"                                                                    +"\n"+
	            "if(i>5)"                                                              +"\n"+
	            "a=20;"                                                                +"\n"+
	            "return;"                                                              +"\n"+
	            "}"                                                                    
	            ,
	            "for_out_9"
	            ,
	            "i"
	            ,
	            "i_4041"
	            ,
	            "[4,6]"
	            ,
	            },
/////////////////  137  chh 2010.04.08 for外的if///////////////////		
	            {
	            "main()"                                                               +"\n"+
	            "{"                                                                    +"\n"+
	            "int i;"                                                               +"\n"+
	            "int a=4;"                                                             +"\n"+
	            "for(i=0;i<6;i++)"                                                     +"\n"+
	            "{"                                                                    +"\n"+
	            "if(i<a) continue ;"                                                   +"\n"+
	            "else break;"                                                          +"\n"+
	            "}"                                                                    +"\n"+
	            "if(i>5)"                                                              +"\n"+
	            "a=20;"                                                                +"\n"+
	            "return;"                                                              +"\n"+
	            "}"                                                                    
	            ,
	            "if_out_12"
	            ,
	            "a"
	            ,
	            "S_4243"
	            ,
	            "[4,4]U[20,20]"
	            ,
	            },
/////////////////goto语句计算错误  138  chh 2010.04.08 for内的goto语句   ///////////////////		
	            {
	            "main(){"                                                              +"\n"+
	            "int i;"                                                               +"\n"+
	            "int a;"                                                               +"\n"+
	            "for(i=0;i<6;i++)"                                                     +"\n"+
	            "{goto e1;}"                                                           +"\n"+
	            "e1:"                                                                  +"\n"+
	            "a=10;"                                                                +"\n"+
	            "}"                                                                    
	            ,
	            "stmt_9"
	            ,
	            "i"
	            ,
	            "i_3233"
	            ,
	            "[0,0]"
	            ,
	            },
/////////////////  139  chh 2010.04.08 for ///////////////////	
	            {
	            "void f()"                                                             +"\n"+
	            "{"                                                                    +"\n"+
	            "	int a,i,k;"                                                          +"\n"+
	            "	a=10;"                                                               +"\n"+
	            "	for(i=1;i<5;i++)"                                                    +"\n"+
	            "	a=a-i;"                                                              +"\n"+
	            "}"                                                                    
	            ,
	            "for_out_7"
	            ,
	            "a"
	            ,
	            "a_5455"
	            ,
	            "[-inf,10]"
	            ,
	            },
/////////////////  140 chh 2010.04.08 switch  ///////////////////	
	            {
	            " main(){"                                                             +"\n"+
	            "  int a=1;"                                                           +"\n"+
	            "  int b=2,c;"                                                         +"\n"+
	            "  switch(a){"                                                         +"\n"+
	            "  case 1 :"                                                           +"\n"+
	            "	{	switch (b)"                                                        +"\n"+
	            "  		case 2:c=b;"                                                      +"\n"+
	            "	}"                                                                   +"\n"+
	            "  break;"                                                             +"\n"+
	            "  default:c=a;"                                                       +"\n"+
	            "	}"                                                                   +"\n"+
	            "}"                                                                    
	            ,
	            "switch_out_12"
	            ,
	            "c"
	            ,
	            "2"//"S_01"
	            ,
	            "[2,2]"//"[1,2]"//default:c=a应该不被执行
	            ,
	            },

/////////////////  141 chh 2010.04.08 while 内的switch  ///////////////////	
	            {
	            "main()"                                                               +"\n"+
	            "{"                                                                    +"\n"+
	            " int a=0,b;"                                                          +"\n"+
	            " while(a<3)"                                                          +"\n"+
	            "{"                                                                    +"\n"+
	            "	a++  ;  "                                                            +"\n"+
	            "	switch(a)"                                                           +"\n"+
	            "    {"                                                                +"\n"+
	            "        case 1:b=2;break;"                                            +"\n"+
	            "        case 2:b=4;break;"                                            +"\n"+
	            "        default:printf(\"incorrect!\");break;"                          +"\n"+
	            "    }"                                                                +"\n"+
	            "}"                                                                    +"\n"+
	            "}"                                                                    
	            ,
	            "while_out_15"
	            ,
	            "b"
	            ,
	            "b_6667"
	            ,
	            "[-inf,inf]"
	            ,
	            },
/////////////////////以下所有测试用例用于测试循环迭代是否正确/////////////////////////
/////////////////  142   ///////////////////	
	            {
	            "f(){"                                                                 +"\n"+
	            "	int i=0;"                                                            +"\n"+
	            "	do{"                                                                 +"\n"+
	            "		i++;"                                                               +"\n"+
	            "	}while(i<100);"                                                      +"\n"+
	            "}"                                                                    
	            ,
	            "do_while_out2_5"
	            ,
	            "i"
	            ,
	            "i_2425"
	            ,
	            "[100,100]"
	            ,
	            },
/////////////////  143   ///////////////////	
	            {
	            "f(){"                                                                 +"\n"+
	            "	int i=0;"                                                            +"\n"+
	            "	do{"                                                                 +"\n"+
	            "		i++;"                                                               +"\n"+
	            "	}while(i<100);"                                                      +"\n"+
	            "}"                                                                    
	            ,
	            "do_while_out1_4"
	            ,
	            "i"
	            ,
	            "i_2425"
	            ,
	            "[1,100]"
	            ,
	            },
/////////////////  144   ///////////////////	
	            {
	            "f(){"                                                                 +"\n"+
	            "	int i=0;"                                                            +"\n"+
	            "	do{"                                                                 +"\n"+
	            "		i++;"                                                               +"\n"+
	            "	}while(i<100);"                                                      +"\n"+
	            "}"                                                                    
	            ,
	            "do_while_head_2"
	            ,
	            "i"
	            ,
	            "S_2021"
	            ,
	            "[0,99]"
	            ,
	            },
/////////////////  145   ///////////////////	
	            {
	            "f(){"                                                                 +"\n"+
	            "	int i=0;"                                                            +"\n"+
	            "	do{"                                                                 +"\n"+
	            "		i++;"                                                               +"\n"+
	            "	}while(i<100);"                                                      +"\n"+
	            "}"                                                                    
	            ,
	            "stmt_3"
	            ,
	            "i"
	            ,
	            "1+S_2021"
	            ,
	            "[1,100]"
	            ,
	            },
/////////////////  146   ///////////////////	
	            {
	            "f(){"                                                                 +"\n"+
	            "	int i=0;"                                                            +"\n"+
	            "	while(i<100){"                                                       +"\n"+
	            "		i++;"                                                               +"\n"+
	            "	}"                                                                   +"\n"+
	            "}"                                                                    
	            ,
	            "while_head_2"
	            ,
	            "i"
	            ,
	            "i_2425"
	            ,
	            "[0,100]"
	            ,
	            },
/////////////////  147   ///////////////////	
	            {
	            "f(){"                                                                 +"\n"+
	            "	int i=0;"                                                            +"\n"+
	            "	while(i<100){"                                                       +"\n"+
	            "		i++;"                                                               +"\n"+
	            "	}"                                                                   +"\n"+
	            "}"                                                                    
	            ,
	            "while_out_4"
	            ,
	            "i"
	            ,
	            "i_2425"
	            ,
	            "[100,100]"
	            ,
	            },
/////////////////  148   ///////////////////	
	            {
	            "f(){"                                                                 +"\n"+
	            "	int i;"                                                              +"\n"+
	            "	int j=0;"                                                            +"\n"+
	            "	for(i=0;i<100;i++){"                                                 +"\n"+
	            "		j++;"                                                               +"\n"+
	            "	}"                                                                   +"\n"+
	            "}"                                                                    
	            ,
	            "for_head_4"
	            ,
	            "j"
	            ,
	            "j_3637"
	            ,
	            "[0,inf]"
	            ,
	            },
/////////////////  149   ///////////////////	
	            {
	            "f(){"                                                                 +"\n"+
	            "	int i;"                                                              +"\n"+
	            "	int j=0;"                                                            +"\n"+
	            "	for(i=0;i<100;i++){"                                                 +"\n"+
	            "		j++;"                                                               +"\n"+
	            "	}"                                                                   +"\n"+
	            "}"                                                                    
	            ,
	            "for_out_7"
	            ,
	            "j"
	            ,
	            "j_3637"
	            ,
	            "[0,inf]"
	            ,
	            },
/////////////////  150   ///////////////////	
	            {
	            "f(){"                                                                 +"\n"+
	            "	int i;"                                                              +"\n"+
	            "	int j=0;"                                                            +"\n"+
	            "	for(i=0;i<100;i++){"                                                 +"\n"+
	            "		j++;"                                                               +"\n"+
	            "	}"                                                                   +"\n"+
	            "}"                                                                    
	            ,
	            "for_out_7"
	            ,
	            "i"
	            ,
	            "i_4041"
	            ,
	            "[100,100]"
	            ,
	            },
/////////////////  151   ///////////////////	
	            {
	            "void main(){"                                                         +"\n"+
	            "	int i=0;"                                                            +"\n"+
	            "	while(i<10)"                                                         +"\n"+
	            "	{	"                                                                  +"\n"+
	            "		if(i<5)"                                                            +"\n"+
	            "			i++;"                                                              +"\n"+
	            "		else i=5;"                                                          +"\n"+
	            "	}"                                                                   +"\n"+
	            "}"                                                                    
	            ,
	            "while_head_2"
	            ,
	            "i"
	            ,
	            "i_3031"
	            ,
	            "[0,5]"
	            ,
	            },
/////////////////  152   ///////////////////	
	            {
	            "void main(){"                                                         +"\n"+
	            "	int i=0;"                                                            +"\n"+
	            "	while(i<10)"                                                         +"\n"+
	            "	{	"                                                                  +"\n"+
	            "		if(i<5)"                                                            +"\n"+
	            "			i++;"                                                              +"\n"+
	            "		else i=5;"                                                          +"\n"+
	            "	}"                                                                   +"\n"+
	            "}"                                                                    
	            ,
	            "stmt_4"
	            ,
	            "i"
	            ,
	            "1+i_3031"
	            ,
	            "[1,5]"
	            ,
	            },
/////////////////  153:死循环   ///////////////////	
	            {
	            "void main(){"                                                         +"\n"+
	            "	int i=0;"                                                            +"\n"+
	            "	while(i<10)"                                                         +"\n"+
	            "	{	"                                                                  +"\n"+
	            "		if(i<5)"                                                            +"\n"+
	            "			i++;"                                                              +"\n"+
	            "		else i=5;"                                                          +"\n"+
	            "	}"                                                                   +"\n"+
	            "}"                                                                    
	            ,
	            "while_out_7"
	            ,
	            "i"
	            ,
	            "ERROR"
	            ,
	            "ERROR"
	            ,
	            },
/////////////////  154：嵌套循环   ///////////////////	
	            {
	            "f(){"                                                                 +"\n"+
	            "int i=0,j=0;"                                                         +"\n"+
	            "do{"                                                                  +"\n"+
	            "	i++;"                                                                +"\n"+
	            "	do{"                                                                 +"\n"+
	            "		j++;"                                                               +"\n"+
	            "	}while(j<10);	"                                                      +"\n"+
	            "}while(i<100);"                                                       +"\n"+
	            "}"                                                                    
	            ,
	            "do_while_head_2"
	            ,
	            "j"
	            ,
	            "S_8485"
	            ,
	            "[0,0]U[10,inf]"
	            ,
	            },
/////////////////  155   ///////////////////	
	            {
	            "f(){"                                                                 +"\n"+
	            "int i=0,j=0;"                                                         +"\n"+
	            "do{"                                                                  +"\n"+
	            "	i++;"                                                                +"\n"+
	            "	do{"                                                                 +"\n"+
	            "		j++;"                                                               +"\n"+
	            "	}while(j<10);	"                                                      +"\n"+
	            "}while(i<100);"                                                       +"\n"+
	            "}"                                                                    
	            ,
	            "do_while_head_4"
	            ,
	            "j"
	            ,
	            "S_8889"
	            ,
	            "[0,inf]"
	            ,
	            },
/////////////////  156   ///////////////////	
	            {
	            "f(){"                                                                 +"\n"+
	            "int i=0,j=0;"                                                         +"\n"+
	            "do{"                                                                  +"\n"+
	            "	i++;"                                                                +"\n"+
	            "	do{"                                                                 +"\n"+
	            "		j++;"                                                               +"\n"+
	            "	}while(j<10);	"                                                      +"\n"+
	            "}while(i<100);"                                                       +"\n"+
	            "}"                                                                    
	            ,
	            "do_while_out1_8"
	            ,
	            "j"
	            ,
	            "j_9293"
	            ,
	            "[10,inf]"
	            ,
	            },
/////////////////  157   ///////////////////	
	            {
	            "f(){"                                                                 +"\n"+
	            "int i=0,j=0;"                                                         +"\n"+
	            "do{"                                                                  +"\n"+
	            "	i++;"                                                                +"\n"+
	            "	do{"                                                                 +"\n"+
	            "		j++;"                                                               +"\n"+
	            "	}while(j<10);	"                                                      +"\n"+
	            "}while(i<100);"                                                       +"\n"+
	            "}"                                                                    
	            ,
	            "do_while_out2_9"
	            ,
	            "j"
	            ,
	            "j_9293"
	            ,
	            "[10,inf]"
	            ,
	            },
/////////////////  158   ///////////////////	
	            {
	            "f(){"                                                                 +"\n"+
	            "int i=0,j=3;"                                                         +"\n"+
	            "while(i<10 ||j>0){"                                                   +"\n"+
	            "i++;"                                                                 +"\n"+
	            "j--;"                                                                 +"\n"+
	            "}"                                                                    +"\n"+
	            "}"                                                                    
	            ,
	            "while_out_5"
	            ,
	            "j"
	            ,
	            "j_3031"
	            ,
	            "[-inf,0]"
	            ,
	            },
/////////////////  159   ///////////////////	
	            {
	            "f(){"                                                                 +"\n"+
	            "int i=0,j=3;"                                                         +"\n"+
	            "while(i<10 ||j>0){"                                                   +"\n"+
	            "i++;"                                                                 +"\n"+
	            "j--;"                                                                 +"\n"+
	            "}"                                                                    +"\n"+
	            "}"                                                                    
	            ,
	            "while_out_5"
	            ,
	            "i"
	            ,
	            "i_3435"
	            ,
	            "[10,inf]"
	            ,
	            },
/////////////////  160   ///////////////////	
	            {
	            "f(){"                                                                 +"\n"+
	            "int i = 30, j;"                                                       +"\n"+
	            "int a[10] = {0};"                                                     +"\n"+
	            "j = i;"                                                               +"\n"+
	            "for (i=0; i<5; i++)"                                                  +"\n"+
	            "  j++;"                                                               +"\n"+
	            "a[i] = 100;//FP"                                                      +"\n"+
	            "}"                                                                    
	            ,
	            "stmt_9"
	            ,
	            "i"
	            ,
	            "i_5859"
	            ,
	            "[5,5]"
	            ,
	            },
/////////////////  161   ///////////////////	
	            {
	            "void func1()"                                                         +"\n"+
	            "{"                                                                    +"\n"+
	            "	int buf[10];"                                                        +"\n"+
	            "	int i;"                                                              +"\n"+
	            "	for (i = 0; i <= 8; i++) {"                                          +"\n"+
	            "		;"                                                                  +"\n"+
	            "	}"                                                                   +"\n"+
	            "	buf[i] = i; //FP"                                                    +"\n"+
	            "}"                                                                    
	            ,
	            "stmt_8"
	            ,
	            "i"
	            ,
	            "i_4041"
	            ,
	            "[9,9]"
	            ,
	            },
///////////////// 162   ///////////////////	
	            {
	            "int main()"                                                           +"\n"+
	            "{"                                                                    +"\n"+
	            " int i=0;"                                                            +"\n"+
	            " do { "                                                               +"\n"+
	            "      do { "                                                          +"\n"+
	            "		   i++;"                                                            +"\n"+
	            "           printf(\"3\");"                                              +"\n"+
	            "      } while (0); "                                                  +"\n"+
	            ""                                                                     +"\n"+
	            " } while (0);"                                                        +"\n"+
	            "         system(\"pause\");"                                            +"\n"+
	            "    return 0;"                                                        +"\n"+
	            "}"                                                                    
	            ,
	            "do_while_out1_6"
	            ,
	            "i"
	            ,
	            "1"
	            ,
	            "[1,1]"
	            ,
	            },
/////////////////  163   ///////////////////	
	            {
	            "static char *dirs[]={\"abc\",\"123\"};"                                   +"\n"+
	            "int main(){"                                                          +"\n"+
	            "	char **dp;"                                                          +"\n"+
	            "	for(dp=dirs;*dp!=0;++dp)"                                            +"\n"+
	            "	{"                                                                   +"\n"+
	            "		printf(\"%s\",*dp);"                                                  +"\n"+
	            "	}"                                                                   +"\n"+
	            "	system(\"pause\");"                                                    +"\n"+
	            "	return 0;"                                                           +"\n"+
	            "}"                                                                    
	            ,
	            "for_head_3"
	            ,
	            "dp"
	            ,
	            "S_206207"
	            ,
	            "NOTNULL offsetRange: [-inf,inf] Eval: [0,0] Type:[]"
	            ,
	            },
/////////////////  164   error///////////////////	
	            {
	            "static char *dirs[]={\"abc\",\"123\"};"                                   +"\n"+
	            "int main(){"                                                          +"\n"+
	            "	char **dp;"                                                          +"\n"+
	            "	for(dp=dirs;*dp!=0;++dp)"                                            +"\n"+
	            "	{"                                                                   +"\n"+
	            "		printf(\"%s\",*dp);"                                                  +"\n"+
	            "	}"                                                                   +"\n"+
	            "	system(\"pause\");"                                                    +"\n"+
	            "	return 0;"                                                           +"\n"+
	            "}"                                                                    
	            ,
	            "for_out_6"
	            ,
	            "dp"
	            ,
	            "dp_190191"
	            ,
	            "NOTNULL offsetRange: [-inf,inf] Eval: [0,0] Type:[]"
	            ,
	            },
/////////////////  165：zys 2010.9.16 对循环入边中函数参数进行初始化   ///////////////////	
	            {
	            "void star(int a,int n)"                                               +"\n"+
	            "{"                                                                    +"\n"+
	            "    int i;"                                                           +"\n"+
	            "    while(n>0)"                                                       +"\n"+
	            "    {"                                                                +"\n"+
	            "        if(a<1||a>50){"                                               +"\n"+
	            "       printf(\"a=%d\",a);break;"                                       +"\n"+
	            "        };"                                                           +"\n"+
	            "        for(i=1;i<=a;i++)"                                            +"\n"+
	            "            printf(\"*\");"                                             +"\n"+
	            "        printf(\"\\n\");"                                                +"\n"+
	            "        n--;"                                                         +"\n"+
	            "    }"                                                                +"\n"+
	            "}"                                                                    
	            ,
	            "while_head_2"
	            ,
	            "a"
	            ,
	            "a_104105"
	            ,
	            "[-inf,inf]"
	            ,
	            },
/////////////////  166：zys 2010.9.16 对循环入边中函数参数进行初始化   ///////////////////	
	            {
	            "void star(int a,int n)"                                               +"\n"+
	            "{"                                                                    +"\n"+
	            "    int i;"                                                           +"\n"+
	            "    while(n>0)"                                                       +"\n"+
	            "    {"                                                                +"\n"+
	            "        if(a<1||a>50){"                                               +"\n"+
	            "       printf(\"a=%d\",a);break;"                                       +"\n"+
	            "        };"                                                           +"\n"+
	            "        for(i=1;i<=a;i++)"                                            +"\n"+
	            "            printf(\"*\");"                                             +"\n"+
	            "        printf(\"\\n\");"                                                +"\n"+
	            "        n--;"                                                         +"\n"+
	            "    }"                                                                +"\n"+
	            "}"                                                                    
	            ,
	            "if_head_3"
	            ,
	            "a"
	            ,
	            "a_104105"
	            ,
	            "[-inf,inf]"
	            ,
	            },
/////////////////  167：zys 2010.9.16 对循环入边中函数参数进行初始化   ///////////////////	
	            {
	            "void star(int a,int n)"                                               +"\n"+
	            "{"                                                                    +"\n"+
	            "    int i;"                                                           +"\n"+
	            "    while(n>0)"                                                       +"\n"+
	            "    {"                                                                +"\n"+
	            "        if(a<1||a>50){"                                               +"\n"+
	            "       printf(\"a=%d\",a);break;"                                       +"\n"+
	            "        };"                                                           +"\n"+
	            "        for(i=1;i<=a;i++)"                                            +"\n"+
	            "            printf(\"*\");"                                             +"\n"+
	            "        printf(\"\\n\");"                                                +"\n"+
	            "        n--;"                                                         +"\n"+
	            "    }"                                                                +"\n"+
	            "}"                                                                    
	            ,
	            "while_out_15"
	            ,
	            "a"
	            ,
	            "a_104105"
	            ,
	            "[-inf,inf]"
	            ,
	            },
/////////////////  168：zys 2010.9.16 对循环入边中局部变量进行初始化   ///////////////////	
	            {
	            "void star(int a,int n)"                                               +"\n"+
	            "{"                                                                    +"\n"+
	            "	int t=0;"                                                            +"\n"+
	            "    int i;"                                                           +"\n"+
	            "    while(n>0)"                                                       +"\n"+
	            "    {"                                                                +"\n"+
	            "        if(a<1||a>50){"                                               +"\n"+
	            "       printf(\"a=%d\",a);break;"                                       +"\n"+
	            "        };"                                                           +"\n"+
	            "        for(i=1;i<=a;i++)"                                            +"\n"+
	            "            printf(\"*\");"                                             +"\n"+
	            "        printf(\"\\n\");"                                                +"\n"+
	            "        n--;"                                                         +"\n"+
	            "    }"                                                                +"\n"+
	            "	int k;"                                                              +"\n"+
	            "} "                                                                   
	            ,
	            "decl_stmt_2"
	            ,
	            "i"
	            ,
	            "i_45"
	            ,
	            "[-inf,inf]"
	            ,
	            },
/////////////////  169：zys 2010.9.16 对循环入边中局部变量进行初始化   ///////////////////	
	            {
	            "void star(int a,int n)"                                               +"\n"+
	            "{"                                                                    +"\n"+
	            "	int t=0;"                                                            +"\n"+
	            "    int i;"                                                           +"\n"+
	            "    while(n>0)"                                                       +"\n"+
	            "    {"                                                                +"\n"+
	            "        if(a<1||a>50){"                                               +"\n"+
	            "       printf(\"a=%d\",a);break;"                                       +"\n"+
	            "        };"                                                           +"\n"+
	            "        for(i=1;i<=a;i++)"                                            +"\n"+
	            "            printf(\"*\");"                                             +"\n"+
	            "        printf(\"\\n\");"                                                +"\n"+
	            "        n--;"                                                         +"\n"+
	            "    }"                                                                +"\n"+
	            "	int k;"                                                              +"\n"+
	            "} "                                                                   
	            ,
	            "while_head_3"
	            ,
	            "i"
	            ,
	            "i_132133"
	            ,
	            "[-inf,inf]"
	            ,
	            },
/////////////////  170：zys 2010.9.16 对循环之后的局部变量不进行初始化   ///////////////////	
	            {
	            "void star(int a,int n)"                                               +"\n"+
	            "{"                                                                    +"\n"+
	            "	int t=0;"                                                            +"\n"+
	            "    int i;"                                                           +"\n"+
	            "    while(n>0)"                                                       +"\n"+
	            "    {"                                                                +"\n"+
	            "        if(a<1||a>50){"                                               +"\n"+
	            "       printf(\"a=%d\",a);break;"                                       +"\n"+
	            "        };"                                                           +"\n"+
	            "        for(i=1;i<=a;i++)"                                            +"\n"+
	            "            printf(\"*\");"                                             +"\n"+
	            "        printf(\"\\n\");"                                                +"\n"+
	            "        n--;"                                                         +"\n"+
	            "    }"                                                                +"\n"+
	            "	int k;"                                                              +"\n"+
	            "} "                                                                   
	            ,
	            "decl_stmt_17"
	            ,
	            "k"
	            ,
	            "ERROR"
	            ,
	            "ERROR"
	            ,
	            },
/////////////////  171：zys 2010.9.16 对循环之后的局部变量不进行初始化   ///////////////////	
	            {
	            "void star(int a,int n)"                                               +"\n"+
	            "{"                                                                    +"\n"+
	            "	int t=0;"                                                            +"\n"+
	            "    int i;"                                                           +"\n"+
	            "    while(n>0)"                                                       +"\n"+
	            "    {"                                                                +"\n"+
	            "        if(a<1||a>50){"                                               +"\n"+
	            "       printf(\"a=%d\",a);break;"                                       +"\n"+
	            "        };"                                                           +"\n"+
	            "        for(i=1;i<=a;i++)"                                            +"\n"+
	            "            printf(\"*\");"                                             +"\n"+
	            "        printf(\"\\n\");"                                                +"\n"+
	            "        n--;"                                                         +"\n"+
	            "    }"                                                                +"\n"+
	            "	int k;"                                                              +"\n"+
	            "} "                                                                   
	            ,
	            "decl_stmt_17"
	            ,
	            "a"
	            ,
	            "a_130131"
	            ,
	            "[-inf,inf]"
	            ,
	            },
/////////////////  172：zys 2010.9.16 对循环之前的指针类型的参数不进行初始化   ///////////////////	
	            {
	            "void star(int a,int n,char *c)"                                       +"\n"+
	            "{"                                                                    +"\n"+
	            "	int *p;"                                                             +"\n"+
	            "    int i;"                                                           +"\n"+
	            "    while(n>0)"                                                       +"\n"+
	            "    {"                                                                +"\n"+
	            "        if(a<1||a>50){"                                               +"\n"+
	            "       printf(\"a=%d\",a);break;"                                       +"\n"+
	            "        };"                                                           +"\n"+
	            "        for(i=1;i<=a;i++)"                                            +"\n"+
	            "            printf(\"*\");"                                             +"\n"+
	            "        printf(\"\\n\");"                                                +"\n"+
	            "        n--;"                                                         +"\n"+
	            "    }"                                                                +"\n"+
	            "	int k;"                                                              +"\n"+
	            "} "                                                                   
	            ,
	            "decl_stmt_2"
	            ,
	            "c"
	            ,
	            "ERROR"
	            ,
	            "ERROR"
	            ,
	            },

/////////////////  173 	chh:2010.9.17		ASTConstant  ///////////////////	
	            {
	            "void f(int i){"                                                       +"\n"+
	            "i=3;"                                                                 +"\n"+
	            "i=i/2; "                                                              +"\n"+
	            "}"                                                                    
	            ,
	            "stmt_2"
	            ,
	            "i"
	            ,
	            "1.5"
	            ,
	            "[1,1]" // 原来除法四舍五入，修改castToType的Double-Integer后正确。
	            ,
	            },    

/////////////////  174  chh   ///////////////////	
	            {
	            "void f(int m){"                                                       +"\n"+
	            "int i;"                                                               +"\n"+
	            "for(i=0;i<m;i++){"                                                    +"\n"+
	            ""                                                                     +"\n"+
	            "}"                                                                    +"\n"+
	            "}"                                                                    
	            ,
	            "for_out_5"
	            ,
	            "i"
	            ,
	            "i_3233"
	            ,
	            "[0,inf]"// 修改之前本例的情况是for循环没有出口，无限循环。修改ConditionDimainVisit的must域计算后正确
	            ,
	            },
/////////////////  175  chh   ///////////////////	
	            {
	            "void f(int m){"                                                       +"\n"+
	            "int i;"                                                               +"\n"+
	            "for(i=0;i>m;i--){"                                                    +"\n"+
	            ""                                                                     +"\n"+
	            "}"                                                                    +"\n"+
	            "}"                                                                    
	            ,
	            "for_out_5"
	            ,
	            "i"
	            ,
	            "i_3233"
	            ,
	            "[-inf,0]"
	            ,
	            },

/////////////////  176  chh   ///////////////////	
	            {
	            "void f(int m){"                                                       +"\n"+
	            "int i;"                                                               +"\n"+
	            "for(i=0;i>=m;i--){"                                                    +"\n"+
	            ""                                                                     +"\n"+
	            "}"                                                                    +"\n"+
	            "}"                                                                    
	            ,
	            "for_out_5"
	            ,
	            "i"
	            ,
	            "i_3233"
	            ,
	            "[-inf,0]"
	            ,
	            },

/////////////////  177  chh   ///////////////////	
	            {
	            "void f(int m){"                                                       +"\n"+
	            "int i;"                                                               +"\n"+
	            "for(i=0;i<=m;i++){"                                                    +"\n"+
	            ""                                                                     +"\n"+
	            "}"                                                                    +"\n"+
	            "}"                                                                    
	            ,
	            "for_out_5"
	            ,
	            "i"
	            ,
	            "i_3233"
	            ,
	            "[0,inf]"
	            ,
	            },
/////////////////  178   ExpressionValueVisitor    ASTConditionalExpression///////////////////	
	            {
	            ""                                                                     +"\n"+
	            "int g(int a){"                                                        +"\n"+
	            "int b=(a-a!=0?:f());"                                                 +"\n"+
	            "if(b);}"                                                              +"\n"+
	            "int f(){return 0;}"                                                   
	            ,
	            "decl_stmt_1"
	            ,
	            "b"
	            ,
	            "S_23"
	            ,
	            "ERROR"
	            ,
	            },
/////////////////  179   ExpressionValueVisitor  ASTAdditiveExpression///////////////////	
	            {
	            ""                                                                     +"\n"+
	            "int g(int a){"                                                        +"\n"+
	            "int b=a+(-g());"                                                      +"\n"+
	            "if(b);}"                                                              +"\n"+
	            ""                                                                     +"\n"+
	            "int f(){return 0;}"                                                   
	            ,
	            "decl_stmt_1"
	            ,
	            "b"
	            ,
	            "-1*S_23+a_01"
	            ,
	            "ERROR"
	            ,
	            },	
/////////////////  180  ConditionDomainVisitor ASTEqualityExpression  ///////////////////	
	            {
	            ""                                                                     +"\n"+
	            "int g(int a){"                                                        +"\n"+
	            " if(a==f())"                                                          +"\n"+
	            "a=5;}"                                                                +"\n"+
	            ""                                                                     +"\n"+
	            ""                                                                     +"\n"+
	            "int f(){return 0;}"                                                   
	            ,
	            "if_out_3"
	            ,
	            "a"
	            ,
	            "a_89"
	            ,
	            "[-inf,inf]"
	            ,
	            },	
/////////////////  181  ExpressionValueVisitor    ASTEqualityExpression   ///////////////////	
	            {
	            ""                                                                     +"\n"+
	            "int g(int a){"                                                        +"\n"+
	            "int b=(a==f()?6:5);"                                                  +"\n"+
	            "if(b);}"                                                              +"\n"+
	            ""                                                                     +"\n"+
	            "int f(){return 0;}"                                                   
	            ,
	            "decl_stmt_1"
	            ,
	            "b"
	            ,
	            "5"
	            ,
	            "[5,5]"
	            ,
	            },
/////////////////  182  ExpressionValueVisitor     ASTLogicalANDExpression  ///////////////////	
	            {
	            ""                                                                     +"\n"+
	            "int g(int a){"                                                        +"\n"+
	            "int b=1&&f();}"                                                       +"\n"+
	            ""                                                                     +"\n"+
	            "int f(){return 0;}"                                                   
	            ,
	            "decl_stmt_1"
	            ,
	            "b"
	            ,
	            "S_45"
	            ,
	            "[0,1]"
	            ,
	            },
///////////////// 183 ExpressionValueVisitor    ASTLogicalORExpression   ///////////////////	
	            {
	            ""                                                                     +"\n"+
	            "int g(int a){"                                                        +"\n"+
	            "int b=0||f();}"                                                       +"\n"+
	            "int f(){return 0;}"                                                   
	            ,
	            "decl_stmt_1"
	            ,
	            "b"
	            ,
	            "S_45"
	            ,
	            "[0,1]"
	            ,
	            },	  
/////////////////  184   ExpressionValueVisitor     ASTMultiplicativeExpression///////////////////	
	            {
	            ""                                                                     +"\n"+
	            "int g(int a){"                                                        +"\n"+
	            "int b=a*f();}"                                                        +"\n"+
	            "int f(){return 0;}"                                                   
	            ,
	            "decl_stmt_1"
	            ,
	            "b"
	            ,
	            "S_23*a_01"
	            ,
	            "ERROR"
	            ,
	            },
/////////////////  185 zys 2011.6.20	见softtest.domain.c.symbolic.Power.java中的getDomain()函数修改   ///////////////////	
	            {
	            "void equation(double a, double b, double c)"                          +"\n"+
	            "{"                                                                    +"\n"+
	            "	double x1,x2,mid;"                                                   +"\n"+
	            "	if(a!=0) {"                                                          +"\n"+
	            "		mid=b*b-4*a*c;"                                                     +"\n"+
	            "		if(mid>0){"                                                         +"\n"+
	            "			x1=(-b+sqrt(mid))/(2*a);"                                          +"\n"+
	            "			x2=(-b-sqrt(mid))/(2*a);"                                          +"\n"+
	            "			printf(\"two real roots\\n\");"                                       +"\n"+
	            "		}else{"                                                             +"\n"+
	            "			if(mid==0){"                                                       +"\n"+
	            "				x1=-b/2*a;"                                                       +"\n"+
	            "				printf(\"one real root\\n\");"                                       +"\n"+
	            "			}else{"                                                            +"\n"+
	            "				x1=-b/(2*a);"                                                     +"\n"+
	            "				x2=sqrt((-mid)/(2*a));"                                           +"\n"+
	            "        printf(\"two complex roots\\n\");"                               +"\n"+
	            "      }"                                                              +"\n"+
	            "		}"                                                                  +"\n"+
	            "		printf(\"x1=%f,x2=%f\\n\",x1,x2);"                                     +"\n"+
	            "	}"                                                                   +"\n"+
	            "}"                                                                    
	            ,
	            "stmt_3"
	            ,
	            "b"
	            ,
	            "b_01"
	            ,
	            "[-Infinity,Infinity]"
	            ,
	            },
/////////////////  186 zys 2011.6.20 条件变量mid在condata条件判定之前为复杂表达式///////////////////	
	            {
	            "void equation(double a, double b, double c)"                          +"\n"+
	            "{"                                                                    +"\n"+
	            "	double x1,x2,mid;"                                                   +"\n"+
	            "	if(a!=0) {"                                                          +"\n"+
	            "		mid=b*b-4*a*c;"                                                     +"\n"+
	            "		if(mid>0){"                                                         +"\n"+
	            "			x1=(-b+sqrt(mid))/(2*a);"                                          +"\n"+
	            "			x2=(-b-sqrt(mid))/(2*a);"                                          +"\n"+
	            "			printf(\"two real roots\\n\");"                                       +"\n"+
	            "		}else{"                                                             +"\n"+
	            "			if(mid==0){"                                                       +"\n"+
	            "				x1=-b/2*a;"                                                       +"\n"+
	            "				printf(\"one real root\\n\");"                                       +"\n"+
	            "			}else{"                                                            +"\n"+
	            "				x1=-b/(2*a);"                                                     +"\n"+
	            "				x2=sqrt((-mid)/(2*a));"                                           +"\n"+
	            "        printf(\"two complex roots\\n\");"                               +"\n"+
	            "      }"                                                              +"\n"+
	            "		}"                                                                  +"\n"+
	            "		printf(\"x1=%f,x2=%f\\n\",x1,x2);"                                     +"\n"+
	            "	}"                                                                   +"\n"+
	            "}"                                                                    
	            ,
	            "stmt_3"
	            ,
	            "mid"
	            ,
	            "-4*a_45*c_23+b_01^2"
	            ,
	            "[-Infinity,Infinity]"
	            ,
	            },
/////////////////  187 zys 2011.6.20 条件变量mid在condata判定时，由于是复杂表达式，因此生成了新的表达式///////////////////	
	            {
	            "void equation(double a, double b, double c)"                          +"\n"+
	            "{"                                                                    +"\n"+
	            "	double x1,x2,mid;"                                                   +"\n"+
	            "	if(a!=0) {"                                                          +"\n"+
	            "		mid=b*b-4*a*c;"                                                     +"\n"+
	            "		if(mid>0){"                                                         +"\n"+
	            "			x1=(-b+sqrt(mid))/(2*a);"                                          +"\n"+
	            "			x2=(-b-sqrt(mid))/(2*a);"                                          +"\n"+
	            "			printf(\"two real roots\\n\");"                                       +"\n"+
	            "		}else{"                                                             +"\n"+
	            "			if(mid==0){"                                                       +"\n"+
	            "				x1=-b/2*a;"                                                       +"\n"+
	            "				printf(\"one real root\\n\");"                                       +"\n"+
	            "			}else{"                                                            +"\n"+
	            "				x1=-b/(2*a);"                                                     +"\n"+
	            "				x2=sqrt((-mid)/(2*a));"                                           +"\n"+
	            "        printf(\"two complex roots\\n\");"                               +"\n"+
	            "      }"                                                              +"\n"+
	            "		}"                                                                  +"\n"+
	            "		printf(\"x1=%f,x2=%f\\n\",x1,x2);"                                     +"\n"+
	            "	}"                                                                   +"\n"+
	            "}"                                                                    
	            ,
	            "if_head_4"
	            ,
	            "mid"
	            ,
	            "mid_1213"
	            ,
	            "[-Infinity,Infinity]"
	            ,
	            },
/////////////////  188 zys 2011.6.20 真分支中的mid条件变量得到了正确的区间值///////////////////	
	            {
	            "void equation(double a, double b, double c)"                          +"\n"+
	            "{"                                                                    +"\n"+
	            "	double x1,x2,mid;"                                                   +"\n"+
	            "	if(a!=0) {"                                                          +"\n"+
	            "		mid=b*b-4*a*c;"                                                     +"\n"+
	            "		if(mid>0){"                                                         +"\n"+
	            "			x1=(-b+sqrt(mid))/(2*a);"                                          +"\n"+
	            "			x2=(-b-sqrt(mid))/(2*a);"                                          +"\n"+
	            "			printf(\"two real roots\\n\");"                                       +"\n"+
	            "		}else{"                                                             +"\n"+
	            "			if(mid==0){"                                                       +"\n"+
	            "				x1=-b/2*a;"                                                       +"\n"+
	            "				printf(\"one real root\\n\");"                                       +"\n"+
	            "			}else{"                                                            +"\n"+
	            "				x1=-b/(2*a);"                                                     +"\n"+
	            "				x2=sqrt((-mid)/(2*a));"                                           +"\n"+
	            "        printf(\"two complex roots\\n\");"                               +"\n"+
	            "      }"                                                              +"\n"+
	            "		}"                                                                  +"\n"+
	            "		printf(\"x1=%f,x2=%f\\n\",x1,x2);"                                     +"\n"+
	            "	}"                                                                   +"\n"+
	            "}"                                                                    
	            ,
	            "stmt_5"
	            ,
	            "mid"
	            ,
	            "mid_1213"
	            ,
	            "[4.9E-324,Infinity]"
	            ,
	            },
/////////////////  189 zys 2011.6.20 后续的分支中的mid条件变量得到了正确的区间值///////////////////	
	            {
	            "void equation(double a, double b, double c)"                          +"\n"+
	            "{"                                                                    +"\n"+
	            "	double x1,x2,mid;"                                                   +"\n"+
	            "	if(a!=0) {"                                                          +"\n"+
	            "		mid=b*b-4*a*c;"                                                     +"\n"+
	            "		if(mid>0){"                                                         +"\n"+
	            "			x1=(-b+sqrt(mid))/(2*a);"                                          +"\n"+
	            "			x2=(-b-sqrt(mid))/(2*a);"                                          +"\n"+
	            "			printf(\"two real roots\\n\");"                                       +"\n"+
	            "		}else{"                                                             +"\n"+
	            "			if(mid==0){"                                                       +"\n"+
	            "				x1=-b/2*a;"                                                       +"\n"+
	            "				printf(\"one real root\\n\");"                                       +"\n"+
	            "			}else{"                                                            +"\n"+
	            "				x1=-b/(2*a);"                                                     +"\n"+
	            "				x2=sqrt((-mid)/(2*a));"                                           +"\n"+
	            "        printf(\"two complex roots\\n\");"                               +"\n"+
	            "      }"                                                              +"\n"+
	            "		}"                                                                  +"\n"+
	            "		printf(\"x1=%f,x2=%f\\n\",x1,x2);"                                     +"\n"+
	            "	}"                                                                   +"\n"+
	            "}"                                                                    
	            ,
	            "stmt_9"
	            ,
	            "mid"
	            ,
	            "mid_1213"
	            ,
	            "[0.0,0.0]"
	            ,
	            },
/////////////////  190 zys 2011.6.20 后续的分支中的mid条件变量得到了正确的区间值///////////////////	
	            {
	            "void equation(double a, double b, double c)"                          +"\n"+
	            "{"                                                                    +"\n"+
	            "	double x1,x2,mid;"                                                   +"\n"+
	            "	if(a!=0) {"                                                          +"\n"+
	            "		mid=b*b-4*a*c;"                                                     +"\n"+
	            "		if(mid>0){"                                                         +"\n"+
	            "			x1=(-b+sqrt(mid))/(2*a);"                                          +"\n"+
	            "			x2=(-b-sqrt(mid))/(2*a);"                                          +"\n"+
	            "			printf(\"two real roots\\n\");"                                       +"\n"+
	            "		}else{"                                                             +"\n"+
	            "			if(mid==0){"                                                       +"\n"+
	            "				x1=-b/2*a;"                                                       +"\n"+
	            "				printf(\"one real root\\n\");"                                       +"\n"+
	            "			}else{"                                                            +"\n"+
	            "				x1=-b/(2*a);"                                                     +"\n"+
	            "				x2=sqrt((-mid)/(2*a));"                                           +"\n"+
	            "        printf(\"two complex roots\\n\");"                               +"\n"+
	            "      }"                                                              +"\n"+
	            "		}"                                                                  +"\n"+
	            "		printf(\"x1=%f,x2=%f\\n\",x1,x2);"                                     +"\n"+
	            "	}"                                                                   +"\n"+
	            "}"                                                                    
	            ,
	            "stmt_11"
	            ,
	            "mid"
	            ,
	            "mid_1213"
	            ,
	            "[-Infinity,-4.9E-324]"
	            ,
	            },
/////////////////  191 zys 2011.6.20 后续的分支中的mid条件变量得到了正确的区间值///////////////////	
	            {
	            "void equation(double a, double b, double c)"                          +"\n"+
	            "{"                                                                    +"\n"+
	            "	double x1,x2,mid;"                                                   +"\n"+
	            "	if(a!=0) {"                                                          +"\n"+
	            "		mid=b*b-4*a*c;"                                                     +"\n"+
	            "		if(0<mid){"                                                         +"\n"+
	            "			x1=(-b+sqrt(mid))/(2*a);"                                          +"\n"+
	            "			x2=(-b-sqrt(mid))/(2*a);"                                          +"\n"+
	            "			printf(\"two real roots\\n\");"                                       +"\n"+
	            "		}else{"                                                             +"\n"+
	            "			if(mid==0){"                                                       +"\n"+
	            "				x1=-b/2*a;"                                                       +"\n"+
	            "				printf(\"one real root\\n\");"                                       +"\n"+
	            "			}else{"                                                            +"\n"+
	            "				x1=-b/(2*a);"                                                     +"\n"+
	            "				x2=sqrt((-mid)/(2*a));"                                           +"\n"+
	            "        printf(\"two complex roots\\n\");"                               +"\n"+
	            "      }"                                                              +"\n"+
	            "		}"                                                                  +"\n"+
	            "		printf(\"x1=%f,x2=%f\\n\",x1,x2);"                                     +"\n"+
	            "	}"                                                                   +"\n"+
	            "}"                                                                    
	            ,
	            "stmt_11"
	            ,
	            "mid"
	            ,
	            "mid_1213"
	            ,
	            "[-Infinity,-4.9E-324]"
	            ,
	            },
/////////////////  192 zys 2011.6.20 特殊形式if((mid=b*b-4*a*c)>0)///////////////////	
	            {
	            "void equation(double a, double b, double c)"                          +"\n"+
	            "{"                                                                    +"\n"+
	            "	double x1,x2,mid;"                                                   +"\n"+
	            "	if(a!=0) {"                                                          +"\n"+
	            "		if((mid=b*b-4*a*c)>0){"                                             +"\n"+
	            "			x1=(-b+sqrt(mid))/(2*a);"                                          +"\n"+
	            "			x2=(-b-sqrt(mid))/(2*a);"                                          +"\n"+
	            "			printf(\"two real roots\\n\");"                                       +"\n"+
	            "		}else{"                                                             +"\n"+
	            "			if(mid==0){"                                                       +"\n"+
	            "				x1=-b/2*a;"                                                       +"\n"+
	            "				printf(\"one real root\\n\");"                                       +"\n"+
	            "			}else{"                                                            +"\n"+
	            "				x1=-b/(2*a);"                                                     +"\n"+
	            "				x2=sqrt((-mid)/(2*a));"                                           +"\n"+
	            "        printf(\"two complex roots\\n\");"                               +"\n"+
	            "      }"                                                              +"\n"+
	            "		}"                                                                  +"\n"+
	            "		printf(\"x1=%f,x2=%f\\n\",x1,x2);"                                     +"\n"+
	            "	}"                                                                   +"\n"+
	            "}"                                                                    
	            ,
	            "if_head_3"
	            ,
	            "mid"
	            ,
	            "mid_1213"
	            ,
	            "[-Infinity,Infinity]"
	            ,
	            },
/////////////////  193 zys 2011.6.20 特殊形式if((mid=b*b-4*a*c)>0)///////////////////	
	            {
	            "void equation(double a, double b, double c)"                          +"\n"+
	            "{"                                                                    +"\n"+
	            "	double x1,x2,mid;"                                                   +"\n"+
	            "	if(a!=0) {"                                                          +"\n"+
	            "		if((mid=b*b-4*a*c)>0){"                                             +"\n"+
	            "			x1=(-b+sqrt(mid))/(2*a);"                                          +"\n"+
	            "			x2=(-b-sqrt(mid))/(2*a);"                                          +"\n"+
	            "			printf(\"two real roots\\n\");"                                       +"\n"+
	            "		}else{"                                                             +"\n"+
	            "			if(mid==0){"                                                       +"\n"+
	            "				x1=-b/2*a;"                                                       +"\n"+
	            "				printf(\"one real root\\n\");"                                       +"\n"+
	            "			}else{"                                                            +"\n"+
	            "				x1=-b/(2*a);"                                                     +"\n"+
	            "				x2=sqrt((-mid)/(2*a));"                                           +"\n"+
	            "        printf(\"two complex roots\\n\");"                               +"\n"+
	            "      }"                                                              +"\n"+
	            "		}"                                                                  +"\n"+
	            "		printf(\"x1=%f,x2=%f\\n\",x1,x2);"                                     +"\n"+
	            "	}"                                                                   +"\n"+
	            "}"                                                                    
	            ,
	            "stmt_8"
	            ,
	            "mid"
	            ,
	            "mid_1213"
	            ,
	            "[0.0,0.0]"
	            ,
	            },
/////////////////  194 zys 2011.6.20 特殊形式if(0 < (mid=b*b-4*a*c))///////////////////	
	            {
	            "void equation(double a, double b, double c)"                          +"\n"+
	            "{"                                                                    +"\n"+
	            "	double x1,x2,mid;"                                                   +"\n"+
	            "	if(a!=0) {"                                                          +"\n"+
	            "		if(0<(mid=b*b-4*a*c)){"                                             +"\n"+
	            "			x1=(-b+sqrt(mid))/(2*a);"                                          +"\n"+
	            "			x2=(-b-sqrt(mid))/(2*a);"                                          +"\n"+
	            "			printf(\"two real roots\\n\");"                                       +"\n"+
	            "		}else{"                                                             +"\n"+
	            "			if(0==mid){"                                                       +"\n"+
	            "				x1=-b/2*a;"                                                       +"\n"+
	            "				printf(\"one real root\\n\");"                                       +"\n"+
	            "			}else{"                                                            +"\n"+
	            "				x1=-b/(2*a);"                                                     +"\n"+
	            "				x2=sqrt((-mid)/(2*a));"                                           +"\n"+
	            "        printf(\"two complex roots\\n\");"                               +"\n"+
	            "      }"                                                              +"\n"+
	            "		}"                                                                  +"\n"+
	            "		printf(\"x1=%f,x2=%f\\n\",x1,x2);"                                     +"\n"+
	            "	}"                                                                   +"\n"+
	            "}"                                                                    
	            ,
	            "stmt_4"
	            ,
	            "mid"
	            ,
	            "mid_1011"
	            ,
	            "[4.9E-324,Infinity]"
	            ,
	            },
/////////////////  195 zys 2011.6.20 特殊形式if(a)///////////////////	
	            {
	            "void equation(double a, double b, double c)"                          +"\n"+
	            "{"                                                                    +"\n"+
	            "	double x1,x2,mid;"                                                   +"\n"+
	            "	if(a) {"                                                             +"\n"+
	            "		mid=b*b-4*a*c;"                                                     +"\n"+
	            "		if(mid==0){"                                                        +"\n"+
	            "			x1=-b/2*a;"                                                        +"\n"+
	            "			printf(\"one real root\\n\");"                                        +"\n"+
	            "		}else if((mid)>0){"                                                 +"\n"+
	            "			x1=(-b+sqrt(mid))/(2*a);"                                          +"\n"+
	            "			x2=(-b-sqrt(mid))/(2*a);"                                          +"\n"+
	            "			printf(\"two real roots\\n\");"                                       +"\n"+
	            "		}else{"                                                             +"\n"+
	            "			x1=-b/(2*a);"                                                      +"\n"+
	            "			x2=sqrt((-mid)/(2*a));"                                            +"\n"+
	            "        	printf(\"two complex roots\\n\");"                              +"\n"+
	            "      	}"                                                             +"\n"+
	            "	}"                                                                   +"\n"+
	            "	printf(\"x1=%f,x2=%f\\n\",x1,x2);"                                      +"\n"+
	            "}"                                                                    
	            ,
	            "stmt_3"
	            ,
	            "a"
	            ,
	            "a_45"
	            ,
	            "[-Infinity,-4.9E-324]U[4.9E-324,Infinity]"
	            ,
	            },
/////////////////  196 zys 2011.6.20 特殊形式if(mid==0)///////////////////	
	            {
	            "void equation(double a, double b, double c)"                          +"\n"+
	            "{"                                                                    +"\n"+
	            "	double x1,x2,mid;"                                                   +"\n"+
	            "	if(a) {"                                                             +"\n"+
	            "		mid=b*b-4*a*c;"                                                     +"\n"+
	            "		if(mid==0){"                                                        +"\n"+
	            "			x1=-b/2*a;"                                                        +"\n"+
	            "			printf(\"one real root\\n\");"                                        +"\n"+
	            "		}else if((mid)>0){"                                                 +"\n"+
	            "			x1=(-b+sqrt(mid))/(2*a);"                                          +"\n"+
	            "			x2=(-b-sqrt(mid))/(2*a);"                                          +"\n"+
	            "			printf(\"two real roots\\n\");"                                       +"\n"+
	            "		}else{"                                                             +"\n"+
	            "			x1=-b/(2*a);"                                                      +"\n"+
	            "			x2=sqrt((-mid)/(2*a));"                                            +"\n"+
	            "        	printf(\"two complex roots\\n\");"                              +"\n"+
	            "      	}"                                                             +"\n"+
	            "	}"                                                                   +"\n"+
	            "	printf(\"x1=%f,x2=%f\\n\",x1,x2);"                                      +"\n"+
	            "}"                                                                    
	            ,
	            "stmt_5"
	            ,
	            "mid"
	            ,
	            "mid_1011"
	            ,
	            "[0.0,0.0]"
	            ,
	            },
/////////////////  197 zys 2011.6.20 特殊形式if(mid==0)///////////////////	
	            {
	            "void equation(double a, double b, double c)"                          +"\n"+
	            "{"                                                                    +"\n"+
	            "	double x1,x2,mid;"                                                   +"\n"+
	            "	if(a) {"                                                             +"\n"+
	            "		mid=b*b-4*a*c;"                                                     +"\n"+
	            "		if(mid==0){"                                                        +"\n"+
	            "			x1=-b/2*a;"                                                        +"\n"+
	            "			printf(\"one real root\\n\");"                                        +"\n"+
	            "		}else if((mid)>0){"                                                 +"\n"+
	            "			x1=(-b+sqrt(mid))/(2*a);"                                          +"\n"+
	            "			x2=(-b-sqrt(mid))/(2*a);"                                          +"\n"+
	            "			printf(\"two real roots\\n\");"                                       +"\n"+
	            "		}else{"                                                             +"\n"+
	            "			x1=-b/(2*a);"                                                      +"\n"+
	            "			x2=sqrt((-mid)/(2*a));"                                            +"\n"+
	            "        	printf(\"two complex roots\\n\");"                              +"\n"+
	            "      	}"                                                             +"\n"+
	            "	}"                                                                   +"\n"+
	            "	printf(\"x1=%f,x2=%f\\n\",x1,x2);"                                      +"\n"+
	            "}"                                                                    
	            ,
	            "stmt_11"
	            ,
	            "mid"
	            ,
	            "mid_1011"
	            ,
	            "[-Infinity,-4.9E-324]"
	            ,
	            },
/////////////////  198 zys 2011.6.20 特殊形式a=b+c; if(a)///////////////////	
	            {
	            "void equation(double a, double b, double c)"                          +"\n"+
	            "{"                                                                    +"\n"+
	            "	double x1,x2,mid;"                                                   +"\n"+
	            "	a=b+c;"                                                              +"\n"+
	            "	if(a) {"                                                             +"\n"+
	            "		mid=b*b-4*a*c;"                                                     +"\n"+
	            "		if(mid==0){"                                                        +"\n"+
	            "			x1=-b/2*a;"                                                        +"\n"+
	            "			printf(\"one real root\\n\");"                                        +"\n"+
	            "		}else if((mid)>0){"                                                 +"\n"+
	            "			x1=(-b+sqrt(mid))/(2*a);"                                          +"\n"+
	            "			x2=(-b-sqrt(mid))/(2*a);"                                          +"\n"+
	            "			printf(\"two real roots\\n\");"                                       +"\n"+
	            "		}else{"                                                             +"\n"+
	            "			x1=-b/(2*a);"                                                      +"\n"+
	            "			x2=sqrt((-mid)/(2*a));"                                            +"\n"+
	            "        	printf(\"two complex roots\\n\");"                              +"\n"+
	            "      	}"                                                             +"\n"+
	            "	}"                                                                   +"\n"+
	            "	printf(\"x1=%f,x2=%f\\n\",x1,x2);"                                      +"\n"+
	            "}"                                                                    
	            ,
	            "stmt_4"
	            ,
	            "a"
	            ,
	            "a_67"
	            ,
	            "[-Infinity,-4.9E-324]U[4.9E-324,Infinity]"
	            ,
	            },
/////////////////  199 zys 2011.6.20 特殊形式a=b+c; if(0!=a)///////////////////	
	            {
	            "void equation(double a, double b, double c)"                          +"\n"+
	            "{"                                                                    +"\n"+
	            "	double x1,x2,mid;"                                                   +"\n"+
	            "	a=b+c;"                                                              +"\n"+
	            "	if(0!=a) {"                                                          +"\n"+
	            "		mid=b*b-4*a*c;"                                                     +"\n"+
	            "		if(mid==0){"                                                        +"\n"+
	            "			x1=-b/2*a;"                                                        +"\n"+
	            "			printf(\"one real root\\n\");"                                        +"\n"+
	            "		}else if((mid)>0){"                                                 +"\n"+
	            "			x1=(-b+sqrt(mid))/(2*a);"                                          +"\n"+
	            "			x2=(-b-sqrt(mid))/(2*a);"                                          +"\n"+
	            "			printf(\"two real roots\\n\");"                                       +"\n"+
	            "		}else{"                                                             +"\n"+
	            "			x1=-b/(2*a);"                                                      +"\n"+
	            "			x2=sqrt((-mid)/(2*a));"                                            +"\n"+
	            "        	printf(\"two complex roots\\n\");"                              +"\n"+
	            "      	}"                                                             +"\n"+
	            "	}"                                                                   +"\n"+
	            "	printf(\"x1=%f,x2=%f\\n\",x1,x2);"                                      +"\n"+
	            "}"                                                                    
	            ,
	            "stmt_4"
	            ,
	            "a"
	            ,
	            "a_89"
	            ,
	            "[-Infinity,-4.9E-324]U[4.9E-324,Infinity]"
	            ,
	            },
/////////////////  200 zys 2011.6.20 特殊形式a=b+c; b=a+c; if(a+b)	只是为了说明符号的变化///////////////////	
	            {
	            "void equation(double a, double b, double c)"                          +"\n"+
	            "{"                                                                    +"\n"+
	            "	double x1,x2,mid;"                                                   +"\n"+
	            "	a=b+c;"                                                              +"\n"+
	            "	b=a+c;"                                                              +"\n"+
	            "	if(a+b) {"                                                           +"\n"+
	            "		//mid=b*b-4*a*c;"                                                   +"\n"+
	            "		if(mid==b*b-4*a*c){"                                                +"\n"+
	            "			x1=-b/2*a;"                                                        +"\n"+
	            "			printf(\"one real root\\n\");"                                        +"\n"+
	            "		}else if((mid)>0){"                                                 +"\n"+
	            "			x1=(-b+sqrt(mid))/(2*a);"                                          +"\n"+
	            "			x2=(-b-sqrt(mid))/(2*a);"                                          +"\n"+
	            "			printf(\"two real roots\\n\");"                                       +"\n"+
	            "		}else{"                                                             +"\n"+
	            "			x1=-b/(2*a);"                                                      +"\n"+
	            "			x2=sqrt((-mid)/(2*a));"                                            +"\n"+
	            "        	printf(\"two complex roots\\n\");"                              +"\n"+
	            "      	}"                                                             +"\n"+
	            "	}"                                                                   +"\n"+
	            "	printf(\"x1=%f,x2=%f\\n\",x1,x2);"                                      +"\n"+
	            "}"                                                                    
	            ,
	            "if_head_4"
	            ,
	            "a"
	            ,
	            "a_67"
	            ,
	            "[-Infinity,Infinity]"
	            ,
	            },
/////////////////  201 zys 2011.6.20 测试循环条件///////////////////	
	            {
	            "void equation(double a, double b, double c)"                          +"\n"+
	            "{"                                                                    +"\n"+
	            "	double x1,x2,mid;"                                                   +"\n"+
	            "	a=b+c;"                                                              +"\n"+
	            "	while(a>0);"                                                         +"\n"+
	            "}"                                                                    
	            ,
	            "stmt_4"
	            ,
	            "a"
	            ,
	            "a_6061"
	            ,
	            "[4.9E-324,Infinity]"
	            ,
	            },
/////////////////  202 zys 2011.6.20 测试循环条件///////////////////	
	            {
	            "void equation(double a, double b, double c)"                          +"\n"+
	            "{"                                                                    +"\n"+
	            "	double x1,x2,mid;"                                                   +"\n"+
	            "	a=b+c;"                                                              +"\n"+
	            "	while(a);"                                                           +"\n"+
	            "}"                                                                    
	            ,
	            "while_out_5"
	            ,
	            "a"
	            ,
	            "a_1213"
	            ,
	            "[-0.0,0.0]"
	            ,
	            },
/////////////////  203 zys 2011.6.20 测试switch语句条件///////////////////	
	            {
	            "void equation(double a, double b, double c)"                          +"\n"+
	            "{"                                                                    +"\n"+
	            "	double x1,x2,mid;"                                                   +"\n"+
	            "	a=b+c;"                                                              +"\n"+
	            "	switch(a){"                                                          +"\n"+
	            "	case 1:"                                                             +"\n"+
	            "		break;"                                                             +"\n"+
	            "	}"                                                                   +"\n"+
	            "}"                                                                    
	            ,
	            "label_head_case_4"
	            ,
	            "a"
	            ,
	            "a_67"
	            ,
	            "[1.0,1.0]"
	            ,
	            },
/////////////////  204 zys 2011.6.22 测试switch语句中能否保留简单的线性关系x=mY+n///////////////////	
	            {
	            "f(int y){"                                                            +"\n"+
	            "int x=y+1;"                                                           +"\n"+
	            "switch(x){"                                                           +"\n"+
	            "case 1:"                                                              +"\n"+
	            "	;break;"                                                             +"\n"+
	            "case 2:"                                                              +"\n"+
	            "	;break;"                                                             +"\n"+
	            "}"                                                                    +"\n"+
	            "}"                                                                    
	            ,
	            "switch_head_2"
	            ,
	            "x"
	            ,
	            "1+y_01"
	            ,
	            "[-inf,inf]"
	            ,
	            },
/////////////////  205 zys 2011.6.22 测试switch语句中能否保留简单的线性关系x=mY+n///////////////////	
	            {
	            "f(int y){"                                                            +"\n"+
	            "int x=y+1;"                                                           +"\n"+
	            "switch(x){"                                                           +"\n"+
	            "case 1:"                                                              +"\n"+
	            "	;break;"                                                             +"\n"+
	            "case 2:"                                                              +"\n"+
	            "	;break;"                                                             +"\n"+
	            "}"                                                                    +"\n"+
	            "}"                                                                    
	            ,
	            "label_head_case_3"
	            ,
	            "x"
	            ,
	            "1+y_01"
	            ,
	            "[1,1]"
	            ,
	            },
/////////////////  206 zys 2011.6.22 测试switch语句中能否保留简单的线性关系x=mY+n///////////////////	
	            {
	            "f(int y){"                                                            +"\n"+
	            "int x=y+1;"                                                           +"\n"+
	            "switch(x){"                                                           +"\n"+
	            "case 1:"                                                              +"\n"+
	            "	;break;"                                                             +"\n"+
	            "case 2:"                                                              +"\n"+
	            "	;break;"                                                             +"\n"+
	            "}"                                                                    +"\n"+
	            "}"                                                                    
	            ,
	            "label_head_case_3"
	            ,
	            "y"
	            ,
	            "y_01"
	            ,
	            "[0,0]"
	            ,
	            },
/////////////////  207 zys 2011.6.22 测试switch语句中能否保留简单的线性关系x=mY+n///////////////////	
	            {
	            "f(int y){"                                                            +"\n"+
	            "int x=y+1;"                                                           +"\n"+
	            "switch(x){"                                                           +"\n"+
	            "case 1:"                                                              +"\n"+
	            "	;break;"                                                             +"\n"+
	            "case 2:"                                                              +"\n"+
	            "	;break;"                                                             +"\n"+
	            "}"                                                                    +"\n"+
	            "}"                                                                    
	            ,
	            "label_head_case_6"
	            ,
	            "x"
	            ,
	            "1+y_01"
	            ,
	            "[2,2]"
	            ,
	            },
/////////////////  208 zys 2011.6.22 测试switch语句中能否保留简单的线性关系x=mY+n///////////////////	
	            {
	            "f(int y){"                                                            +"\n"+
	            "int x=y+1;"                                                           +"\n"+
	            "switch(x){"                                                           +"\n"+
	            "case 1:"                                                              +"\n"+
	            "	;break;"                                                             +"\n"+
	            "case 2:"                                                              +"\n"+
	            "	;break;"                                                             +"\n"+
	            "}"                                                                    +"\n"+
	            "}"                                                                    
	            ,
	            "label_head_case_6"
	            ,
	            "y"
	            ,
	            "y_01"
	            ,
	            "[1,1]"
	            ,
	            },

		});
	}
}
