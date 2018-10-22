package softtest.test.c.callgraph;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.fail;

import java.io.File;
import java.io.FileInputStream;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
import java.util.List;

import org.junit.After;
import org.junit.AfterClass;
import org.junit.Before;
import org.junit.BeforeClass;
import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.runners.Parameterized;
import org.junit.runners.Parameterized.Parameters;

import softtest.ast.c.ASTTranslationUnit;
import softtest.ast.c.CCharStream;
import softtest.ast.c.CParser;
import softtest.fsmanalysis.c.AnalysisElement;
import softtest.interpro.c.InterCallGraph;
import softtest.interpro.c.InterContext;
import softtest.interpro.c.InterMethodVisitor;
import softtest.interpro.c.MethodNode;
import softtest.pretreatment.PlatformType;
import softtest.pretreatment.Pretreatment;
import softtest.symboltable.c.OccurrenceAndExpressionTypeFinder;
import softtest.symboltable.c.ScopeAndDeclarationFinder;

/**
 * @author Liuli
 *2010-4-9
 */
@RunWith(Parameterized.class)
public class TestInterCallGraph
{
	private String source = null;
	private String compiletype=null;
	private String graphStr = null;
	
	private List<AnalysisElement> elements= new ArrayList<AnalysisElement>();;
	private List<String> files=new ArrayList<String>();
	private InterCallGraph interCGraph =InterCallGraph.getInstance();	
	private Pretreatment pre=new Pretreatment();
	
	
	public TestInterCallGraph(String source,String compiletype, String graphStr) {
		this.source = source;
		this.compiletype=compiletype;
		this.graphStr = graphStr;
	}
	
	@BeforeClass
	public static void setUpBase()  {
	}

	@AfterClass
	public static void tearDownBase() {
	}
	
	private void analysis(){			
		String graphString="";	
		List<MethodNode> topo = interCGraph.getMethodTopoOrder();
		try {			
			graphString=toString(topo);
			
		} catch (Exception e) {
			e.printStackTrace();
		} 
		InterCallGraph.getInstance().clear();
		assertEquals(""+CParser.getType()+" type error",graphStr,graphString);		
	}
	
	private String toString(List<MethodNode> topo) {
		StringBuffer sb = new StringBuffer();
		sb.append("Graph {\n");
		
		for(MethodNode mtnode : topo) {
			String nodeName = format(mtnode.getMethod().toString());
			sb.append(nodeName + "\n");
		}
		//拓扑排序后第一个结点不会调用其它结点，所以从第二个结点开始
		for(int i = 1; i < topo.size(); i++) {
			MethodNode curNode = topo.get(i);
			int callnum = 1;	//记录调用顺序
			for(MethodNode callNode : curNode.getOrderCalls()) {
				if(callNode.getToponum() < curNode.getToponum()) {
					String caller = format(curNode.getMethod().toString());
					String callee = format(callNode.getMethod().toString());
					sb.append(caller + " -> " + callee + "\n");
					callnum++;
				}
			}
		}
		sb.append("}");

		return sb.toString();
	}
	
	private static String format(String nodeName) {
		if(nodeName.startsWith("::"))
			return nodeName.substring(2);
		else
			return nodeName.contains("~")?nodeName.replaceAll("::", "__").replace('~', '_'):nodeName.replaceAll("::", "__");
	}

	private void PreAnalysis(){
		for(String srcFile:files)
		{
			AnalysisElement element=new AnalysisElement(srcFile);
			elements.add(element);
			//预编译之后的.I源文件
			String afterPreprocessFile=null;
			List<String> include = new ArrayList<String>();
			List<String> macro = new ArrayList<String>();
			
			afterPreprocessFile=pre.pretreat(srcFile, include, macro);
			
			try {
				//产生抽象语法树			
				CParser parser=CParser.getParser(new CCharStream(new FileInputStream(afterPreprocessFile)));
				ASTTranslationUnit root=parser.TranslationUnit();
				
				//产生符号表				
				root.jjtAccept(new ScopeAndDeclarationFinder(), null);
				root.jjtAccept(new OccurrenceAndExpressionTypeFinder(), null);
				
				//生成全局函数调用关系
				root.jjtAccept(new InterMethodVisitor(), element);
				
			} catch (Exception e) {
				e.printStackTrace();
				fail("parse error");
			}
		}
	}
	
	//收集测试路径下的所有.C源文件
	private void collect(File srcFileDir) {
		if (srcFileDir.isFile() && srcFileDir.getName().matches(InterContext.SRCFILE_POSTFIX)) {
			files.add(srcFileDir.getPath());
		}else if (srcFileDir.isDirectory()) {
			File[] fs = srcFileDir.listFiles();
			for (int i = 0; i < fs.length; i++) {
				collect(fs[i]);
			}
		}
	}

	@Before
	public void init() {
		File srcFileDir=new File(source);
		collect(srcFileDir);
		
		String INCLUDE = null;
		if(compiletype.equals("gcc")){
			pre.setPlatform(PlatformType.GCC);
			INCLUDE = System.getenv("GCCINC");
			if(INCLUDE==null){
				throw new RuntimeException("System environment variable \"GCCINC\" error!");
			}
		}else if(compiletype.equals("keil")){
			pre.setPlatform(PlatformType.KEIL);
			INCLUDE = System.getenv("GCCINC");
			if(INCLUDE==null){
				throw new RuntimeException("System environment variable \"GCCINC\" error!");
			}
		}
		String[] Inctemp = INCLUDE.split(";");
		for(int i = 0;i<Inctemp.length;i++){
			Pretreatment.systemInc.add(Inctemp[i]);
		}
	}

	@After
	public void shutdown() {
		//清除临时文件夹
	}
	
	@Test
	public void test() {
		if(compiletype.equals("gcc")){
			CParser.setType("gcc");
			pre.setPlatform(PlatformType.GCC);
			PreAnalysis();
			analysis();
		}else if(compiletype.equals("keil")){
			CParser.setType("keil");
			pre.setPlatform(PlatformType.KEIL);
			PreAnalysis();
			analysis();
		}else{
			CParser.setType("gcc");
			pre.setPlatform(PlatformType.GCC);
			PreAnalysis();
			analysis();
			
			CParser.setType("keil");
			pre.setPlatform(PlatformType.KEIL);
			PreAnalysis();
			analysis();
		}
	}
	
	@Parameters
	public static Collection<Object[]> testcaseAndResults(){
		return Arrays.asList(new Object[][] {
				  /////////////////  0   ///////////////////	
                {
                "testcase/interpro_graph/samefunc"                                                                                                                    
                ,
                "gcc"
                ,
                "Graph {"                                                        +"\n"+
                "Test2_f_0"                                        +"\n"+
                "Test2_g_0"                                        +"\n"+
                "Test1_f_0"                                        +"\n"+
                "Test1_main_0"                                        +"\n"+
                "Test1_main_0 -> Test1_f_0"                                        +"\n"+
                "Test1_main_0 -> Test2_g_0"                                        +"\n"+
            "}"
                ,
                },			
/////////////////  1   ///////////////////			
                {
                "testcase/interpro_graph/funccall"                                                                                                                    
                ,
                "gcc"
                ,
                "Graph {"                                                        +"\n"+
                "Caller_h_0"                                        +"\n"+
                "Caller_d_0"                                        +"\n"+
                "Caller_c_0"                                        +"\n"+
                "Caller_b_0"                                        +"\n"+
                "Callee_h_0"                                        +"\n"+
                "Callee_g_0"                                        +"\n"+
                "Callee_f_0"                                        +"\n"+
                "Caller_a_0"                                        +"\n"+
                "Caller_main_0"                                        +"\n"+
                "Caller_d_0 -> Caller_h_0"                                        +"\n"+
                "Caller_c_0 -> Caller_d_0"                                        +"\n"+
                "Caller_b_0 -> Caller_c_0"                                        +"\n"+
                "Caller_b_0 -> Caller_d_0"                                        +"\n"+
                "Callee_g_0 -> Callee_h_0"                                        +"\n"+
                "Callee_f_0 -> Callee_g_0"                                        +"\n"+
                "Callee_f_0 -> Callee_h_0"                                        +"\n"+
                "Caller_a_0 -> Caller_b_0"                                        +"\n"+
                "Caller_a_0 -> Caller_b_0"                                        +"\n"+
                "Caller_a_0 -> Caller_c_0"                                        +"\n"+
                "Caller_a_0 -> Caller_d_0"                                        +"\n"+
                "Caller_a_0 -> Callee_f_0"                                        +"\n"+
                "Caller_main_0 -> Caller_a_0"                                        +"\n"+
                "Caller_main_0 -> Callee_f_0"                                        +"\n"+
                "Caller_main_0 -> Callee_g_0"                                        +"\n"+
                "Caller_main_0 -> Caller_d_0"                                        +"\n"+
            "}"
                ,
                },
//////////////  2   ///////////////////			
                {
                "testcase/interpro_graph/userheadfile"                                                                                                                    
                ,
                "gcc"
                ,				
                "Graph {"                                                        +"\n"+
                "My_print_1"                                        +"\n"+
                "Main_main_0"                                        +"\n"+
                "Main_main_0 -> My_print_1"                                        +"\n"+
                "Main_main_0 -> My_print_1"                                        +"\n"+
                "Main_main_0 -> My_print_1"                                        +"\n"+
                "Main_main_0 -> My_print_1"                                        +"\n"+
            "}"
				,
                },
		});
	}
}