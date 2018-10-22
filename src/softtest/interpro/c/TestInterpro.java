package softtest.interpro.c;

import java.io.File;
import java.io.FileInputStream;
import java.util.ArrayList;
import java.util.List;

import softtest.ast.c.ASTTranslationUnit;
import softtest.ast.c.CCharStream;
import softtest.ast.c.CParser;
import softtest.config.c.Config;
import softtest.fsmanalysis.c.AnalysisElement;
import softtest.fsmanalysis.c.CAnalysis;
import softtest.interpro.c.InterContext;
import softtest.interpro.c.InterCallGraph;
import softtest.interpro.c.InterMethodVisitor;
import softtest.pretreatment.PlatformType;
import softtest.pretreatment.Pretreatment;
import softtest.symboltable.c.OccurrenceAndExpressionTypeFinder;
import softtest.symboltable.c.ScopeAndDeclarationFinder;
import softtest.tools.c.testcasegenerator.TestCaseGeneratorForCallGraphVisitor;

public class TestInterpro {
	private List<AnalysisElement> elements= new ArrayList<AnalysisElement>();;
	//private String analysisDir="testcase/interpro_graph";
	private String analysisDir="testcase/interpro_graph/funccall";
	private List<String> files=new ArrayList<String>();
	private InterCallGraph interCGraph =InterCallGraph.getInstance();
	
	private Pretreatment pre=new Pretreatment();
	
	public TestInterpro()
	{
		init();
	}
	
	//进行预编译的初始化
	private void init()
	{
		pre.setPlatform(PlatformType.GCC);
		
		File srcFileDir=new File(analysisDir);
		collect(srcFileDir);
	}
	
	//对所有.C源文件依次进行处理：预编译、分析、生成全局函数调用关系图
	private void Process()
	{
		//第一步：对所有.C源文件进行预编译
		PreAnalysis();
		
		//第二步：生成全局函数调用关系图
		Config.TRACE=true;
		List<AnalysisElement> orders = interCGraph.getAnalysisTopoOrder();
		
		// 如果有的文件没有在函数调用图上出现，则直接将它们添加到拓扑列表最后
		if (orders.size() != elements.size()) {
			for (AnalysisElement element : elements) {
				boolean exist = false;
				for (AnalysisElement order : orders) {
					if (order == element) {
						exist = true;
					}
				}
				if (!exist) {
					orders.add(element);
				}
			}
		}
	}
	
	private void PreAnalysis()
	{
		for(String srcFile:files)
		{
			AnalysisElement element=new AnalysisElement(srcFile);
			elements.add(element);
			//预编译之后的.I源文件
			String afterPreprocessFile=null;
			List<String> include = new ArrayList<String>();
			List<String> macro = new ArrayList<String>();
			afterPreprocessFile=pre.pretreat(srcFile, include, macro);
			afterPreprocessFile=CAnalysis.fileReplace(afterPreprocessFile);
			try {
				//产生抽象语法树
				System.out.println("生成抽象语法树...");
				CParser parser=CParser.getParser(new CCharStream(new FileInputStream(afterPreprocessFile)));
				ASTTranslationUnit root=parser.TranslationUnit();
				
				//产生符号表
				System.out.println("生成符号表...");
				ScopeAndDeclarationFinder sc=new ScopeAndDeclarationFinder();
				root.jjtAccept(sc, null);
				OccurrenceAndExpressionTypeFinder o=new OccurrenceAndExpressionTypeFinder();
				root.jjtAccept(o, null);
				
				//生成全局函数调用关系
				System.out.println("生成全局函数调用关系...");
				root.jjtAccept(new InterMethodVisitor(), element);
				
			} catch (Exception e) {
				e.printStackTrace();
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
	//liuli:打印调用图
	private  void dump() {
		List<MethodNode> topo = interCGraph.getMethodTopoOrder();
		StringBuffer sb = new StringBuffer();
		
		appendTab(sb,4);
		sb.append("\"Graph {\"");
		appendTab(sb,14);
		sb.append("+\"\\n\"+\n");
		
		for(MethodNode mtnode : topo) {
			String nodeName = format(mtnode.getMethod().toString());
			appendTab(sb,4);
			sb.append("\""+nodeName+"\"");
			appendTab(sb,10);
			sb.append("+\"\\n\"+\n");
		}
		for(int i = 1; i < topo.size(); i++) {
			MethodNode curNode = topo.get(i);
			int callnum = 1;	//记录调用顺序
			for(MethodNode callNode : curNode.getOrderCalls()) {
				if(callNode.getToponum() < curNode.getToponum()) {
					String caller = format(curNode.getMethod().toString());
					String callee = format(callNode.getMethod().toString());
					
					appendTab(sb,4);
					sb.append("\""+caller + " -> " + callee+"\"");
					appendTab(sb,10);
					sb.append("+\"\\n\"+\n");
					callnum++;
				}
			}
		}
				
		appendTab(sb,3);
		sb.append("\"}\"");
		
		System.out.println(sb);		
	}
	
	private static String format(String nodeName) {
		if(nodeName.startsWith("::"))
			return nodeName.substring(2);
		else
			return nodeName.contains("~")?nodeName.replaceAll("::", "__").replace('~', '_'):nodeName.replaceAll("::", "__");
	}
	private void appendTab(StringBuffer tb, int times){
		for(int i=0;i<TestCaseGeneratorForCallGraphVisitor.TAB_SIZE*times;i++){
			tb.append(" ");
		}
	}

	public static void main(String[] args) {
		TestInterpro test=new TestInterpro();
		test.Process();
		test.dump();
	}

}
