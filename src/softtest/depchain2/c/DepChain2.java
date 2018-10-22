package softtest.depchain2.c;

import java.io.File;
import java.io.FileInputStream;
import java.io.FileOutputStream;
import java.io.ObjectOutputStream;
import java.io.OutputStream;
import java.util.ArrayList;
import java.util.Collections;
import java.util.List;

import softtest.DefUseAnalysis.c.DUAnalysisVisitor;
import softtest.ast.c.ASTFunctionDefinition;
import softtest.ast.c.ASTTranslationUnit;
import softtest.ast.c.CCharStream;
import softtest.ast.c.CParser;
import softtest.ast.c.SimpleNode;
import softtest.callgraph.c.CGraph;
import softtest.callgraph.c.CVexNode;
import softtest.cfg.c.ControlFlowData;
import softtest.cfg.c.ControlFlowVisitor;
import softtest.cfg.c.Graph;
import softtest.domain.c.analysis.ControlFlowDomainVisitor;
import softtest.fsmanalysis.c.AnalysisElement;
import softtest.interpro.c.InterCallGraph;
import softtest.interpro.c.InterContext;
import softtest.interpro.c.InterMethodVisitor;
import softtest.pretreatment.PlatformType;
import softtest.pretreatment.Pretreatment;
import softtest.scvp.c.SCVPVisitor;
import softtest.symboltable.c.AbstractScope;
import softtest.symboltable.c.OccurrenceAndExpressionTypeFinder;
import softtest.symboltable.c.ScopeAndDeclarationFinder;

public class DepChain2 {
	private List<AnalysisElement> elements= new ArrayList<AnalysisElement>();;
	private String analysisDir="";
	private List<String> files=new ArrayList<String>();
	private InterCallGraph interCGraph =InterCallGraph.getInstance();
	private String[] args;
	private Pretreatment pre=new Pretreatment();
	public DepChain2(String[] args)
	{
		this.analysisDir=args[0];
		this.args=args;
		init();
	}
	private void init()
	{
		pre.setPlatform(PlatformType.GCC);
		
		File srcFileDir=new File(analysisDir);
		collect(srcFileDir);
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
	private void process()
	{
		//第一步：对所有.C源文件进行预编译
		PreAnalysis();
		
		//第二步：生成全局函数调用关系图
		List<AnalysisElement> orders = interCGraph.getAnalysisTopoOrder();
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
			include.add("C:/Program Files (x86)/DTS/DTS/DTSGCC/include");
			List<String> macro = new ArrayList<String>();
			afterPreprocessFile=pre.pretreat(srcFile, include, macro);
	        ObjectOutputStream oos = null;   
	        FileOutputStream fos = null;     
			try {
				String temp=element.getFileName();
				//产生抽象语法树
				System.out.println("生成抽象语法树...");
				CParser parser=CParser.getParser(new CCharStream(new FileInputStream(afterPreprocessFile)));
				ASTTranslationUnit root=parser.TranslationUnit();
				//astmap.put(srcFile, root);//把语法树扔内存里，通过文件名检索

				System.out.println("生成符号表...");
				ScopeAndDeclarationFinder sc=new ScopeAndDeclarationFinder();
				root.jjtAccept(sc, null);
				OccurrenceAndExpressionTypeFinder o=new OccurrenceAndExpressionTypeFinder();
				root.jjtAccept(o, null);
				
				//生成全局函数调用关系
				System.out.println("生成全局函数调用关系...");
				root.jjtAccept(new InterMethodVisitor(), element);
				
				//文件内函数调用关系图
				System.out.println("生成文件内函数调用关系...");
				CGraph g = new CGraph();
				((AbstractScope)(root.getScope())).resolveCallRelation(g);
				List<CVexNode> list = g.getTopologicalOrderList(element);
				Collections.reverse(list);
			//	cgMap.put(srcFile, g);
				
				//生成控制流图
				System.out.println("生成控制流图...");
				ControlFlowVisitor cfv = new ControlFlowVisitor(element.getFileName());
				ControlFlowData flow = new ControlFlowData();
				for (CVexNode cvnode : list) {
					SimpleNode node = cvnode.getMethodNameDeclaration().getNode();
					if (node instanceof ASTFunctionDefinition) {
						cfv.visit((ASTFunctionDefinition)node, flow);
					} 
				}
				
				//生成定义使用链
				System.out.println("生成定义使用链...");
				//root.jjtAccept(new DUAnalysisVisitor(), null);
				
				//区间运算
				System.out.println("区间运算...");
				ControlFlowDomainVisitor cfd = new ControlFlowDomainVisitor();
				for (CVexNode cvnode : list) {
					SimpleNode node = cvnode.getMethodNameDeclaration().getNode();
					if (node instanceof ASTFunctionDefinition) {
						//cfd.visit((ASTFunctionDefinition)node, null);
					} 
				}
				
				//计算SCVP
				System.out.println("计算scvp...");
				//root.jjtAccept(new SCVPVisitor(), null);
				
				//缓存语法树
				System.out.println("缓存语法树...");
				String fileName = srcFile.substring(srcFile.lastIndexOf("\\"));
	            fos = new FileOutputStream(new File("E:/ast/" +fileName+ ".ast"));   
	            oos = new ObjectOutputStream(fos);   
	            oos.writeObject(root);   
	            
	            fos.close();
	            oos.close();
	            
	            //缓存控制流图
	            for (CVexNode cVexNode : list) {
	            	//System.out.println(cVexNode.getMethodDeclaration().getGraph());
	            	Graph cfg = cVexNode.getMethodDeclaration().getGraph();
	        		String funcname = cVexNode.getMethodDeclaration().getImage();
	        		
	        		String fullpath = "E:/ast/cfg/" + fileName + "_" + funcname + ".cfg";
	        		
	        		System.out.println(fullpath);
	        		fos = new FileOutputStream(new File(fullpath));   
	    	        oos = new ObjectOutputStream(fos);   
	    	        oos.writeObject(cfg);
	    	        oos.close();
	    	        fos.close();
	            }
				System.out.println("OK.");
				
			} catch (Exception e) {
				e.printStackTrace();
			}
			
		}
	}
	public static void main(String[] args) throws Exception {
		DepChain2 test=new DepChain2(args);
		test.process();
	}
	

}
