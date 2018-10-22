package softtest.depchain.c;


import java.io.BufferedReader;
import java.io.File;
import java.io.FileInputStream;
import java.io.FileOutputStream;
import java.io.FileWriter;
import java.io.IOException;
import java.io.InputStreamReader;
import java.io.OutputStream;
import java.io.PrintStream;
import java.io.Serializable;
import java.util.ArrayList;
import java.util.Collections;
import java.util.HashMap;

import java.util.HashSet;
import java.util.Hashtable;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Queue;
import java.util.Set;
import java.util.concurrent.ConcurrentHashMap;

import com.alibaba.fastjson.JSON;
import com.alibaba.fastjson.JSONArray;
import com.alibaba.fastjson.JSONObject;

import com.sun.swing.internal.plaf.basic.resources.basic;

import softtest.DefUseAnalysis.c.DUAnalysisVisitor;
import softtest.ast.c.ASTArgumentExpressionList;
import softtest.ast.c.ASTAssignmentExpression;
import softtest.ast.c.ASTExpression;
import softtest.ast.c.ASTFunctionDeclaration;
import softtest.ast.c.ASTFunctionDefinition;
import softtest.ast.c.ASTParameterDeclaration;
import softtest.ast.c.ASTPrimaryExpression;
import softtest.ast.c.ASTSelectionStatement;
import softtest.ast.c.ASTStatement;
import softtest.ast.c.ASTTranslationUnit;
import softtest.ast.c.CCharStream;
import softtest.ast.c.CParser;
import softtest.ast.c.CParserVisitor;
import softtest.ast.c.Node;
import softtest.ast.c.SimpleNode;
import softtest.callgraph.c.CEdge;
import softtest.callgraph.c.CGraph;
import softtest.callgraph.c.CVexNode;
import softtest.cfg.c.ControlFlowData;
import softtest.cfg.c.ControlFlowVisitor;
import softtest.cfg.c.Edge;
import softtest.cfg.c.Graph;
import softtest.cfg.c.GraphVisitor;
import softtest.cfg.c.VexNode;
import softtest.domain.c.analysis.ControlFlowDomainVisitor;
import softtest.fsmanalysis.c.AnalysisElement;
import softtest.interpro.c.InterCallGraph;
import softtest.interpro.c.InterContext;
import softtest.interpro.c.InterMethodVisitor;
import softtest.interpro.c.Method;
import softtest.interpro.c.MethodNode;
import softtest.pretreatment.PlatformType;
import softtest.pretreatment.Pretreatment;
import softtest.rules.gcc.fault.OOB_CheckStateMachine;
import softtest.scvp.c.Position;
import softtest.scvp.c.SCVPString;
import softtest.scvp.c.SCVPVisitor;
import softtest.symboltable.c.AbstractScope;
import softtest.symboltable.c.NameOccurrence;
import softtest.symboltable.c.OccurrenceAndExpressionTypeFinder;
import softtest.symboltable.c.ScopeAndDeclarationFinder;
import softtest.symboltable.c.NameOccurrence.OccurrenceType;


public class DepChainTest implements Serializable{
	/**
	 * 序列化ID
	 */
	private static final long serialVersionUID = 5802149016969017989L;
	private List<AnalysisElement> elements= new ArrayList<AnalysisElement>();;
	private String analysisDir="";
	private List<String> files=new ArrayList<String>();			//用于存储收集到的所有.c文件
	private InterCallGraph interCGraph =InterCallGraph.getInstance();   //得到包含这些函数的文件的依赖关系
	private String[] args;
	private Pretreatment pre=new Pretreatment();
	
	public DepChainTest(String[] args)
	{
		
		
		//add by lsc 2018/9/20
		//此处为分析路径下的文件，args[0]表示分析路径下的所有.c文件，args[1]表示分析指定的.c文件
		this.analysisDir=args[1];
		this.setArgs(args);
		init();
	}
	private HashMap<String, ASTTranslationUnit> astmap = new HashMap<String, ASTTranslationUnit>();
	private HashMap<String, Graph> cfgmap = new HashMap<String, Graph>();
	private HashMap<Graph, String> cfgmap2 = new HashMap<Graph, String>();
	private HashMap<String, CGraph> cgMap = new HashMap<String, CGraph>();
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

	//进行预编译的初始化
	private void init()
	{
		pre.setPlatform(PlatformType.GCC);
		
		File srcFileDir=new File(analysisDir);
		collect(srcFileDir);
	}
	
	
	public static void main(String[] args) throws Exception {
		DepChainTest test=new DepChainTest(args);
		int type = Integer.valueOf(args[5]);
		if(type==2) {
			
			
			
			
			System.out.println(test.analyse2());//输入域分析
			
			
		
			
			
	
			//这行代码在输出中没能得到体现
			System.out.println(test.getCondLineMap());//高亮的条件节点
			System.out.println("调用路径：");
			for(String p : test.pathSet) {//调用路径
				System.out.println(p);
			}
		

			test.listSCVP(args[2]);                    //打印响应函数的scvp信息
			
			
			
		       

		    
		} 
	}
	
	 
	
	/**对所有.C源文件依次进行处理：预编译、分析、生成全局函数调用关系图*/
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
			afterPreprocessFile=pre.pretreat(srcFile, include, macro);//调用各编译器的预处理指令生成中间文件
			
			try {
				String temp=element.getFileName();
				//产生抽象语法树
				System.out.println("生成抽象语法树...");
				System.out.println(afterPreprocessFile);
				CParser parser=CParser.getParser(new CCharStream(new FileInputStream(afterPreprocessFile)));
				ASTTranslationUnit root=parser.TranslationUnit();
				astmap.put(srcFile, root);//把语法树扔内存里，通过文件名检索
				
				//产生符号表
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
				cgMap.put(srcFile, g);
				
				//生成控制流图
				System.out.println("生成控制流图...");
				ControlFlowVisitor cfv = new ControlFlowVisitor(element.getFileName());
				ControlFlowData flow = new ControlFlowData();
				for (CVexNode cvnode : list) {
					SimpleNode node = cvnode.getMethodNameDeclaration().getNode();
					if (node instanceof ASTFunctionDefinition) {
						cfv.visit((ASTFunctionDefinition)node, flow);
						cfgmap.put(node.getImage(), ((ASTFunctionDefinition)node).getGraph());
						cfgmap2.put(((ASTFunctionDefinition)node).getGraph(), node.getImage());
					} 
				}
				
				//生成定义使用链
				System.out.println("生成定义使用链...");
				
				/**add by lsc 2018/9/14此处比较关键的调用了ASTTranslationUnit.java中的
				 * public Object jjtAccept(CParserVisitor visitor, Object data) 方法
				 * DUAnalysisVisitor.java中的visit方法， 之后initDefUse(),再之后AbstractScope.java中的
				 * checkOccurrenceType()其中"进行修正"出现在NameOccurrence中*/
				root.jjtAccept(new DUAnalysisVisitor(), null);
			
		
				
				//计算SCVP
				System.out.println("计算scvp...");
			

				for (CVexNode cvnode : list) {
					SimpleNode node = cvnode.getMethodNameDeclaration().getNode();
					if (node instanceof ASTFunctionDefinition) {
//						System.out.println(cvnode.toString());
						
						node.jjtAccept(new SCVPVisitor(), null);
					
					} 
				}
				System.out.println("OK.");
				
			} catch (Exception e) {
				e.printStackTrace();
			}
			
		}
	}
	
	
	
	//全局变量map2中存储有每个函数中相关溯源点的行号
	private Map<String, Set<Integer>> map2 = new HashMap<>();
	public Map<String, Set<Integer>> analyse2(){
		

		process();
		// 获取要求变量的NameOccurrence
		NameOccurrence occ = locate(args[1],args[2],args[3],Integer.valueOf(args[4]));
		
		//add test by lsc 2018/9/16
//	    System.out.println("lsc");
//	    System.out.println(occ.getOccurrenceType());
//	    System.out.println(occ.toString());
		
	    
	    
		generate2(occ);
		
	
		//add test by lsc 2018/9/27, 可以获取全部的变量信息
		System.out.println(vis.toString());
		
		
		//modifyResult();
		return map2;
	}

	
	
	public HashSet<String> pathSet = new HashSet<String>();

	/**
	 * 
	 * @param occ
	 */
	private void generate2(NameOccurrence occ) {
		DepGraphNode g = new DepGraphNode(occ);
		
		//清空路径容器
		pathSet.clear();
		
		//清空Set容器，用来准备存储变量信息(NameOccurrence),此set容器是用来遍历用
		vis.clear();
		
		//此dfs仅仅是模拟递归，无输出值，作用是为下面提供g,即全局变量，进而输出函数间的调用关系，和完成map2记录
		dfs(occ, g, 0, 1);
		
		
        /*
         * test point add by lsc 2018/9/20 ,全局变量map2中存储有每个函数中相关溯源点的行号
		for(Map.Entry<String, Set<Integer>> entry : map2.entrySet()) {
			String fun = entry.getKey();
			Set<Integer> set = entry.getValue();
			for(int i : set) {
				System.out.print(i+" ");
			}
			System.out.println();
		}
		*/
		
		//下面几行代码的意义即是输出函数间的调用关系
		String funcname = cfgmap2.get(occ.getLocation().getCurrentVexNode().getGraph());
		pathSet.add(funcname);
		dfsGetAllPath(g,funcname);
		
	}
	


	
	/**
	 * 打印出函数内各个节点的scvp的信息
	 * @param funcName
	 * 为了可序列化该方法能被调用，将其private修饰去除 2018/10/17 add by lsc
	 */
	void listSCVP(String funcName) {
		Graph cfg = cfgmap.get(funcName);
		JSONObject jsonObject = new JSONObject(true);
		
		GraphVisitor visitor = new DepChainUtil.listSCVPVisitor();
		cfg.numberOrderVisit(visitor, jsonObject);
		
		//modify by lsc 2018/9/18这句话要好好分析
		System.out.println(JSON.toJSONString(jsonObject, true));
	}
	
	private Map<String, Set<String>> vexMap = new HashMap<>();
	private Map<String, Boolean> condMap = new HashMap<>();
	private Map<String, Boolean> condLineMap = new HashMap<>();
	
	private void dfsGetAllPath(DepGraphNode root, String path) {
		if (root.child == null || root.child.size() == 0) {
			pathSet.add(path);
		}
		String curFuncName = cfgmap2.get(root.occ.getLocation().getCurrentVexNode().getGraph());
		for (DepGraphNode child : root.child) {
			String childFuncname = cfgmap2.get(child.occ.getLocation().getCurrentVexNode().getGraph());
			
			if (!curFuncName.equals(childFuncname))
				
				dfsGetAllPath(child, path + "<-" + childFuncname);
			else
				dfsGetAllPath(child, path);
		}
	}




	private HashSet<NameOccurrence> vis = new HashSet<>();
	/**
	 * 
	 * @param NameOccurrence occ
	 * @param DepGraphNode g
	 * @param int cond
	 * @param int depth
	 */
	
	private void dfs(NameOccurrence occ, DepGraphNode g, int cond, int depth) {
		if (vis.contains(occ)) {
			return;
		}
	
		
		vis.add(occ);
		//count++;
		if (g==null)
			return;
		//if (depth > 5) return;

		String func = ((ASTFunctionDefinition)occ.getLocation().getFirstParentOfType(ASTFunctionDefinition.class)).getImage();
		
		int line = Integer.valueOf(occ.toString().split(":")[1]);
		
		
		//add by lsc2018/9/16
		VexNode vexNode = occ.getLocation().getCurrentVexNode();      //获取当前变量所在的节点
		
		//add by lsc 2018/10/9
//		System.out.println("10/9测试："+vexNode.toString());
		
		boolean flag = vexNode.toString().contains("if_head");
		boolean flag2 = vexNode.toString().contains("if_out");
//		System.out.println(flag2);
		
		

		
			if (!map2.containsKey(func)  ) {
				map2.put(func, new HashSet<Integer>());
			}
			map2.get(func).add(line);

		
		
		
		
		//add by lsc 2018/9/16
		if (cond == 1) {

			
			condLineMap.put(func +"_"+ occ.toString().split(":")[1], true);
//			System.out.println(func +"_"+ occ.toString().split(":")[1]+"lsc");
			//g.setCond(true);
		} else {
			
		}
		if(occ==null)
			return;
		
	
		if(occ.getOccurrenceType()==OccurrenceType.USE) {
			
			//获得可以到达本使用出现的所有定义出现
			List<NameOccurrence> def = occ.getUse_def();
		
			for(NameOccurrence o : def) {
//				if(o.getImage().equals(occ.getImage()))
//					continue;
				DepGraphNode g2 = g.addChild(o);
				//List<DepGraphNode> ifNodes = new ArrayList<DepChain.DepGraphNode>();

				VexNode from = o.getLocation().getCurrentVexNode();
				VexNode to = occ.getLocation().getCurrentVexNode();
				List<VexNode> pList = Graph.findAPath(from, to);
				
				//add by lsc 2018/9/25处理条件分支
				//为什么pList.size-1 ?
				for(int i=0;i<pList.size();i++) {
					VexNode a = pList.get(i);
					
					//add test by lsc,接下来可以以此为突破口处理if-else分支
//					System.out.println("test2018/10/9:"+a.toString() +a.getOccurrences().toString());
					
					
					if(a.toString().contains("if_head")) {
						for(NameOccurrence o1:a.getOccurrences()){
							DepGraphNode g3 = g.addChild(o1);
							dfs(o1, g3, 1, depth+1);
						}
					}
				}
				
				dfs(o,g2, cond, depth+1);
			}
		
			if (def == null || def.size() == 0) {
				//无定义点，尝试找全局
				Graph cfg = occ.getLocation().getCurrentVexNode().getGraph();
				String funcname = cfgmap2.get(cfg);
				InterCallGraph callGraph = InterCallGraph.getInstance();
				MethodNode curMNode = null;
				for(MethodNode mn : callGraph.getINTERMETHOD()) {
					Method m = mn.getMethod();
					if (m.getName().equals(funcname)) {
						curMNode = mn;
						break;
					}
				}
				if (curMNode != null){
					Map<Position, ArrayList<SCVPString>> callerInfo = curMNode.getMethod().getCallerInfo();
					if (callerInfo == null || callerInfo.size() == 0) {
						List<Method> callers = new ArrayList<>();//curMNode的调用者
						for(MethodNode mn : callGraph.getINTERMETHOD()) {
							for (MethodNode mn2 : mn.getCalls()) {
								if (mn2 == curMNode) {
									callers.add(mn.getMethod());
								}
							}
						}
						
						for (Method caller : callers) {
							Map<String, List<SCVPString>> ext = caller.getExternalEffects();
							for (String occstr : ext.keySet()) {
								SCVPString value = ext.get(occstr).get(0);//假设只有1个
								String occName = occ.toString().split(":")[0];
								String occName1 = occstr.split(":")[0];
								if (occName.equals(occName1)) {
									String fileName = value.getPosition().getfileName();
									String funcName = value.getPosition().getFunctionName();
									String symbolName = occName1;
									int line2 = Integer.valueOf( occstr.split(":")[1]);
									NameOccurrence next = locate(fileName, funcName, symbolName, line2);
									if (next != null) {
										DepGraphNode g4 = g.addChild(next);
										dfs(next, g4, cond, depth+1);
									}
								}							
							}
						}
					} else {
						for (List<SCVPString> val : callerInfo.values()) {
							SCVPString scvp = val.get(0);
							for (String nextocc : scvp.getOccs()) {
								String fileName = scvp.getPosition().getfileName();
								String funcName = scvp.getPosition().getFunctionName();
								String symbolName = nextocc.split(":")[0];
								int line2 = Integer.valueOf( nextocc.split(":")[1]);
								NameOccurrence next = locate(fileName, funcName, symbolName, line2);
								if (next != null) {
									DepGraphNode g5 = g.addChild(next);
									dfs(next, g5, cond, depth+1);
								}
							}
						}
					}
				}

			}
		} else 	if(occ.getOccurrenceType()==OccurrenceType.DEF_AFTER_USE) {     //使用后定义 i++ ,i+=5等
			//regenerateDU(occ, occ.getLocation().getCurrentVexNode());
			List<NameOccurrence> def = occ.getDef_use();
			for(NameOccurrence o : def) {
				DepGraphNode g2 = g.addChild(o);

				VexNode from = o.getLocation().getCurrentVexNode();
				VexNode to = occ.getLocation().getCurrentVexNode();
				List<VexNode> pList = Graph.findAPath(from, to);
				for(int i=0;i<pList.size();i++) {
					VexNode a = pList.get(i);
					if(a.toString().contains("if_head")) {
						for(NameOccurrence o1:a.getOccurrences()){
							DepGraphNode g3 = g.addChild(o1);
							dfs(o1, g3, 1, depth+1);
						}
					}
				}
				
				dfs(o,g2, cond, depth+1);
			}
		}
		else if(occ.getOccurrenceType() == OccurrenceType.DEF) {
			SCVPString scvp = occ.getSCVP();
			List<String> vlist = scvp.getOccs();
			
			//add test by lsc 2018/10/9
			//System.out.println("test2018/10:"+vlist.toString());
			
			
			for(String v : vlist) {
				Graph cfg = occ.getLocation().getCurrentVexNode().getGraph();
				NameOccurrence o = cfg.getOcctable().get(v);
				if(o.getImage().toString().equals(occ.getImage()))
					continue;
				DepGraphNode g2 = g.addChild(o);

				VexNode from = o.getLocation().getCurrentVexNode();
				VexNode to = occ.getLocation().getCurrentVexNode();
				List<VexNode> pList = Graph.findAPath(from, to);
				for(int i=0;i<pList.size();i++) {
					VexNode a = pList.get(i);
					if(a.toString().contains("if_head")) {
						for(NameOccurrence o1:a.getOccurrences()){
							DepGraphNode g3 = g.addChild(o1);
//							if (cond==0) {
//								cond=1;
//								System.out.println(o + "," + g);
//							}
							dfs(o1, g3,1, depth+1);
						}
					}
				}
				
				dfs(o, g2, cond, depth+1);
			}
			String s = scvp.getStructure();
			
			if(s.contains("Function:")) { //返回值
				int id = s.indexOf("Function");
				s=s.substring(id);
				String[] fs = s.trim().split("Function:");
			
				ASTStatement statement = (ASTStatement) occ.getLocation().getFirstParentOfType(ASTStatement.class);
				List<Node> priList = statement.findChildrenOfType(ASTPrimaryExpression.class);

				for(String f:fs) {
					for(Node n : priList) {
						ASTPrimaryExpression pri = (ASTPrimaryExpression)n;
						if(pri.isMethod() && pri.getImage().equals(f)) {
							//2011.6.24 目前尚未解决的问题：如果是函数指针形式的函数调用，如何获取正确的函数调用？
							if(pri.getMethodDecl()==null)
								continue;
							Method m = pri.getMethodDecl().getMethod();
							SimpleNode entNode = pri.getMethodDecl().getMethodNameDeclaratorNode();
							Graph cfg = null;
							if(entNode instanceof ASTFunctionDefinition)
								cfg = ((ASTFunctionDefinition)entNode).getGraph();
							List<SCVPString> ret = m.getReturnList();
							for(SCVPString scvpString : ret) {
								for(String v : scvpString.getOccs()) {
									if(cfg!=null) {
										NameOccurrence o = cfg.occtable.get(v);
										DepGraphNode g2 = g.addChild(o);
										dfs(o, g2,cond, depth+1);
									}
								}
							}
						}
					}
				}
			}
		}
		else if(occ.getOccurrenceType() == OccurrenceType.ENTRANCE) {
			ASTFunctionDefinition funcdef = (ASTFunctionDefinition) occ.getLocation().getFirstParentOfType(ASTFunctionDefinition.class);
			
			System.out.println("参数个数 :"+funcdef.getParameterCount()+"    行号： "+ occ.toString().split(":")[1]); //获取这一行的参数个数
			
		
			//可以得到lsc:MethodScope(null): (variables:d < int >,n < int >,m < int >)，注意参数顺序逆序
			System.out.println("lsc:"+funcdef.getScope());         
			
			String string = funcdef.getScope().toString().split("variables:")[1];
			string = string.substring(0 ,string.length() - 1);
			System.out.println(string);
			
			String[] strings = string.split(",");
			for(int i = 0 ; i < strings.length ; i ++) {
				strings[i] = strings[i].split(" <")[0];
				System.out.println(strings[i]);
			}
			
			int index = 0 ;
//			boolean isFind = false;       //判断是否找到
			
			System.out.println("当前参数"+occ.toString().split(":")[0]);
			
			for(int i = strings.length - 1 ; i >= 0 ; i --) {
			
				index ++;
				if(occ.toString().split(":")[0].equals(strings[i]))
				{
//					isFind = true;
					break;
				}
		
			}
			
			
			
			System.out.println("得出此变量："+occ.toString().split(":")[0]+"的index为:" + index);
			
//			add test by lsc 2018/9/27
//			System.out.println("当前参数："+occ.toString());
//			System.out.println();
//			
//			VexNode vexNode1 = occ.getLocation().getCurrentVexNode();      //获取当前变量所在的节点
//            
//			
//			int index = 1;
//			
//			for(NameOccurrence nameOccurrence : vis) {
//				System.out.println(nameOccurrence.toString());
				
//				if(Integer.parseInt(occ.toString().split(":")[1]) == Integer.parseInt(nameOccurrence.toString().split(":")[1])){
//					System.out.println("当前行号:"+Integer.parseInt(nameOccurrence.toString().split(":")[1]));
//					System.out.println("当前变量:"+nameOccurrence.toString().split(":")[0]);
//					index ++ ;
//					if(nameOccurrence.toString().split(":")[0].equals(occ.toString().split(":")[0])){
//						System.out.println("index:"+index);
//						break;
//					}
//				}
				
//			}
			
			
			if(funcdef!=null) {
				//用一个HashMap来记录前置摘要，来处理被调用函数参数问题，即参数向上溯源问题
				//我觉得需要添加一个参数的索引index，用于区分到达溯源哪个参数 2018/9/27 lsc
				HashMap<Position, ArrayList<SCVPString>> callerInfo = funcdef.getDecl().getMethod().getCallerInfo();
				for(Position p : callerInfo.keySet()) {
					//add by lsc 2018/9/27
					
//					System.out.println("test:" + index);
					
					System.out.println("test："+p.toString());
					System.out.println("scvpstring :" + callerInfo.get(p).toString());
					
					Graph cfg = cfgmap.get(p.getFunctionName());
					if(cfg!=null) {
						for(SCVPString scvp : callerInfo.get(p)) {
							
							String fileName = p.getFileName();
							String funcName = p.getFunctionName();
							String symbolName = scvp.getVar();
							
					
							
							//add test by lsc
							System.out.println("test:"+symbolName);
							System.out.println("index:"+p.getIndex());
							int line1 = p.getBeginLine(); 
						   
							
							//用于对比参数索引进行精确溯源 add by lsc 2018/10/9
							if(p.getIndex() == index){
								 System.out.println("行号:"+line1 +"  变量： "+symbolName+"  索引："+index);
							NameOccurrence occ2 = locate(fileName, funcName, symbolName, line1);
							System.out.println("occ2内容："+ occ.toString());
							
							if (occ2 == null)
								continue;
							DepGraphNode g3 = g.addChild(occ2);
							dfs(occ2, g3, cond, depth+1);
							
				
							
							
							
							for(String v:scvp.getOccs()) {
								
								System.out.println(scvp.getOccs()+"lsc");
								
								NameOccurrence o = cfg.occtable.get(v);
								DepGraphNode g2 = g.addChild(o);
								dfs(o, g2,cond, depth+1);
							}
							
							}
							
							
						}
					}
				}
			}
		}
	}
	
	/**add by lsc 2018/9/19
	 * 获取要求变量的NameOccurrence
	 * @param fileName
	 * @param funcName
	 * @param symbolName
	 * @param line
	 * @return
	 */
	private NameOccurrence locate(String fileName, String funcName, String symbolName, int line) {
		Graph cfg = cfgmap.get(funcName);
		String occStr = symbolName+":"+line;
		if (cfg == null) return null;
		return cfg.getOcctable().get(occStr);
	}
	
	/**
	 * occ;
		 child;
		private List<VexNode> path;
		 isCond;
	 * @author lsc
	 *
	 */
	@SuppressWarnings("unused")
	private class DepGraphNode {
		private NameOccurrence occ;
		private List<DepGraphNode> child;
		private List<VexNode> path;
		private boolean isCond;
		public DepGraphNode(NameOccurrence occ) {
			this.occ=occ;
			child = new ArrayList<DepGraphNode>();
			path = new ArrayList<VexNode>();
			isCond = false;
			
		}
		
	
		public DepGraphNode addChild(NameOccurrence o) {
			DepGraphNode childNode = new DepGraphNode(o);
			child.add(childNode);
			
			try {
			
				VexNode from = o.getLocation().getCurrentVexNode();
				VexNode to = occ.getLocation().getCurrentVexNode();
				childNode.path = Graph.findAPath(from, to);
				 
				return childNode;
			} catch (Exception e) {
				//e.printStackTrace();
				return null;
			}
		}
		
	

	}

	

	public void setArgs(String[] args) {
		this.args = args;
	}
	public Map<String, Boolean> getCondLineMap() {
		return condLineMap;
	}
	public void setCondLineMap(Map<String, Boolean> condLineMap) {
		this.condLineMap = condLineMap;
	}

}


//用于将输出写入外存文件
class LogWriter {
	// 可以写作配置：true写文件; false输出控制台
	private static boolean fileLog = true;
	private static String logFileName = "C:\\Users\\lsc\\Desktop\\out.txt";

	public static void log(String info) throws IOException {
		OutputStream out = getOutputStream();
		out.write(info.getBytes("utf-8"));
	}

	public static OutputStream getOutputStream() throws IOException {
		if (fileLog) {
			File file = new File(logFileName);
			if (!file.exists())
				file.createNewFile();
			return new FileOutputStream(file);
		} else {
			return System.out;
		}
	}
}