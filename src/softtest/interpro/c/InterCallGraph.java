package softtest.interpro.c;

import java.io.FileWriter;
import java.io.IOException;
import java.io.Serializable;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Stack;
import java.util.concurrent.ConcurrentHashMap;
import org.apache.log4j.Logger;
import softtest.config.c.Config;
import softtest.fsmanalysis.c.AnalysisElement;
/**
 * 根据被调用关系建立的全局函数之间的有向图，
 * 对有向图进行拓扑排序，破环，得到所有调用顺序的拓扑排序，
 * 进而得出包含这些函数的文件之间的依赖关系
 */

public class InterCallGraph implements Serializable {
	/**
	 * 序列化ID add by lsc 2018/10/16
	 */
	private static final long serialVersionUID = -3646773338345645552L;
	static Logger logger = Logger.getLogger(InterCallGraph.class);
	//单例模式
	private static InterCallGraph instance=null;
	/**
	 * 当前分析过程中全局的函数节点信息
	 */
	private HashSet<MethodNode> INTER_METHODS = new LinkedHashSet<MethodNode>();
	
	/**
	 * 全局分析过程中全局的函数调用关系图
	 */
//	private HashMap<Method, MethodNode> INTER_METHODS_TABLE = new LinkedHashMap<Method, MethodNode>();
	private ConcurrentHashMap <Method, MethodNode> INTER_METHODS_TABLE = new ConcurrentHashMap<Method, MethodNode>();
	
	private int COLOR_WHITE = 0;
	private int COLOR_GRAY = 1;
	private int COLOR_BLACK = 2;
	//add by ALUO
	/** 邻接矩阵 **/
	private int adjustMatrix[][];
	
	//add by ALUO
	/** 顶点数组 **/
	private MethodNode methodNodeList[];
	
	//add by ALUO
	/** 用于初始化顶点数组 **/
	private int nodeNum;
	
	//add by ALUO
	public int[][] getAdjustMatrix(){
		return adjustMatrix;
	}
	
	//add by ALUO
	public MethodNode[] getMethodNodeList(){
		return methodNodeList;
	}
	
	//add by ALUO
	public MethodNode displayMethodNode(int i) {  
        return methodNodeList[i];  
    }
	
	//add by ALUO
	public HashSet<MethodNode> getINTERMETHOD(){
		return INTER_METHODS;
	}
	private InterCallGraph()
	{
		
	}
	public static InterCallGraph getInstance()
	{
		if(instance==null)
		{
			instance=new InterCallGraph();
			return instance;
		}
		return instance;
	}
	
	public ConcurrentHashMap<Method, MethodNode> getCallRelationTable(){
		return INTER_METHODS_TABLE;
	}
	
	public MethodNode addMethodNode(MethodNode mtNode) {
		
		// 该节点之前已经生成，更新分析单元信息
		if (INTER_METHODS_TABLE.containsKey(mtNode.getMethod())) {
			MethodNode node = INTER_METHODS_TABLE.get(mtNode.getMethod());
			if(node.getFileName().equals("unknown"))
			{
				node.getMethod().setFileName(mtNode.getFileName());
			}
			node.updateElement(mtNode.getElement());
			return node;
		} else {
			INTER_METHODS.add(mtNode);
			INTER_METHODS_TABLE.put(mtNode.getMethod(), mtNode);
			return mtNode;
		}
	}
	
	public MethodNode findMethodNode(String fileName, Method method) {
		MethodNode mtNode = INTER_METHODS_TABLE.get(method);
		// 该函数对应文件还没有分析到
		if (mtNode == null) {
			mtNode = new MethodNode(fileName, method);
			INTER_METHODS.add(mtNode);
			INTER_METHODS_TABLE.put(mtNode.getMethod(), mtNode);
		}
		return mtNode;
	}
	
	public MethodNode findMethodNode(Method method) {
		if (method == null) {
			return null;
		}
		return INTER_METHODS_TABLE.get(method);
	}
	
	/**
	 * <p>
	 * 对全局上下文中的函数调用关系进行拓扑排序
	 * </p>
	 * 
	 * @return
	 */
	public List<MethodNode> getMethodTopoOrder() {
		//add by suntao 用于给拓扑序中的节点编号
		int i = 0;
		List<MethodNode> topo = new ArrayList<MethodNode>();
		Stack<MethodNode> util = new Stack<MethodNode>();
		for (MethodNode node : INTER_METHODS) {
//			HashSet<MethodNode> callSet = node.getCalls();
			List<MethodNode> callSet = node.getOrderCalls();
			if (callSet.size() == 0) {
				util.push(node);
				continue;
			}
			node.setDegree(callSet.size());
		}
		while (topo.size() < INTER_METHODS.size()) {
			// 优先选取出度为0的节点(逆拓扑排序)
			while (!util.empty()) {
				MethodNode top = util.pop();
				top.setToponum(i++);
				topo.add(top);
				for (MethodNode node : INTER_METHODS) {
//					HashSet<MethodNode> callSet = node.getCalls();
					List<MethodNode> callSet = node.getOrderCalls();
					if (callSet.contains(top)) {
						node.decDegree();
						if (node.getDegree() == 0) {
							util.push(node);
						}
					}
				}
			}
			
			// 打破调用图中的环，选取最小出度的节点破环
			if (topo.size() < INTER_METHODS.size()) {
				MethodNode minDegreeNode = null;
				for (MethodNode node : INTER_METHODS) {
					if(node.getDegree() > 0) {			//modified by suntao
						if(minDegreeNode == null || node.getDegree() < minDegreeNode.getDegree()) {
							minDegreeNode = node;
						}
					}
				}
				if(minDegreeNode!=null)
				{
					minDegreeNode.setDegree(0);
					util.push(minDegreeNode);
				}
			}
		}
		return topo;
	}
	
	/**
	 * <p>
	 * 根据函数的全局拓扑顺序，近似得出文件的依赖顺序
	 * </p>
	 * @return
	 */
	public List<AnalysisElement> getAnalysisTopoOrder() {
		if (Config.TRACE) 
		{
			for (MethodNode node : INTER_METHODS) {
				HashSet<MethodNode> callSet = node.getCalls();
				System.err.println(node.getMethod() + " " + node.getFileName());
				for (MethodNode node2 : callSet) {
					System.err.println("    => " + node2.getMethod() +  " in " + node2.getFileName());
				}
			}
		}
		HashMap<AnalysisElement, LinkedHashSet<AnalysisElement>> fdg = 
			new LinkedHashMap<AnalysisElement, LinkedHashSet<AnalysisElement>>();
		// 临时集合，存放所有出现的element，用于排序
		// 根据函数调用初步判定分析单元依赖
		for (MethodNode node : INTER_METHODS) {
			AnalysisElement element = node.getElement();
			if (element == null || element.getFileName().matches(InterContext.INCFILE_POSTFIX)) {
				continue;
			}
			
			LinkedHashSet<AnalysisElement> set;
			if (fdg.containsKey(element)) {
				set = fdg.get(element);
			} else {
				set = new LinkedHashSet<AnalysisElement>();
			}
			HashSet<MethodNode> callSet = node.getCalls();
			for (MethodNode call : callSet) {
				if (call.getElement() == null 
						||call.getElement().equals(element) || call.getElement().getFileName().matches(InterContext.INCFILE_POSTFIX)) {
					continue;
				}
				set.add(call.getElement());
			}
			fdg.put(element, set);
		}
		dumpICG();
		dumpFDG(fdg, false);
		List<AnalysisElement> topo = new ArrayList<AnalysisElement>();
		Stack<AnalysisElement> util = new Stack<AnalysisElement>();
		// 对分析单元进行拓扑排序
		for (AnalysisElement element : fdg.keySet()) {
			HashSet<AnalysisElement> callSet = fdg.get(element);
			if (callSet.size() == 0) {
				util.push(element);
				continue;
			}
			for (AnalysisElement call : callSet) {
				call.incInDegree();
			}
			element.setOutDegree(callSet.size());
		}
		int size = fdg.size();
		while (topo.size() < size) {
			// 优先选取出度为0的节点
			while (!util.empty()) {
				AnalysisElement top = util.pop();
				topo.add(top);
				for (AnalysisElement element : fdg.keySet()) {
					HashSet<AnalysisElement> callSet = fdg.get(element);
					if (callSet.contains(top)) {
						element.decOutDegree();
						callSet.remove(top);
						if (element.getOutDegree() == 0) {
							util.push(element);
						}
					}
				}
			}
			
			//删除出度为0的节点
			HashSet<AnalysisElement> temp = new LinkedHashSet<AnalysisElement>();
			for (AnalysisElement element : fdg.keySet()) {
				element.setColor(COLOR_WHITE);
				if (element.getOutDegree() == 0 || fdg.get(element).size() == 0) {
					temp.add(element);
				}
			}
			for (AnalysisElement element : temp) {
				fdg.remove(element);
			}
			
			// 在有向图中寻找一个环，并移出这个环
			if (topo.size() < size) {
				dumpFDG(fdg, true);
				HashSet<AnalysisElement> loops = findLoop(fdg);
				if (loops.size() != 0) {
					AnalysisElement minDegreeElt = null;
					if (Config.TRACE) {
						System.err.println("Loop [");
					}
					for (AnalysisElement element : loops) {
						if (Config.TRACE) {
							System.err.print(element + ", ");
						}
						if (minDegreeElt == null || 
								(element.getOutDegree() > 0 && element.getOutDegree() < minDegreeElt.getOutDegree())) {
							minDegreeElt = element;
						}
					}
					if (Config.TRACE) {
						System.err.println(" ]");
					}
					minDegreeElt.setOutDegree(0);
					util.push(minDegreeElt);
				}else{
					System.err.println("Find loop error!");
					//throw new RuntimeException("文件分析次序生成时调用环分析出错！");
				}
			}
		}
		return topo;
	}
	
	private HashSet<AnalysisElement> findLoop(HashMap<AnalysisElement, LinkedHashSet<AnalysisElement>> fdg) {
		HashSet<AnalysisElement> loop = new LinkedHashSet<AnalysisElement>();
//		HashSet<AnalysisElement> util = new LinkedHashSet<AnalysisElement>();
//		// 删除出度为0的节点
//		for (AnalysisElement element : fdg.keySet()) {
//			element.setColor(COLOR_WHITE);
//			if (element.getOutDegree() == 0 || fdg.get(element).size() == 0) {
//				util.add(element);
//			}
//		}
//		for (AnalysisElement element : util) {
//			fdg.remove(element);
//		}
		// 寻找入度为0的节点，FDG的连通分量可能不为一,如果没有的话，剩下的所有分析单元自身构成一个环
		for (AnalysisElement element : fdg.keySet()) {
			if (element.getInDegree() == 0) {
				AnalysisElement begin = dfs(fdg, element);
				// 从入度为0的节点深度遍历图，查找环
				if (begin != null) {
					// 找到环
					AnalysisElement end = begin;
					int pre = 0;
					do {
						HashSet<AnalysisElement> callSet = fdg.get(end);
						for (AnalysisElement call : callSet) {
							if (call.getColor() == COLOR_GRAY) {
								end = call;
								loop.add(end);
								break;
							}
						}
						pre++;
						if (loop.size() < pre) {
							break;
						}
					} while (end != begin);
					return loop;
				}
			}
		}
		
		// 所有剩余节点均在环中
		loop.addAll(fdg.keySet());
		return loop;
	}
	
	private AnalysisElement dfs(HashMap<AnalysisElement, LinkedHashSet<AnalysisElement>> fdg, AnalysisElement element) {
		element.setColor(COLOR_GRAY);
		HashSet<AnalysisElement> callSet = fdg.get(element);
		for (AnalysisElement call : callSet) {
			if (call.getColor() == COLOR_WHITE) {
				return dfs(fdg, call);
			} else if (call.getColor() == COLOR_GRAY) {
				return call;
			}
			//zys:这条语句多余了吧？
			call.setColor(COLOR_BLACK);
		}
		return null;
	}
	
	private void dumpFDG(HashMap<AnalysisElement, LinkedHashSet<AnalysisElement>> fdg, boolean loop) {
		if(!Config.SKIP_METHODANALYSIS|| Config.TRACE || Config.TRACE_FCG){
			if (Config.GlobalFileCallRelation || Config.TRACE || Config.TRACE_FCG) 
			{
				String str = "GlobalFileCallRelation";
				if (loop) {
					str += "_loop";
				}
				String dot = "temp/" + str + ".dot";
				String pic = "temp/" + str + ".jpg";
				FileWriter out = null;
				try {
					int edge = 0;
					out = new FileWriter(dot);
					
					if(!Config.SKIP_METHODANALYSIS){
						if(Config.GlobalFileCallRelation){
							logger.info("【全局文件依赖】节点关系(.dot)temp/GlobalFileCallRelation.dot");
							logger.info("digraph G {\n");
						}
					}
					
					out.write("digraph G {\n");
					for (AnalysisElement element : fdg.keySet()) {
						if (loop && fdg.get(element).size() == 0) {
							continue;
						}
						String fileName = element.getFileName();
						fileName = fileName.substring(fileName.lastIndexOf("\\") + 1, fileName.lastIndexOf("."));
						
						if(!Config.SKIP_METHODANALYSIS){
							if(Config.GlobalFileCallRelation){
								logger.info(fileName + "[label=\"" +fileName +"\"];\n");
							}
						}
						
						out.write(fileName + "[label=\"" +fileName +"\"];\n");
					}
					HashSet<String> edges = new LinkedHashSet<String>();
					for (AnalysisElement element : fdg.keySet()) {
						if (loop && fdg.get(element).size() == 0) {
							continue;
						}
						HashSet<AnalysisElement> callSet = fdg.get(element);
						String fileName = element.getFileName();
						fileName = fileName.substring(fileName.lastIndexOf("\\") + 1, fileName.lastIndexOf("."));
						for (AnalysisElement element2 : callSet) {
							if (element2 == null) {
								continue;
							}
							String temp = element2.getFileName();
							temp = temp.substring(temp.lastIndexOf("\\") + 1, temp.lastIndexOf("."));
							if (!edges.contains(fileName+temp)) {
								
								if(!Config.SKIP_METHODANALYSIS){
									if(Config.GlobalFileCallRelation){
										logger.info(fileName + " -> " + temp + "[label=\"" + (edge++) +"\"];\n");
									}
								}
								
								out.write(fileName + " -> " + temp + "[label=\"" + (edge++) +"\"];\n");
								edges.add(fileName+temp);
							}
						}
					}
					
					if(!Config.SKIP_METHODANALYSIS){
						if(Config.GlobalFileCallRelation){
							logger.info(" }");
						}
					}
					
					out.write(" }");
					Runtime rt = Runtime.getRuntime();
					String execStr = "dot -Tjpg -o " + pic + " " + dot;
					
					if(!Config.SKIP_METHODANALYSIS){
						if(Config.GlobalFileCallRelation){
							logger.info("【全局文件依赖】关系图打印到了："+pic);
						}
					}
					
					System.out.println("全局文件依赖关系图打印到了："+pic);
					rt.exec(execStr);
				} catch (IOException e) {
					e.printStackTrace();
					logger.error("请安装程序Graphvix后再运行程序");
					logger.error(e);
				}
				//added finally by liuyan 2015.6.3
				finally{
					if( out != null ){
						try {
							out.close();
						} catch (IOException e) {
							// TODO Auto-generated catch block
							e.printStackTrace();
						}
					}
				}
			}
		}
	}
	
	/**
	 *@author suntao，输出全局函数调用图
	 **/
	private void dumpICG() {
		if(!Config.SKIP_METHODANALYSIS){
			if(Config.GlobalFunctionCall) {
				List<MethodNode> topo = getMethodTopoOrder();
				//dqh
				String dot = "temp/OverAllMethodCallGraph.dot";
				String pic = "temp/OverAllMethodCallGraph.jpg";
				FileWriter out = null;
				try {
					out = new FileWriter(dot);
					//added by liuyan 2015/10/29
					if(!Config.SKIP_METHODANALYSIS){
						if(Config.GlobalFunctionCall){
							logger.info("【全局函数调用】节点关系(.dot)temp/OverAllMethodCallGraph.dot");
//							logger.info("！！注意：如果将开关TRACE开关置为true，该部分在"
//									+ "temp/InterproMethodCallGraph.dot，"
//									+ "与temp/InterproMethodCallGraph.jpg对应");
							logger.info("digraph G {\n");
						}
					}
					out.write("digraph G {\n");
					for(MethodNode mtnode : topo) {
						String nodeName = format(mtnode.getMethod().toString());
						
						if(!Config.SKIP_METHODANALYSIS){
							if(Config.GlobalFunctionCall){
								logger.info(nodeName + "[label=\"" + nodeName + "\"];\n");
							}
						}
						
						out.write(nodeName + "[label=\"" + nodeName + "\"];\n");
					}
					//拓扑排序后第一个结点不会调用其它结点，所以从第二个结点开始
					for(int i = 1; i < topo.size(); i++) {
						MethodNode curNode = topo.get(i);
						int callnum = 1;	//记录调用顺序
						for(MethodNode callNode : curNode.getOrderCalls()) {
							if(callNode.getToponum() < curNode.getToponum()) {
								String caller = format(curNode.getMethod().toString());
								String callee = format(callNode.getMethod().toString());
								
								if(!Config.SKIP_METHODANALYSIS){
									if(Config.GlobalFunctionCall){
										logger.info(caller + " -> " + callee + "[label=\"" + callnum + "\"];\n");
									}
								}
								
								out.write(caller + " -> " + callee + "[label=\"" + callnum + "\"];\n");
								callnum++;
							}
						}
					}
					
					if(!Config.SKIP_METHODANALYSIS){
						if(Config.GlobalFunctionCall){
							logger.info("}");
						}
					}
					
					out.write("}");
					out.close();
					
					if(!Config.SKIP_METHODANALYSIS){
						if(Config.GlobalFunctionCall){
							logger.info("【全局函数调用】关系图打印到了："+pic);
						}
					}
					
					System.out.println("全局函数调用关系图打印到了："+pic);
					String cmd = "dot -Tjpg -o " + pic + " " + dot;
					Runtime.getRuntime().exec(cmd);
				} catch (IOException e) {
					e.printStackTrace();
					logger.error("请安装程序Graphvix后再运行程序");
					logger.error(e);
				}
				//added finally by liuyan 2015.6.3
				finally{
					if( out != null ){
						try {
							out.close();
						} catch (IOException e) {
							// TODO Auto-generated catch block
							e.printStackTrace();
						}
					}
				}
			}
		}
		}
	
	private static String format(String nodeName) {
		if(nodeName.startsWith("::"))
			return nodeName.substring(2);
		else
			return nodeName.contains("~")?nodeName.replaceAll("::", "__").replace('~', '_'):nodeName.replaceAll("::", "__");
	}
	
	public void clear() {
		INTER_METHODS.clear();
		INTER_METHODS_TABLE.clear();
	}

	//add by ALUO
	/** 获取点到点所有路径前,先生成邻接矩阵等信息 **/
	public void getAllPathPre(){
		adjustMatrix = new int[INTER_METHODS.size()][INTER_METHODS.size()];
		methodNodeList = new MethodNode[INTER_METHODS.size()];
		nodeNum = 0;
		for (MethodNode methodNode : INTER_METHODS) {
			methodNode.matrixNumber = nodeNum;
			methodNodeList[nodeNum] = methodNode;
			nodeNum++;
		}
		for (int i = 0; i < INTER_METHODS.size(); i++) {  
            for (int j = 0; j < INTER_METHODS.size(); j++) {  
                adjustMatrix[i][j] = 0;  
            }   
        } 
		for (MethodNode methodNode : INTER_METHODS) {
			for(MethodNode methodNode2 : methodNode.getCalls()){
				adjustMatrix[methodNode.matrixNumber][methodNode2.matrixNumber] = 1;
			}
		}
	}
	
	//add by ALUO
	/** 获取函数调用图上目标点1到目标点2的所有路径信息 **/
	public ArrayList<ArrayList<MethodNode>> getAllPath(MethodNode node1, MethodNode node2){
		getAllPathPre();
//			CVexNode node1 = null;
//			CVexNode node2 = null;
//			for (CVexNode cVexNode : nodes.values()) {
//				if(cVexNode.name.equals("f0_0_1")){
//					node1 = cVexNode;
//				}
//				if(cVexNode.name.equals("f4_0_4")){
//					node2 = cVexNode;
//				}
//			}
		GetAllICGPath getAllPath = new GetAllICGPath(this, node1, node2);
		getAllPath.getResult();
		
		// 将节点访问标志置为false
		for (MethodNode methodNode : INTER_METHODS) {
			methodNode.visited = false;
		}
//			ArrayList<ArrayList<CVexNode>> allPathList = new ArrayList<ArrayList<CVexNode>>();
//			Stack<CVexNode> stack = new Stack<CVexNode>();
//			Map<CVexNode, Boolean> statesMap = new HashMap<CVexNode, Boolean>();
		for(ArrayList<MethodNode> list : getAllPath.allPathList) {
			for(MethodNode methodNode : list){
				System.out.print(methodNode.getMethod().getName() + "->");
			}
			System.out.println();
		}
		return getAllPath.allPathList;
	}
}
