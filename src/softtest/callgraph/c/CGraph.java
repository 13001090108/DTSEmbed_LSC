package softtest.callgraph.c;

import java.io.BufferedWriter;
import java.io.FileWriter;
import java.io.IOException;
import java.util.*;

import softtest.callgraph.c.CEdge;
import softtest.callgraph.c.CVexNode;
import softtest.config.c.Config;
import softtest.fsmanalysis.c.AnalysisElement;
import softtest.interpro.c.Method;
import softtest.symboltable.c.*;
import softtest.symboltable.c.MethodNameDeclaration;
import softtest.tools.c.testcasegenerator.TestCaseGeneratorForCallGraphVisitor;

/** 代表调用关系图的类 */
public class CGraph extends CElement {
	/** 不是实际的计数，用于产生名字 */
	private int nodecount = 0;

	/** 不是实际的计数，用于产生名字 */
	private int edgecount = 0;

	/** 结点集合 */
	public Hashtable<String, CVexNode> nodes = new Hashtable<String, CVexNode>();
	protected AnalysisElement element=null;
	/** 边集合 */
	public Hashtable<String, CEdge> edges = new Hashtable<String, CEdge>();

	/** 缺省参数构造函数 */
	public CGraph() {

	}

	/** 增加一个节点，如果该节点已经存在，则抛出异常 */
	public CVexNode addVex(CVexNode vex) {
		if (nodes.get(vex.name) != null) {
			throw new RuntimeException("The vexnode has already existed.");
		}
		nodes.put(vex.name, vex);
		vex.snumber = nodecount++;
		return vex;
	}

	/** 增加一个指定名称的节点，并设定该节点关联的函数声明，最终的名称将为name+nodecount */
	public CVexNode addVex(String name, MethodNameDeclaration mnd) {
		CVexNode vex = new CVexNode(name + nodecount, mnd);
		return addVex(vex);
	}

	/** 增加一个节点 并设定该节点关联的函数声明 */
	public CVexNode addVex(MethodNameDeclaration mnd) {
		String name = "" + nodecount;
		return addVex(name, mnd);
	}

	/** 增加一个指定尾、头节点的边，并设定名称 */
	public CEdge addEdge(CVexNode tailnode, CVexNode headnode, String name) {
		if (headnode == null || tailnode == null) {
			throw new RuntimeException("An edge's head or tail cannot be null.");
		}
		if (edges.get(name) != null) {
			throw new RuntimeException("The edge has already existed.");
		}
		if (nodes.get(headnode.name) != headnode || nodes.get(tailnode.name) != tailnode) {
			throw new RuntimeException("There is a contradiction.");
		}

		if (headnode.inedges.get(name) != null) {
			throw new RuntimeException("There is a contradiction.");
		}

		if (tailnode.outedges.get(name) != null) {
			throw new RuntimeException("There is a contradiction.");
		}

		CEdge e = new CEdge(name, tailnode, headnode);
		edges.put(name, e);
		e.snumber = edgecount++;

		return e;
	}

	/** 增加一个指定尾、头节点的边，并设定名称 */
	public CEdge addEdge(String tail, String head, String name) {
		CVexNode tailnode = nodes.get(tail);
		CVexNode headnode = nodes.get(head);
		return addEdge(tailnode, headnode, name);
	}

	/** 增加一个指定尾、头节点的边 */
	public CEdge addEdge(String tail, String head) {
		String name = "" + edgecount;
		return addEdge(tail, head, name);
	}

	/** 增加一个指定尾、头节点的边 */
	public CEdge addEdge(CVexNode tailnode, CVexNode headnode) {
		String name = "" + edgecount;
		return addEdge(tailnode, headnode, name);
	}

	/** 增加一个指定尾、头节点的边，并设定名称为name+edgecount */
	public CEdge addEdge(String name, CVexNode tailnode, CVexNode headnode) {
		name = name + edgecount;
		return addEdge(tailnode, headnode, name);
	}

	/** 删除指定的边，如果找不到该边或者该边不是图中的边则抛出异常 */
	public void removeEdge(CEdge e) {
		if (edges.get(e.name) != e || e == null) {
			throw new RuntimeException("Cannot find the edge.");
		}
		if (e.headnode == null || e.tailnode == null) {
			throw new RuntimeException("There is a contradiction.");
		}
		if (e.headnode.inedges.get(e.name) != e || e.tailnode.outedges.get(e.name) != e) {
			throw new RuntimeException("There is a contradiction.");
		}

		e.headnode.inedges.remove(e.name);
		e.tailnode.outedges.remove(e.name);
		edges.remove(e.name);
	}

	/** 删除指定的边 */
	public void removeEdge(String name) {
		CEdge e = edges.get(name);
		removeEdge(e);
	}

	/** 删除指定节点的所有入边 */
	public void removeInedges(CVexNode vex) {
		LinkedList<CEdge> temp = new LinkedList<CEdge>();
		temp.clear();
		for (Enumeration<CEdge> e = vex.inedges.elements(); e.hasMoreElements();) {
			temp.add(e.nextElement());
		}
		ListIterator<CEdge> i = temp.listIterator();
		while (i.hasNext()) {
			CEdge edge = i.next();
			removeEdge(edge);
		}
	}

	/** 删除指定节点的所有出边 */
	public void removeOutedges(CVexNode vex) {
		LinkedList<CEdge> temp = new LinkedList<CEdge>();
		temp.clear();
		for (Enumeration<CEdge> e = vex.outedges.elements(); e.hasMoreElements();) {
			temp.add(e.nextElement());
		}
		ListIterator<CEdge> i = temp.listIterator();
		while (i.hasNext()) {
			CEdge edge = i.next();
			removeEdge(edge);
		}
	}

	/** 删除指定节点及其关联的边 */
	public void removeVex(CVexNode vex) {
		if (nodes.get(vex.name) != vex || vex == null) {
			throw new RuntimeException("Cannot find the vexnode.");
		}
		removeInedges(vex);
		removeOutedges(vex);
		nodes.remove(vex.name);
	}

	/** 删除指定节点的所有入边 */
	public void removeVex(String name) {
		CVexNode vex = nodes.get(name);
		removeVex(vex);
	}

	/** 控制流图访问者的accept方法 */
	@Override
	public void accept(CGraphVisitor visitor, Object data) {
		visitor.visit(this, data);
	}

	/** 获得指定节点的一个没有访问的相邻节点，可能返回null,节点顺序由自然顺序决定 */
	private CVexNode getAdjUnvisitedVertex(CVexNode v) {
		if (v.outedges.size() <= 0) {
			return null;
		}
		List<CVexNode> list = new ArrayList<CVexNode>();
		for (Enumeration<CEdge> e = v.outedges.elements(); e.hasMoreElements();) {
			CEdge edge = e.nextElement();
			if (!edge.headnode.getVisited()) {
				list.add(edge.headnode);
			}
		}
		Collections.sort(list);
		if (!list.isEmpty()) {
			return list.get(0);
		} else {
			return null;
		}
	}

	/** 深度优先遍历，visitor为对节点的访问者，data为数据 */
	public void dfs(CGraphVisitor visitor, Object data) {
		// 找到图入口开始
		CVexNode first = null;
		Stack<CVexNode> stack = new Stack<CVexNode>();
		for (Enumeration e = nodes.elements(); e.hasMoreElements();) {
			CVexNode n = (CVexNode) e.nextElement();
			if (!n.getVisited() && n.inedges.size() == 0) {
				first = n;
				break;
			}
		}
		if (first == null) {
			throw new RuntimeException("控制流图入口错误");
		}
		first.accept(visitor, data);
		first.setVisited(true);
		stack.push(first);
		while (!stack.isEmpty()) {
			CVexNode next = getAdjUnvisitedVertex(stack.peek());
			if (next == null) {
				stack.pop();
			} else {
				next.accept(visitor, data);
				next.setVisited(true);
				stack.push(next);
			}
		}
		// 处理那些图入口到达不了的节点，不掉用访问者
		for (Enumeration<CVexNode> e = nodes.elements(); e.hasMoreElements();) {
			CVexNode n = e.nextElement();
			if (!n.getVisited()) {
				// first.accept(visitor, data);
				first.setVisited(true);
				stack.push(first);
				while (!stack.isEmpty()) {
					CVexNode next = getAdjUnvisitedVertex(stack.peek());
					if (next == null) {
						stack.pop();
					} else {
						// next.accept(visitor, data);
						next.setVisited(true);
						stack.push(next);
					}
				}
			}
		}

		// 将访问标志重新设置回false
		for (Enumeration<CVexNode> e = nodes.elements(); e.hasMoreElements();) {
			CVexNode n = e.nextElement();
			n.setVisited(false);
		}
	}

	/** 节点顺序遍历 */
	public void numberOrderVisit(CGraphVisitor visitor, Object data) {
		List<CVexNode> list = new ArrayList<CVexNode>();
		for (Enumeration<CVexNode> e = nodes.elements(); e.hasMoreElements();) {
			CVexNode vex = e.nextElement();
			list.add(vex);
		}
		Collections.sort(list);

		Iterator<CVexNode> i = list.iterator();
		while (i.hasNext()) {
			i.next().accept(visitor, data);
		}
	}

	/** 清除所有节点的访问标志 */
	public void clearVisited() {
		for (Enumeration<CVexNode> e = nodes.elements(); e.hasMoreElements();) {
			CVexNode n = e.nextElement();
			n.setVisited(false);
		}
	}

	/** 得到所有节点的拓扑排序列表，对于存在环路的情况，选取入度最小的节点，删除入边破坏环路 */
	public List<CVexNode> getTopologicalOrderList() {
		Stack<CVexNode> stack = new Stack<CVexNode>();
		ArrayList<CVexNode> list = new ArrayList<CVexNode>();
		// 初始化入度
		for (Enumeration<CVexNode> e = nodes.elements(); e.hasMoreElements();) {
			CVexNode n = e.nextElement();
			n.indegree = 0;
			for (Enumeration<CEdge> e1 = n.getInedges().elements(); e1.hasMoreElements();) {
				CEdge edge = e1.nextElement();
				if (edge.getTailNode() != n) {
					// 自环不算入度
					n.indegree++;
				}
			}
			if (n.indegree == 0) {
				// 入度为0的节点入栈
				stack.push(n);
			}
		}
		while (list.size() < nodes.size()) {
			while (!stack.empty()) {
				CVexNode n = stack.pop();
				list.add(n);

				for (Enumeration<CEdge> e = n.getOutedges().elements(); e.hasMoreElements();) {
					CEdge edge = e.nextElement();
					CVexNode headnode = edge.getHeadNode();
					// 非自环
					if (headnode != n) {
						// 头节点入度-1
						if (headnode.indegree > 0) {
							headnode.indegree--;
							if (headnode.indegree == 0) {
								// 入度为0则入栈
								stack.push(headnode);
							}
						}
					}
				}
			}

			if (list.size() < nodes.size()) {
				// 存在环路
				CVexNode mindegreenode = null;
				// 选取入度>0，且最小的节点
				for (Enumeration<CVexNode> e = nodes.elements(); e.hasMoreElements();) {
					CVexNode n = e.nextElement();
					if (n.indegree > 0) {
						if (mindegreenode == null || mindegreenode.indegree > n.indegree) {
							mindegreenode = n;
						}
					}
				}
				// 破坏环路
				mindegreenode.indegree = 0;
				stack.push(mindegreenode);
			}
		}
		return list;
	}
	public List<CVexNode> getTopologicalOrderList(AnalysisElement element) {
		// 最后处理类的析构函数，如果没有的话，自动添加合成析构函数
		this.element=element;
		if(!Config.SKIP_METHODANALYSIS){
			if(Config.MethodAnalysisInterMethodVisitor){
				dumpfunctioncall(nodes);
			}
		}
	
		Stack<CVexNode> stack = new Stack<CVexNode>();
		ArrayList<CVexNode> list = new ArrayList<CVexNode>();
		// 初始化入度
		for (Enumeration<CVexNode> e = nodes.elements(); e.hasMoreElements();) {
			CVexNode n = e.nextElement();
			n.indegree = 0;
			for (Enumeration<CEdge> e1 = n.getInedges().elements(); e1.hasMoreElements();) {
				CEdge edge = e1.nextElement();
				if (edge.getTailNode() != n) {
					// 自环不算入度
					n.indegree++;
				}
			}
			if (n.indegree == 0) {
				// 入度为0的节点入栈
				stack.push(n);
			}
		}
		while (list.size() < nodes.size()) {
			while (!stack.empty()) {
				CVexNode n = stack.pop();
				list.add(n);

				for (Enumeration<CEdge> e = n.getOutedges().elements(); e.hasMoreElements();) {
					CEdge edge = e.nextElement();
					CVexNode headnode = edge.getHeadNode();
					// 非自环
					if (headnode != n) {
						// 头节点入度-1
						if (headnode.indegree > 0) {
							headnode.indegree--;
							if (headnode.indegree == 0) {
								// 入度为0则入栈
								stack.push(headnode);
							}
						}
					}
				}
			}

			if (list.size() < nodes.size()) {
				// 存在环路
				CVexNode mindegreenode = null;
				// 选取入度>0，且最小的节点
				for (Enumeration<CVexNode> e = nodes.elements(); e.hasMoreElements();) {
					CVexNode n = e.nextElement();
					if (n.indegree > 0) {
						if (mindegreenode == null || mindegreenode.indegree > n.indegree) {
							mindegreenode = n;
						}
					}
				}
				// 破坏环路
				mindegreenode.indegree = 0;
				stack.push(mindegreenode);
			}
		}
		return list;
	}
	
	/**
	 *@author liuli	2010.4.9
	 **/
	private void appendTab(StringBuffer tb, int times){
		for(int i=0;i<TestCaseGeneratorForCallGraphVisitor.TAB_SIZE*times;i++){
			tb.append(" ");
		}
	}
	/**
	 * @author Liuli，为调用图CallGraphVisitor生成测试用例
	 *2010-4-9
	 */
	public String printGraphForTestCaseGeneratorForCG(){
		StringBuffer sb = new StringBuffer();
		
		sb.append("Graph {\"");
		appendTab(sb,14);
		sb.append("+\"\\n\"+\n");
		for (Enumeration<CVexNode> e = nodes.elements(); e.hasMoreElements();) {
			CVexNode n = e.nextElement();
			appendTab(sb,4);
			sb.append("\"  "+n.name+"\"");
			appendTab(sb,10);
			sb.append("+\"\\n\"+\n");
		}
		
		for (Enumeration<CEdge> e = edges.elements(); e.hasMoreElements();) {
			CEdge edge = e.nextElement();
			appendTab(sb,4);
			sb.append("\"  "+edge.tailnode.name + " -> " + edge.headnode.name+"\"");
			appendTab(sb,10);
			sb.append("+\"\\n\"+\n");
		}
		
		appendTab(sb,3);
		sb.append("\"}");

		return sb.toString();	
	}
	/**
	 * @author Liuli，打印调用图
	 *2010-4-9
	 */
	@Override
	public String toString() {
		StringBuffer sb = new StringBuffer();

		sb.append("Graph {\n");
		for (Enumeration<CVexNode> e = nodes.elements(); e.hasMoreElements();) {
			CVexNode n = e.nextElement();
			sb.append("  "+n.name+"\n");
		}

		for (Enumeration<CEdge> e = edges.elements(); e.hasMoreElements();) {
			CEdge edge = e.nextElement();
			sb.append("  "+edge.tailnode.name + " -> " + edge.headnode.name+"\n");
		}
				
		sb.append("}");

		return sb.toString();
	}
	private  void dumpfunctioncall(Hashtable<String, CVexNode> nodes) {
		try {
			
			String filepaths[]=element.getFileName().split("\\\\");
			String filepath=filepaths[filepaths.length-1];
			String str = Config.TRACEPATH + "\\" + filepath +".txt";
			FileWriter out = new FileWriter(str);
			BufferedWriter bf = new BufferedWriter(out);
			bf.write("开始输出"+filepath+"文件内函数的信息"+"\r\n");
			bf.write("1：文件内待分析函数的总数为"+nodes.size()+"\r\n");
			bf.write("2: 接下来输出文件内函数被调用关系"+"\r\n");
			for (Enumeration<CVexNode> e = nodes.elements(); e.hasMoreElements();) {
				CVexNode n = e.nextElement();
				for (Enumeration<CEdge> e1 = n.getInedges().elements(); e1.hasMoreElements();) {
					CEdge edge = e1.nextElement();
					String headfunctionnameresult[]=getEdgeheadfunctionName(edge);
					String tailfunctionnameresult[]=getEdgetailfunctionName(edge);
					bf.write(headfunctionnameresult[0]+"(),"+"( "+"line "+headfunctionnameresult[1]+", "+headfunctionnameresult[2]+")"+"called by →→→→"+tailfunctionnameresult[0]+"(),"+"( "+"line "+tailfunctionnameresult[1]+", "+tailfunctionnameresult[2]+")"+"\r\n"+"\r\n");
					bf.flush();
				}
			}
			Stack<CVexNode> stack = new Stack<CVexNode>();
			ArrayList<CVexNode> list = new ArrayList<CVexNode>();
			// 初始化入度
			for (Enumeration<CVexNode> e = nodes.elements(); e.hasMoreElements();) {
				CVexNode n = e.nextElement();
				n.indegree = 0;
				for (Enumeration<CEdge> e1 = n.getInedges().elements(); e1.hasMoreElements();) {
					CEdge edge = e1.nextElement();
					if (edge.getTailNode() != n) {
						// 自环不算入度
						n.indegree++;
					}
				}
				if (n.indegree == 0) {
					// 入度为0的节点入栈
					stack.push(n);
				}
			}
			while (list.size() < nodes.size()) {
				while (!stack.empty()) {
					CVexNode n = stack.pop();
					list.add(n);

					for (Enumeration<CEdge> e = n.getOutedges().elements(); e.hasMoreElements();) {
						CEdge edge = e.nextElement();
						CVexNode headnode = edge.getHeadNode();
						// 非自环
						if (headnode != n) {
							// 头节点入度-1
							if (headnode.indegree > 0) {
								headnode.indegree--;
								if (headnode.indegree == 0) {
									// 入度为0则入栈
									stack.push(headnode);
								}
							}
						}
					}
				}

				if (list.size() < nodes.size()) {
					// 存在环路
					CVexNode mindegreenode = null;
					// 选取入度>0，且最小的节点
					for (Enumeration<CVexNode> e = nodes.elements(); e.hasMoreElements();) {
						CVexNode n = e.nextElement();
						if (n.indegree > 0) {
							if (mindegreenode == null || mindegreenode.indegree > n.indegree) {
								mindegreenode = n;
							}
						}
					}
					// 破坏环路
					mindegreenode.indegree = 0;
					stack.push(mindegreenode);
				}
			}
			bf.write("3: 根据函数调用关系图得到的函数分析次序为"+"\r\n");
			for(int i=0;i<list.size();i++){
				String functionnameresult[]=getCexNodename(list.get(i));
				bf.write("第"+(i+1)+"个分析的函数为"+functionnameresult[0]+"(),"+"( "+"line "+functionnameresult[1]+", "+functionnameresult[2]+")"+"\r\n");
			}
			bf.close();
			out.close();

		} catch (IOException e) {
			e.printStackTrace();
		}
	}
	private String[] getEdgeheadfunctionName(CEdge edge){
		String Headfunctions[]=edge.getHeadNode().toString().split("CallVexNode:");
		String Headfunction=Headfunctions[Headfunctions.length-1];
		String splitfunctions1[]=Headfunction.split(" in line ");
		String splitresulttemp=splitfunctions1[0];
		String splittemp[]=splitresulttemp.split("\\(");
		String splitresult1=splittemp[0];
		String splitfunction2=splitfunctions1[1];
		String splitfunctions2[]=splitfunction2.split(" in file ");
		String splitresult2=splitfunctions2[0];
		String splitfunction3=splitfunctions2[1];
		String splitfunctions3[]=splitfunction3.split(" :");
		String splitresult3=splitfunctions3[0];
		String splitresult[]={splitresult1,splitresult2,splitresult3};
		return splitresult;
	}
	private String[] getEdgetailfunctionName(CEdge edge){
		String Headfunctions[]=edge.getTailNode().toString().split("CallVexNode:");
		String Headfunction=Headfunctions[Headfunctions.length-1];
		String splitfunctions1[]=Headfunction.split(" in line ");
		String splitresulttemp=splitfunctions1[0];
		String splittemp[]=splitresulttemp.split("\\(");
		String splitresult1=splittemp[0];
		String splitfunction2=splitfunctions1[1];
		String splitfunctions2[]=splitfunction2.split(" in file ");
		String splitresult2=splitfunctions2[0];
		String splitfunction3=splitfunctions2[1];
		String splitfunctions3[]=splitfunction3.split(" :");
		String splitresult3=splitfunctions3[0];
		String splitresult[]={splitresult1,splitresult2,splitresult3};
		return splitresult;
	}
	private String[] getCexNodename(CVexNode node){
		String functions[]=node.toString().split("CallVexNode:");
		String function=functions[functions.length-1];
		String splitfunctions1[]=function.split(" in line ");
		String splitresulttemp=splitfunctions1[0];
		String splittemp[]=splitresulttemp.split("\\(");
		String splitresult1=splittemp[0];
		String splitfunction2=splitfunctions1[1];
		String splitfunctions2[]=splitfunction2.split(" in file ");
		String splitresult2=splitfunctions2[0];
		String splitfunction3=splitfunctions2[1];
		String splitfunctions3[]=splitfunction3.split(" :");
		String splitresult3=splitfunctions3[0];
		String splitresult[]={splitresult1,splitresult2,splitresult3};
		return splitresult;
	}
}