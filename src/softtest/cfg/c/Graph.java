package softtest.cfg.c;

import java.io.FileWriter;
import java.io.IOException;
import java.util.*;

import org.apache.log4j.Logger;

import com.sun.org.apache.xpath.internal.Expression;

import softtest.ast.c.*;
import softtest.config.c.Config;
import softtest.fsmanalysis.c.FSMPathInsensitiveVisitor;
import softtest.interpro.c.MethodNode;
import softtest.symboltable.c.NameOccurrence;
import softtest.tools.c.testcasegenerator.TestCaseGeneratorForControlFlowVisitor;

/** 代表控制流图的类 */
public class Graph extends Element {
	static Logger logger = Logger.getLogger(Graph.class);
	
	private void appendTab(StringBuffer tb, int times){
		for(int i=0;i<TestCaseGeneratorForControlFlowVisitor.TAB_SIZE*times;i++){
			tb.append(" ");
		}
	}
	
	/**
	 * 与定义使用链DUAnalysisVisitor生成的测试用例进行比较
	 * @return
	 */
	public String printForDefUse() {
		StringBuffer sb = new StringBuffer();
		ArrayList<VexNode> listnodes=new ArrayList<VexNode>();
		listnodes.addAll(nodes.values());
		Collections.sort(listnodes);
		sb.append("Graph {\n");
		for(VexNode v:listnodes){
			sb.append("  "+v.getName()+":"+v.getLiveDefs()+"\n");
		}
		
		sb.append("}");

		return sb.toString();
	}
	
	/**
	 * 为定义使用链DUAnalysisVisitor生成测试用例
	 * @return
	 */
	public String printGraphForTestCaseGeneratorForDUAnalysis()
	{
		StringBuffer sb = new StringBuffer();
		ArrayList<VexNode> listnodes=new ArrayList<VexNode>();
		listnodes.addAll(nodes.values());
		Collections.sort(listnodes);
		sb.append("Graph {\"");
		appendTab(sb,14);
		sb.append("+\"\\n\"+\n");
		for(VexNode v:listnodes){
			appendTab(sb,4);
			sb.append("\"  "+v.getName()+":"+v.getLiveDefs()+"\"");
			appendTab(sb,10);
			sb.append("+\"\\n\"+\n");
		}
		
		appendTab(sb,3);
		sb.append("\"}");
		
		
		return sb.toString();
	}
	
	//为控制流图ControlFlowVisitor生成测试用例
	public String printGraphForTestCaseGeneratorForCFG()
	{
		StringBuffer sb = new StringBuffer();
		ArrayList<VexNode> listnodes=new ArrayList<VexNode>();
		listnodes.addAll(nodes.values());
		Collections.sort(listnodes);
		sb.append("Graph {\"");
		appendTab(sb,14);
		sb.append("+\"\\n\"+\n");
		for(VexNode v:listnodes){
			appendTab(sb,4);
			sb.append("\"  "+v.toString()+"\"");
			appendTab(sb,10);
			sb.append("+\"\\n\"+\n");
		}
		
		ArrayList<Edge> listedges=new ArrayList<Edge>();
		listedges.addAll(edges.values());
		Collections.sort(listedges);
		for(Edge e:listedges){
			appendTab(sb,4);
			sb.append("\"  "+e.toString()+"\"");
			appendTab(sb,10);
			sb.append("+\"\\n\"+\n");
		}
		
		appendTab(sb,3);
		sb.append("\"}");
		//added by liuyan 2015/10/31
//		if(Config.DU){
//			logger.info("测试测试测试！！！！！");
//		}

		return sb.toString();
	}
	@Override
	public String toString() {
		StringBuffer sb = new StringBuffer();
		ArrayList<VexNode> listnodes=new ArrayList<VexNode>();
		listnodes.addAll(nodes.values());
		Collections.sort(listnodes);
		sb.append("Graph {\n");
		for(VexNode v:listnodes){
			sb.append("  "+v.toString()+"\n");
		}
		
		ArrayList<Edge> listedges=new ArrayList<Edge>();
		listedges.addAll(edges.values());
		Collections.sort(listedges);
		for(Edge e:listedges){
			sb.append("  "+e.toString()+"\n");
		}
		sb.append("}");

		return sb.toString();
	}

	/** 路径总数(删除矛盾边后的) */
	private int pathcount = 0;
	
	/** 不是实际的计数，用于产生名字 */
	private int nodecount = 0;

	/** 不是实际的计数，用于产生名字 */
	private int edgecount = 0;

	/** 结点集合 */
	public Hashtable<String, VexNode> nodes = new Hashtable<String, VexNode>();

	/** 边集合 */
	public Hashtable<String, Edge> edges = new Hashtable<String, Edge>();

	/** String to NameOcc, ytang add 20161108*/
	public Hashtable<String, NameOccurrence> occtable= new Hashtable<String, NameOccurrence>();
	
	/** 缺省参数构造函数 */
	public Graph() {

	}

	public Hashtable<String, NameOccurrence> getOcctable(){
		return occtable;
	}
	
	/** 增加一个节点，如果该节点已经存在，则抛出异常 */
	VexNode addVex(VexNode vex) {
		if (nodes.get(vex.name) != null) {
			throw new RuntimeException("The vexnode has already existed.");
		}
		nodes.put(vex.name, vex);
		vex.snumber = nodecount++;
		return vex;
	}

	/** 增加一个指定名称的节点，并设定该节点关联的抽象语法节点，最终的名称将为name+nodecount */
	VexNode addVex(String name, SimpleNode treenode) {
		VexNode vex = new VexNode(name + nodecount, treenode);
		vex.setGraph(this);
		return addVex(vex);
	}

	/** 增加一个节点，并设定该节点关联的抽象语法节点 */
	VexNode addVex(SimpleNode treenode) {
		String name = "" + nodecount;
		return addVex(name, treenode);
	}

	/** 增加一个指定尾、头节点的边，并设定名称 */
	Edge addEdge(VexNode tailnode, VexNode headnode, String name) {
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

		Edge e = new Edge(name, tailnode, headnode);
		edges.put(name, e);
		e.snumber = edgecount++;

		return e;
	}

	/** 增加一个指定尾、头节点的边，并设定名称 */
	Edge addEdge(String tail, String head, String name) {
		VexNode tailnode = nodes.get(tail);
		VexNode headnode = nodes.get(head);
		return addEdge(tailnode, headnode, name);
	}

	/** 增加一个指定尾、头节点的边 */
	Edge addEdge(String tail, String head) {
		String name = "" + edgecount;
		return addEdge(tail, head, name);
	}

	/** 增加一个指定尾、头节点的边 */
	Edge addEdge(VexNode tailnode, VexNode headnode) {
		String name = "" + edgecount;
		return addEdge(tailnode, headnode, name);
	}

	/** 增加一个指定尾、头节点的边，并设定名称为name+edgecount */
	Edge addEdge(String name, VexNode tailnode, VexNode headnode) {
		name = name + edgecount;
		return addEdge(tailnode, headnode, name);
	}

	/** 增加一个指定尾、头节点的边，并设定其可能的真假分支情况，真分支名称以T_开头，假分支以F_开头 */
	Edge addEdgeWithFlag(VexNode tailnode, VexNode headnode) {
		String name = "";
		Edge edge = null;
		if(tailnode.getName().startsWith("assert_")){
			if(headnode.getName().startsWith("func_"))
				tailnode.falsetag = true;
			else
				tailnode.truetag = true;
		}
		if (tailnode.truetag) {
			name = "T_";
			tailnode.truetag = false;
		} else if (tailnode.falsetag) {
			name = "F_";
			tailnode.falsetag = false;
		}
		edge = addEdge(name, tailnode, headnode);
		return edge;
	}	

	/** 删除指定的边，如果找不到该边或者该边不是图中的边则抛出异常 */
	void removeEdge(Edge e) {
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
	void removeEdge(String name) {
		Edge e = edges.get(name);
		removeEdge(e);
	}

	/** 删除指定节点的所有入边 */
	void removeInedges(VexNode vex) {
		LinkedList<Edge> temp = new LinkedList<Edge>();
		temp.clear();
		for (Enumeration<Edge> e = vex.inedges.elements(); e.hasMoreElements();) {
			temp.add(e.nextElement());
		}
		ListIterator<Edge> i = temp.listIterator();
		while (i.hasNext()) {
			Edge edge = i.next();
			removeEdge(edge);
		}
	}

	/** 删除指定节点的所有出边 */
	void removeOutedges(VexNode vex) {
		LinkedList<Edge> temp = new LinkedList<Edge>();
		temp.clear();
		for (Enumeration<Edge> e = vex.outedges.elements(); e.hasMoreElements();) {
			temp.add(e.nextElement());
		}
		ListIterator<Edge> i = temp.listIterator();
		while (i.hasNext()) {
			Edge edge = i.next();
			removeEdge(edge);
		}
	}

	/** 删除指定节点及其关联的边 */
	void removeVex(VexNode vex) {
		if (nodes.get(vex.name) != vex || vex == null) {
			throw new RuntimeException("Cannot find the vexnode.");
		}
		removeInedges(vex);
		removeOutedges(vex);
		nodes.remove(vex.name);
	}

	/** 删除指定节点的所有入边 */
	void removeVex(String name) {
		VexNode vex = nodes.get(name);
		removeVex(vex);
	}

	/** 控制流图访问者的accept方法 */
	@Override
	public void accept(GraphVisitor visitor, Object data) {
		visitor.visit(this, data);
	}

	/** 获得指定节点的一个没有访问的相邻节点，可能返回null,节点顺序由自然顺序决定 */
	private VexNode getAdjUnvisitedVertex(VexNode v) {
		if (v.outedges.size() <= 0) {
			return null;
		}
		List<VexNode> list = new ArrayList<VexNode>();
		for (Enumeration<Edge> e = v.outedges.elements(); e.hasMoreElements();) {
			Edge edge = e.nextElement();
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
	public void dfs(GraphVisitor visitor, Object data) {
		// 找到控制流图入口开始
		VexNode first = null;
		Stack<VexNode> stack = new Stack<VexNode>();
		for (Enumeration<VexNode> e = nodes.elements(); e.hasMoreElements();) {
			VexNode n = (VexNode) e.nextElement();
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
			VexNode next = getAdjUnvisitedVertex(stack.peek());
			if (next == null) {
				stack.pop();
			} else {
				next.accept(visitor, data);
				next.setVisited(true);
				stack.push(next);
			}
		}
		// 处理那些控制流图入口到达不了的节点，不掉用访问者
		for (Enumeration<VexNode> e = nodes.elements(); e.hasMoreElements();) {
			VexNode n = e.nextElement();
			if (!n.getVisited()) {
				// first.accept(visitor, data);
				first.setVisited(true);
				stack.push(first);
				while (!stack.isEmpty()) {
					VexNode next = getAdjUnvisitedVertex(stack.peek());
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
		for (Enumeration<VexNode> e = nodes.elements(); e.hasMoreElements();) {
			VexNode n = e.nextElement();
			n.setVisited(false);
		}
	}

	/** 节点顺序遍历 */
	public void numberOrderVisit(GraphVisitor visitor, Object data) {
		List<VexNode> list = new ArrayList<VexNode>();
		for (Enumeration<VexNode> e = nodes.elements(); e.hasMoreElements();) {
			VexNode vex = e.nextElement();
			list.add(vex);
		}
		Collections.sort(list);

		Iterator<VexNode> i = list.iterator();
		while (i.hasNext()) {
			i.next().accept(visitor, data);
		}
	}
	
	/** 清除所有节点的访问标志 */
	public void clearVisited(){
		for (Enumeration<VexNode> e = nodes.elements(); e.hasMoreElements();) {
			VexNode n = e.nextElement();
			n.setVisited(false);
		}
	}

	/** 清除所有边上的矛盾标志 */
	public void clearEdgeContradict() {
		for (Enumeration<Edge> e = edges.elements(); e.hasMoreElements();) {
			Edge n = e.nextElement();
			n.setContradict(false);
		}
	}

	/** 清除所有节点上的矛盾标志 */
	public void clearVexNodeContradict() {
		for (Enumeration<VexNode> e = nodes.elements(); e.hasMoreElements();) {
			VexNode n = e.nextElement();
			n.setContradict(false);
		}
	}
	
	/**
	 * @param fromvex 出发节点
	 * @param tovex	目的节点
	 * @param tempe 不能经过的边
	 * @return 如果可达则返回true，否则返回false
	 */
	public static boolean checkVexReachable(VexNode fromvex,VexNode tovex,Edge tempe){
		if(fromvex==null||tovex==null||tempe==null){
			return false;
		}
		if(fromvex==tovex){
			return true;
		}
		Stack<VexNode> stack = new Stack<VexNode>();
		HashSet<VexNode> table=new HashSet<VexNode>();
		stack.push(fromvex);
		table.add(fromvex);
		while (!stack.isEmpty()) {
			VexNode v=stack.pop();
			for (Enumeration<Edge> e = v.outedges.elements(); e.hasMoreElements();) {
				Edge edge = e.nextElement();
				if(edge==tempe){
					continue;
				}
				VexNode tempnode=edge.headnode;
				if (!table.contains(tempnode)) {
					if(tempnode==tovex){
						return true;
					}
					table.add(tempnode);
					stack.push(tempnode);
				}
			}
		}
		return false;
	}
	
	/**
	 * @param fromvex 出发节点
	 * @param tovex	目的节点
	 * @return 一条路径
	 */
	public static List<VexNode> findAPath(VexNode fromvex,VexNode tovex){
		List<VexNode> ret=new ArrayList<VexNode>();
		if(fromvex==null||tovex==null){
			return ret;
		}
		if(fromvex==tovex){
			ret.add(fromvex);
			return ret;
		}
		Stack<VexNode> stack = new Stack<VexNode>();
		HashSet<VexNode> table=new HashSet<VexNode>();
		stack.push(fromvex);
		table.add(fromvex);
		
		while (!stack.isEmpty()) {
			VexNode current=stack.peek();
			VexNode next=null;
			for (Enumeration<Edge> e = current.outedges.elements(); e.hasMoreElements();) {
				Edge edge = e.nextElement();
				VexNode tempnode=edge.headnode;
				if(!table.contains(tempnode)){
					next=tempnode;
					//zys:2010.4.22	这个算法是不是有问题？应该添加break?
					//break;
				}
			}
			if (next == null) {
				stack.pop();
			} else {
				if(next==tovex){
					for(VexNode v:stack){
						ret.add(v);
					}
					ret.add(tovex);
					return ret;
				}else{
					table.add(next);
					stack.push(next);
				}
			}
		}		
		
		
		return ret;
	}
	
	/**
	 * @return 返回入口节点
	 */
	public VexNode getEntryNode(){
		for (Enumeration<VexNode> e = nodes.elements(); e.hasMoreElements();) {
			VexNode vex = e.nextElement();
			if(vex.getName().startsWith("func_head_")){
				return vex;
			}
		}
		throw new RuntimeException("Cannot find entry node.");
	}
	
	/**
	 * @return 返回出口节点
	 */
	public VexNode getExitNode(){
		for (Enumeration<VexNode> e = nodes.elements(); e.hasMoreElements();) {
			VexNode vex = e.nextElement();
			if(vex.getName().startsWith("func_out_")){
				return vex;
			}
		}
		throw new RuntimeException("Cannot find exit node.");
	}

	/**
	 * @return the pathcount
	 */
	public int getPathcount() {
		return pathcount;
	}

	/**
	 * @param pathcount the pathcount to set
	 */
	public void setPathcount(int pathcount) {
		this.pathcount = pathcount;
	}

	public void clear() {
		
		//两个for循环应该是冗余   answer by lsc 2018/9/19
		for (String key: edges.keySet()) {
			edges.get(key).clear();
		}
		for (String key: nodes.keySet()) {
			nodes.get(key).clear();
		}
		edges.clear();
		nodes.clear();
	}
	
	/**获取控制流图中的节点个数 */
	public int getVexNum(){
		return nodes.size();
	}
	
	//add by ALUO
	/** 找到下一个函数调用点在本函数控制流图中的节点 **/
	public HashMap<VexNode, ArrayList<ArrayList<VexNode>>> visitBeginToTargetPointBasisPath(MethodNode methodNode){
		HashMap<VexNode, ArrayList<ArrayList<VexNode>>> hashMap = new HashMap<>();
		if(methodNode == null){ // 下一个函数调用点是空时，输出当前函数的基本路径
			ArrayList<ArrayList<VexNode>> arrayList1 = visitBasisPath();
			hashMap.put(null, arrayList1);
			return hashMap;
		}
		String MethodName = methodNode.getMethod().getName();
		//String MethodName = str;
		
		ArrayList<VexNode> target = new ArrayList<>();
		for(VexNode vexNode : nodes.values()){
			// 控制流图上节点对应的抽象语法树节点不准确 有的对应的抽象语法树节点层次更高 所以需要详细处理
			if(vexNode.name.contains("func_head_") || vexNode.name.contains("func_out_") 
					|| vexNode.name.contains("if_out_") || vexNode.name.contains("for_out_")
					|| vexNode.name.contains("while_out_") || vexNode.name.contains("do_while_out2_")
					|| vexNode.name.contains("do_while_head_") || vexNode.name.contains("switch_out_")
					|| vexNode.name.contains("label_head_case_") || vexNode.name.contains("label_head_default_")){
				continue;
			}
			if(vexNode.name.contains("if_head_") || vexNode.name.contains("switch_head_")){
				ASTSelectionStatement astExpression = (ASTSelectionStatement)vexNode.treenode;
				ASTExpression expression = (ASTExpression)astExpression.jjtGetChild(0);
				List<Node> list = expression.findChildrenOfType(ASTPrimaryExpression.class);
				for(Node node : list){
					ASTPrimaryExpression astPrimaryExpression = (ASTPrimaryExpression)node;
					if(astPrimaryExpression.isMethod()){
						if(astPrimaryExpression.getImage().equals(MethodName)){
							target.add(vexNode);
							break;
						}
					}
				}
			}else if(vexNode.name.contains("while_head_")){
				ASTIterationStatement astIterationStatement = (ASTIterationStatement)vexNode.treenode;
				ASTExpression expression = (ASTExpression)astIterationStatement.jjtGetChild(0);
				List<Node> list = expression.findChildrenOfType(ASTPrimaryExpression.class);
				for(Node node : list){
					ASTPrimaryExpression astPrimaryExpression = (ASTPrimaryExpression)node;
					if(astPrimaryExpression.isMethod()){
						if(astPrimaryExpression.getImage().equals(MethodName)){
							target.add(vexNode);
							break;
						}
					}
				}
			}else if(vexNode.name.contains("for_head_")){
				ASTIterationStatement astIterationStatement = (ASTIterationStatement)vexNode.treenode;
				ASTExpression expression = (ASTExpression)astIterationStatement.jjtGetChild(1);
				List<Node> list = expression.findChildrenOfType(ASTPrimaryExpression.class);
				for(Node node : list){
					ASTPrimaryExpression astPrimaryExpression = (ASTPrimaryExpression)node;
					if(astPrimaryExpression.isMethod()){
						if(astPrimaryExpression.getImage().equals(MethodName)){
							target.add(vexNode);
							break;
						}
					}
				}
			}else{
				List<Node> list = vexNode.treenode.findChildrenOfType(ASTPrimaryExpression.class);
				for(Node node : list){
					ASTPrimaryExpression astPrimaryExpression = (ASTPrimaryExpression)node;
					if(astPrimaryExpression.isMethod()){
						if(astPrimaryExpression.getImage().equals(MethodName)){
							target.add(vexNode);
							break;
						}
					}
				}
			}
		}
		for(VexNode vexNode : target){
			ArrayList<ArrayList<VexNode>> allBeginToTarget = new ArrayList<>();
			ArrayList<VexNode> beginToTarget = new ArrayList<>();
			visitBeginToTargetPointBasisPathHelp(allBeginToTarget, beginToTarget, vexNode, vexNode);
			hashMap.put(vexNode, allBeginToTarget);
			// 将访问标志重新设置回false
			for (Enumeration<VexNode> e = nodes.elements(); e.hasMoreElements();) {
				VexNode n = e.nextElement();
				n.setVisited(false);
			}
		}
		
		//测试打印结果
		Iterator iterator = hashMap.entrySet().iterator();
		while(iterator.hasNext()){
			Map.Entry entry = (Map.Entry)iterator.next();
			VexNode key = (VexNode)entry.getKey();
			ArrayList<ArrayList<VexNode>> list = (ArrayList<ArrayList<VexNode>>)entry.getValue();
			System.out.println("节点：" + key.name);
			int i = 1;
			for(ArrayList<VexNode> list2 : list){
				System.out.print("第" + i + "条：");
				for(VexNode nodee : list2){
					System.out.print(nodee.name + "->");
				}
				System.out.println();
				i++;
			}
		}
		
		return hashMap;
	}
	
	//add by ALUO
	/** 获取函数控制流图中函数入口到调用序列中下一个函数调用点的基本路径 **/
	public void visitBeginToTargetPointBasisPathHelp(ArrayList<ArrayList<VexNode>> allBasisPathList,
			ArrayList<VexNode> basisPathList, VexNode curNode, VexNode targetNode){
		if(curNode == null) {
			System.out.println("获取节点出现错误！");
			return;
		}
		if(curNode == targetNode && curNode.visited){
			return;
		}
		if(curNode.inedges.size() == 0){
			curNode.setVisited(true);
			basisPathList.add(curNode);
			Collections.reverse(basisPathList);
			allBasisPathList.add(basisPathList);
		} else if(curNode.inedges.size() == 1){  //顺序执行
			curNode.setVisited(true);
			basisPathList.add(curNode);
			Enumeration<String> e = curNode.inedges.keys();
			while(e.hasMoreElements()){
				Edge curEdge = (Edge)curNode.inedges.get(e.nextElement());
				VexNode nextNode = curEdge.tailnode;
				visitBeginToTargetPointBasisPathHelp(allBasisPathList, basisPathList, nextNode, targetNode);
			}
		} else if(curNode.inedges.size() == 2){  //有两种情况，第一种分支语句， 第二种循环语句
			if(curNode.visited){  //已经访问过的分支节点，随便走一条分支
				if(curNode.name.contains("while_head_") 
						|| curNode.name.contains("do_while_head_") 
						|| curNode.name.contains("for_head_") ){
					Enumeration<String> e = curNode.inedges.keys();
					while(e.hasMoreElements()){
						Edge curEdge = (Edge)curNode.inedges.get(e.nextElement());
						VexNode nextNode = curEdge.tailnode;
						if(Integer.parseInt(nextNode.name.split("_")[nextNode.name.split("_").length - 1])
								> Integer.parseInt(curNode.name.split("_")[curNode.name.split("_").length - 1])){
							continue;
						}else if(Integer.parseInt(nextNode.name.split("_")[nextNode.name.split("_").length - 1])
								< Integer.parseInt(curNode.name.split("_")[curNode.name.split("_").length - 1])){
							basisPathList.add(curNode);
							visitBeginToTargetPointBasisPathHelp(allBasisPathList, basisPathList, nextNode, targetNode);
							break;	
						}
					}
				}else{
					Enumeration<String> e = curNode.inedges.keys();
					while(e.hasMoreElements()){
						Edge curEdge = (Edge)curNode.inedges.get(e.nextElement());
						VexNode nextNode = curEdge.tailnode;
						basisPathList.add(curNode);
						visitBeginToTargetPointBasisPathHelp(allBasisPathList, basisPathList, nextNode, targetNode);
						break;
					}
				}
			} else {  //没有访问过的分支节点，真假分支都走
				curNode.setVisited(true);
				Enumeration<String> e = curNode.inedges.keys();
				basisPathList.add(curNode);
				while(e.hasMoreElements()){
					Edge curEdge = (Edge)curNode.inedges.get(e.nextElement());
					VexNode nextNode = curEdge.tailnode;
					ArrayList<VexNode> newBasisPathList = new ArrayList<VexNode>(basisPathList);
					visitBeginToTargetPointBasisPathHelp(allBasisPathList, newBasisPathList, nextNode, targetNode);
				}
			}
		} else if(curNode.inedges.size() > 2){  //Switch语句
			if(curNode.visited){  //已经访问过的分支节点，走出边集合的数值小的节点
				Enumeration<String> e = curNode.inedges.keys();
				while(e.hasMoreElements()){
					Edge curEdge = (Edge)curNode.inedges.get(e.nextElement());
					VexNode nextNode = curEdge.tailnode;
					basisPathList.add(curNode);
					visitBeginToTargetPointBasisPathHelp(allBasisPathList, basisPathList, nextNode, targetNode);
					break;
				}
				
			} else {  //没有访问过的节点，所有分支都走
				curNode.setVisited(true);
				Enumeration<String> e = curNode.inedges.keys();
				basisPathList.add(curNode);
				while(e.hasMoreElements()){
					Edge curEdge = (Edge)curNode.inedges.get(e.nextElement());
					VexNode nextNode = curEdge.tailnode;
					ArrayList<VexNode> newBasisPathList = new ArrayList<VexNode>(basisPathList);
					visitBeginToTargetPointBasisPathHelp(allBasisPathList, newBasisPathList, nextNode, targetNode);
				}
			}
		}
	}
	
	//add by ALUO
	/**获取函数基本路径**/
	public ArrayList<ArrayList<VexNode>> visitBasisPath(){
		ArrayList<ArrayList<VexNode>> allBasisPathList = new ArrayList<ArrayList<VexNode>>();
		ArrayList<VexNode> basisPathList = new ArrayList<VexNode>();
		// 找到控制流图入口开始
		VexNode first = null;
		
		for (Enumeration<VexNode> e = nodes.elements(); e.hasMoreElements();) {
			VexNode n = (VexNode) e.nextElement();
			if (!n.getVisited() && n.inedges.size() == 0) {
				first = n;
				break;
			}
		}
		if (first == null) {
			throw new RuntimeException("控制流图入口错误");
		}
		//Stack<VexNode> stack = new Stack<VexNode>();
		visitBasisPathHelp(allBasisPathList, basisPathList, first);
		// 将访问标志重新设置回false
		for (Enumeration<VexNode> e = nodes.elements(); e.hasMoreElements();) {
			VexNode n = e.nextElement();
			n.setVisited(false);
		}
		
		/*
		 *  测试基本路径生成结果，打印到文件中
		 */
//		try {
//			FileWriter fw = new FileWriter("D:\\workspace\\DTSEmbed20171030\\temp\\Basis.txt", true);
//			StringBuilder sb = new StringBuilder();
//			sb.append("Method:" + allBasisPathList.get(0).get(0).name.split("func_head_")[1].split("_0")[0] + "\r\n");
//			int i = 1;
//			for(ArrayList<VexNode> temp : allBasisPathList){
//				sb.append("第" + i + "条：");
//				for(VexNode temp2 : temp){
//					sb.append(temp2.name + "->");
//				}
//				sb.append("\r\n");
//				i++;
//			}
//			sb.append("OVER!\r\n");
//			fw.write(sb.toString());
//			fw.close();
//		} catch (IOException e) {
//			// TODO 自动生成的 catch 块
//			e.printStackTrace();
//		}
		int i = 1;
		for(ArrayList<VexNode> temp : allBasisPathList){
			System.out.print("第" + i + "条：");
			for(VexNode temp2 : temp){
				System.out.print(temp2.name + "->");
			}
			System.out.println();
			i++;
		}
		System.out.println("OVER!");
		
		return allBasisPathList;
	}
	
	//add by ALUO
	/**获取函数基本路径具体实现**/
	public void visitBasisPathHelp(ArrayList<ArrayList<VexNode>> allBasisPathList, ArrayList<VexNode> basisPathList, VexNode curNode){
		if(curNode == null) {
			System.out.println("获取尾节点出现错误！");
			return;
		}
		if(curNode.outedges.size() == 0){
			curNode.setVisited(true);
			basisPathList.add(curNode);
			allBasisPathList.add(basisPathList);
		} else if(curNode.outedges.size() == 1){  //顺序执行
			curNode.setVisited(true);
			basisPathList.add(curNode);
			Enumeration<String> e = curNode.outedges.keys();
			while(e.hasMoreElements()){
				Edge curEdge = (Edge)curNode.outedges.get(e.nextElement());
				VexNode nextNode = curEdge.headnode;
				visitBasisPathHelp(allBasisPathList, basisPathList, nextNode);
			}
		} else if(curNode.outedges.size() == 2){  //有两种情况，第一种分支语句， 第二种循环语句
			if(curNode.visited){  //已经访问过的分支节点，随便走一条分支
				if(curNode.name.contains("for_head")){
					Enumeration<String> e = curNode.outedges.keys();
					while(e.hasMoreElements()){
						Edge curEdge = (Edge)curNode.outedges.get(e.nextElement());
						VexNode nextNode = curEdge.headnode;
						if(nextNode.name.contains("for_out")){
							basisPathList.add(curNode);
							visitBasisPathHelp(allBasisPathList, basisPathList, nextNode);
							break;
						}else{
							continue;
						}
					}
				}else if(curNode.name.contains("while_head")){
					Enumeration<String> e = curNode.outedges.keys();
					while(e.hasMoreElements()){
						Edge curEdge = (Edge)curNode.outedges.get(e.nextElement());
						VexNode nextNode = curEdge.headnode;
						if(nextNode.name.contains("while_out")){
							basisPathList.add(curNode);
							visitBasisPathHelp(allBasisPathList, basisPathList, nextNode);
							break;
						}else{
							continue;
						}
					}
				}else if(curNode.name.contains("do_while_out1_")){
					Enumeration<String> e = curNode.outedges.keys();
					while(e.hasMoreElements()){
						Edge curEdge = (Edge)curNode.outedges.get(e.nextElement());
						VexNode nextNode = curEdge.headnode;
						if(nextNode.name.contains("do_while_out2_")){
							basisPathList.add(curNode);
							visitBasisPathHelp(allBasisPathList, basisPathList, nextNode);
							break;
						}else{
							continue;
						}
					}
				}else{
					Enumeration<String> e = curNode.outedges.keys();
					while(e.hasMoreElements()){
						Edge curEdge = (Edge)curNode.outedges.get(e.nextElement());
						VexNode nextNode = curEdge.headnode;
						basisPathList.add(curNode);
						visitBasisPathHelp(allBasisPathList, basisPathList, nextNode);
						break;
					}
				}
			} else {  //没有访问过的分支节点，真假分支都走
				curNode.setVisited(true);
				Enumeration<String> e = curNode.outedges.keys();
				basisPathList.add(curNode);
				while(e.hasMoreElements()){
					Edge curEdge = (Edge)curNode.outedges.get(e.nextElement());
					VexNode nextNode = curEdge.headnode;
					ArrayList<VexNode> newBasisPathList = new ArrayList<VexNode>(basisPathList);
					visitBasisPathHelp(allBasisPathList, newBasisPathList, nextNode);
				}
			}
		} else if(curNode.outedges.size() > 2){  //Switch语句
			if(curNode.visited){  //已经访问过的分支节点，走出边集合的第一个边分支
				Enumeration<String> e = curNode.outedges.keys();
				while(e.hasMoreElements()){
					Edge curEdge = (Edge)curNode.outedges.get(e.nextElement());
					VexNode nextNode = curEdge.headnode;
					basisPathList.add(curNode);
					visitBasisPathHelp(allBasisPathList, basisPathList, nextNode);
					break;
				}
			} else {  //没有访问过的节点，所有分支都走
				curNode.setVisited(true);
				Enumeration<String> e = curNode.outedges.keys();
				basisPathList.add(curNode);
				while(e.hasMoreElements()){
					Edge curEdge = (Edge)curNode.outedges.get(e.nextElement());
					VexNode nextNode = curEdge.headnode;
					ArrayList<VexNode> newBasisPathList = new ArrayList<VexNode>(basisPathList);
					visitBasisPathHelp(allBasisPathList, newBasisPathList, nextNode);
				}
			}
		}
	}
}