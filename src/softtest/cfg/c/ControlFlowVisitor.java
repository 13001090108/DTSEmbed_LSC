package softtest.cfg.c;

import java.util.*;
import softtest.ast.c.*;
import softtest.symboltable.c.NameOccurrence;
import softtest.symboltable.c.Search;
import softtest.symboltable.c.NameDeclaration;
import softtest.symboltable.c.Scope;
import softtest.symboltable.c.VariableNameDeclaration;
import softtest.symboltable.c.NameOccurrence.OccurrenceType;
import softtest.symboltable.c.Type.CType_Enum;



/** 用于生成控制流图的抽象语法树访问者 */
public class ControlFlowVisitor extends CParserVisitorAdapter {
	
	public String parserFileName=null;
	public ControlFlowVisitor(){
		
	}
	public ControlFlowVisitor(String parserFileName){
		this.parserFileName=parserFileName;
		
	}
	
	public Object visit(ASTFunctionDefinition node, Object data){
		String name=node.getImage();
		ControlFlowData flowdata = new ControlFlowData();
		Graph g = new Graph();
		flowdata.graph=g;
		node.setGraph(g);

		//产生函数入口节点
		VexNode head = g.addVex("func_head_" + name+"_", node); 
		flowdata.vexnode=head;
		//add by cmershen,2016.3.14
		//函数头结点上应该有变量信息，将其加入
		if(head!=null) {
			Scope funcheadScope = head.getTreenode().getScope();
			for(VariableNameDeclaration key : funcheadScope.getVariableDeclarations().keySet()) {
				SimpleNode location = key.getNode();
				String image = key.getImage();
				NameOccurrence nameocc = new NameOccurrence(key, location, image);
				nameocc.setOccurrenceType(OccurrenceType.ENTRANCE);
				head.getOccurrences().add(nameocc);
			}	
		}
		node.jjtGetChild(node.jjtGetNumChildren()-1).jjtAccept(this, flowdata);
		
		//产生函数出口节点，并连接
		VexNode in = flowdata.vexnode;
		VexNode out = flowdata.graph.addVex("func_out_" + name + "_", node);
		if(in!=null){
			flowdata.graph.addEdgeWithFlag(in, out);
		}
		
		//处理跳转语句,return 也被看作是转跳
		LabelData labeldata = flowdata.labeltable.get("return");
		if (labeldata == null) {
			labeldata = new LabelData();
			flowdata.labeltable.put("return", labeldata);
		}
		labeldata.labelnode = out;
		
		//zys:
		labeldata=flowdata.labeltable.get("return");
		ListIterator<VexNode> i = labeldata.jumpnodes.listIterator();
		while (i.hasNext()) {
			VexNode node1 = i.next();
			VexNode node2 = labeldata.labelnode;
			if (node1 != null && node2 != null) {
				flowdata.graph.addEdgeWithFlag(node1, node2);
			}
		}
		flowdata.labeltable.remove("return");
		
		
		for (Enumeration<LabelData> e = flowdata.labeltable.elements(); e.hasMoreElements();) {
			labeldata = e.nextElement();
			if(labeldata.labelnode == null)
				labeldata.labelnode = out;
			ListIterator<VexNode> ii = labeldata.jumpnodes.listIterator();
			while (ii.hasNext()) {
				VexNode node1 = ii.next();
				VexNode node2 = labeldata.labelnode;				
				if (node1 != null && node2 != null) {
					flowdata.graph.addEdgeWithFlag(node1, node2);
				}
			}
		}
		
		return null;
	}
	
	public Object visit(ASTNestedFunctionDefinition node, Object data){
		String name=node.getImage();
		ControlFlowData flowdata = new ControlFlowData();
		Graph g = new Graph();
		flowdata.graph=g;
		node.setGraph(g);

		//产生函数入口节点
		VexNode in = flowdata.vexnode;
		VexNode head = g.addVex("nestedfunc_head_" + name+"_", node); 
		if(in!=null){
			g.addEdge(in,head);
		}
		flowdata.vexnode=head;
		
		node.jjtGetChild(node.jjtGetNumChildren()-1).jjtAccept(this, flowdata);
		
		//产生函数出口节点，并连接
		in = flowdata.vexnode;
		VexNode out = flowdata.graph.addVex("nestedfunc_out_" + name + "_", node);
		if(in!=null){
			flowdata.graph.addEdgeWithFlag(in, out);
		}
		flowdata.vexnode=out;
		
		//处理跳转语句,return 也被看作是转跳
		LabelData labeldata = flowdata.labeltable.get("nestReturn");
		if (labeldata == null) {
			labeldata = new LabelData();
			flowdata.labeltable.put("nestReturn", labeldata);
		}
		labeldata.labelnode = out;

		//zys:
		labeldata=flowdata.labeltable.get("nestReturn");
		ListIterator<VexNode> i = labeldata.jumpnodes.listIterator();
		while (i.hasNext()) {
			VexNode node1 = i.next();
			VexNode node2 = labeldata.labelnode;
			if (node1 != null && node2 != null) {
				flowdata.graph.addEdgeWithFlag(node1, node2);
			}
		}
		flowdata.labeltable.remove("nestReturn");
		
		for (Enumeration<LabelData> e = flowdata.labeltable.elements(); e.hasMoreElements();) {
			labeldata = e.nextElement();
			ListIterator<VexNode> ii = labeldata.jumpnodes.listIterator();
			while (ii.hasNext()) {
				VexNode node1 = ii.next();
				VexNode node2 = labeldata.labelnode;
				if (node1 != null && node2 != null) {
					flowdata.graph.addEdgeWithFlag(node1, node2);
				}
			}
		}
		return null;
	}
	
	public Object visit(ASTLabelDeclaration node, Object data){
		ControlFlowData flowdata = (ControlFlowData) data;
		Graph graph = flowdata.graph;
		VexNode in = flowdata.vexnode;
		VexNode out = graph.addVex("label_decl_stmt_", node);
		if (in != null) {
			graph.addEdgeWithFlag(in, out);
		}		
		flowdata.vexnode = out;
		return null;
	}
	
	public Object visit(ASTDeclaration node, Object data){
		if(node.jjtGetParent() instanceof ASTExternalDeclaration)
		{
			//zys:对外部声明，控制流图不做任何处理
			return null;
		}
		ControlFlowData flowdata = (ControlFlowData) data;
		Graph graph = flowdata.graph;
		VexNode in = flowdata.vexnode;
		VexNode out = graph.addVex("decl_stmt_", node);
		if (in != null) {
			graph.addEdgeWithFlag(in, out);
		}		
		flowdata.vexnode = out;
		return null;
	}
	
	public Object visit(ASTLabeledStatement node, Object data){
		ControlFlowData flowdata = (ControlFlowData) data;
		Graph g = flowdata.graph;
		VexNode in = flowdata.vexnode;

		// 产生头节点
		String name = node.getImage();
		VexNode head = g.addVex("label_head_" + name + "_", node);
		if (in != null) {
			g.addEdgeWithFlag(in, head);
		}

		// 以头节点为入口，调用子语句处理
		flowdata.vexnode = head;
		
		if(name.equals("case")||name.equals("default")){
			LoopData loopdata = flowdata.loopstack.peek();
			VexNode switchnode = loopdata.head;
			g.addEdgeWithFlag(switchnode, head);

			// 设置default标志
			if (name.equals("default")) {
				loopdata.hasdefault = true;
			}
		}else{
			// 在转跳表中填写标号节点
			LabelData labeldata = flowdata.labeltable.get(name);
			if (labeldata == null) {
				labeldata = new LabelData();
				flowdata.labeltable.put(name, labeldata);
			}
			labeldata.labelnode = head;
		}

		node.jjtGetChild(node.jjtGetNumChildren()-1).jjtAccept(this, flowdata);
		
		return null;
	}
	
	//liuli:2010.8.2 判断exit是否处于分支中
	public boolean isSingle(Graph graph){
		ArrayList<VexNode> listnodes=new ArrayList<VexNode>();
		Hashtable<String, VexNode> nodes = graph.nodes;
		listnodes.addAll(nodes.values());
		Collections.sort(listnodes);
		
		int count_out=0,count_head=0;
		for(VexNode v:listnodes){
			String  s = v.toString();
			String[] s1 = s.split(":");
			s = s1[1];
			if(s.startsWith("if_out") 
					|| s.startsWith("for_out") 
					|| s.startsWith("do_while_out") 
					|| s.startsWith("while_out") 
					|| s.startsWith("switch_out") ){
				count_out++;
			}
			if(s.startsWith("if_head") 
					|| s.startsWith("for_init") 
					|| s.startsWith("do_while_head") 
					|| s.startsWith("while_head") 
					|| s.startsWith("switch_head") ){
				count_head++;
			}
		}
		if(count_out == count_head)
			return true;
		else
			return false;	
	}
	
	public Object visit(ASTExpressionStatement node, Object data){
		ControlFlowData flowdata = (ControlFlowData) data;
		Graph graph = flowdata.graph;
		VexNode in = flowdata.vexnode;
		//liuli：在控制流上添加exit和abort节点
		ASTFunctionDefinition func = null;
		ASTPrimaryExpression temp = (ASTPrimaryExpression)node.getFirstChildOfType(ASTPrimaryExpression.class);
		
		if(temp!=null && temp.isMethod()){//当前为函数节点
			if(temp.getImage().equals("exit")){
				func = (ASTFunctionDefinition)node.getFirstParentOfType(ASTFunctionDefinition.class);
				VexNode out = graph.addVex("exit_", node);
				if (in != null) {
					graph.addEdgeWithFlag(in, out);
				}
				LabelData labeldata = flowdata.labeltable.get("exit");
				if (labeldata == null) {
					labeldata = new LabelData();
					flowdata.labeltable.put("exit", labeldata);
				}
				labeldata.jumpnodes.add(out);
				//此处还需判断exit是否处于分支中
				if(isSingle(graph))
					func.EXIT = true;
				// 控制流已经转跳走了
				flowdata.vexnode = null;
			}else if(temp.getImage().equals("abort")){
				func = (ASTFunctionDefinition)node.getFirstParentOfType(ASTFunctionDefinition.class);
				VexNode out = graph.addVex("abort_", node);
				if (in != null) {
					graph.addEdgeWithFlag(in, out);
				}
				LabelData labeldata = flowdata.labeltable.get("abort");
				if (labeldata == null) {
					labeldata = new LabelData();
					flowdata.labeltable.put("abort", labeldata);
				}
				labeldata.jumpnodes.add(out);
				//此处还需判断abort是否处于分支中			
				if(isSingle(graph))
					func.EXIT = true;
				// 控制流已经转跳走了
				flowdata.vexnode = null;
				//liuli:华为中assert的格式
			}else if(temp.getImage().equals("VOS_Assert_X")){
				func = (ASTFunctionDefinition)node.getFirstParentOfType(ASTFunctionDefinition.class);
				VexNode out = graph.addVex("assert_", node);
				if (in != null) {
					graph.addEdgeWithFlag(in, out);
				}
				LabelData labeldata = flowdata.labeltable.get("assert");
				if (labeldata == null) {
					labeldata = new LabelData();
					flowdata.labeltable.put("assert", labeldata);
				}
				labeldata.jumpnodes.add(out);
				//此处还需判断abort是否处于分支中			
				if(isSingle(graph))
					func.EXIT = true;
				// 控制流已经转跳走了
				flowdata.vexnode = out;
			}else{
				String image = temp.getImage();
				VexNode out = graph.addVex("stmt_", node);
				
				if (in != null) {
					graph.addEdgeWithFlag(in, out);
				}
				Scope s=node.getScope(); 
				NameDeclaration decl = Search.searchInMethodUpward(image, s);
				if(decl!=null && decl.getNode() instanceof ASTFunctionDefinition){
					func = (ASTFunctionDefinition)decl.getNode();
					if(func.EXIT){//添加一条指向func_out的边
						LabelData labeldata = flowdata.labeltable.get("exit");
						if (labeldata == null) {
							labeldata = new LabelData();
							flowdata.labeltable.put("exit", labeldata);
						}
						labeldata.jumpnodes.add(out);
						flowdata.vexnode = null;
					}else{
						flowdata.vexnode = out;
					}
				}else{
					flowdata.vexnode = out;
				}
				
			}
			//liuli:处理assert
		}else if(temp!=null && temp.containsChildOfType(ASTPrimaryExpression.class)){
			List<Node> list = temp.findChildrenOfType(ASTPrimaryExpression.class);
			Boolean flag = false;
			for(Node n : list){
				ASTPrimaryExpression n1 = (ASTPrimaryExpression)n;
				if(n1.isMethod() && n1.getImage().startsWith("__assert")){
					flag = true;
					func = (ASTFunctionDefinition)node.getFirstParentOfType(ASTFunctionDefinition.class);
					VexNode out = graph.addVex("assert_", node);
					if (in != null) {
						graph.addEdgeWithFlag(in, out);
					}
					LabelData labeldata = flowdata.labeltable.get("assert");
					if (labeldata == null) {
						labeldata = new LabelData();
						flowdata.labeltable.put("assert", labeldata);
					}
					labeldata.jumpnodes.add(out);
					//此处还需判断assert是否处于分支中
					if(isSingle(graph))
						func.EXIT = true;
					// 控制流已经转跳走了
					flowdata.vexnode = out;
				}
			}
			
			if(flag == false){
				VexNode out = graph.addVex("stmt_", node);
				
				if (in != null) {
					graph.addEdgeWithFlag(in, out);
				}
				
				flowdata.vexnode = out;
			}
		}else{
			VexNode out = graph.addVex("stmt_", node);
			
			if (in != null) {
				graph.addEdgeWithFlag(in, out);
			}
			
			flowdata.vexnode = out;
		}
		
		return null;
		
	}
	
	public Object visit(ASTSelectionStatement node, Object data){
		String image = node.getImage();
		if (image.equals("if")){
			visitIfStatement(node, data);
		} else {
			visitSwitchStatement(node, data);
		}
		return null;
	}
	
	private void visitIfStatement(ASTSelectionStatement node, Object data){
		VexNode head, out, f_branch, t_branch;
		ControlFlowData flowdata = (ControlFlowData) data;
		VexNode in = flowdata.vexnode;
		Graph g = flowdata.graph;

		// 产生if语句的头结点head
		head = g.addVex("if_head_", node);
		
		if (in != null) {
			g.addEdgeWithFlag(in, head);
		}

		// 以头节点为入口，调用真分支语句处理
		head.truetag = true;
		flowdata.vexnode = head;
		node.jjtGetChild(1).jjtAccept(this, flowdata);
		t_branch = flowdata.vexnode;
		
		//真分支为空语句
		if(head==t_branch){
			head.truetag = false;
		}

		// 以头节点为入口，调用假分支语句处理
		head.falsetag = true;
		if (node.jjtGetNumChildren() > 2) {
			// 大于2说明有else分支
			flowdata.vexnode = head;
			node.jjtGetChild(2).jjtAccept(this, flowdata);
			f_branch = flowdata.vexnode;
		} else {
			f_branch = head;
		}

		// 考虑出口结点的不同情况
		if (t_branch == null && f_branch == null) {
			// 真假分支都已经转跳走了，不需要产生if出口了
			out = null;
		} else {
			// 产生出口，并连接
			out = g.addVex("if_out_", node);
			//真分支为空语句
			if(head==t_branch){
				head.truetag = true;
			}
			if (t_branch != null) {
				g.addEdgeWithFlag(t_branch, out);
			}
			if (f_branch != null) {
				g.addEdgeWithFlag(f_branch, out);
			}
		}
		flowdata.vexnode = out;
	}
	
	private void visitSwitchStatement(ASTSelectionStatement node, Object data){
		ControlFlowData flowdata = (ControlFlowData) data;
		VexNode head, out, subout;
		VexNode in = flowdata.vexnode;
		Graph g = flowdata.graph;

		LoopData loopdata = new LoopData();
		loopdata.name = "switch";

		// 产生switch语句的头结点head
		head = g.addVex("switch_head_", node);
		loopdata.head = head;

		if (in != null) {
			g.addEdgeWithFlag(in, head);
		}
		// 当前循环入栈，switch和循环统一处理
		flowdata.loopstack.push(loopdata);
		
		// 以null为入口，调用子语句处理
		flowdata.vexnode = null;
		node.jjtGetChild(1).jjtAccept(this, flowdata);
		subout = flowdata.vexnode;

		// 产生出口节点
		out = g.addVex("switch_out_", node);
		if (subout != null) {
			g.addEdgeWithFlag(subout, out);
		}

		// 当前循环出栈
		loopdata = flowdata.loopstack.pop();

		// 如果没有default子句，增加一条从head到out的边
		if (!loopdata.hasdefault && node.jjtGetChild(0) instanceof ASTExpression && ((ASTExpression)node.jjtGetChild(0)).getFirstChildOfType(ASTPrimaryExpression.class)!=null) {
			ASTPrimaryExpression pri=(ASTPrimaryExpression)((ASTExpression)node.jjtGetChild(0)).getFirstChildOfType(ASTPrimaryExpression.class);
			VariableNameDeclaration v=pri.getVariableDecl();
			if(v!=null && v.getType() instanceof CType_Enum){
				//判断case是否处理了所有的enum枚举值
				ASTStatementList list=(ASTStatementList)node.getFirstChildOfType(ASTStatementList.class);
				if(list!=null && list.jjtGetNumChildren()!=((CType_Enum)v.getType()).getValue()){
					g.addEdgeWithFlag(head, out);
				}
			}else{
				g.addEdgeWithFlag(head, out);
			}
		}

		// 处理break
		ListIterator<VexNode> i = loopdata.breaknodes.listIterator();
		while (i.hasNext()) {
			VexNode node1 = i.next();
			if (node1 != null) {
				flowdata.graph.addEdgeWithFlag(node1, out);
			}
		}
		flowdata.vexnode = out;
	}
	
	public Object visit(ASTIterationStatement node, Object data){
		String image = node.getImage();
		if (image.equals("for")){
			visitForStatement(node, data);
		} else if (image.equals("while")){
			visitWhileStatement(node, data);
		} else{
			visitDoStatement(node, data);
		}
		return null;
	}
	
	private void visitForStatement(ASTIterationStatement node, Object data){
		ControlFlowData flowdata = (ControlFlowData) data;
		VexNode head=null, init=null, add=null, out=null, subout=null;
		VexNode in = flowdata.vexnode;
		Graph g = flowdata.graph;

		LoopData loopdata = new LoopData();
		loopdata.name = "for";

		int count=0;
		// 产生for语句的初始化节点
		if(node.forChild[0]){
			init = g.addVex("for_init_", (SimpleNode) node.jjtGetChild(count++));
			if (in != null) {
				g.addEdgeWithFlag(in, init);
			}
		}else{
			init = in;
		}
		
		//这是暂时没有用到
		ASTExpression con=null;
		if(node.forChild[1]){
			con=(ASTExpression)node.jjtGetChild(count++);
		}
		
		// 产生for语句的头结点head
		head = g.addVex("for_head_", node);
		if (init != null) {
			g.addEdgeWithFlag(init, head);
		}
		loopdata.head = head;
		
		// 当前循环入栈
		flowdata.loopstack.push(loopdata);

		// 以头节点为入口，调用子语句处理
		head.truetag = true;
		flowdata.vexnode = head;
		// for 语句的初始化、条件和增量子句都可能没有
		node.jjtGetChild(node.jjtGetNumChildren() - 1).jjtAccept(this, flowdata);
		subout = flowdata.vexnode;// 子语句出口
		
		if(node.forChild[2]){
			add = g.addVex("for_inc_", (SimpleNode) node.jjtGetChild(count++));// 产生for语句的增量结点
			if (subout != null) {
				g.addEdgeWithFlag(subout, add);
			}
		} else {
			add = subout;
		}

		if (add != null) {
			g.addEdgeWithFlag(add, head);
		}

		// 产生for语句的出口节点
		out = g.addVex("for_out_", node);
		head.falsetag = true;
		g.addEdgeWithFlag(head, out);

		// 当前循环出栈
		loopdata = flowdata.loopstack.pop();
		// 处理break
		ListIterator<VexNode> i = loopdata.breaknodes.listIterator();
		while (i.hasNext()) {
			VexNode node1 = i.next();
			if (node1 != null) {
				flowdata.graph.addEdgeWithFlag(node1, out);
			}
		}

		// 处理continue
		i = loopdata.continuenodes.listIterator();
		while (i.hasNext()) {
			VexNode node1 = i.next();
			if (node1 != null) {
				if(add!=null){
					flowdata.graph.addEdgeWithFlag(node1, add);// continue到add节点
				}
				else{
					flowdata.graph.addEdgeWithFlag(node1, head);
				}
			}
		}
		flowdata.vexnode = out;
	}
	
	private void visitWhileStatement(ASTIterationStatement node, Object data){
		VexNode head, out, subout;
		ControlFlowData flowdata = (ControlFlowData) data;
		VexNode in = flowdata.vexnode;
		Graph g = flowdata.graph;

		//产生当前循环辅助结构
		LoopData loopdata = new LoopData();
		loopdata.name = "while";

		// 产生while语句的头结点head
		head = g.addVex("while_head_", node);
		loopdata.head = head;
		if (in != null) {
			g.addEdgeWithFlag(in, head);
		}

		// 当前循环入栈
		flowdata.loopstack.push(loopdata);

		// 以头节点为入口，调用子语句处理
		head.truetag = true;
		flowdata.vexnode = head;
		node.jjtGetChild(1).jjtAccept(this, flowdata);
		subout = flowdata.vexnode;
		if (subout != null) {
			g.addEdgeWithFlag(subout, head);
		}

		// 产生while语句出口节点
		out = g.addVex("while_out_", node);
		head.falsetag = true;
		g.addEdgeWithFlag(head, out);

		// 当前循环出栈
		loopdata = flowdata.loopstack.pop();

		// 处理当前循环的break
		ListIterator<VexNode> i = loopdata.breaknodes.listIterator();
		while (i.hasNext()) {
			VexNode node1 = i.next();
			if (node1 != null) {
				flowdata.graph.addEdgeWithFlag(node1, out);
			}
		}

		// 处理当前循环的continue
		i = loopdata.continuenodes.listIterator();
		while (i.hasNext()) {
			VexNode node1 = i.next();
			if (node1 != null) {
				flowdata.graph.addEdgeWithFlag(node1, head);
			}
		}
		flowdata.vexnode = out;
	}
	
	private void visitDoStatement(ASTIterationStatement node, Object data){
		ControlFlowData flowdata = (ControlFlowData) data;
		VexNode head, out1, out2, subout;
		VexNode in = flowdata.vexnode;
		Graph g = flowdata.graph;

		LoopData loopdata = new LoopData();
		loopdata.name = "do-while";
		// 产生do-while语句的头结点head
		head = g.addVex("do_while_head_", node);
		loopdata.head = head;

		if (in != null) {
			g.addEdgeWithFlag(in, head);
		}

		// 当前循环入栈
		flowdata.loopstack.push(loopdata);

		// 以头节点为入口，调用子语句处理
		flowdata.vexnode = head;
		node.jjtGetChild(0).jjtAccept(this, flowdata);
		subout = flowdata.vexnode;
		out1 = g.addVex("do_while_out1_", (SimpleNode) node.jjtGetChild(1));// 出口节点
		out2 = g.addVex("do_while_out2_", node);// 最终出口节点
		if (subout != null) {
			g.addEdgeWithFlag(subout, out1);
		}
		out1.truetag = true;
		g.addEdgeWithFlag(out1, head);
		out1.falsetag = true;
		g.addEdgeWithFlag(out1, out2);
		
		// 当前循环出栈
		loopdata = flowdata.loopstack.pop();

		// 处理break
		ListIterator<VexNode> i = loopdata.breaknodes.listIterator();
		while (i.hasNext()) {
			VexNode node1 = i.next();
			if (node1 != null) {
				flowdata.graph.addEdgeWithFlag(node1, out2);
			}
		}

		// 处理continue
		i = loopdata.continuenodes.listIterator();
		while (i.hasNext()) {
			VexNode node1 = i.next();
			if (node1 != null) {
				flowdata.graph.addEdgeWithFlag(node1, out1);
			}
		}
		flowdata.vexnode = out2;
	}
	
	public Object visit(ASTJumpStatement node, Object data){
		String image = node.getImage();
		if (image.equals("goto")){
			visitGotoStatement(node, data);
		} else if (image.equals("continue")){
			visitContinueStatement(node, data);
		} else if (image.equals("break")){
			visitBreakStatement(node, data);
		} else{
			visitReturnStatement(node, data);
		}
		return null;
	}
	
	private void visitGotoStatement(ASTJumpStatement node, Object data) {
		ControlFlowData flowdata = (ControlFlowData) data;
		Graph graph = flowdata.graph;
		VexNode in = flowdata.vexnode;

		VexNode out = graph.addVex("goto_", node);
		if (in != null) {
			graph.addEdgeWithFlag(in, out);
		}

		// 在转跳表中相应位置加入转跳节点
		String label=node.getLabel();
		if(!label.equals("")){
			LabelData labeldata = flowdata.labeltable.get(label);
			if (labeldata == null) {
				labeldata = new LabelData();
				flowdata.labeltable.put(label, labeldata);
			}
			labeldata.jumpnodes.add(out);
		}else{//zys:
			//gcc扩展不知道怎么处理
			ASTUnaryExpression ue=(ASTUnaryExpression)node.jjtGetChild(0);
			ASTPrimaryExpression pe=(ASTPrimaryExpression)ue.getFirstChildOfType(ASTPrimaryExpression.class);
			label=pe.getImage();
			if(!label.equals(""))
			{
				/*
				 * 找到label声明时所对应的标签变量，如：__label__ label; void *ptr=&&label;
				 * 则ptr所对应的标签为label.
				 */
				String realLabel="";//指针所指向的标签，即label
				NameDeclaration varLabel=(NameDeclaration)Search.searchInVariableAndMethodUpward(label,node.getScope());
				if(varLabel==null)
				{
					throw new RuntimeException("Pointer to the local Label must be Declarated first!");
				}
				//liuli:goto指针可能会指向函数
				SimpleNode direct = varLabel.getNode();
				ArrayList<NameOccurrence> list = null;
				if(direct instanceof ASTDirectDeclarator){
					direct=(ASTDirectDeclarator)varLabel.getNode();
					list=(ArrayList<NameOccurrence>)direct.getScope().getVariableDeclarations().get(varLabel);
				}else if(direct instanceof ASTFunctionDefinition){
					direct=(ASTFunctionDefinition)varLabel.getNode();
					list=(ArrayList<NameOccurrence>)((SimpleNode)direct.jjtGetParent()).getScope().getMethodDeclarations().get(varLabel);
				}
				//end
				if(list != null && list.size()>1)//goto *ptr;自身为最后一次occurence；
					//如果还有其他的occurence，如void *ptr;	ptr=&&labe;则取goto之前的一次occurence，即list.get(list.size()-2);
				{
					NameOccurrence no=(NameOccurrence)list.get(list.size()-2);
					SimpleNode locationNode=no.getLocation();
					
					if(locationNode instanceof ASTPrimaryExpression)
					{
						ASTAssignmentExpression ass=(ASTAssignmentExpression)locationNode.getFirstParentOfType(ASTAssignmentExpression.class);
						ASTAssignmentExpression child=(ASTAssignmentExpression)ass.jjtGetChild(2);
						ASTPrimaryExpression pri=(ASTPrimaryExpression)child.getFirstChildOfType(ASTPrimaryExpression.class);
						realLabel=pri.getImage();
					}else if(locationNode instanceof ASTDirectDeclarator)
					{
						ASTDeclarator dec=(ASTDeclarator)locationNode.getFirstParentOfType(ASTDeclarator.class);
						ASTInitializer init=(ASTInitializer)dec.getNextSibling();
						ASTPrimaryExpression pri=(ASTPrimaryExpression)init.getFirstChildOfType(ASTPrimaryExpression.class);
						realLabel=pri.getImage();
					}
				}
				
				LabelData labeldata = flowdata.labeltable.get(realLabel);
				if (labeldata == null) {
					labeldata = new LabelData();
					flowdata.labeltable.put(realLabel, labeldata);
				}
				labeldata.jumpnodes.add(out);
			}
		}
		// 控制流已经转跳走了
		flowdata.vexnode = null;
	}

	private void visitContinueStatement(ASTJumpStatement node, Object data) {
		ControlFlowData flowdata = (ControlFlowData) data;
		Graph graph = flowdata.graph;
		VexNode in = flowdata.vexnode;
		VexNode out = graph.addVex("continue_", node);
		if (in != null) {
			graph.addEdgeWithFlag(in, out);
		}
		// 控制流已经转跳走了，出口置为null
		flowdata.vexnode = null;

		LoopData loopdata = null;
		// 查找非switch的循环
		ListIterator<LoopData> i = flowdata.loopstack.listIterator(flowdata.loopstack.size());
		while (i.hasPrevious()) {
			loopdata = i.previous();
			if (loopdata.name != "switch") {
				break;
			}
		}
		loopdata.continuenodes.add(out);	
	}

	private void visitBreakStatement(ASTJumpStatement node, Object data) {
		ControlFlowData flowdata = (ControlFlowData) data;
		Graph graph = flowdata.graph;
		VexNode in = flowdata.vexnode;
		VexNode out = graph.addVex("break_", node);
		if (in != null) {
			graph.addEdgeWithFlag(in, out);
		}
		// 控制流已经转跳走了，出口置为null
		flowdata.vexnode = null;
		
		LoopData loopdata = flowdata.loopstack.peek();
		loopdata.breaknodes.add(out);
	}

	private void visitReturnStatement(ASTJumpStatement node, Object data) {
		ControlFlowData flowdata = (ControlFlowData) data;
		Graph graph = flowdata.graph;
		VexNode in = flowdata.vexnode;

		VexNode out = graph.addVex("return_", node);
		if (in != null) {
			graph.addEdgeWithFlag(in, out);
		}

		// 在转跳表中相应位置加入转跳节点
		//如果是位于嵌套函数内部,则return语句的标志设为nestReturn
		if(node.getFirstParentOfType(ASTNestedFunctionDefinition.class)!=null)
		{
			LabelData labeldata = flowdata.labeltable.get("nestReturn");
			if (labeldata == null) {
				labeldata = new LabelData();
				flowdata.labeltable.put("nestReturn", labeldata);
			}
			labeldata.jumpnodes.add(out);
		}else
		{
			LabelData labeldata = flowdata.labeltable.get("return");
			if (labeldata == null) {
				labeldata = new LabelData();
				flowdata.labeltable.put("return", labeldata);
			}
			labeldata.jumpnodes.add(out);
		}
		
		// 控制流已经转跳走了
		flowdata.vexnode = null;
	}
}