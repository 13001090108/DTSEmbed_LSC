package softtest.fsm.c;

//import net.sourceforge.pmd.jaxen.*;
//import net.sourceforge.pmd.ast.*;

import softtest.ast.c.*;
import softtest.tools.c.jaxen.DocumentNavigator;
import softtest.tools.c.jaxen.*;

import org.jaxen.*;
import org.w3c.dom.Node;

import softtest.cfg.c.*;

import java.util.*;

/** xpath条件 */
public class FSMXpathCondition extends FSMCondition {
	/** xpath */
	private String xpath = "";

	/** 以指定的xpath构造转换条件 */
	public FSMXpathCondition(String xpath) {
		this.xpath = xpath;
	}

	/** 设置xpath */
	public void setXpath(String xpath) {
		this.xpath = xpath;
	}

	/** 获得xpath */
	public String getXpath() {
		return xpath;
	}

	/** 对条件进行计算，判断其是否满足 */
	@Override
	/*
	public boolean evaluate(FSMMachineInstance fsm, FSMStateInstance state, VexNode vex) {
		boolean b = false;
		List evaluationResults = null;
		SimpleNode treenode = vex.getTreenode();

		// xpath不处理那些尾节点
		if (vex.isBackNode()) {
			return b;
		}
		
		try {
			XPath xpath = new BaseXPath(this.xpath, new DocumentNavigator());
			treenode = treenode.getConcreteNode();
			// func_decl_def, 不做处理是C89的特殊参数声明方式
			//zys:为什么屏蔽FunctionDefinition节点？？？？if(treenode==null || treenode instanceof ASTFunctionDefinition)
			if (treenode == null ) {
				return false;
			}
			evaluationResults = xpath.selectNodes(treenode);

		} catch (JaxenException e) {
			 e.printStackTrace();
			throw new RuntimeException("xpath error",e);
		}
		
		if (evaluationResults != null && evaluationResults.size() > 0) {
			if (relatedmethod == null) {
				b = true;
			} else {
				Object[] args = new Object[2];
				args[0] = evaluationResults;
				args[1] = fsm;
				try {
					Boolean r = (Boolean) relatedmethod.invoke(null, args);
					b = r;
				} catch (Exception e) {
					 e.printStackTrace();
					throw new RuntimeException("action error", e);
				}
			}
		}
		return b;
	}
	*/
	
	public boolean evaluate(FSMMachineInstance fsm, FSMStateInstance state, VexNode vex)
	{
		if (vex.getName().startsWith("doWhile_head_") || vex.getName().startsWith("if_out_"))
			return false;
		boolean b = false;
		List evaluationResults = null;
		SimpleNode treenode = vex.getTreenode();
		// xpath不处理那些尾节点
		if (vex.isBackNode()) {
			return b;
		}
		try
		{
			// for(;i<n;) or while(i<n) or do{}while(i < n)
			if (fsm.getFSMMachine().getName().equalsIgnoreCase("TD")
					&& (vex.getName().startsWith("for_head_") || vex.getName().startsWith("while_head_") || vex.getName().startsWith(
							"doWhile_out_"))
					&& (state.getState().toString().equalsIgnoreCase("fromout") || state.getState().toString().equalsIgnoreCase("error")))
			{
				treenode = (SimpleNode) treenode.jjtGetParent();
				List<SimpleNode> mylist = new LinkedList<SimpleNode>();
				mylist.add(treenode);
				evaluationResults = mylist;
			} else
			{
				
				XPath xpath = new BaseXPath(this.xpath, new DocumentNavigator());
				if (treenode instanceof ASTSelectionStatement)
				{
					treenode = (SimpleNode) treenode.jjtGetChild(0);
				} else if (treenode instanceof ASTIterationStatement && treenode.getImage() != "for")
				{
					treenode = (SimpleNode) treenode.jjtGetChild(0);
				} else if (treenode instanceof ASTIterationStatement && treenode.getImage() == "for")
				{
					List results = treenode.findDirectChildOfType(ASTExpression.class);
					if (!results.isEmpty())
					{
						treenode = (SimpleNode) results.get(0);
					}
				}

				evaluationResults = xpath.selectNodes(treenode);
			}

		} catch (JaxenException e)
		{
			e.printStackTrace();
			throw new RuntimeException("xpath error");
		}
		if (evaluationResults != null && evaluationResults.size() > 0)
		{
			if (relatedmethod == null)
			{
				b = true;
			} else
			{
				Object[] args = new Object[2];
				args[0] = evaluationResults;
				args[1] = fsm;
				try
				{
					Boolean r = (Boolean) relatedmethod.invoke(null, args);
					b = r;
				} catch (Exception e)
				{
					e.printStackTrace();
					throw new RuntimeException("action error");
				}
			}
		}
		return b;
	}
	
	/** 对条件进行计算，判断其是否满足, 匹配当前的抽象语法树节点，用于全局检测或者文件范围内检测的状态机 */
	public boolean evaluate(FSMMachineInstance fsm, FSMStateInstance state, SimpleNode treenode) {
		boolean b = false;
		List evaluationResults = null;
		
		try {
			XPath xpath = new BaseXPath(this.xpath, new DocumentNavigator());
			treenode = treenode.getConcreteNode();
			// func_decl_def, 不做处理是C89的特殊参数声明方式
			if (treenode == null) {
				return false;
			}
			evaluationResults = xpath.selectNodes(treenode);

		} catch (JaxenException e) {
			 e.printStackTrace();
			throw new RuntimeException("xpath error",e);
		}
		
		if (evaluationResults != null && evaluationResults.size() > 0) {
			if (relatedmethod == null) {
				b = true;
			} else {
				Object[] args = new Object[2];
				args[0] = evaluationResults;
				args[1] = fsm;
				try {
					Boolean r = (Boolean) relatedmethod.invoke(null, args);
					b = r;
				} catch (Exception e) {
					 e.printStackTrace();
					throw new RuntimeException("action error", e);
				}
			}
		}
		return b;
	}

	/** 解析xml */
	@Override
	public void loadXML(Node n) {
		Node value = n.getAttributes().getNamedItem("Value");
		if (value == null) {
			throw new RuntimeException("Xpath condition must have a value.");
		}
		xpath = value.getNodeValue();
		if (fsm != null && fsm.getRelatedClass() != null) {
			loadAction(n, fsm.getRelatedClass());
		}
	}
}
