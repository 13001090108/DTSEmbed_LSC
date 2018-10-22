package softtest.domain.c.analysis;

import java.io.Serializable;
import java.util.ArrayList;
import java.util.List;

import softtest.ast.c.ASTEqualityExpression;
import softtest.ast.c.ASTExpression;
import softtest.ast.c.ASTPrimaryExpression;
import softtest.ast.c.ASTRelationalExpression;
import softtest.ast.c.AbstractExpression;
import softtest.ast.c.Node;
import softtest.ast.c.SimpleNode;
import softtest.cfg.c.VexNode;
import softtest.config.c.Config;
import softtest.domain.c.interval.Domain;
import softtest.domain.c.interval.DomainType;
import softtest.symboltable.c.VariableNameDeclaration;

/**
 * 循环迭代抽象类
 * @author zys	
 * 2010-5-17
 */
public abstract class IterationCalculation implements Serializable {
	/** 一次迭代后，循环条件中变量区间是否发生改变*/
	boolean domainChanged=true;
	
	/**标识循环迭代是否应该终止 */
	boolean calculateOver=false;
	
	/** 记录循环条件中变量每次迭代后的区间，以备下次迭代时widening*/
	transient Domain lastDomain=null;
	
	/** 保存当前节点每次迭代后所有变量的区间，以务下次迭代时widening（主要是针对非循环条件中的变量）*/
	transient VarDomainSet lastVarDomainSet=null;
	
	int counter=0;
	
	/** 对循环进行迭代，参数为循环头结点：while_head,for_head,do_while_out1*/
	public abstract void iterationExec(VexNode iterationHead);

	/** 每次widening或narrowing迭代终止后，清空临时数据结构释放内存*/
	public void clear()
	{
		if(lastVarDomainSet!=null)
			lastVarDomainSet.clearDomainSet();
		if(lastDomain!=null)
			lastDomain=null;
	}
	
	/**暂时只处理简单循环，如while(i<100 && j<100 || k>100)，取循环条件中的变量 */
	public List<VariableNameDeclaration> getLeftVar(VexNode iterationHead)
	{
		List<VariableNameDeclaration> varList=new ArrayList<VariableNameDeclaration>();
		List<Node> expressionList=getRelationalExpression(iterationHead);
		for(Node node : expressionList){
			AbstractExpression expressionNode=null;
			if(node instanceof ASTRelationalExpression)
				expressionNode=(ASTRelationalExpression)node;
			else if(node instanceof ASTEqualityExpression)
				expressionNode=(ASTEqualityExpression)node;
			ASTPrimaryExpression priExpr=(ASTPrimaryExpression) ((SimpleNode)(expressionNode.jjtGetChild(0))).getFirstChildOfType(ASTPrimaryExpression.class);
			if(priExpr!=null && priExpr.getVariableNameDeclaration()!=null)
				varList.add(priExpr.getVariableNameDeclaration());
		}
		return varList;
	}
	
	/** 获取循环中的条件表达式*/
	private List<Node> getRelationalExpression(VexNode iterationHead)
	{
		List<Node> relationExprList=new ArrayList<Node>();
		
		String nodeName=iterationHead.getName();
		SimpleNode treeNode=iterationHead.getTreenode();
		ASTExpression expressionNode=null;
		if(nodeName.startsWith("while_head")){
			expressionNode=(ASTExpression) treeNode.jjtGetChild(0);
		}else if(nodeName.startsWith("for_head")){
			if(treeNode.forChild[1]){
				if(treeNode.forChild[0]){
					expressionNode=(ASTExpression) treeNode.jjtGetChild(1);
				}else{
					expressionNode=(ASTExpression) treeNode.jjtGetChild(0);
				}
			}
		}else if(nodeName.startsWith("do_while_out1"))
		{
			expressionNode=(ASTExpression) treeNode;
		}
		if(expressionNode==null)
			return null;
		//for(;i<5;i++)
		relationExprList=expressionNode.findChildrenOfType(ASTRelationalExpression.class);
		//for(;i==5;i++)
		expressionNode.findChildrenOfType(ASTEqualityExpression.class, relationExprList);
		
		return relationExprList;
	}
	
	public boolean isDomainChanged(Domain lastDomain, Domain thisDomain) {
		boolean ret=true;
		DomainType domainType=lastDomain.getDomaintype();
		switch(domainType)
		{
		case INTEGER:
		case DOUBLE:
			if(lastDomain.equals(thisDomain))
				ret=false;
			break;
		case POINTER:
			break;
		case UNKNOWN:
			break;
		default:
			break;
		}
		
		return ret;
	}
	
	public boolean isIterationOver() {
		if(counter>=Config.LOOPNUM)
			return false;
		return domainChanged&&!calculateOver;
	}

	public void setDomainChanged(boolean domainChanged) {
		this.domainChanged = domainChanged;
	}

	public Domain getLastDomain() {
		return lastDomain;
	}

	public void setLastDomain(Domain lastDomain) {
		this.lastDomain = lastDomain;
	}

	public VarDomainSet getLastVarDomainSet() {
		return lastVarDomainSet;
	}

	public void setLastVarDomainSet(VarDomainSet lastVarDomainSet) {
		this.lastVarDomainSet = lastVarDomainSet;
	}
}
