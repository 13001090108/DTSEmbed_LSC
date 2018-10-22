

/*package softtest.rules.c.fault;

import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;
import softtest.fsm.c.FSMMachine;
import softtest.fsm.c.FSMMachineInstance;
import softtest.rules.c.StateMachineUtils;
import softtest.domain.c.analysis.*;
import softtest.domain.c.symbolic.*;
import softtest.domain.c.interval.*;
import softtest.ast.c.*;


//
 // @author songying
 // illegal calculation,ILC,非法计算,除零错
 //2010-04-13
//
public class ILCStateMachine {
	
	public static List<FSMMachineInstance> createILCStateMachines(SimpleNode node, FSMMachine fsm) 
	{
		List<FSMMachineInstance> list = new LinkedList<FSMMachineInstance>();
		String xPath = ".//MultiplicativeExpression[@Operators='/'] "
			+"| .//AssignmentExpression[./AssignmentOperator[@Operators='/=']]"
			+".//PostfixExpression[./PrimaryExpression[@Image = 'sqrt']]";
		
		List<SimpleNode> evaluationResults = StateMachineUtils.getEvaluationResults(node, xPath);
		for(SimpleNode snode : evaluationResults)  
		{
			FSMMachineInstance fsminstance = fsm.creatInstance();
			fsminstance.setRelatedASTNode(snode);
			fsminstance.setReleatedVexNode(snode.getCurrentVexNode());
			fsminstance.setDesp("第"+node.getBeginLine()+"行可能存在非法计算错误");
			list.add(fsminstance);
		}	
		
		return list;
	}

	
	public static boolean checkSqrtExpression(List nodes, FSMMachineInstance fsmin)
	{
		Iterator nodeIterator = nodes.iterator();
		while(nodeIterator.hasNext())
		{
			ASTExpression snode = (ASTExpression) nodeIterator.next();
			SimpleNode nodesqrt = (SimpleNode)snode.jjtGetChild(1).jjtGetChild(0);
			System.out.println(nodesqrt);//AssignmentExpression
			
			ExpressionValueVisitor expvst = new ExpressionValueVisitor();
			ExpressionVistorData visitdata = new ExpressionVistorData();
			visitdata.currentvex = nodesqrt.getCurrentVexNode();//yuan:snode.getCurrentVexNode();
			
			visitdata.currentvex.setfsmCompute(true);
			expvst.visit(nodesqrt, visitdata);
			visitdata.currentvex.setfsmCompute(false);
			
			Expression value1 = visitdata.value;
			Domain mydomain = value1.getDomain(visitdata.currentvex.getLastsymboldomainset());
			System.out.println(mydomain);
			
			IntegerDomain intNegdomain = new IntegerDomain(Long.MIN_VALUE, 0, false, true);
			DoubleDomain doubleNegdomain = new DoubleDomain(Double.MIN_VALUE, 0, false, true);
			if ( ( (mydomain instanceof IntegerDomain) && ((IntegerDomain)mydomain).contains(intNegdomain) ) || ( (mydomain instanceof DoubleDomain) && ((DoubleDomain)mydomain).contains(doubleNegdomain) )  )
				
			{
				return true;
			}
			
		}
		return false;
	}
}

*/


package softtest.rules.c.fault;

import java.util.LinkedList;
import java.util.List;
import softtest.fsm.c.FSMMachine;
import softtest.fsm.c.FSMMachineInstance;
import softtest.rules.c.StateMachineUtils;
import softtest.domain.c.analysis.*;
import softtest.domain.c.symbolic.*;
import softtest.domain.c.interval.*;
import softtest.ast.c.*;

/**
 * @author songying
 * illegal calculation,ILC,非法计算（除零错 负数开平方）
 *2010-04-13
 */
public class ILCStateMachine {
	
	public static List<FSMMachineInstance> createILCStateMachines(SimpleNode node, FSMMachine fsm) 
	{
		List<FSMMachineInstance> list = new LinkedList<FSMMachineInstance>();
		String xPath = ".//MultiplicativeExpression[@Operators='/'] "
			+"| .//AssignmentExpression[./AssignmentOperator[@Operators='/=']]";
		
		List<SimpleNode> evaluationResults = StateMachineUtils.getEvaluationResults(node, xPath);
		for(SimpleNode snode : evaluationResults)  //除零错
		{
			SimpleNode exp=null;
			if (snode instanceof ASTMultiplicativeExpression)
			{
				exp=(AbstractExpression) snode.jjtGetChild(1);
			}
			else if(snode instanceof ASTAssignmentExpression)
			{
				exp=(AbstractExpression) snode.jjtGetChild(2);
			}
			
			ExpressionValueVisitor expvst = new ExpressionValueVisitor();
			ExpressionVistorData visitdata = new ExpressionVistorData();
			visitdata.currentvex = exp.getCurrentVexNode();//yuan:snode.getCurrentVexNode();
			//visitdata.currentvex = snode.getCurrentVexNode();
			//visitdata.sideeffect = true;

			visitdata.currentvex.setfsmCompute(true);
			expvst.visit(exp, visitdata);
			visitdata.currentvex.setfsmCompute(false);
			
			Expression value1 = visitdata.value;
			Domain mydomain = value1.getDomain(visitdata.currentvex.getLastsymboldomainset());
			if ((mydomain instanceof IntegerDomain && ((IntegerDomain) mydomain).contains(0))||(mydomain instanceof DoubleDomain && ((DoubleDomain) mydomain).contains(0)) )
			{
				addFSM(list, snode, fsm,mydomain);
			}
		}
		/*----------------------sqrt(neg)----------------------------*/
		xPath = ".//PostfixExpression[./PrimaryExpression[@Image = 'sqrt']]";
		evaluationResults = StateMachineUtils.getEvaluationResults(node, xPath);
		for(SimpleNode snode : evaluationResults)
		{
			SimpleNode nodesqrt = (SimpleNode)snode.jjtGetChild(1).jjtGetChild(0);
			//System.out.println(nodesqrt);//AssignmentExpression
			
			ExpressionValueVisitor expvst = new ExpressionValueVisitor();
			ExpressionVistorData visitdata = new ExpressionVistorData();
			visitdata.currentvex = nodesqrt.getCurrentVexNode();//yuan:snode.getCurrentVexNode();
			
			visitdata.currentvex.setfsmCompute(true);
			expvst.visit(nodesqrt, visitdata);
			visitdata.currentvex.setfsmCompute(false);
			
			Expression value1 = visitdata.value;
			Domain mydomain = value1.getDomain(visitdata.currentvex.getLastsymboldomainset());
			System.out.println(mydomain);
			
			IntegerDomain intNegdomain = new IntegerDomain(Long.MIN_VALUE, 0, false, true);
			DoubleDomain doubleNegdomain = new DoubleDomain(Double.MIN_VALUE, 0, false, true);
			//if ( ( (mydomain instanceof IntegerDomain) && ((IntegerDomain)mydomain).contains(intNegdomain) ) || ( (mydomain instanceof DoubleDomain) && ((DoubleDomain)mydomain).contains(doubleNegdomain) )  )
			if ( mydomain instanceof IntegerDomain )	
			{
				IntegerDomain intdomain = (IntegerDomain)mydomain;
				if( ! IntegerDomain.intersect(intdomain, intNegdomain).isEmpty() )
				System.out.println("int");
				addFSM(list, snode, fsm,mydomain);
			}
			else if ( mydomain instanceof DoubleDomain )	
			{
				DoubleDomain doubledomain = (DoubleDomain)mydomain;
				System.out.println("double");
				if( ! DoubleDomain.intersect(doubledomain, doubleNegdomain).isEmpty() )
				System.out.println("double");
				addFSM(list, snode, fsm,mydomain);
			}
		}
		
		return list;
	}
	private static void addFSM(List<FSMMachineInstance> list, SimpleNode node, FSMMachine fsm, Domain mydomain) {
		FSMMachineInstance fsminstance = fsm.creatInstance();
		fsminstance.setRelatedASTNode(node);
		fsminstance.setReleatedVexNode(node.getCurrentVexNode());
		fsminstance.setDesp("位于第"+node.getBeginLine()+"行的表达式,其区间为"+mydomain.toString()+",有可能存在非法计算");
		list.add(fsminstance);
	}
	
	public static boolean checkSqrtExpression(List nodes, FSMMachineInstance fsmin)
	{
		List<SimpleNode> evaluationResults = nodes;
		for(SimpleNode snode : evaluationResults)
		{
			SimpleNode nodesqrt = (SimpleNode)snode.jjtGetChild(1).jjtGetChild(0);
			System.out.println(nodesqrt);//AssignmentExpression
			
			ExpressionValueVisitor expvst = new ExpressionValueVisitor();
			ExpressionVistorData visitdata = new ExpressionVistorData();
			visitdata.currentvex = nodesqrt.getCurrentVexNode();//yuan:snode.getCurrentVexNode();
			
			visitdata.currentvex.setfsmCompute(true);
			expvst.visit(nodesqrt, visitdata);
			visitdata.currentvex.setfsmCompute(false);
			
			Expression value1 = visitdata.value;
			Domain mydomain = value1.getDomain(visitdata.currentvex.getLastsymboldomainset());
			System.out.println(mydomain);
			
			IntegerDomain intNegdomain = new IntegerDomain(Long.MIN_VALUE, 0, false, true);
			DoubleDomain doubleNegdomain = new DoubleDomain(Double.MIN_VALUE, 0, false, true);
			if ( ( (mydomain instanceof IntegerDomain) && ((IntegerDomain)mydomain).contains(intNegdomain) ) || ( (mydomain instanceof DoubleDomain) && ((DoubleDomain)mydomain).contains(doubleNegdomain) )  )
				
			{
				return true;
			}
			
		}
		return false;
	}
}


	
	