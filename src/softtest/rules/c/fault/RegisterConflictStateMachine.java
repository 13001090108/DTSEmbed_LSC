package softtest.rules.c.fault;

import java.util.LinkedList;
import java.util.List;

import softtest.ast.c.ASTFunctionDefinition;
import softtest.ast.c.ASTInterrupt;
import softtest.ast.c.ASTPRAGMA;
import softtest.ast.c.ASTPrimaryExpression;
import softtest.ast.c.ASTStatement;
import softtest.ast.c.ASTUsing;
import softtest.ast.c.Node;
import softtest.ast.c.SimpleNode;
import softtest.fsm.c.FSMMachine;
import softtest.fsm.c.FSMMachineInstance;
import softtest.rules.c.StateMachineUtils;
import softtest.symboltable.c.MethodNameDeclaration;
import softtest.symboltable.c.VariableNameDeclaration;

/**
 * 中断函数中调用其它函数（普通函数），必须和中断使用相同的寄存器组
 * @author zys	
 * 2010-3-11
 */
public class RegisterConflictStateMachine {
	
	private static final String ARGS="NOAREGS";
	private static boolean isCallOK=false;
	/**
	 * 检测当前函数定义节点是否为中断函数
	 * @param nodes
	 * @param fsmin
	 * @return
	 */
	public static List<FSMMachineInstance> checkIsInterruptMethod(SimpleNode node, FSMMachine fsm)
	{
		List<FSMMachineInstance> list=new LinkedList<FSMMachineInstance>();
		
		String usingRegisterNum="0";
		String interruptPriority;
			if(node instanceof ASTFunctionDefinition)
			{
				//判断是否为中断函数：根据其结点是否包含interrupt
				List temp=node.findChildrenOfType(ASTInterrupt.class);
				if(temp.size()>0)
				{
					//中断优先级
					ASTInterrupt interruptNode=(ASTInterrupt)temp.get(0);
					interruptPriority=interruptNode.getInternum();
					
					//查看中断函数是否指定了与主程序不同的寄存器组，目前主程序寄存器组默认为0
					Node usingNode=interruptNode.getNextSibling();
					if(usingNode instanceof ASTUsing)
					{
						usingRegisterNum=((ASTUsing)usingNode).getUsingnum();
						if(Integer.parseInt(usingRegisterNum)==0){
							isCallOK=true;
							return list;
						}
						addFSM(list, node, fsm, Integer.parseInt(interruptPriority), Integer.parseInt(usingRegisterNum));
					}
				}
			}
		return list;
	}
	
	/**
	 * 检测在中断函数内部调用外部普通函数时，是否加入了控制参数对
	 * @param nodes
	 * @param fsmin
	 * @return
	 */
	public static boolean checkCallOuterFunctionOK(List nodes, FSMMachineInstance fsmin)
	{
		return isCallOuterFunctionOK(nodes, fsmin);
	}
	
	public static boolean checkCallOuterFunctionError(List nodes, FSMMachineInstance fsmin)
	{
		
		return !isCallOuterFunctionOK(nodes, fsmin);
	}
	
	private static int num=1;
	private static void addFSM(List<FSMMachineInstance> list, SimpleNode node, FSMMachine fsm,int priority,int usingRegister) {
		FSMMachineInstance fsminstance = fsm.creatInstance();
		MethodNameDeclaration varDecl = ((ASTFunctionDefinition)node).getDecl();
		fsminstance.setRelatedASTNode(node);
		fsminstance.setReleatedVexNode(node.getCurrentVexNode());
		fsminstance.setDesp("函数" + varDecl.getImage() + "声明为中断函数,中断优先级为"+priority
				+",使用的寄存器组为"+(usingRegister==0?"0(默认寄存器组)":usingRegister));
		list.add(fsminstance);
	}
	
	private static boolean isCallOuterFunctionOK(List nodes, FSMMachineInstance fsmin)
	{
		if(isCallOK)
			return true;
		for(Object node:nodes)
		{
			if(node instanceof ASTPrimaryExpression)
			{
				Node statementNode=((ASTPrimaryExpression)node).getFirstParentOfType(ASTStatement.class);
				Node prevStatementNode=((ASTStatement)statementNode).getPrevSibling();
				if(prevStatementNode instanceof ASTStatement)
				{
					Node pragmaNode=prevStatementNode.jjtGetChild(0);
					if(pragmaNode instanceof ASTPRAGMA)
					{
						boolean b=((ASTPRAGMA)pragmaNode).pragmaInfoStringList().trim().equals(ARGS);
						return b;
					}
				}
				
			}
		}
		return false;
	}
}
